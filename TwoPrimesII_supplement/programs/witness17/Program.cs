// An explicit witness from a lattice certificate, by rounding in the certificate basis.
// How the digits are found does not matter: the integer k is verified exactly at the end.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;

using var doc = JsonDocument.Parse(File.ReadAllText(args[0]), new JsonDocumentOptions { MaxDepth = 64 });
var root = doc.RootElement;
BigInteger Big(JsonElement e) => BigInteger.Parse(e.ValueKind == JsonValueKind.String ? e.GetString() : e.GetRawText());
BigInteger D = Big(root.GetProperty("D"));
int s = (int)Big(root.GetProperty("s")), t = (int)Big(root.GetProperty("t"));
var sel = root.GetProperty("selected_digits").EnumerateArray()
    .Select(e => (prime: (int)Big(e.GetProperty("prime")), j: (int)Big(e.GetProperty("j")))).ToList();
var B = root.GetProperty("basis").EnumerateArray().Select(r => r.EnumerateArray().Select(Big).ToArray()).ToArray();
int h = sel.Count;
BigInteger Pw(int b, int e) => BigInteger.Pow(b, e);
BigInteger u = Pw(3, s * s);
var w = sel.Select(x => Pw(x.prime, (x.j - 1) * (x.j - 1))).ToArray();
var N = sel.Select(x => 2 * (Pw(x.prime, 2 * x.j - 1) / D) + 1).ToArray();
foreach (var row in B)
{
    BigInteger a = 0;
    for (int j = 0; j < h; j++) a += row[j] * w[j];
    if (!(a % u).IsZero) throw new Exception("row not in the lattice");
}
var width = new BigInteger[h];
for (int j = 0; j < h; j++) for (int i = 0; i < h; i++) width[j] += BigInteger.Abs(B[i][j]);

double Ratio(BigInteger a, BigInteger b) => a.IsZero ? 0 : a.Sign * Math.Exp(BigInteger.Log(BigInteger.Abs(a)) - BigInteger.Log(b));

// inverse of the scaled basis B[i][j] / N[j]
var M = new double[h, 2 * h];
for (int i = 0; i < h; i++)
{
    for (int j = 0; j < h; j++) M[i, j] = Ratio(B[i][j], N[j]);
    M[i, h + i] = 1;
}
for (int c = 0; c < h; c++)
{
    int piv = c;
    for (int r = c + 1; r < h; r++) if (Math.Abs(M[r, c]) > Math.Abs(M[piv, c])) piv = r;
    for (int k = 0; k < 2 * h; k++) (M[c, k], M[piv, k]) = (M[piv, k], M[c, k]);
    double inv = 1 / M[c, c];
    for (int k = 0; k < 2 * h; k++) M[c, k] *= inv;
    for (int r = 0; r < h; r++)
    {
        if (r == c) continue;
        double f = M[r, c];
        if (f == 0) continue;
        for (int k = 0; k < 2 * h; k++) M[r, k] -= f * M[c, k];
    }
}

// Reduce a representative d of the residue c modulo the rows.
BigInteger[] Reduce(BigInteger c, out int rounds)
{
    int p0 = sel.FindIndex(x => x.prime == 2);
    // inverse of w[p0] modulo u = 3^R, by Euler's theorem
    BigInteger inv = BigInteger.ModPow(w[p0], u / 3 * 2 - 1, u);
    var d = new BigInteger[h];
    d[p0] = ((c % u + u) % u) * inv % u;
    for (rounds = 0; rounds < 5000; rounds++)
    {
        long e = long.MinValue;
        for (int j = 0; j < h; j++)
            if (!d[j].IsZero) e = Math.Max(e, (long)BigInteger.Abs(d[j]).GetBitLength() - (long)N[j].GetBitLength());
        int shift = (int)Math.Max(0, e - 40);
        var v = new double[h];
        for (int j = 0; j < h; j++) v[j] = Ratio(d[j] >> shift, N[j]);
        var x = new BigInteger[h];
        bool any = false;
        for (int i = 0; i < h; i++)
        {
            double acc = 0;
            for (int j = 0; j < h; j++) acc += v[j] * M[j, h + i];
            x[i] = new BigInteger(Math.Round(acc));
            any |= !x[i].IsZero;
        }
        if (!any) break;
        for (int j = 0; j < h; j++)
        {
            BigInteger acc = 0;
            for (int i = 0; i < h; i++) if (!x[i].IsZero) acc += x[i] * B[i][j];
            d[j] -= acc << shift;
        }
    }
    return d;
}

(double value, int level) Norm(BigInteger k, int p)
{
    double best = 0; int at = 0;
    for (int m = 1; ; m++)
    {
        BigInteger mod = Pw(p, m * m);
        BigInteger r = k % mod; if (r.Sign < 0) r += mod;
        double val = Ratio(BigInteger.Min(r, mod - r), mod);
        if (val > best) { best = val; at = m; }
        // beyond this point the norm is |k| / mod and decreases
        if (mod > 2 * BigInteger.Abs(k) && Ratio(BigInteger.Abs(k), mod) <= best) break;
    }
    return (best, at);
}

Console.WriteLine($"D={D}  max (width/2)/N = {Enumerable.Range(0, h).Max(j => Ratio(width[j] / 2, N[j])):E6}");
BigInteger Witness(BigInteger target, bool print)
{
    var d = Reduce(target, out int rounds);
    BigInteger all = 0, pPart = 0;
    for (int j = 0; j < h; j++)
    {
        all += w[j] * d[j];
        if (sel[j].prime == 2) pPart += w[j] * d[j];
    }
    if (!((all - target) % u).IsZero) throw new Exception("wrong residue");
    BigInteger k = target - pPart;
    var (n3, m3) = Norm(k, 3);
    var (n2, m2) = Norm(k - target, 2);
    bool inBox = Enumerable.Range(0, h).All(j => BigInteger.Abs(d[j]) <= width[j] / 2);
    if (print)
    {
        Console.WriteLine($"target {(BigInteger.Abs(target) < 1000000 ? target.ToString() : "large")}: rounds {rounds}, all |d_j| <= width_j/2: {inBox}");
        Console.WriteLine($"  P_3(k) = {n3:E6} (level {m3})   P_2(k - t) = {n2:E6} (level {m2})");
        Console.WriteLine($"  log2|k| = {BigInteger.Log(BigInteger.Abs(k), 2):F3}   decimal digits {BigInteger.Abs(k).ToString().Length}");
        double L = -Math.Log(Math.Max(n3, n2));
        Console.WriteLine($"  ln|k| / ln^2(1/P) = {BigInteger.Log(BigInteger.Abs(k)) / (L * L):F4}");
    }
    return k;
}
var k1 = Witness(1, true);
File.WriteAllText(args[1], k1.ToString() + "\n");
Witness(-1, true);
Witness(12345, true);
Witness(Pw(2, 10000) + 7, true);

// A bound for every residue, from the column widths alone.
double Uniform(int p)
{
    double best = 0;
    for (int m = 1; m <= 200; m++)
    {
        BigInteger acc = 0;
        for (int j = 0; j < h; j++)
            if (sel[j].prime == p && sel[j].j <= m) acc += Pw(p, (sel[j].j - 1) * (sel[j].j - 1)) * (width[j] / 2);
        best = Math.Max(best, Ratio(acc, Pw(p, m * m)));
    }
    return best;
}
BigInteger zMax = 0, yMax = 0;
for (int j = 0; j < h; j++)
{
    var term = w[j] * (width[j] / 2);
    if (sel[j].prime == 2) zMax += term; else yMax += term;
}
Console.WriteLine($"uniform: digit-sum norm bounds  q: {Uniform(3):E6}  p: {Uniform(2):E6}");
Console.WriteLine($"uniform: log2 of the largest |z| = {BigInteger.Log(zMax, 2):F3}, of the largest |y| = {BigInteger.Log(yMax, 2):F3}");
Console.WriteLine($"uniform: log2 of 3^((s+1)^2) = {BigInteger.Log(Pw(3, (s + 1) * (s + 1)), 2):F3}");

// exact certification of the uniform bounds
bool good = true;
var ten18 = BigInteger.Pow(10, 18);
foreach (int p in new[] { 3, 2 })
    for (int m = 1; m <= 200; m++)
    {
        BigInteger acc = 0;
        for (int j = 0; j < h; j++)
            if (sel[j].prime == p && sel[j].j <= m) acc += Pw(p, (sel[j].j - 1) * (sel[j].j - 1)) * (width[j] / 2);
        good &= acc * ten18 < 7 * Pw(p, m * m);
    }
Console.WriteLine($"exact: both digit-sum norms below 7e-18 at every level up to 200: {good}");
Console.WriteLine($"exact: no selected digit above level 200: {sel.All(x => x.j <= 200)}");
Console.WriteLine($"exact: |z| < 2^10143: {zMax < Pw(2, 10143)}   |y| < 2^10077: {yMax < Pw(2, 10077)}");
var T = Pw(2, 10300);
// levels m >= 81 of the base 3: the norm of k = t + z is at most |k| / 3^6561
var error = T + zMax;
Console.WriteLine($"exact: (2^10300 + |z|) * 10^18 < 7 * 3^6561, so levels above 80 are below 7e-18: {error * ten18 < 7 * Pw(3, 6561)}");

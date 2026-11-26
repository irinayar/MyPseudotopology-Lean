// Independent check of a mixed-digit lattice certificate for kappa.
// Only D, s, t, the selected (prime, index) pairs and the integer matrix are read from the file.
// Everything else is recomputed. The determinant is certified by Gaussian elimination modulo
// many primes and a Hadamard bound.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;

if (args.Length < 1) { Console.Error.WriteLine("usage: basis124 certificate.json"); return 2; }
using var doc = JsonDocument.Parse(File.ReadAllText(args[0]), new JsonDocumentOptions { MaxDepth = 64 });
var root = doc.RootElement;
BigInteger Big(JsonElement e) => BigInteger.Parse(e.ValueKind == JsonValueKind.String ? e.GetString() : e.GetRawText());

BigInteger D = Big(root.GetProperty("D"));
int s = (int)Big(root.GetProperty("s")), t = (int)Big(root.GetProperty("t"));
const int p = 2, q = 3;
var sel = root.GetProperty("selected_digits").EnumerateArray()
    .Select(e => (prime: (int)Big(e.GetProperty("prime")), j: (int)Big(e.GetProperty("j")))).ToList();
var B = root.GetProperty("basis").EnumerateArray()
    .Select(row => row.EnumerateArray().Select(Big).ToArray()).ToArray();
int h = sel.Count;
bool ok = true;
void Check(bool c, string name) { Console.WriteLine($"{(c ? "pass" : "FAIL")}  {name}"); ok &= c; }

Console.WriteLine($"D={D} s={s} t={t} h={h}");
Check(B.Length == h && B.All(r => r.Length == h), "matrix is h by h");
Check(sel.Distinct().Count() == h, "selected digits are distinct");
Check(sel.All(x => (x.prime == p && x.j >= 1 && x.j <= t) || (x.prime == q && x.j >= 1 && x.j <= s)),
      "p indices at most t, q indices at most s");

BigInteger Pw(int b, int e) => BigInteger.Pow(b, e);
bool IsPower(BigInteger x, int b) { while (x % b == 0) x /= b; return x.IsOne; }
BigInteger u = Pw(q, s * s), v = Pw(p, t * t);
Check(D >= BigInteger.Max(100, 2 * q * q) && !IsPower(D, p) && !IsPower(D, q), "D >= max(100,2q^2) and regular");
Check(v >= 20 * D * u, "v >= 20 D u");
Check(D * D * v < BigInteger.Min(Pw(q, (s + 1) * (s + 1)), Pw(p, (t + 1) * (t + 1))), "D v below both caps");

var N = sel.Select(x => 2 * (Pw(x.prime, 2 * x.j - 1) / D) + 1).ToArray();
var w = sel.Select(x => Pw(x.prime, (x.j - 1) * (x.j - 1)) % u).ToArray();
Check(N.All(n => n > 1), "every selected digit is active");
Check(sel.Select((x, i) => x.prime == p && !(w[i] % q).IsZero).Any(b => b), "some weight is a unit mod u");

bool congr = true;
foreach (var row in B)
{
    BigInteger acc = 0;
    for (int j = 0; j < h; j++) acc += row[j] * w[j];
    congr &= (acc % u).IsZero;
}
Check(congr, "every row lies in the congruence lattice");

// Hadamard bound in bits (an upper bound: each squared row norm < 2^(its bit length)).
long hadBits = 0;
foreach (var row in B)
{
    BigInteger sq = 0;
    foreach (var x in row) sq += x * x;
    hadBits += ((long)sq.GetBitLength() + 1) / 2;
}
long need = Math.Max(hadBits, (long)u.GetBitLength()) + 2;
bool IsPrime(long n) { if (n < 2) return false; for (long d = 2; d * d <= n; d++) if (n % d == 0) return false; return true; }
long PowMod(long a, long e, long m) { long r = 1; a %= m; while (e > 0) { if ((e & 1) == 1) r = r * a % m; a = a * a % m; e >>= 1; } return r; }
long prime = 2147483647L;
double bits = 0; int used = 0, plus = 0, minus = 0, other = 0;
while (bits <= need)
{
    while (!IsPrime(prime)) prime--;
    long m = prime;
    var A = B.Select(r => r.Select(x => { var y = (long)(x % m); return y < 0 ? y + m : y; }).ToArray()).ToArray();
    long det = 1;
    for (int c = 0; c < h; c++)
    {
        int piv = -1;
        for (int r = c; r < h; r++) if (A[r][c] != 0) { piv = r; break; }
        if (piv < 0) { det = 0; break; }
        if (piv != c) { (A[piv], A[c]) = (A[c], A[piv]); det = (m - det) % m; }
        det = det * A[c][c] % m;
        long inv = PowMod(A[c][c], m - 2, m);
        for (int r = c + 1; r < h; r++)
        {
            long f = A[r][c] * inv % m;
            if (f == 0) continue;
            for (int k = c; k < h; k++) A[r][k] = (A[r][k] - f * A[c][k] % m + m) % m;
        }
    }
    long um = (long)(u % m);
    if (det == um) plus++; else if (det == (m - um) % m) minus++; else other++;
    bits += Math.Log2(m); used++; prime--;
}
Console.WriteLine($"Hadamard bound below 2^{hadBits}; primes used {used}, product above 2^{(long)bits}");
Check(other == 0 && (plus == used || minus == used), "determinant equals +u or -u (certified)");

// Column widths and the exact rationals U, L, E.
var width = new BigInteger[h];
for (int j = 0; j < h; j++) for (int i = 0; i < h; i++) width[j] += BigInteger.Abs(B[i][j]);
BigInteger den = 1, upNum = 1, loNum = 1;
bool allPos = true;
for (int j = 0; j < h; j++)
{
    den *= N[j];
    upNum *= N[j] + width[j] - 1;
    var lo = N[j] - width[j] + 1;
    allPos &= lo > 0;
    loNum *= BigInteger.Max(lo, 0);
}
Check(allPos, "every width is below N+1");
// E = (U-1)(1-L) = eNum / eDen
BigInteger eNum = (upNum - den) * (den - loNum), eDen = den * den;
string Dec(BigInteger a, BigInteger b, int k) { var z = a * Pw(10, k) / b; var str = z.ToString().PadLeft(k + 1, '0'); return str[..^k] + "." + str[^k..]; }
Console.WriteLine($"U = {Dec(upNum, den, 20)}\nL = {Dec(loNum, den, 20)}\nE = {Dec(eNum, eDen, 20)}");
double sumAlpha = 0;
for (int j = 0; j < h; j++) sumAlpha += Math.Exp(BigInteger.Log(width[j] - 1 > 0 ? width[j] - 1 : 1) - BigInteger.Log(N[j]));
Console.WriteLine($"sum of alpha about {sumAlpha:F10}");
Check(eNum * Pw(10, 12) < 282780231673 * eDen, "E < 0.282780231673");
// C <= (4/3)(1+5/D)(1+E)
BigInteger cNum = 4 * (D + 5) * (eDen + eNum), cDen = 3 * D * eDen;
Console.WriteLine($"energy bound = {Dec(cNum, cDen, 20)}");
Check(cNum * 1000 < 1711 * cDen, "C < 1.711");
// the same basis at a smaller radius parameter D1: the energy bound with D1
foreach (BigInteger D1 in new[] { BigInteger.Parse("900000000000000"), BigInteger.Parse("881127231234234") })
{
    var N1 = sel.Select(x => 2 * (Pw(x.prime, 2 * x.j - 1) / D1) + 1).ToArray();
    bool mono = Enumerable.Range(0, h).All(j => N1[j] >= N[j]);
    BigInteger c1 = 4 * (D1 + 5) * (eDen + eNum), d1 = 3 * D1 * eDen;
    Check(mono && c1 * 1000 < 1711 * d1 && v >= 20 * D1 * u, $"lengths do not decrease and C < 1.711 at D = {D1}");
}
// no power of p or q in [881127231234234, 10^15]
BigInteger lo0 = BigInteger.Parse("881127231234234"), hi0 = BigInteger.Parse("1000000000000000");
bool free = true;
foreach (int b in new[] { p, q }) { BigInteger z = 1; while (z <= hi0) { if (z >= lo0) free = false; z *= b; } }
Check(free, "no power of 2 or 3 in the interval");
Check(D == hi0, "certificate is for D = 10^15");
// height: ln(Dv) / ln^2 D, in floating point for display only
foreach (var D1 in new[] { D, lo0 })
    Console.WriteLine($"ln(D v)/ln^2 D at D={D1}: {BigInteger.Log(D1 * v) / Math.Pow(BigInteger.Log(D1), 2):F9}");
// collision criterion: targets |t| with |t| + 2X + 2 <= 2 L0, L0 >= (2X+1)/C
BigInteger X = D * v;
BigInteger L0 = ((2 * X + 1) * cDen + cNum - 1) / cNum;
Check(X / 3 + 2 * X + 2 <= 2 * L0, "every |t| <= X/3 satisfies the collision criterion");
Console.WriteLine(ok ? "ALL CHECKS PASSED" : "SOME CHECK FAILED");
return ok ? 0 : 1;

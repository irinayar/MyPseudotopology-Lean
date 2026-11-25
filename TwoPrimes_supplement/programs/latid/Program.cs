using System;
using System.Collections.Generic;
using System.Linq;

// latid: check of the identity E(A,B) = sum w(m,n) c(mu-nv) for two-sided uncut balls A=T_N(p), B=T_M(q)
// and measurement of (L)-type quantities: number of lattice points in the support of c, the part of E from (0,0),
// and R = E / (d0 * (|Y||Z|)^2) where d0 = (sum of w over the strip)/(2W+1) is the average weight per integer t.
// usage: latid p q D N M [validate]
class P
{
    static long Pow(long b, int e) { long r = 1; for (int i = 0; i < e; i++) r = checked(r * b); return r; }
    static long[] Digits(int ell, long D, int levels, out long[] Js)
    {
        var set = new List<long> { 0 }; Js = new long[levels + 1];
        for (int n = 1; n <= levels; n++)
        {
            long J = Pow(ell, 2 * n - 1) / D; Js[n] = J; long w = Pow(ell, (n - 1) * (n - 1));
            if (J == 0) continue;
            var next = new List<long>(set.Count * (int)(2 * J + 1));
            foreach (var s in set) for (long j = -J; j <= J; j++) next.Add(s + j * w);
            set = next;
        }
        return set.ToArray();
    }
    static void Main(string[] a)
    {
        int p = int.Parse(a[0]), q = int.Parse(a[1]); long D = long.Parse(a[2]); int N = int.Parse(a[3]), M = int.Parse(a[4]);
        bool validate = a.Length > 5;
        long[] JA, JB, JY, JZ;
        long[] A = Digits(p, D, N, out JA), B = Digits(q, D, M, out JB);
        long[] Y = Digits(p, D, N - 1, out JY), Z = Digits(q, D, M - 1, out JZ);
        long u = Pow(p, (N - 1) * (N - 1)), v = Pow(q, (M - 1) * (M - 1)); long jA = JA[N], jB = JB[M];
        long UY = Y.Max(), UZ = Z.Max(); long W = 2 * (UY + UZ);
        double sz = (double)Y.Length * Z.Length;
        if (sz > 2.5e7) { Console.WriteLine("too large |Y||Z|=" + sz); return; }
        // V = Z - Y multiset
        long[] V = new long[(long)Y.Length * Z.Length]; int idx = 0;
        foreach (var z in Z) foreach (var y in Y) V[idx++] = z - y;
        Array.Sort(V);
        var keys = new List<long>(); var cnt = new List<long>();
        for (int i = 0; i < V.Length;) { int j = i; while (j < V.Length && V[j] == V[i]) j++; keys.Add(V[i]); cnt.Add(j - i); i = j; }
        long[] K = keys.ToArray(); long[] f = cnt.ToArray(); V = null;
        Func<long, double> c = t =>
        { // sum_x f(x) f(x - t), two pointers
            double s = 0; int jp = 0;
            for (int i = 0; i < K.Length; i++)
            {
                long target = K[i] - t; while (jp < K.Length && K[jp] < target) jp++;
                if (jp < K.Length && K[jp] == target) s += (double)f[i] * f[jp];
            }
            return s;
        };
        double c0 = c(0);
        var pts = new List<(long m, long n, long t, double w)>();
        for (long m = -2 * jA; m <= 2 * jA; m++)
        {
            long t0 = m * u; long n0 = (long)Math.Round((double)t0 / v);
            for (long n = n0 - 1; n <= n0 + 1; n++)
            {
                if (Math.Abs(n) > 2 * jB) continue; long t = t0 - n * v;
                if (Math.Abs(t) <= W) pts.Add((m, n, t, (double)(2 * jA + 1 - Math.Abs(m)) * (2 * jB + 1 - Math.Abs(n))));
            }
        }
        double E = 0, F = 0; int pos = 0; double e00 = 0;
        foreach (var pt in pts) { double cv = c(pt.t); E += pt.w * cv; F += pt.w; if (cv > 0) pos++; if (pt.m == 0 && pt.n == 0) e00 = pt.w * cv; }
        double Omega = 2.0 * W + 1; double d0 = F / Omega; double Eeq = d0 * sz * sz;
        double lam_norm = (double)A.Length * B.Length;
        Console.WriteLine($"p={p} q={q} D={D} N={N} M={M}: |Y|={Y.Length} |Z|={Z.Length} J_A={jA} J_B={jB} u={u} v={v} W={W} |A|={A.Length} |B|={B.Length}");
        double bal = (double)jA * u / ((double)jB * v); Console.WriteLine($"  balance J_A u/(J_B v)={bal:F2} valid(W<v/2)={(2 * W < v)} count formula (4J_A+1)*min(1,2W/v)={(4.0 * jA + 1) * Math.Min(1.0, 2.0 * W / v):F1}"); Console.WriteLine($"  lattice points in strip: {pts.Count}, with c>0: {pos}, estimate 8J_A/D = {8.0 * jA / D:F1}");
        Console.WriteLine($"  E(identity)={E:E6}  part from (0,0)={e00 / E:F4}  E_eq={Eeq:E6}  R=E/E_eq={E / Eeq:F4}  c(0)/(|Y||Z|)^2*Omega={c0 * Omega / (sz * sz):F3}");
        if (validate)
        {
            var rA = new Dictionary<long, long>(); foreach (var x in A) foreach (var y in A) { long h = x - y; rA.TryGetValue(h, out long g); rA[h] = g + 1; }
            var rB = new Dictionary<long, long>(); foreach (var x in B) foreach (var y in B) { long h = x - y; rB.TryGetValue(h, out long g); rB[h] = g + 1; }
            double Ed = 0; foreach (var kv in rA) if (rB.TryGetValue(kv.Key, out long g)) Ed += (double)kv.Value * g;
            Console.WriteLine($"  E(direct)={Ed:E6}  identity {(Math.Abs(Ed - E) < 0.5 ? "OK" : "MISMATCH")}");
        }
    }
}

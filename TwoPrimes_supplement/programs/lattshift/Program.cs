using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;

// Unit-target height h_D(1) for {2,3} (floating-point enumeration, exact verification): least |k| with P_3(k) < 1/D and P_2(k-1) < 1/D,
// where P_p(x) = sup_{n>=1} || x / p^(n^2) ||.   Affine lattice enumeration (Fincke-Pohst with a shift),
// adapted from an earlier lattice enumeration program of the author.  Every candidate is verified in exact integers.
// usage:  lattshift D0 D1 [nodeCap] [startK]      |   lattshift brute D Kmax
class P {
  static BigInteger Pow(int p, int e) => BigInteger.Pow(p, e);
  static int Forced(int p, int D) { int a = 0; while (Pow(p, (a + 1) * (a + 1)) <= D) a++; return a; }
  static BigInteger Mod(BigInteger a, BigInteger m) { var r = BigInteger.Remainder(a, m); if (r < 0) r += m; return r; }
  static BigInteger Cent(BigInteger a, BigInteger m) { var r = Mod(a, m); if (2 * r > m) r -= m; return r; }
  // exact definition: all n >= 1 with p^(n^2) <= D(|x|+2)  (larger n are automatic)
  static bool Valid(BigInteger k, int D) {
    BigInteger ak = BigInteger.Abs(k);
    foreach (var (p, t) in new[] { (2, 1), (3, 0) }) {
      BigInteger x = k - t;
      for (int n = 1; ; n++) {
        BigInteger q = Pow(p, n * n); if (q > (ak + 2) * D) break;
        BigInteger rm = Mod(x, q); BigInteger dist = BigInteger.Min(rm, q - rm);
        if (dist * D >= q) return false;
      }
    }
    return true;
  }
  // ---- integral LLL (Cohen 2.6.7), delta = 3/4
  static void Lll(BigInteger[][] b) {
    int n = b.Length, kmax = 0, k = 1; var d = new BigInteger[n + 1]; var lam = new BigInteger[n][]; for (int i = 0; i < n; i++) lam[i] = new BigInteger[n];
    d[0] = 1; d[1] = Dot(b[0], b[0]);
    Action<int, int> red = (kk, l) => {
      if (2 * BigInteger.Abs(lam[kk][l]) > d[l + 1]) {
        BigInteger q = Round(lam[kk][l], d[l + 1]);
        for (int t = 0; t < b[kk].Length; t++) b[kk][t] -= q * b[l][t];
        lam[kk][l] -= q * d[l + 1]; for (int i = 0; i < l; i++) lam[kk][i] -= q * lam[l][i];
      }
    };
    while (k < n) {
      if (k > kmax) {
        kmax = k;
        for (int j = 0; j <= k; j++) {
          BigInteger u = Dot(b[k], b[j]);
          for (int i = 0; i < j; i++) u = (d[i + 1] * u - lam[k][i] * lam[j][i]) / d[i];
          if (j < k) lam[k][j] = u; else d[k + 1] = u;
        }
      }
      red(k, k - 1);
      if (4 * d[k + 1] * d[k - 1] < 3 * d[k] * d[k] - 4 * lam[k][k - 1] * lam[k][k - 1]) {
        var tmp = b[k]; b[k] = b[k - 1]; b[k - 1] = tmp;
        for (int j = 0; j < k - 1; j++) { var t = lam[k][j]; lam[k][j] = lam[k - 1][j]; lam[k - 1][j] = t; }
        BigInteger lm = lam[k][k - 1]; BigInteger B = (d[k - 1] * d[k + 1] + lm * lm) / d[k];
        for (int i = k + 1; i <= kmax; i++) { BigInteger t = lam[i][k]; lam[i][k] = (d[k + 1] * lam[i][k - 1] - lm * t) / d[k]; lam[i][k - 1] = (B * t + lm * lam[i][k]) / d[k + 1]; }
        d[k] = B; k = Math.Max(1, k - 1);
      } else {
        for (int l = k - 2; l >= 0; l--) red(k, l);
        k++;
      }
    }
  }
  static BigInteger Round(BigInteger a, BigInteger b) { BigInteger q = BigInteger.DivRem(2 * a + b, 2 * b, out var r); if (r < 0) q -= 1; return q; }
  static BigInteger Dot(BigInteger[] x, BigInteger[] y) { BigInteger s = 0; for (int i = 0; i < x.Length; i++) s += x[i] * y[i]; return s; }
  static double[] ToD(BigInteger[] x, BigInteger Z) { var r = new double[x.Length]; for (int t = 0; t < x.Length; t++) r[t] = (double)(BigInteger.Divide(x[t] << 50, Z)) / Math.Pow(2, 50); return r; }
  static void Gs(BigInteger[][] b, BigInteger Z, out double[][] v, out double[][] mu, out double[][] bs, out double[] nb) {
    int n = b.Length, m = b[0].Length; v = new double[n][]; for (int i = 0; i < n; i++) v[i] = ToD(b[i], Z);
    mu = new double[n][]; bs = new double[n][]; nb = new double[n];
    for (int i = 0; i < n; i++) { mu[i] = new double[n]; bs[i] = (double[])v[i].Clone(); for (int j = 0; j < i; j++) { double dot = 0; for (int t = 0; t < m; t++) dot += v[i][t] * bs[j][t]; mu[i][j] = dot / nb[j]; for (int t = 0; t < m; t++) bs[i][t] -= mu[i][j] * bs[j][t]; } double s = 0; for (int t = 0; t < m; t++) s += bs[i][t] * bs[i][t]; nb[i] = s; }
  }
  static long nodes, nodeCap;
  // all z with  max_t |sum_j z_j v_j[t] + wd[t]| <= 1 (box), via the Euclidean ball of radius^2 r2; w is Babai-reduced
  static List<long[]> Enumerate(double[][] v, double[][] mu, double[][] bs, double[] nb, double[] wd, double r2, out bool capped) {
    int n = v.Length, m = v[0].Length; var om = new double[n];
    for (int i = 0; i < n; i++) { double dot = 0; for (int t = 0; t < m; t++) dot += wd[t] * bs[i][t]; om[i] = dot / nb[i]; }
    var res = new List<long[]>(); var z = new long[n]; nodes = 0; bool cap = false;
    void Rec(int i, double rem) {
      if (cap) return; nodes++; if (nodes > nodeCap) { cap = true; return; }
      double c = om[i]; for (int j = i + 1; j < n; j++) c += mu[j][i] * z[j];
      double rad = Math.Sqrt(Math.Max(0, rem / nb[i])); long lo = (long)Math.Ceiling(-c - rad - 1e-9), hi = (long)Math.Floor(-c + rad + 1e-9);
      for (long zi = lo; zi <= hi; zi++) {
        z[i] = zi; double dd = zi + c; double rem2 = rem - dd * dd * nb[i]; if (rem2 < -1e-9) continue;
        if (i == 0) {
          bool okb = true; for (int t = 0; t < m && okb; t++) { double sum = wd[t]; for (int jj = 0; jj < n; jj++) sum += z[jj] * v[jj][t]; if (Math.Abs(sum) > 1 + 1e-6) okb = false; }
          if (okb) res.Add((long[])z.Clone());
        } else Rec(i - 1, rem2);
      }
      z[i] = 0;
    }
    Rec(n - 1, r2); capped = cap; return res;
  }
  // all valid k with |k0 + M s| , |s| <= Bc  (exact list of verified |k|-values), capped flag
  static List<BigInteger> Search(int D, BigInteger M, BigInteger k0, BigInteger Bc, out bool capped, out int dim) {
    BigInteger Xmax = BigInteger.Abs(k0) + M * Bc;
    var qs = new List<BigInteger>(); var ts = new List<int>();
    foreach (var (p, t) in new[] { (2, 1), (3, 0) }) { int a = Forced(p, D); for (int n = a + 1; ; n++) { var q = Pow(p, n * n); if (q > (Xmax + 2) * D) break; qs.Add(q); ts.Add(t); } }
    int c = qs.Count; dim = c + 1; capped = false; var outl = new List<BigInteger>();
    if (c == 0) { for (BigInteger s = -Bc; s <= Bc; s++) { var k = k0 + M * s; if (Valid(k, D)) outl.Add(BigInteger.Abs(k)); } return outl.Distinct().ToList(); }
    BigInteger Lq = 1; foreach (var q in qs) Lq = Lq / BigInteger.GreatestCommonDivisor(Lq, q) * q;
    var b = new BigInteger[c + 1][]; var w = new BigInteger[c + 1];
    b[0] = new BigInteger[c + 1]; b[0][0] = Lq; for (int i = 0; i < c; i++) b[0][i + 1] = M * D * Bc * (Lq / qs[i]);
    for (int i = 0; i < c; i++) { b[i + 1] = new BigInteger[c + 1]; b[i + 1][i + 1] = qs[i] * D * Bc * (Lq / qs[i]); w[i + 1] = Cent(k0 - ts[i], qs[i]) * D * Bc * (Lq / qs[i]); }
    BigInteger Z = Bc * Lq;
    Lll(b);
    Gs(b, Z, out var v, out var mu, out var bs, out var nb);
    // Babai nearest plane, exact
    for (int i = c; i >= 0; i--) {
      var wd = ToD(w, Z); double dot = 0; for (int t = 0; t <= c; t++) dot += wd[t] * bs[i][t]; double cf = Math.Round(dot / nb[i]);
      if (cf != 0) { var cb = new BigInteger(cf); for (int t = 0; t <= c; t++) w[t] -= cb * b[i][t]; }
    }
    var wd2 = ToD(w, Z);
    var sols = Enumerate(v, mu, bs, nb, wd2, (c + 1) * (1.0 + 1e-6) + 1e-6, out bool cp); capped = cp;
    foreach (var zz in sols) {
      var vec = new BigInteger[c + 1]; for (int i = 0; i <= c; i++) { BigInteger s = w[i]; for (int t = 0; t <= c; t++) s += zz[t] * b[t][i]; vec[i] = s; }
      bool ok = true; for (int i = 1; i <= c && ok; i++) if (BigInteger.Abs(vec[i]) >= Z) ok = false; if (!ok) continue;
      if (!(vec[0] % Lq).IsZero) continue; BigInteger s0 = vec[0] / Lq; if (BigInteger.Abs(s0) > Bc) continue;
      BigInteger kk = k0 + M * s0; if (Valid(kk, D)) outl.Add(BigInteger.Abs(kk));
    }
    return outl.Distinct().ToList();
  }
  // exact least |k|; lb = proved lower bound for the answer
  static BigInteger Least(int D, BigInteger lb, out bool capped, out long totalNodes, out int dimMax) {
    int a2 = Forced(2, D), a3 = Forced(3, D); BigInteger A = Pow(2, a2 * a2), B = Pow(3, a3 * a3), M = A * B;
    BigInteger k0 = A.IsOne ? BigInteger.Zero : B * BigInteger.ModPow(Mod(B, A), A / 2 - 1, A) % M; // k = 1 mod A, 0 mod B
    if (!A.IsOne && (Mod(k0, A) != 1 || !Mod(k0, B).IsZero)) throw new Exception("crt");
    capped = false; totalNodes = 0; dimMax = 0;
    BigInteger Bc = BigInteger.Max(1, lb / M);
    for (int step = 0; step < 4000; step++) {
      var sols = Search(D, M, k0, Bc, out bool cp, out int dim); totalNodes += nodes; dimMax = Math.Max(dimMax, dim); if (cp) { capped = true; }
      if (sols.Count > 0) {
        BigInteger best = sols.Min();
        if (M * Bc - BigInteger.Abs(k0) >= best) return best;       // every |k| <= best has |s| <= Bc: complete
        Bc = (best + BigInteger.Abs(k0)) / M + 2; continue;
      }
      if (cp) return 0;
      Bc *= 2;
    }
    return 0;
  }
  static void Main(string[] args) {
    if (args[0] == "brute") { int D = int.Parse(args[1]); long K = long.Parse(args[2]); for (long k = 0; k <= K; k++) { if (Valid(k, D)) { Console.WriteLine($"brute D={D}: |k|={k}"); return; } if (k > 0 && Valid(-k, D)) { Console.WriteLine($"brute D={D}: |k|={k} (negative)"); return; } } Console.WriteLine("brute: none"); return; }
    int D0 = int.Parse(args[0]), D1 = int.Parse(args[1]); nodeCap = args.Length > 2 ? long.Parse(args[2]) : 50000000L; BigInteger prev = args.Length > 3 ? BigInteger.Parse(args[3]) : 1; bool prevCert = true;
    BigInteger wit = 0; // last witness (value k, sign unknown): stored as the |k| of a certified answer
    for (int D = D0; D <= D1; D++) {
      var sw = Stopwatch.StartNew();
      // monotonicity: h_D(1) >= h_{D-1}(1); if a certified previous witness (either sign) is still valid, it is the answer
      if (prevCert && prev > 1 && (Valid(prev, D) || Valid(-prev, D))) { Console.WriteLine($"D={D}: h={prev} status=monotone-same e={Math.Log((double)prev) / Math.Pow(Math.Log(D), 2):F3} [{sw.Elapsed.TotalSeconds:F2}s]"); continue; }
      BigInteger h = Least(D, prev, out bool capped, out long nd, out int dim);
      if (h.IsZero) { Console.WriteLine($"D={D}: not found (capped={capped}, nodes={nd}, dim={dim}) [{sw.Elapsed.TotalSeconds:F1}s]"); prevCert = false; continue; }
      string st = capped ? "witness-only(capped)" : "complete"; if (!capped) { prev = h; prevCert = true; } else prevCert = false;
      Console.WriteLine($"D={D}: h={h} status={st} e={Math.Log((double)h) / Math.Pow(Math.Log(D), 2):F3} dim={dim} nodes={nd} [{sw.Elapsed.TotalSeconds:F1}s]");
    }
  }
}

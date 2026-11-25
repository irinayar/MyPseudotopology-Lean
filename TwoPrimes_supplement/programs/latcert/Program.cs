using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Numerics;

// latcert: least |k| with P_3(k) < 1/D and P_2(k-t) < 1/D, where P_p(x) = sup_{n>=1} || x / p^(n^2) ||,
// by an affine lattice enumeration that cannot lose a point.
//
// Why no point is lost:
//  * the basis reduction, the Gram-Schmidt data d[i], lam[i][j] and the coefficients of the shift are exact integers;
//  * every real number used to prune the enumeration is an interval [lo,hi] of doubles which contains the exact
//    value (IEEE-754 round-to-nearest results are moved one step outwards after every operation);
//  * a branch is discarded only if the LOWER bound of its partial squared norm exceeds the squared radius;
//  * every surviving point is tested with exact integers, and a candidate k is tested against the definition.
// There is no node limit: the program either finishes the enumeration or does not report a result.
//
// usage:  latcert unit D0 D1                 (target t = 1, one line per D)
//         latcert targets t0 t1 D1,D2,...    (every target t in [t0,t1], t != 0, ascending D)
//         latcert brute D t Kmax             (direct search, for tests)
class P {
  static BigInteger Pow(int p, int e) => BigInteger.Pow(p, e);
  static int Forced(int p, int D) { int a = 0; while (Pow(p, (a + 1) * (a + 1)) <= D) a++; return a; }
  static BigInteger Mod(BigInteger a, BigInteger m) { var r = BigInteger.Remainder(a, m); if (r < 0) r += m; return r; }
  static BigInteger Cent(BigInteger a, BigInteger m) { var r = Mod(a, m); if (2 * r > m) r -= m; return r; }
  static BigInteger TT = 1;
  // the definition, exactly: all n >= 1 with p^(n^2) <= D(|k|+|t|+2); every larger n is automatic
  static bool Valid(BigInteger k, int D) {
    BigInteger ak = BigInteger.Abs(k);
    foreach (var (p, t) in new[] { (2, TT), (3, BigInteger.Zero) }) {
      BigInteger x = k - t;
      for (int n = 1; ; n++) {
        BigInteger q = Pow(p, n * n); if (q > (ak + BigInteger.Abs(TT) + 2) * D) break;
        BigInteger rm = Mod(x, q); BigInteger dist = BigInteger.Min(rm, q - rm);
        if (dist * D >= q) return false;
      }
    }
    return true;
  }

  // ---------------- exact lattice data ----------------
  static BigInteger Dot(BigInteger[] x, BigInteger[] y) { BigInteger s = 0; for (int i = 0; i < x.Length; i++) s += x[i] * y[i]; return s; }
  static BigInteger Round(BigInteger a, BigInteger b) { BigInteger q = BigInteger.DivRem(2 * a + b, 2 * b, out var r); if (r < 0) q -= 1; return q; }
  // integral LLL (Cohen 2.6.7); only used to find a good basis, completeness does not depend on its quality
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
  static BigInteger Div(BigInteger a, BigInteger b) { var q = BigInteger.DivRem(a, b, out var r); if (!r.IsZero) throw new Exception("inexact division"); return q; }
  // fresh exact Gram-Schmidt data of the final basis: d[i] = Gram determinant, lam[i][j] = d[j+1] * mu_ij
  static void Gram(BigInteger[][] b, out BigInteger[] d, out BigInteger[][] lam) {
    int n = b.Length; d = new BigInteger[n + 1]; lam = new BigInteger[n][]; d[0] = 1;
    for (int k = 0; k < n; k++) {
      lam[k] = new BigInteger[n];
      for (int j = 0; j <= k; j++) {
        BigInteger u = Dot(b[k], b[j]);
        for (int i = 0; i < j; i++) u = Div(d[i + 1] * u - lam[k][i] * lam[j][i], d[i]);
        if (j < k) lam[k][j] = u; else d[k + 1] = u;
      }
      if (d[k + 1] <= 0) throw new Exception("basis not independent");
    }
  }
  // lamw[j] = d[j+1] * (coefficient of w on the Gram-Schmidt vector j)
  static BigInteger[] Shift(BigInteger[] w, BigInteger[][] b, BigInteger[] d, BigInteger[][] lam) {
    int n = b.Length; var lw = new BigInteger[n];
    for (int j = 0; j < n; j++) {
      BigInteger u = Dot(w, b[j]);
      for (int i = 0; i < j; i++) u = Div(d[i + 1] * u - lw[i] * lam[j][i], d[i]);
      lw[j] = u;
    }
    return lw;
  }

  // ---------------- outward rounded intervals ----------------
  static double Down(double x) => Math.BitDecrement(x);
  static double Up(double x) => Math.BitIncrement(x);
  // an interval containing num/den (den > 0)
  static (double lo, double hi) Enclose(BigInteger num, BigInteger den) {
    if (num.IsZero) return (0.0, 0.0);
    bool neg = num.Sign < 0; BigInteger a = BigInteger.Abs(num);
    int e = (int)((long)den.GetBitLength() - (long)a.GetBitLength()) + 52;
    BigInteger q = e >= 0 ? (a << e) / den : a / (den << -e);       // floor(a 2^e / den), below 2^53
    if (q >= (BigInteger.One << 53)) throw new Exception("enclosure: mantissa too large");
    if (e > 900 || e < -900) throw new Exception("enclosure: exponent out of range");
    double lo = Math.ScaleB((double)(long)q, -e), hi = Math.ScaleB((double)((long)q + 1), -e);
    return neg ? (-hi, -lo) : (lo, hi);
  }

  static long nodes;
  // all z for which the point w + sum z_j b_j can satisfy |coordinate| < Z (a superset), n = dimension
  static List<long[]> Enumerate(BigInteger[][] b, BigInteger[] w, BigInteger Z, BigInteger[] d, BigInteger[][] lam, BigInteger[] lw) {
    int n = b.Length;
    var muLo = new double[n][]; var muHi = new double[n][]; var vLo = new double[n][]; var vHi = new double[n][];
    for (int i = 0; i < n; i++) {
      muLo[i] = new double[n]; muHi[i] = new double[n]; vLo[i] = new double[n]; vHi[i] = new double[n];
      for (int j = 0; j < i; j++) (muLo[i][j], muHi[i][j]) = Enclose(lam[i][j], d[j + 1]);
      for (int t = 0; t < n; t++) (vLo[i][t], vHi[i][t]) = Enclose(b[i][t], Z);
    }
    var nbLo = new double[n]; var nbHi = new double[n]; var omLo = new double[n]; var omHi = new double[n]; var wLo = new double[n]; var wHi = new double[n];
    for (int j = 0; j < n; j++) {
      (nbLo[j], nbHi[j]) = Enclose(d[j + 1], d[j] * Z * Z);
      if (!(nbLo[j] > 0)) throw new Exception("norm enclosure not positive");
      (omLo[j], omHi[j]) = Enclose(lw[j], d[j + 1]);
      (wLo[j], wHi[j]) = Enclose(w[j], Z);
    }
    double R = n;                               // every point of the open box [-1,1]^n has squared norm < n
    var res = new List<long[]>(); var z = new long[n];
    const double LIM = 4503599627370496.0;      // 2^52: z must be exactly representable
    void Rec(int i, double partialLo) {
      nodes++;
      double cLo = omLo[i], cHi = omHi[i];
      for (int j = i + 1; j < n; j++) {
        if (z[j] == 0) continue;
        double x = z[j]; double p1 = muLo[j][i] * x, p2 = muHi[j][i] * x;
        cLo = Down(cLo + Down(Math.Min(p1, p2))); cHi = Up(cHi + Up(Math.Max(p1, p2)));
      }
      double rem = Up(R - partialLo); if (rem < 0) return;
      double rad = Up(Math.Sqrt(Up(rem / nbLo[i])));
      double zlo = Math.Ceiling(Down(-cHi - rad)), zhi = Math.Floor(Up(-cLo + rad));
      if (Math.Abs(zlo) > LIM || Math.Abs(zhi) > LIM) throw new Exception("coefficient too large");
      for (long zi = (long)zlo; zi <= (long)zhi; zi++) {
        double tLo = Down(zi + cLo), tHi = Up(zi + cHi);
        double m = tLo > 0 ? tLo : (tHi < 0 ? -tHi : 0.0);
        double part = m == 0 ? partialLo : Down(partialLo + Down(nbLo[i] * Down(m * m)));
        if (part > R) continue;
        z[i] = zi;
        if (i == 0) {
          bool maybe = true;                    // reject only if some coordinate is certainly outside [-1,1]
          for (int t = 0; t < n && maybe; t++) {
            double sLo = wLo[t], sHi = wHi[t];
            for (int j = 0; j < n; j++) {
              if (z[j] == 0) continue;
              double x = z[j]; double p1 = vLo[j][t] * x, p2 = vHi[j][t] * x;
              sLo = Down(sLo + Down(Math.Min(p1, p2))); sHi = Up(sHi + Up(Math.Max(p1, p2)));
            }
            if (sLo > 1 || sHi < -1) maybe = false;
          }
          if (maybe) res.Add((long[])z.Clone());
        } else Rec(i - 1, part);
      }
      z[i] = 0;
    }
    Rec(n - 1, 0.0);
    return res;
  }

  // all valid k = k0 + M s with |s| <= Bc (returned as |k|)
  static List<BigInteger> Search(int D, BigInteger M, BigInteger k0, BigInteger Bc, out int dim) {
    BigInteger Xmax = BigInteger.Abs(k0) + M * Bc;
    var qs = new List<BigInteger>(); var ts = new List<BigInteger>();
    foreach (var (p, t) in new[] { (2, TT), (3, BigInteger.Zero) }) { int a = Forced(p, D); for (int n = a + 1; ; n++) { var q = Pow(p, n * n); if (q > (Xmax + BigInteger.Abs(TT) + 2) * D) break; qs.Add(q); ts.Add(t); } }
    int c = qs.Count; dim = c + 1; var outl = new List<BigInteger>();
    if (c == 0) { for (BigInteger s = -Bc; s <= Bc; s++) { var k = k0 + M * s; if (Valid(k, D)) outl.Add(BigInteger.Abs(k)); } return outl.Distinct().ToList(); }
    BigInteger Lq = 1; foreach (var q in qs) Lq = Lq / BigInteger.GreatestCommonDivisor(Lq, q) * q;
    var b = new BigInteger[c + 1][]; var w = new BigInteger[c + 1];
    b[0] = new BigInteger[c + 1]; b[0][0] = Lq; for (int i = 0; i < c; i++) b[0][i + 1] = M * D * Bc * (Lq / qs[i]);
    for (int i = 0; i < c; i++) { b[i + 1] = new BigInteger[c + 1]; b[i + 1][i + 1] = qs[i] * D * Bc * (Lq / qs[i]); w[i + 1] = Cent(k0 - ts[i], qs[i]) * D * Bc * (Lq / qs[i]); }
    BigInteger Z = Bc * Lq;
    Lll(b);
    Gram(b, out var d, out var lam);
    var lw = Shift(w, b, d, lam);
    // nearest plane reduction of the shift, exact
    for (int i = c; i >= 0; i--) {
      BigInteger cf = Round(lw[i], d[i + 1]); if (cf.IsZero) continue;
      for (int t = 0; t <= c; t++) w[t] -= cf * b[i][t];
      for (int j = 0; j < i; j++) lw[j] -= cf * lam[i][j];
      lw[i] -= cf * d[i + 1];
    }
    foreach (var zz in Enumerate(b, w, Z, d, lam, lw)) {
      var vec = new BigInteger[c + 1]; for (int i = 0; i <= c; i++) { BigInteger s = w[i]; for (int t = 0; t <= c; t++) if (zz[t] != 0) s += zz[t] * b[t][i]; vec[i] = s; }
      bool ok = true; for (int i = 1; i <= c && ok; i++) if (BigInteger.Abs(vec[i]) >= Z) ok = false; if (!ok) continue;
      if (!(vec[0] % Lq).IsZero) throw new Exception("coordinate 0 is not a multiple");
      BigInteger s0 = vec[0] / Lq; if (BigInteger.Abs(s0) > Bc) continue;
      BigInteger kk = k0 + M * s0; if (Valid(kk, D)) outl.Add(BigInteger.Abs(kk));
    }
    return outl.Distinct().ToList();
  }

  // least |k|; lb is a lower bound used only to choose the first box
  static BigInteger Least(int D, BigInteger lb, out int dimMax) {
    int a2 = Forced(2, D), a3 = Forced(3, D); BigInteger A = Pow(2, a2 * a2), B = Pow(3, a3 * a3), M = A * B;
    BigInteger k0 = A.IsOne ? BigInteger.Zero : B * (Mod(TT, A) * BigInteger.ModPow(Mod(B, A), A / 2 - 1, A) % A) % M;   // k = t mod A, 0 mod B
    if (!A.IsOne && (Mod(k0, A) != Mod(TT, A) || !Mod(k0, B).IsZero)) throw new Exception("crt");
    dimMax = 0; BigInteger Bc = BigInteger.Max(1, lb / M);
    for (int step = 0; step < 4000; step++) {
      var sols = Search(D, M, k0, Bc, out int dim); dimMax = Math.Max(dimMax, dim);
      if (sols.Count > 0) {
        BigInteger best = sols.Min();
        if (M * Bc - BigInteger.Abs(k0) >= best) return best;      // every |k| <= best has |s| <= Bc: complete
        Bc = (best + BigInteger.Abs(k0)) / M + 2; continue;
      }
      Bc *= 2;
    }
    throw new Exception("no witness found");
  }

  static void Main(string[] args) {
    if (args[0] == "brute") {
      int D = int.Parse(args[1]); TT = int.Parse(args[2]); long K = long.Parse(args[3]);
      for (long k = 0; k <= K; k++) { if (Valid(k, D)) { Console.WriteLine($"brute D={D} t={TT}: |k|={k}"); return; } if (k > 0 && Valid(-k, D)) { Console.WriteLine($"brute D={D} t={TT}: |k|={k}"); return; } }
      Console.WriteLine("brute: none"); return;
    }
    if (args[0] == "targets") {
      int t0 = int.Parse(args[1]), t1 = int.Parse(args[2]); int[] Ds = args[3].Split(',').Select(int.Parse).OrderBy(x => x).ToArray();
      for (int t = t0; t <= t1; t++) {
        if (t == 0) continue; TT = t; BigInteger pv = 0;
        foreach (int D in Ds) {
          if (Valid(0, D)) { Console.WriteLine($"t={t} D={D} h=0"); continue; }
          // h_D(t) does not decrease with D, so a previous minimum which is still valid is the minimum
          if (pv > 0 && (Valid(pv, D) || Valid(-pv, D))) { Console.WriteLine($"t={t} D={D} h={pv}"); continue; }
          pv = Least(D, BigInteger.Max(1, pv), out _); Console.WriteLine($"t={t} D={D} h={pv}");
        }
      }
      return;
    }
    if (args[0] == "unit") {
      int D0 = int.Parse(args[1]), D1 = int.Parse(args[2]); TT = 1; BigInteger prev = 0; var total = Stopwatch.StartNew();
      for (int D = D0; D <= D1; D++) {
        var sw = Stopwatch.StartNew(); nodes = 0;
        if (prev > 0 && (Valid(prev, D) || Valid(-prev, D))) { Console.WriteLine($"D={D}: h={prev} monotone"); continue; }
        prev = Least(D, BigInteger.Max(1, prev), out int dim);
        Console.WriteLine($"D={D}: h={prev} enumerated dim={dim} nodes={nodes} [{sw.Elapsed.TotalSeconds:F1}s]");
      }
      Console.WriteLine($"finished D={D0}..{D1} [{total.Elapsed.TotalSeconds:F0}s]");
      return;
    }
    Console.WriteLine("usage: latcert unit D0 D1 | targets t0 t1 D1,D2,... | brute D t Kmax");
  }
}

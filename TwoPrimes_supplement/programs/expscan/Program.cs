using System;
// Level-structure exponent: for D = e^L (real), the smallest ln X / L^2 over level pairs (N for base 2, M for base l) and heights X with
//   both balls cut inside their top level (D u <= X < l^(N^2)/D), i.e. J'_A, J'_B >= D and X < r q,   and   lambda = |A||B|/(2X+1) >= LAM.
// |A^+| ~ (X/u + 1/2) * prod_{n<N} (2 J_n + 1),  J_n = floor(l^(2n-1)/D).
// Usage: expscan l LAM Lmin Lmax step
class P {
  static double SumLn(int p, double L, int n) { double s = 0; for (int j = 1; j <= n; j++) { double lnrho = (2 * j - 1) * Math.Log(p) - L; double J = lnrho > 30 ? double.PositiveInfinity : Math.Floor(Math.Exp(lnrho)); s += J == double.PositiveInfinity ? Math.Log(2) + lnrho : Math.Log(2 * J + 1); } return s; }
  static double One(int p, double L, int j) { double lnrho = (2 * j - 1) * Math.Log(p) - L; double J = lnrho > 30 ? double.PositiveInfinity : Math.Floor(Math.Exp(lnrho)); return J == double.PositiveInfinity ? Math.Log(2) + lnrho : Math.Log(2 * J + 1); }
  static void Main(string[] a) {
    int pp = int.Parse(a[5]); int l = int.Parse(a[0]); double LAM = double.Parse(a[1], System.Globalization.CultureInfo.InvariantCulture);
    double L0 = double.Parse(a[2], System.Globalization.CultureInfo.InvariantCulture), L1 = double.Parse(a[3], System.Globalization.CultureInfo.InvariantCulture), st = double.Parse(a[4], System.Globalization.CultureInfo.InvariantCulture);
    double ln2 = Math.Log(pp), lnl = Math.Log(l); double supx = 0, supL = 0, infx = 99, infL = 0;
    var rows = new System.Collections.Generic.List<(double L, double x)>();
    for (double L = L0; L <= L1; L += st) {
      double L2 = L * L; double best = 1e18; int nmax = (int)Math.Sqrt(6.5 * L2 / ln2) + 3, mmax = (int)Math.Sqrt(6.5 * L2 / lnl) + 3;
      var SAarr = new double[nmax + 1]; var SBarr = new double[mmax + 1]; for (int j = 1; j <= nmax; j++) SAarr[j] = SAarr[j - 1] + One(pp, L, j); for (int j = 1; j <= mmax; j++) SBarr[j] = SBarr[j - 1] + One(l, L, j);
      for (int N = 2; N <= nmax; N++) {
        double aN = (N - 1.0) * (N - 1) * ln2 + L, bN = N * (double)N * ln2 - L; if (aN >= bN) continue; double lnu = (N - 1.0) * (N - 1) * ln2; double SA = SAarr[N - 1];
        for (int M = 2; M <= mmax; M++) {
          double aM = (M - 1.0) * (M - 1) * lnl + L, bM = M * (double)M * lnl - L; if (aM >= bM) continue; double lnv = (M - 1.0) * (M - 1) * lnl; double SB = SBarr[M - 1];
          double lo = Math.Max(aN, aM); double hi = Math.Min(bN, bM); if (lo >= hi) continue;
          double lnXlam = Math.Log(LAM) + ln2 + lnu + lnv - SA - SB; lo = Math.Max(lo, lnXlam);
          if (lo < hi && lo < best) best = lo;
        }
      }
      double x = best / L2; if (best > 1e17) continue; rows.Add((L, x)); if (x > supx) { supx = x; supL = L; } if (x < infx) { infx = x; infL = L; }
    }
    Console.WriteLine($"l={l} LAM={LAM} L in [{L0},{L1}] step {st}: points={rows.Count} sup x={supx:F4} at L={supL:F2} (D=e^L), inf x={infx:F4} at L={infL:F2}");
    // sup over windows of L
    foreach (var (lo, hi) in new[] { (5.0, 10.0), (10.0, 20.0), (20.0, 40.0), (40.0, 80.0), (80.0, 160.0), (160.0, 320.0) }) {
      double s = 0, sl = 0; int c = 0; foreach (var r in rows) if (r.L >= lo && r.L < hi) { c++; if (r.x > s) { s = r.x; sl = r.L; } }
      if (c > 0) Console.WriteLine($"  L in [{lo},{hi}): sup x={s:F4} at L={sl:F2}");
    }
  }
}

using System;
using System.Collections.Generic;
using System.Numerics;
// Multi-level model: the top K levels of each ball are exact (cluster j-index, then digit levels), the rest uniform on the hull.
// C_K = 2X * sum(weights * H_low(residual)) / (massA massB)^2.   Usage: nonres levk D l n m JA JB Kmax
partial class P {
  class Lv2 { public Int128 w; public long J; public double hullBelow; }
  static List<Lv2> LevList(List<Lv> L, int top, long Jtop) {
    var R = new List<Lv2>(); R.Add(new Lv2 { w = (Int128)L[top].step, J = Jtop, hullBelow = (double)L[top].U });
    for (int j = top - 1; j >= 0; j--) if (L[j].J >= 1) R.Add(new Lv2 { w = (Int128)L[j].step, J = (long)L[j].J, hullBelow = (double)L[j].U });
    return R;
  }
  static double EnergyK(List<Lv2> A, List<Lv2> B, int K, double Xabs, out long nodes) {
    // returns sum over exact digit-difference vectors of weights * H_low(residual)
    double hA = A[K - 1].hullBelow, hB = B[K - 1].hullBelow; double[] wd = { 2 * hA, 2 * hA, 2 * hB, 2 * hB };
    double total = 0; long cnt = 0;
    var Wk = new double[K]; for (int k = 0; k < K; k++) Wk[k] = 2 * A[k].hullBelow + 2 * B[k].hullBelow;
    Action<int, Int128, double> rec = null;
    rec = (k, z, wt) => {
      // choose (alpha_k, beta_k) with |z + alpha wA - beta wB| < Wk[k]  (z includes previous choices)
      var a = A[k]; var b = B[k]; long Ja = (k == 0) ? a.J : 2 * a.J, Jb = (k == 0) ? b.J : 2 * b.J; // top level: differences of cluster indices in [-J, J]
      bool loopA = a.w >= b.w; // loop over the digit of the ball with the larger step
      double W = Wk[k]; double wa = (double)a.w, wb = (double)b.w;
      if (loopA) {
        for (long al = -Ja; al <= Ja; al++) {
          Int128 zz = z + (Int128)al * a.w; double t = (double)zz / wb; // need beta with |zz - beta wb| < W
          long b0 = (long)Math.Floor(t - W / wb) - 1, b1 = (long)Math.Ceiling(t + W / wb) + 1;
          for (long be = b0; be <= b1; be++) { if (Math.Abs(be) > Jb) continue; Int128 r = zz - (Int128)be * b.w; double rd = (double)r; if (Math.Abs(rd) >= W) continue;
            double cA = (k == 0 ? (a.J + 1 - Math.Abs(al)) : (2 * a.J + 1 - Math.Abs(al))), cB = (k == 0 ? (b.J + 1 - Math.Abs(be)) : (2 * b.J + 1 - Math.Abs(be)));
            if (cA <= 0 || cB <= 0) continue;
            if (k == K - 1) { total += wt * cA * cB * Hn(rd, wd); cnt++; } else rec(k + 1, r, wt * cA * cB);
          }
        }
      } else {
        for (long be = -Jb; be <= Jb; be++) {
          Int128 zz = z - (Int128)be * b.w; double t = -(double)zz / wa; // need alpha with |zz + alpha wa| < W
          long a0 = (long)Math.Floor(t - W / wa) - 1, a1 = (long)Math.Ceiling(t + W / wa) + 1;
          for (long al = a0; al <= a1; al++) { if (Math.Abs(al) > Ja) continue; Int128 r = zz + (Int128)al * a.w; double rd = (double)r; if (Math.Abs(rd) >= W) continue;
            double cA = (k == 0 ? (a.J + 1 - Math.Abs(al)) : (2 * a.J + 1 - Math.Abs(al))), cB = (k == 0 ? (b.J + 1 - Math.Abs(be)) : (2 * b.J + 1 - Math.Abs(be)));
            if (cA <= 0 || cB <= 0) continue;
            if (k == K - 1) { total += wt * cA * cB * Hn(rd, wd); cnt++; } else rec(k + 1, r, wt * cA * cB);
          }
        }
      }
    };
    rec(0, 0, 1.0); nodes = cnt; return total;
  }
  static void LevK(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); int n = int.Parse(a[3]), m = int.Parse(a[4]); long JA = long.Parse(a[5]), JB = long.Parse(a[6]); int Kmax = int.Parse(a[7]);
    int nA = n + 2, nB = m + 2; var LA = Levels(2, D, nA); var LB = Levels(l, D, nB);
    var A = LevList(LA, n - 1, JA); var B = LevList(LB, m - 1, JB);
    double Xabs = (double)JA * (double)A[0].w + A[0].hullBelow;
    Console.WriteLine($"D={D} l={l} n={n} m={m} JA'={JA} JB'={JB}; exact levels available: A {A.Count}, B {B.Count}; top steps u={(double)A[0].w:E3} v={(double)B[0].w:E3}");
    for (int K = 1; K <= Kmax && K <= A.Count && K <= B.Count; K++) {
      double massA = JA + 1, massB = JB + 1; for (int k = 1; k < K; k++) { massA *= 2 * A[k].J + 1; massB *= 2 * B[k].J + 1; }
      long nodes; var sw = System.Diagnostics.Stopwatch.StartNew(); double E = EnergyK(A, B, K, Xabs, out nodes);
      double C = 2 * Xabs * E / (massA * massA * massB * massB);
      Console.WriteLine($"  K={K}: C_K = {C:F5}   (terms {nodes}, {sw.Elapsed.TotalSeconds:F1}s)");
    }
  }
}
partial class P {
  static double Hn(double x, double[] w) {
    var v = new List<double>(); foreach (var wi in w) if (wi > 0) v.Add(wi); int n = v.Count;
    if (n == 0) return Math.Abs(x) < 0.5 ? 1.0 : 0.0;
    double s = 0, prod = 1; foreach (var wi in v) { s += wi / 2; prod *= wi; } double t = x + s, r = 0; double fact = 1; for (int i = 2; i < n; i++) fact *= i;
    for (int m = 0; m < (1 << n); m++) { double sh = 0; int bits = 0; for (int i = 0; i < n; i++) if ((m >> i & 1) != 0) { sh += v[i]; bits++; } double y = t - sh; if (y > 0) r += ((bits & 1) == 0 ? 1 : -1) * Math.Pow(y, n - 1) / fact; }
    return r / prod;
  }
}

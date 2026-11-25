using System;
using System.Collections.Generic;
using System.Numerics;
// Cluster model of two one-sided balls: A = U_{j=0..JtA} (j*uA + T_lowerA), B = U_{i=0..JtB} (i*vB + T_lowerB).
// Energy E = sum_{m,n} (JtA+1-|m|)(JtB+1-|n|) G(m uA - n vB),  G(D) = sum_x rA(x) rB(x+D),  r = autocorrelation counts of the lower sets.
// Usage: clmodel D pA nTopA JtA pB nTopB JtB X [fscan]
partial class P {
  static double H4c(double x, double[] w) { double s = 0; foreach (var wi in w) s += wi / 2; double prod = 1; foreach (var wi in w) prod *= wi; double t = x + s, r = 0; for (int m = 0; m < 16; m++) { double sh = 0; int bits = 0; for (int i = 0; i < 4; i++) if ((m >> i & 1) != 0) { sh += w[i]; bits++; } double y = t - sh; if (y > 0) r += ((bits & 1) == 0 ? 1 : -1) * y * y * y / 6; } return r / prod; }
  static List<(long w, long J)> Lower(int p, long D, int nTop) {
    var L = new List<(long, long)>();
    for (int n = 1; n < nTop; n++) {
      BigInteger q = BigInteger.Pow(p, n * n), qp = BigInteger.Pow(p, (n - 1) * (n - 1));
      long J = (long)((q - 1) / (D * qp)); if (J > 0) L.Add(((long)qp, J));
    }
    return L;
  }
  static double R(List<(long w, long J)> L, long y) {
    double wt = 1;
    for (int i = L.Count - 1; i >= 0; i--) {
      long a = (long)Math.Round((double)y / L[i].w); long J2 = 2 * L[i].J;
      if (Math.Abs(a) > J2) return 0;
      y -= a * L[i].w; wt *= (J2 + 1 - Math.Abs(a));
    }
    return y == 0 ? wt : 0;
  }
  static void Enum(List<(long w, long J)> L, int i, long x, double wt, List<(long, double)> o) {
    if (i < 0) { o.Add((x, wt)); return; }
    long J2 = 2 * L[i].J;
    for (long a = -J2; a <= J2; a++) Enum(L, i - 1, x + a * L[i].w, wt * (J2 + 1 - Math.Abs(a)), o);
  }
  static double Size(List<(long w, long J)> L) { double s = 1; foreach (var t in L) s *= 2 * t.J + 1; return s; }
  static void Main(string[] a) {
    long D = long.Parse(a[0]); int pA = int.Parse(a[1]), nA = int.Parse(a[2]); long JA = long.Parse(a[3]);
    int pB = int.Parse(a[4]), nB = int.Parse(a[5]); long JB = long.Parse(a[6]); double X = double.Parse(a[7], System.Globalization.CultureInfo.InvariantCulture);
    var LA = Lower(pA, D, nA); var LB = Lower(pB, D, nB);
    long uA = (long)BigInteger.Pow(pA, (nA - 1) * (nA - 1)), vB0 = (long)BigInteger.Pow(pB, (nB - 1) * (nB - 1));
    var supp = new List<(long, double)>(); Enum(LA, LA.Count - 1, 0, 1, supp);
    double sizeA = (JA + 1) * Size(LA), sizeB = (JB + 1) * Size(LB);
    Console.WriteLine($"D={D} uA={uA} vB={vB0} |A|={sizeA} |B|={sizeB} lambda_model={sizeA * sizeB / (2 * X + 1):F3} supp={supp.Count}  lowerA=[{string.Join(",", LA)}] lowerB=[{string.Join(",", LB)}]");
    Func<double, double> Cf = f => {
      long vB = (long)Math.Round(vB0 * f); double E = 0;
      for (long m = -JA; m <= JA; m++) for (long n = -JB; n <= JB; n++) {
        long Dl = m * uA - n * vB; double G = 0;
        foreach (var (x, w) in supp) G += w * R(LB, x + Dl);
        E += (JA + 1 - Math.Abs(m)) * (double)(JB + 1 - Math.Abs(n)) * G;
      }
      return (2 * X + 1) * E / (sizeA * sizeA * sizeB * sizeB / (sizeA * sizeB) * 1.0) / (sizeA * sizeB) ; // placeholder replaced below
    };
    double hullA = 0, hullB = 0; foreach (var t in LA) hullA += (double)t.J * t.w; foreach (var t in LB) hullB += (double)t.J * t.w; double supB = 2 * (hullA + hullB) + 1;
    Func<double, double> C2 = f => {
      long vB = (long)Math.Round(vB0 * f); double E = 0;
      for (long m = -JA; m <= JA; m++) for (long n = -JB; n <= JB; n++) {
        long Dl = m * uA - n * vB; if (Math.Abs((double)Dl) > supB) continue; double G = 0;
        foreach (var (x, w) in supp) G += w * R(LB, x + Dl);
        if (Environment.GetEnvironmentVariable("DUMPG") != null && f == 1.0) { double[] ww = { 2 * hullA, 2 * hullA, 2 * hullB, 2 * hullB }; double Ge = Size(LA) * Size(LA) * Size(LB) * Size(LB) * H4c((double)Dl, ww); Console.WriteLine("G m=" + m + " n=" + n + " Dl=" + Dl + " G=" + G + " Genv=" + Ge.ToString("E4") + " ratio=" + (G / Ge).ToString("F3")); }
        E += (JA + 1 - Math.Abs(m)) * (double)(JB + 1 - Math.Abs(n)) * G;
      }
      return (2 * X + 1) * E / (sizeA * sizeB) / (sizeA * sizeB);
    };
    Console.WriteLine($"f=1: C_model = {C2(1.0):F4}");
    if (a.Length > 8) {
      double lo = double.Parse(a[8].Split(',')[0], System.Globalization.CultureInfo.InvariantCulture), hi = double.Parse(a[8].Split(',')[1], System.Globalization.CultureInfo.InvariantCulture), st = double.Parse(a[8].Split(',')[2], System.Globalization.CultureInfo.InvariantCulture);
      for (double f = lo; f <= hi + 1e-12; f += st) Console.WriteLine($"f={f:F4} C={C2(f):F4}");
    }
  }
}
partial class Hh { }

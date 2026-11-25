using System;
using System.Collections.Generic;
// Peak of the cluster-model energy at a near-coincidence a*u = b*v of the two top steps (order = a), as a function of D and of the top ranges.
// Units: u = 1, v = rho = a/b (>=1), UA = 1/D, UB = rho/D (hull of the lower levels, about step/D).
// Usage: ordscan D Jmult amax
class P {
  static double H4(double x, double[] w) {
    double s = 0; foreach (var wi in w) s += wi / 2; double prod = 1; foreach (var wi in w) prod *= wi;
    double t = x + s, r = 0;
    for (int m = 0; m < 16; m++) { double sh = 0; int bits = 0; for (int i = 0; i < 4; i++) if ((m >> i & 1) != 0) { sh += w[i]; bits++; }
      double y = t - sh; if (y > 0) r += ((bits & 1) == 0 ? 1 : -1) * y * y * y / 6; }
    return r / prod;
  }
  // continuous-part model energy normalized: C = 2X * sum Phi / ((JA+1)(JB+1))^2, X = JA + UA (units of u)
  static double Cm(double rho, double UAr, double UBr, long JA, long JB, out double ccontEnv) {
    double[] w = { 2 * UAr, 2 * UAr, 2 * UBr, 2 * UBr }; double sup = 2 * UAr + 2 * UBr; double sum = 0;
    for (long m = -JA; m <= JA; m++) {
      double cm = JA + 1 - Math.Abs(m); long n0 = (long)Math.Round(m / rho); long kmax = (long)(sup / rho) + 2;
      for (long n = n0 - kmax; n <= n0 + kmax; n++) {
        if (Math.Abs(n) > JB) continue; double d = m - n * rho; if (Math.Abs(d) >= sup) continue;
        sum += cm * (JB + 1 - Math.Abs(n)) * H4(d, w);
      }
    }
    double X = JA + UAr; double den = ((double)(JA + 1)) * (JB + 1); ccontEnv = 0;
    return 2 * X * sum / (den * den);
  }
  public static double CmPub(double r,double ua,double ub,long ja,long jb,out double e){ return Cm(r,ua,ub,ja,jb,out e); }
  static int Gcd(int a, int b) { while (b != 0) { int t = a % b; a = b; b = t; } return a; }
  static void Main(string[] args) {
    long D = long.Parse(args[0]); double Jm = double.Parse(args[1]); if (args.Length > 4 && args[3] == "prof") { Prof.Run(D, Jm, int.Parse(args[2]), int.Parse(args[4])); return; } int amax = int.Parse(args[2]);
    long JA = (long)(Jm * D);
    Console.WriteLine($"D={D} JA={JA}  (UA=1/D, UB=rho/D, units of u)");
    // generic (non-resonant) reference: rho = golden-ish irrational
    { double rho = 1.0 + 0.6180339887; double e; long JB = (long)((JA + 1.0 / D) / rho + 1.0 / D); Console.WriteLine($"generic rho=1.618: C={Cm(rho, 1.0 / D, rho / D, JA, JB, out e):F4}"); }
    for (int a = 1; a <= amax; a++) for (int b = 1; b <= a; b++) {
      if (Gcd(a, b) != 1) continue; if (b != a - 1 && !(a == 1 && b == 1) && !(args.Length > 3)) continue; // default: ratios a:(a-1) and 1:1
      double rho0 = (double)a / b; double W = 2.0 / D + 2.0 * rho0 / D; double best = 0, bd = 0;
      int steps = 80; for (int s = -steps; s <= steps; s++) {
        double rho; rho = rho0 + s * (W / 4.0) / steps / Math.Max(1, b); // v*b - a*u shift of up to W/4 (in units of u) at order b
        if (rho < 1) continue;
        long JB = (long)((JA + 1.0 / D) / rho + rho / D / rho); double e; double C = Cm(rho, 1.0 / D, rho / D, JA, JB, out e);
        if (C > best) { best = C; bd = rho - rho0; }
      }
      Console.WriteLine($"order a={a} ratio {a}:{b}: peak C={best:F3} at rho-rho0={bd:E2}");
    }
  }
}
class Prof {
  public static void Run(long D, double Jm, int a, int b) {
    long JA = (long)(Jm * D); double rho0 = (double)a / b; double W = 2.0 / D + 2.0 * rho0 / D;
    Console.WriteLine($"profile D={D} JA={JA} ratio {a}:{b}, W={W:E3}; offset t = b*(rho-rho0)/W");
    foreach (double t in new double[] { 0, 0.0005, 0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.5, 1.0 }) {
      double rho = rho0 + t * W / b; long JB = (long)((JA + 1.0 / D) / rho + 1.0 / D); double e; double C = P.CmPub(rho, 1.0 / D, rho / D, JA, JB, out e);
      Console.WriteLine($"  t={t}: C={C:F3}");
    }
  }
}

using System;
using System.Collections.Generic;
using System.Numerics;
// One-sided ball model: uniform lower sets, clusters j=1..Jreg full, j=0 half cluster [0,U], top cluster cut at X (partial).
partial class P {
  class Cp { public double m, w1, w2, c; }
  static List<Cp> Comps(double step, double U, long J, double Xu, out double mass) {
    // clusters at j*step, half-width U, units of u. returns autocorrelation components and total mass (in units of |T|)
    var sp = new List<(double lo, double hi, double ms)>(); sp.Add((0, U, 0.5));
    long Jreg = J; // largest j with j*step+U <= Xu
    long jmax = (long)Math.Floor((Xu - U) / step + 1e-12); if (jmax < Jreg) Jreg = jmax; if (Jreg < 0) Jreg = 0;
    // partial cluster
    long jp = Jreg + 1; if (jp <= J) { double lo = jp * step - U; if (lo < Xu) { double hi = Xu; double f = Math.Min(1.0, (hi - lo) / (2 * U)); sp.Add((lo, hi, f)); } }
    mass = Jreg; foreach (var s in sp) mass += s.ms;
    var L = new List<Cp>();
    for (long m = -(Jreg - 1); m <= Jreg - 1; m++) L.Add(new Cp { m = Jreg - Math.Abs(m), w1 = 2 * U, w2 = 2 * U, c = m * step });
    foreach (var s in sp) {
      double ws = s.hi - s.lo, cs = (s.hi + s.lo) / 2;
      for (long j = 1; j <= Jreg; j++) { L.Add(new Cp { m = s.ms, w1 = ws, w2 = 2 * U, c = cs - j * step }); L.Add(new Cp { m = s.ms, w1 = 2 * U, w2 = ws, c = j * step - cs }); }
      foreach (var t in sp) L.Add(new Cp { m = s.ms * t.ms, w1 = ws, w2 = t.hi - t.lo, c = cs - (t.hi + t.lo) / 2 });
    }
    return L;
  }
  static void One(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); BigInteger X = BigInteger.Parse(a[3]);
    double lnX = BigInteger.Log(X);
    int nA = (int)Math.Sqrt((lnX + 10) / Math.Log(PA)) + 4, nB = (int)Math.Sqrt((lnX + 10) / Math.Log(l)) + 4;
    var LA = Levels(PA, D, nA); var LB = Levels(l, D, nB);
    int ti = -1, tk = -1;
    for (int i = 0; i < nA; i++) if (LA[i].J >= 1 && LA[i].step - LA[i].U <= X) ti = i;
    for (int k = 0; k < nB; k++) if (LB[k].J >= 1 && LB[k].step - LB[k].U <= X) tk = k;
    double u = (double)LA[ti].step, v = (double)LB[tk].step; // doubles ok for ratios (steps up to 1e300)
    double rho = Math.Exp(BigInteger.Log(LB[tk].step) - BigInteger.Log(LA[ti].step));
    double UA = Math.Exp(BigInteger.Log(LA[ti].U + 1) - BigInteger.Log(LA[ti].step)), UB = Math.Exp(BigInteger.Log(LB[tk].U + 1) - BigInteger.Log(LA[ti].step));
    double Xu = Math.Exp(lnX - BigInteger.Log(LA[ti].step));
    double massA, massB;
    var CA = Comps(1.0, UA, (long)LA[ti].J, Xu, out massA); var CB = Comps(rho, UB, (long)LB[tk].J, Xu, out massB);
    double sum = 0;
    foreach (var ca in CA) foreach (var cb in CB) {
      double d = ca.c - cb.c; double half = (ca.w1 + ca.w2 + cb.w1 + cb.w2) / 2; if (Math.Abs(d) >= half) continue;
      sum += ca.m * cb.m * H4(-d, new double[] { ca.w1, ca.w2, cb.w1, cb.w2 });
    }
    double Cc = 2 * Xu * sum / (massA * massA * massB * massB);
    double lnTA = 0, lnTB = 0; for (int j = 0; j < ti; j++) if (LA[j].J > 0) lnTA += Math.Log(2 * (double)LA[j].J + 1); for (int j = 0; j < tk; j++) if (LB[j].J > 0) lnTB += Math.Log(2 * (double)LB[j].J + 1);
    double lam = Math.Exp(lnTA + Math.Log(massA) + lnTB + Math.Log(massB) - lnX - Math.Log(2));
    Console.WriteLine($"ONE n={ti + 1} m={tk + 1} masses=({massA:F2},{massB:F2}) lambda_model={lam:F2} Ccont_one={Cc:F4}");
  }
}

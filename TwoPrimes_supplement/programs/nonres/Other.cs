using System;
using System.Collections.Generic;
using System.Numerics;
partial class P {
  static int PA = int.Parse(Environment.GetEnvironmentVariable("PA") ?? "2");
  static void Other(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); bool list = a[0] == "list";
    double xmax = 0, J0m = 0, xmin = 0; BigInteger Xat = 0;
    if (list) { xmax = double.Parse(a[3], System.Globalization.CultureInfo.InvariantCulture); J0m = double.Parse(a[4], System.Globalization.CultureInfo.InvariantCulture); xmin = double.Parse(a[5], System.Globalization.CultureInfo.InvariantCulture); }
    else Xat = BigInteger.Parse(a[3]);
    double Ln = Math.Log(D), L2 = Ln * Ln; long J0 = (long)(J0m * D);
    double lnLim = list ? xmax * L2 : BigInteger.Log(Xat);
    int nA = (int)Math.Sqrt((lnLim + 10) / Math.Log(PA)) + 4, nB = (int)Math.Sqrt((lnLim + 10) / Math.Log(l)) + 4;
    var LA = Levels(PA, D, nA); var LB = Levels(l, D, nB);
    Action<int, int, long, long, double> Eval = (i, k, JA, JB, lnX) => {
      double lnu = (double)i * i * Math.Log(PA), lnv = (double)k * k * Math.Log(l);
      double UA = Ratio(LA[i].U + 1, LA[i].step), UB = Math.Exp(BigInteger.Log(LB[k].U + 1) - BigInteger.Log(LA[i].step));
      double lnTA = 0, lnTB = 0;
      for (int j = 0; j < i; j++) if (LA[j].J > 0) lnTA += Math.Log(2 * (double)LA[j].J + 1);
      for (int j = 0; j < k; j++) if (LB[j].J > 0) lnTB += Math.Log(2 * (double)LB[j].J + 1);
      double lam, cc; double C = Cmodel(lnTA, lnTB, lnu, lnv, UA, UB, JA, JB, lnX, out lam, out cc);
      Console.WriteLine($"MODEL n={i + 1} m={k + 1} JA={JA} JB={JB} lambda_model={lam:F2} C_model={C:F4} Ccont={cc:F4} v/u={Math.Exp(lnv - lnu):E3}");
    };
    if (!list) {
      int ti = -1, tk = -1;
      for (int i = 0; i < nA; i++) if (LA[i].J >= 1 && LA[i].step - LA[i].U <= Xat) ti = i;
      for (int k = 0; k < nB; k++) if (LB[k].J >= 1 && LB[k].step - LB[k].U <= Xat) tk = k;
      long JA = (long)BigInteger.Min(LA[ti].J, (Xat + LA[ti].U) / LA[ti].step), JB = (long)BigInteger.Min(LB[tk].J, (Xat + LB[tk].U) / LB[tk].step);
      Eval(ti, tk, JA, JB, BigInteger.Log(Xat)); return;
    }
    for (int i = 0; i < nA; i++) for (int k = 0; k < nB; k++) {
      if (LA[i].J < 1 || LB[k].J < 1) continue;
      for (double jj = J0; jj <= (double)LA[i].J + 1e-9; jj *= 1.6) {
        long JA = (long)jj; BigInteger X = JA * LA[i].step + LA[i].U; double lnX = BigInteger.Log(X); double xr = lnX / L2; if (xr < xmin || xr > xmax) continue;
        BigInteger JBb = (X + LB[k].U) / LB[k].step; if (JBb < J0 || JBb > LB[k].J) continue;
        Console.Write($"X={X} x={xr:F2} "); Eval(i, k, JA, (long)JBb, lnX);
      }
    }
  }
}

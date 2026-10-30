using System;
using System.Collections.Generic;
using System.Numerics;
using System.Text;
// Least positive k with P_2(k-m) < 1/D and P_3(k) < 1/D (strict), by maximal-jump propagation. W_{1/D} contains m iff such k exists.
public static class ShiftJ {
  public static BigInteger Least(int m, int D, long maxSteps) {
    BigInteger k = 1; BigInteger bd = D;
    var p2 = new List<BigInteger>(); var p3 = new List<BigInteger>();
    for (int n = 1; n <= 24; n++) { p2.Add(BigInteger.Pow(2, n * n)); p3.Add(BigInteger.Pow(3, n * n)); }
    for (long steps = 0; steps < maxSteps; steps++) {
      BigInteger best = k; bool failed = false;
      BigInteger lim = (k + BigInteger.Abs(m)) * bd;
      for (int pass = 0; pass < 2; pass++) {
        var list = pass == 0 ? p2 : p3; BigInteger a = pass == 0 ? m : 0;
        for (int i = 0; i < list.Count; i++) {
          BigInteger q = list[i]; if (q > lim) break;
          BigInteger T = (q - 1) / bd;
          BigInteger s = BigInteger.Remainder(BigInteger.Remainder(k - a, q) + q, q);
          if (s > T && s < q - T) { failed = true; BigInteger kp = k + q - T - s; if (kp > best) best = kp; }
        }
      }
      if (!failed) return k;
      k = best;
    }
    return BigInteger.MinusOne;
  }
  public static string Run(int D, int lo, int hi, long maxSteps) {
    var sb = new StringBuilder(); sb.AppendLine("D=" + D + ": least positive k with P_2(k-m)<1/D, P_3(k)<1/D (digits of k; -1 = not finished in " + maxSteps + " steps)");
    int cnt = 0, none = 0;
    for (int m = lo; m <= hi; m++) {
      if (m == 0) continue;
      BigInteger k = Least(m, D, maxSteps);
      if (k.Sign < 0) { none++; sb.AppendLine("  m=" + m + ": unfinished"); } else { cnt++; sb.AppendLine("  m=" + m + ": digits=" + k.ToString().Length + " k=" + k); }
    }
    sb.AppendLine("  found " + cnt + ", unfinished " + none);
    return sb.ToString();
  }
}

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Text;

public static class JumpJA {
  // least positive k with P_2(k-1) < 1/D and P_3(k) < 1/D, by pure maximal-jump propagation (no CRT prefix).
  public static string Run(int D, long maxSteps) {
    BigInteger k = 1;
    long steps = 0;
    BigInteger bd = D;
    // precompute powers
    var p2 = new List<BigInteger>(); var p3 = new List<BigInteger>();
    for (int n = 1; n <= 20; n++) { p2.Add(BigInteger.Pow(2, n * n)); p3.Add(BigInteger.Pow(3, n * n)); }
    while (steps < maxSteps) {
      steps++;
      BigInteger best = k;      // largest proposed next position
      bool failed = false;
      BigInteger lim = k * bd;  // denominators > D*k are automatic
      for (int pass = 0; pass < 2; pass++) {
        var list = pass == 0 ? p2 : p3;
        BigInteger a = pass == 0 ? 1 : 0;
        for (int i = 0; i < list.Count; i++) {
          BigInteger q = list[i];
          if (q > lim) break;
          BigInteger T = (q - 1) / bd;
          BigInteger s = BigInteger.Remainder(k - a, q);
          if (s > T && s < q - T) {
            failed = true;
            BigInteger kp = k + q - T - s;
            if (kp > best) best = kp;
          }
        }
      }
      if (!failed) return "D=" + D + " least positive witness k=" + k + " after " + steps + " steps";
      k = best;
    }
    return "D=" + D + " not finished; k=" + k + " after " + steps + " steps";
  }
}

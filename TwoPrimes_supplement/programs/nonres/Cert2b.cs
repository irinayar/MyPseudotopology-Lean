using System;
using System.Collections.Generic;
using System.Numerics;
partial class P {
  // diagnostic: for the k-th pair of levels (k = 2, 3, ...) below the top, area A_k* of the level body and the indicator 30/sqrt(A_k*)
  static void LevDiag(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); int n = int.Parse(a[3]), m = int.Parse(a[4]);
    var LA = Levels(2, D, n + 1); var LB = Levels(l, D, m + 1); int iA = n - 1, iB = m - 1;
    var ia = new List<int>(); for (int j = iA - 1; j >= 0; j--) if (LA[j].J >= 1) ia.Add(j); var ib = new List<int>(); for (int j = iB - 1; j >= 0; j--) if (LB[j].J >= 1) ib.Add(j);
    Console.WriteLine($"D={D} l={l} n={n} m={m}: lower levels with J>=1: A {ia.Count}, B {ib.Count}");
    for (int k = 0; k < Math.Min(ia.Count, ib.Count); k++) {
      var A = LA[ia[k]]; var B = LB[ib[k]]; double lnA = BigInteger.Log(A.step), lnB = BigInteger.Log(B.step);
      double wb_over_wa = Math.Exp(lnB - lnA); double hA = Math.Exp(BigInteger.Log(A.U + 1) - lnA), hB = Math.Exp(BigInteger.Log(B.U + 1) - lnA);
      double aw = 2 * (double)A.J + 1, bw = 2 * (double)B.J + 1, W = 2 * (hA + hB);
      double rho = wb_over_wa; double Ak = rho >= 1 ? AreaBox(aw, bw, rho, W) : AreaBox(bw, aw, 1 / rho, W / rho);
      Console.WriteLine($"  level pair {k + 2}: J=({A.J},{B.J}) A_k*={Ak:E3} indicator 30/sqrt(A)={30 / Math.Sqrt(Math.Max(Ak, 1e-9)):F3}");
    }
  }
}

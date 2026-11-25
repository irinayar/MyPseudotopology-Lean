using System;
using System.Numerics;
partial class P {
  static void CertRow(string[] a) {
    long D = long.Parse(a[1]); int pA = int.Parse(a[2]), nA = int.Parse(a[3]); long JA = long.Parse(a[4]); int pB = int.Parse(a[5]), nB = int.Parse(a[6]); long JB = long.Parse(a[7]); BigInteger X = a.Length > 8 ? BigInteger.Parse(a[8]) : BigInteger.Zero;
    var LA = Levels(pA, D, nA); var LB = Levels(pB, D, nB); int i = nA - 1, k = nB - 1; if (X.IsZero) X = new BigInteger(JA) * LA[i].step + LA[i].U + 1;
    double lnu = (double)i * i * Math.Log(pA), lnv = (double)k * k * Math.Log(pB);
    double UAu = Ratio(LA[i].U + 1, LA[i].step), UBu = Math.Exp(BigInteger.Log(LB[k].U + 1) - BigInteger.Log(LA[i].step)); double Xu = Math.Exp(BigInteger.Log(X) - lnu);
    double rho = Math.Exp(lnv - lnu); double Cb, Cc, A0, lam0, Aeff; double lnTA = 0, lnTB = 0;
    if (rho >= 1) CertOne(JA + 1, JB + 1, rho, UAu, UBu, Xu, lnTA, lnTB, out Cb, out Cc, out A0, out lam0, out Aeff);
    else { double r2 = 1 / rho; CertOne(JB + 1, JA + 1, r2, UBu * r2, UAu * r2, Xu * r2, lnTB, lnTA, out Cb, out Cc, out A0, out lam0, out Aeff); }
    Console.WriteLine($"rho={rho:F5} A0={A0:F1} lam0={lam0:E3} Aeff={Aeff:F2} C_cont(integral)={Cc:F4} certified bound on lattice sum = {Cb:F4}");
  }
}

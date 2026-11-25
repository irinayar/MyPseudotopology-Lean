using System;
using System.Collections.Generic;
using System.Numerics;
// Closed-form (large-J) evaluation of rho, A0, lambda0', A_eff, C_cont for a given row, to compare with the numerical certificate (nonres certrow).
// Usage: gammarow D p nA JA q nB JB     (levels nA, nB as in nonres: step = p^((nA-1)^2); X = JA*u + hull + 1)
class P {
  static BigInteger Pw(int b, long e) { return BigInteger.Pow(b, (int)e); }
  static double H4(double x, double[] w) {
    double s = 0; foreach (var wi in w) s += wi / 2; double prod = 1; foreach (var wi in w) prod *= wi;
    double t = x + s, r = 0;
    for (int m = 0; m < 16; m++) { double sh = 0; int bits = 0; for (int i = 0; i < 4; i++) if ((m >> i & 1) != 0) { sh += w[i]; bits++; }
      double y = t - sh; if (y > 0) r += ((bits & 1) == 0 ? 1 : -1) * y * y * y / 6; }
    return r / prod;
  }
  static double H0Stable(double ua, double ub) { double w1 = 2 * Math.Min(ua, ub), w3 = 2 * Math.Max(ua, ub); double r = w1 / w3;
    if (r < 1e-3) return (1 / w3) * (1 - w1 / (3 * w3)); double[] ws = { w1 / w3, w1 / w3, 1.0, 1.0 }; return H4(0, ws) / w3; }
  static BigInteger Hull(int p, BigInteger D, int N) { BigInteger U = 0; for (int n = 1; n < N; n++) { BigInteger J = (Pw(p, (long)n * n) - 1) / (D * Pw(p, (long)(n - 1) * (n - 1))); U += J * Pw(p, (long)(n - 1) * (n - 1)); } return U; }
  static double Ld(BigInteger x) { return BigInteger.Log(x); }
  static void Main(string[] a) {
    BigInteger D = BigInteger.Parse(a[0]); int p = int.Parse(a[1]), nA = int.Parse(a[2]); BigInteger JA0 = BigInteger.Parse(a[3]); int q = int.Parse(a[4]), nB = int.Parse(a[5]); BigInteger JB0 = BigInteger.Parse(a[6]);
    BigInteger u = Pw(p, (long)(nA - 1) * (nA - 1)), v = Pw(q, (long)(nB - 1) * (nB - 1)); BigInteger UA0 = Hull(p, D, nA), UB0 = Hull(q, D, nB); BigInteger X = JA0 * u + UA0 + 1;
    bool pSmall = u <= v; BigInteger s1 = pSmall ? u : v, s2b = pSmall ? v : u, J1 = pSmall ? JA0 : JB0, J2 = pSmall ? JB0 : JA0, U1 = pSmall ? UA0 : UB0, U2 = pSmall ? UB0 : UA0;
    double lnS1 = Ld(s1); double rho = Math.Exp(Ld(s2b) - lnS1); double UAu = Math.Exp(Ld(U1 + 1) - lnS1), UBu = Math.Exp(Ld(U2 + 1) - lnS1); double W = 2 * UAu + 2 * UBu;
    double lnJ1 = Ld(J1 + 1), lnJ2 = Ld(J2 + 1); double al = Math.Exp(lnJ1 - Math.Log(rho) - lnJ2); double m = Math.Min(al, 1.0);
    double f = 2 * (al * m - (al + 1) * m * m / 2 + m * m * m / 3); double H0 = H0Stable(UAu, UBu);
    double Aeff = Math.Exp(lnJ2 + Math.Log(f / (al * H0))); double lnXu = Ld(X) - lnS1; double Cc = 2 * Math.Exp(lnXu + Math.Log(f) - Math.Log(rho * al * al) - lnJ2); double A0 = 4 * W * m * Math.Exp(lnJ2);
    double bestg = Math.Max(Math.Exp(-lnJ1), 1.0 / W);
    BigInteger aa = s2b, bb = s1, hm1 = 1, hm2 = 0, km1 = 0, km2 = 1;
    while (bb != 0) { BigInteger qt = aa / bb, r = aa % bb; aa = bb; bb = r; BigInteger hn = qt * hm1 + hm2, kn = qt * km1 + km2; hm2 = hm1; hm1 = hn; km2 = km1; km1 = kn; if (kn == 0) continue; if (hn > J1 + 1 || kn > J2 + 1) break;
      double g1 = Math.Exp(Ld(hn) - lnJ1), g2 = Math.Exp(Ld(kn) - lnJ2); BigInteger diff = BigInteger.Abs(hn * s1 - kn * s2b); double g3 = diff.IsZero ? 0 : Math.Exp(Ld(diff) - lnS1 - Math.Log(W)); double g = Math.Max(g1, Math.Max(g2, g3)); if (g < bestg) bestg = g; }
    double Gam = Cc * (1 + (2 * Math.Sqrt(A0) + 1 + 2 / bestg) / Aeff);
    Console.WriteLine($"rho={rho:F5} A0={A0:F1} lam0={bestg:E3} Aeff={Aeff:F2} C_cont(integral)={Cc:F4} certified bound on lattice sum = {Gam:F4}");
  }
}

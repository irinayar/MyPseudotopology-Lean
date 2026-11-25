using System;
using System.Collections.Generic;
using System.Numerics;
// Gamma_D = C_cont (1 + (2 sqrt(A0) + 1 + 2/lambda0') / A_eff) (Corollary 8.7) at the heights constructed in Proposition 8.14, for huge D.
// Large-J closed forms (relative error W/J): I_Phi = 2 rho int_0^m (a-y)(b-y) dy, m = min(a,b), a = J_A1/rho, b = J_B1; Phi_max = J_A1 J_B1 H(0); A0 = 4 W m; lambda0' exactly from the convergents of the ratio of the steps.
// Usage: gammacheck p q eps x2 L0 L1 step
class P {
  static Dictionary<(int,long),BigInteger> pwc = new(); static BigInteger Pw(int b, long e) { if (pwc.TryGetValue((b,e), out var r)) return r; r = BigInteger.Pow(b, (int)e); pwc[(b,e)] = r; return r; }
  static Dictionary<(int,int),BigInteger> hullc = new();
  static double H4(double x, double[] w) {
    double s = 0; foreach (var wi in w) s += wi / 2; double prod = 1; foreach (var wi in w) prod *= wi;
    double t = x + s, r = 0;
    for (int m = 0; m < 16; m++) { double sh = 0; int bits = 0; for (int i = 0; i < 4; i++) if ((m >> i & 1) != 0) { sh += w[i]; bits++; }
      double y = t - sh; if (y > 0) r += ((bits & 1) == 0 ? 1 : -1) * y * y * y / 6; }
    return r / prod;
  }
  static double H0Stable(double ua, double ub) { // density at 0 of the sum of two U[-ua,ua] and two U[-ub,ub] (half-widths)
    double w1 = 2 * Math.Min(ua, ub), w3 = 2 * Math.Max(ua, ub); double r = w1 / w3;
    if (r < 1e-3) return (1 / w3) * (1 - w1 / (3 * w3));
    double[] ws = { w1 / w3, w1 / w3, 1.0, 1.0 }; return H4(0, ws) / w3; }
  static BigInteger Hull(int p, BigInteger D, int N) { if (hullc.TryGetValue((p,N), out var cached)) return cached; var res = HullRaw(p, D, N); hullc[(p,N)] = res; return res; }
  static BigInteger HullRaw(int p, BigInteger D, int N) { BigInteger U = 0; for (int n = 1; n < N; n++) { BigInteger J = (Pw(p, (long)n * n) - 1) / (D * Pw(p, (long)(n - 1) * (n - 1))); U += J * Pw(p, (long)(n - 1) * (n - 1)); } return U; }
  static double Ld(BigInteger x) { return BigInteger.Log(x); }
  static void Main(string[] a) {
    var ci = System.Globalization.CultureInfo.InvariantCulture;
    int p = int.Parse(a[0]), q = int.Parse(a[1]); double eps = double.Parse(a[2], ci), x2 = double.Parse(a[3], ci), L0 = double.Parse(a[4], ci), L1 = double.Parse(a[5], ci), st = double.Parse(a[6], ci);
    double lp = Math.Log(p), lq = Math.Log(q); double Aa = 1 / Math.Sqrt(lp) + 1 / Math.Sqrt(lq), c = 0.25 * (1 / lp + 1 / lq); double xS = Math.Pow((Aa + Math.Sqrt(Aa * Aa - 4 * c)) / 2, 2);
    Console.WriteLine($"pair {{{p},{q}}} xS={xS:F5} x0={xS + eps:F5} x2={x2}");
    int tot = 0, good = 0; double worstBest = 0; 
    for (double Lr = L0; Lr <= L1; Lr += st) {
      BigInteger D = (BigInteger)Math.Exp(Lr); while (BigInteger.GreatestCommonDivisor(D, p) != 1 || BigInteger.GreatestCommonDivisor(D, q) != 1) D += 1;
      pwc.Clear(); hullc.Clear(); double L = Ld(D); double sstar = (xS + eps) * L * L;
      int Ns = (int)Math.Ceiling(Math.Sqrt((sstar + L) / lp)), Ms = (int)Math.Ceiling(Math.Sqrt((sstar + L) / lq));
      double bestG = 1e300; string bestS = ""; int cand = 0;
      for (int N = Ns; N <= Ns + 6; N++) for (int M = Ms; M <= Ms + 14; M++) {
        double lowN = (N - 1.0) * (N - 1) * lp + L, upN = N * (double)N * lp - L, lowM = (M - 1.0) * (M - 1) * lq + L, upM = M * (double)M * lq - L;
        double lo = Math.Max(Math.Max(lowN, lowM), sstar), hi = Math.Min(upN, upM); if (lo >= hi - 2) continue;
        foreach (double frac in new double[] { 0.5, 0.2, 0.8 }) {
          double s = lo + 1 + frac * (hi - lo - 2); double s2 = s / Math.Log(2); long k = (long)Math.Floor(s2) - 50; BigInteger X = new BigInteger(Math.Pow(2, s2 - k)) << (int)k;
          BigInteger u = Pw(p, (long)(N - 1) * (N - 1)), v = Pw(q, (long)(M - 1) * (M - 1)), qN = Pw(p, (long)N * N), qM = Pw(q, (long)M * M);
          if (!(X >= D * u && X >= D * v && X * D < qN && X * D < qM)) continue;
          BigInteger JN = (qN - 1) / (D * u), JM = (qM - 1) / (D * v); BigInteger JA0 = BigInteger.Min(JN, X / u), JB0 = BigInteger.Min(JM, X / v); if (JA0 < D || JB0 < D) continue;
          BigInteger UA0 = Hull(p, D, N), UB0 = Hull(q, D, M); // hulls in absolute units
          // roles: small step = 'S1' with range J1, hull U1; big step = 'S2'
          bool pSmall = u <= v; BigInteger s1 = pSmall ? u : v, s2b = pSmall ? v : u, J1 = pSmall ? JA0 : JB0, J2 = pSmall ? JB0 : JA0, U1 = pSmall ? UA0 : UB0, U2 = pSmall ? UB0 : UA0;
          double lnS1 = Ld(s1); double rho = Math.Exp(Ld(s2b) - lnS1); // may overflow? rho moderate
          double UAu = Math.Exp(Ld(U1 + 1) - lnS1), UBu = Math.Exp(Ld(U2 + 1) - lnS1); double[] w = { 2 * UAu, 2 * UAu, 2 * UBu, 2 * UBu }; double W = 2 * UAu + 2 * UBu;
          double lnJ1 = Ld(J1 + 1), lnJ2 = Ld(J2 + 1); // a1 = J1+1 (x-range), b1 = J2+1
          double ratio_ab = Math.Exp(lnJ1 - Math.Log(rho) - lnJ2); // alpha = (J1+1)/rho/(J2+1)
          double al = ratio_ab; double m = Math.Min(al, 1.0);
          double f = al * m - (al + 1) * m * m / 2 + m * m * m / 3; f *= 2; // I = rho b^3 f
          double H0 = H0Stable(UAu, UBu);
          double lnAeff = lnJ2 + Math.Log(f / (al * H0)); double Aeff = Math.Exp(lnAeff);
          double lnXu = Ld(X) - lnS1; // X' in units of small step
          double Cc = 2 * Math.Exp(lnXu + Math.Log(f) - Math.Log(rho * al * al) - lnJ2) ; // 2 X' f / (rho alpha^2 b)
          double A0 = 4 * W * m * Math.Exp(lnJ2);
          // lambda0': convergents of s2b / s1
          BigInteger P0 = s2b, Q0 = s1; BigInteger h1 = 1, h0 = 0, k1 = 0, k0 = 1; // h/k convergents m/n with m ~ n rho
          double bestg = 1e300; BigInteger bm = 0, bn = 0; BigInteger num = P0, den = Q0;
          // candidate (1,0)
          bestg = Math.Max(Math.Exp(-lnJ1), Math.Exp(lnS1 - Math.Log(W) - lnS1) * 1.0 / 1.0); // |1*s1 - 0| / W in units of s1 = 1/W
          bestg = Math.Max(Math.Exp(-lnJ1), 1.0 / W); bm = 1; bn = 0;
          BigInteger aa = P0, bb = Q0; BigInteger hm1 = 1, hm2 = 0, km1 = 0, km2 = 1;
          while (bb != 0) {
            BigInteger qt = aa / bb; BigInteger r = aa % bb; aa = bb; bb = r;
            BigInteger hn = qt * hm1 + hm2, kn = qt * km1 + km2; hm2 = hm1; hm1 = hn; km2 = km1; km1 = kn;
            if (kn == 0) continue; if (hn > J1 + 1 || kn > J2 + 1) break;
            // vector (m, n) = (hn, kn): g = max(m/a1, n/b1, |m*s1 - n*s2b| / (W*s1))
            double g1 = Math.Exp(Ld(hn) - lnJ1), g2 = Math.Exp(Ld(kn) - lnJ2); BigInteger diff = BigInteger.Abs(hn * s1 - kn * s2b); double g3 = diff.IsZero ? 0 : Math.Exp(Ld(diff) - lnS1 - Math.Log(W));
            double g = Math.Max(g1, Math.Max(g2, g3)); if (g < bestg) { bestg = g; bm = hn; bn = kn; }
          }
          double lam0 = bestg; double Gam = Cc * (1 + (2 * Math.Sqrt(A0) + 1 + 2 / lam0) / Aeff);
          cand++; if (Environment.GetEnvironmentVariable("DBG") != null) Console.WriteLine($"  dbg N={N} M={M} frac={frac} lnJ1={lnJ1:F1} lnJ2={lnJ2:F1} lnAeff={lnAeff:F1} lam0={lam0:E3} W={W:E3} H0={H0:E3} Ccont={Cc:F4} A0={A0:E3} Gam={Gam:F5}");
          if (Gam < bestG) { bestG = Gam; bestS = $"N={N} M={M} frac={frac} Ccont={Cc:F4} log10(lam0 Aeff)={Math.Log10(lam0) + Math.Log10(Aeff):F1} log10(Aeff)={Math.Log10(Aeff):F0} m={bm.ToString().Substring(0, Math.Min(12, bm.ToString().Length))} x={Ld(X) / (L * L):F4}"; }
        }
      }
      tot++; if (bestG <= 2) good++; if (bestG > worstBest && bestG < 1e299) worstBest = bestG;
      Console.WriteLine($"L={L:F2} candidates={cand} best Gamma={bestG:F4} {bestS}");
    }
    Console.WriteLine($"pair {{{p},{q}}}: cases={tot}, Gamma<=2 found in {good}; worst (over cases) of the best Gamma = {worstBest:F4}");
  }
}

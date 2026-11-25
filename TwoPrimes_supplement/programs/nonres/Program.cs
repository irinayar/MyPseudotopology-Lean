using System;
using System.Collections.Generic;
using System.Numerics;
// Uniform-cluster model of the energy of two one-sided balls (bases 2 and l) at stage heights.
// A = U_{j=0..JA}(j u + T_A), T_A uniform on [-UA,UA]; B likewise with step v.  C = (2X+1) sum cA(m) cB(n) H(m u - n v)/((JA+1)(JB+1))^2 + 1/lambda,
// H = density at Delta of the sum of four uniforms (widths 2UA,2UA,2UB,2UB).
// Usage: nonres row D pA nA JA pB nB JB     (validation, X = JA*u+UA)
//        nonres scan D l xlo xhi J0mult     (scan all level pairs and heights with ln X in [xlo,xhi]*L^2, JA,JB >= J0mult*D)
partial class P {
  static double H4(double x, double[] w) { // density of sum of centered uniforms of widths w[0..3] at x
    double s = 0; foreach (var wi in w) s += wi / 2; double prod = 1; foreach (var wi in w) prod *= wi;
    double t = x + s, r = 0;
    for (int m = 0; m < 16; m++) { double sh = 0; int bits = 0; for (int i = 0; i < 4; i++) if ((m >> i & 1) != 0) { sh += w[i]; bits++; }
      double y = t - sh; if (y > 0) r += ((bits & 1) == 0 ? 1 : -1) * y * y * y / 6; }
    return r / prod;
  }
  class Lv { public double lnq; public BigInteger J; public BigInteger step; public BigInteger U; } // level n: J_n, step q_{n-1}, U = hull of lower levels (n' < n)
  static List<Lv> Levels(int p, long D, int nmax) {
    var L = new List<Lv>(); BigInteger U = 0;
    for (int n = 1; n <= nmax; n++) {
      BigInteger q = BigInteger.Pow(p, n * n), qp = BigInteger.Pow(p, (n - 1) * (n - 1)); BigInteger J = (q - 1) / (D * qp);
      L.Add(new Lv { lnq = n * n * Math.Log(p), J = J, step = qp, U = U });
      U += J * qp;
    }
    return L;
  }
  static double Ratio(BigInteger a, BigInteger b) { return Math.Exp(BigInteger.Log(a) - BigInteger.Log(b)); }
  // returns C for given tops
  static double Cmodel(double lnTA, double lnTB, double lnu, double lnv, double UAr, double UBr, long JA, long JB, double lnX, out double lam, out double cc) {
    // all lengths in units of u: step u = 1, step v = rho, UA = UAr (units of u), UB = UBr*rho? pass UBr in units of u as well
    double rho = Math.Exp(lnv - lnu);
    double[] w = { 2 * UAr, 2 * UAr, 2 * UBr, 2 * UBr };
    double sup = 2 * UAr + 2 * UBr; double sum = 0;
    for (long m = -JA; m <= JA; m++) {
      double cm = JA + 1 - Math.Abs(m); long n0 = (long)Math.Round(m / rho); long kmax = (long)(sup / rho) + 1;
      if (kmax > 40) { if (Math.Abs(n0) <= JB) sum += cm * (JB + 1 - Math.Abs(n0)) / rho; continue; }
      for (long n = n0 - kmax; n <= n0 + kmax; n++) {
        if (Math.Abs(n) > JB) continue; double d = m - n * rho; if (Math.Abs(d) >= sup) continue;
        sum += cm * (JB + 1 - Math.Abs(n)) * H4(d, w);
      }
    }
    double twoX1 = 2 * Math.Exp(lnX - lnu);  // (2X+1) in units of u
    double ccont = twoX1 * sum / (((double)(JA + 1)) * (JB + 1)) / (((double)(JA + 1)) * (JB + 1));
    double lnA = lnTA + Math.Log(JA + 1), lnB = lnTB + Math.Log(JB + 1);
    lam = Math.Exp(lnA + lnB - lnX - Math.Log(2)); cc = ccont;
    return ccont + 1 / lam;
  }
  static void Main(string[] a) {
    if (a[0] == "list" || a[0] == "at") { Other(a); return; }
    if (a[0] == "one") { One(a); return; }
    if (a[0] == "cert") { Cert(a); return; }
    if (a[0] == "levk") { LevK(a); return; }
    if (a[0] == "cert2") { Cert2(a); return; }
    if (a[0] == "levdiag") { LevDiag(a); return; }
    if (a[0] == "certk") { CertK(a); return; }
    if (a[0] == "certm") { CertM(a); return; }
    if (a[0] == "certrow") { CertRow(a); return; }
    if (a[0] == "row") {
      long D = long.Parse(a[1]); int pA = int.Parse(a[2]), nA = int.Parse(a[3]); long JA = long.Parse(a[4]); int pB = int.Parse(a[5]), nB = int.Parse(a[6]); long JB = long.Parse(a[7]);
      var LA = Levels(pA, D, nA); var LB = Levels(pB, D, nB);
      double lnTA = 0, lnTB = 0; for (int i = 0; i < nA - 1; i++) if (LA[i].J > 0) lnTA += Math.Log(2 * (double)LA[i].J + 1); for (int i = 0; i < nB - 1; i++) if (LB[i].J > 0) lnTB += Math.Log(2 * (double)LB[i].J + 1);
      double lnu = Math.Log((double)(nA - 1) * (nA - 1) * Math.Log(pA)); lnu = (nA - 1) * (nA - 1) * Math.Log(pA); double lnv = (nB - 1) * (nB - 1) * Math.Log(pB) + Math.Log(double.Parse(Environment.GetEnvironmentVariable("F") ?? "1", System.Globalization.CultureInfo.InvariantCulture));
      double UA = Ratio(LA[nA - 1].U + 1, LA[nA - 1].step) * 1.0; double UB = Ratio(LB[nB - 1].U + 1, LA[nA - 1].step);
      // units of u: UA/u, UB/u
      UA = Ratio(LA[nA - 1].U + 1, LA[nA - 1].step); UB = Ratio(LB[nB - 1].U + 1, LA[nA - 1].step);
      double X = JA * Math.Exp(lnu) + UA * Math.Exp(lnu); double lnX = Math.Log(X);
      double lam, cc; double C = Cmodel(lnTA, lnTB, lnu, lnv, UA, UB, JA, JB, lnX, out lam, out cc);
      Console.WriteLine($"D={D} UA/u={UA:F5} UB/u={UB:F5} lambda={lam:F2} Ccont={cc:F4} C={C:F4}");
      return;
    }
    {
      long D = long.Parse(a[1]); int l = int.Parse(a[2]); double xlo = double.Parse(a[3]), xhi = double.Parse(a[4]); double J0m = double.Parse(a[5]);
      double Ln = Math.Log(D), L2 = Ln * Ln; long J0 = (long)(J0m * D);
      int nmaxA = (int)Math.Sqrt(xhi * L2 / Math.Log(2)) + 3, nmaxB = (int)Math.Sqrt(xhi * L2 / Math.Log(l)) + 3;
      var LA = Levels(2, D, nmaxA); var LB = Levels(l, D, nmaxB);
      int tot = 0, bad8 = 0, bad2 = 0; double best = 1e9, worst = 0, bpm = 1e9; string worstS = ""; string bestS = ""; var perPair = new List<string>();
      for (int i = 0; i < nmaxA; i++) for (int k = 0; k < nmaxB; k++) {
        if (LA[i].J < 1 || LB[k].J < 1) continue;
        double lnu = (double)i * i * Math.Log(2), lnv = (double)k * k * Math.Log(l);
        long JAmax = (long)Math.Min((double)LA[i].J, 3e6), JBmax = (long)Math.Min((double)LB[k].J, 3e6);
        double UA = Ratio(LA[i].U + 1, LA[i].step), UB = Ratio(LB[k].U + 1, LA[i].step) * (i >= 0 ? 1 : 1); // units of u (u = LA[i].step)
        // UB in units of u: LB[k].U / u
        UB = Math.Exp(BigInteger.Log(LB[k].U + 1) - BigInteger.Log(LA[i].step));
        double lnTA = 0, lnTB = 0; for (int j = 0; j < i; j++) if (LA[j].J > 0) lnTA += Math.Log(2 * (double)LA[j].J + 1); for (int j = 0; j < k; j++) if (LB[j].J > 0) lnTB += Math.Log(2 * (double)LB[j].J + 1);
        double pairMin = 1e9, pairMax = 0; int cnt = 0; double worstJ = 0;
        for (double jj = J0; jj <= (double)LA[i].J + 1e-9; jj *= 1.35) {
          long JA = (long)jj; double lnX = lnu + Math.Log(JA + UA);
          double lnXr = lnX / L2; if (lnXr < xlo || lnXr > xhi) continue;
          double JBd = Math.Floor(Math.Exp(lnX - lnv) + UB * Math.Exp(lnu - lnv)); long JB = (long)JBd;
          if (JB < J0 || JB > (double)LB[k].J || JA > JAmax || JB > JBmax) continue;
          double lam, cc; double C = Cmodel(lnTA, lnTB, lnu, lnv, UA, UB, JA, JB, lnX, out lam, out cc);
          tot++; cnt++; if (C > 8.0 / 3 - 0.05) bad8++; if (C > 2.0) bad2++;
          if (C < pairMin) pairMin = C; if (C > pairMax) { pairMax = C; worstJ = JA; }
          if (C > worst) { worst = C; worstS = $"n={i + 1} m={k + 1} JA={JA} JB={JB} v/u={Math.Exp(lnv - lnu):F4}"; } if (C < best) { best = C; bestS = $"n={i + 1} m={k + 1} JA={JA} JB={JB} lnX/L2={lnXr:F3} lam={lam:F1}"; }
        }
        if (cnt > 0 && pairMax < bpm) { bpm = pairMax; } if (cnt > 0) perPair.Add($"  (n,m)=({i + 1},{k + 1}) v/u={Math.Exp(lnv - lnu):E3} heights={cnt} Cmin={pairMin:F3} Cmax={pairMax:F3}");
      }
      Console.WriteLine($"D={D} l={l} window x in [{xlo},{xhi}] J0={J0}: combos={tot} C>8/3-0.05: {bad8}, C>2: {bad2}, best C={best:F3} WORST C={worst:F3} BPM={bpm:F3} at {worstS}");
      foreach (var s in perPair) Console.WriteLine(s);
    }
  }
}

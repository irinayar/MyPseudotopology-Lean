using System;
using System.Collections.Generic;
using System.Numerics;
// Certificate: rigorous upper bound for the lattice sum of the uniform-cluster model,
//   Sum_{(m,n) in Z^2} Phi(m,n) <= I_Phi + Phimax (2 sqrt(A0) + 1 + 2/lambda0),
// Phi(x,y) = (JA+1-|x|)+ (JB+1-|y|)+ H(x - y rho) (log-concave), K0 = {Phi>0}, A0 = area, lambda0 = first minimum of K0 w.r.t. Z^2.
// Usage: nonres cert D l xlo xhi J0mult
partial class P {
  static double Lam1(double JA, double JB, double rho, double W, out long ba, out long bb) {
    // first minimum of K0 = {|x|<JA, |y|<JB, |x - y rho| < W}, rho >= 1; vectors (a,b): b=1..ceil(JB), a in {floor,ceil}(b rho)
    double best = double.MaxValue; ba = 0; bb = 0;
    long bmax = (long)Math.Floor(JB);
    for (long b = 1; b <= bmax; b++) {
      double t = b * rho; double fl = Math.Floor(t - W) - 1; int cnt = (int)Math.Ceiling(2 * W) + 4;
      for (int c = 0; c < cnt; c++) { double a = fl + c; double nrm = Math.Max(Math.Max(Math.Abs(a) / JA, b / JB), Math.Abs(a - t) / W); if (nrm < best) { best = nrm; ba = (long)a; bb = b; } }
    }
    // vectors with b = 0: (a,0): norm >= |a|/W * 1 (a>=1) -> 1/ W ... (rho >= 1 means |a| >= 1)
    double nb0 = Math.Max(1.0 / JA, 1.0 / W); if (nb0 < best) { best = nb0; ba = 1; bb = 0; }
    return best;
  }
  static void CertOne(double JA1, double JB1, double rho, double UA, double UB, double Xu, double lnTA, double lnTB, out double Cbound, out double Ccont, out double A0, out double lam0, out double Aeff) {
    // JA1 = JA + 1, JB1 = JB + 1 (support half-widths of the weights), all lengths in units of the A step (rho >= 1)
    double[] w = { 2 * UA, 2 * UA, 2 * UB, 2 * UB }; double W = 2 * UA + 2 * UB;
    // area of K0
    int NX = 6000; double A = 0; double dx = 2 * JA1 / NX;
    for (int i = 0; i < NX; i++) { double x = -JA1 + (i + 0.5) * dx; double lo = Math.Max(-JB1, (x - W) / rho), hi = Math.Min(JB1, (x + W) / rho); if (hi > lo) A += (hi - lo) * dx; }
    A0 = A * 1.001; ba_ = 0; bb_ = 0; long ba, bb; lam0 = Lam1(JA1, JB1, rho, W, out ba, out bb);
    // I_Phi = int int (JA1-|x|)(JB1-|y|) H(x - y rho) dx dy ; integrate over x, y in the window
    double I = 0; int NY = 48;
    for (int i = 0; i < NX; i++) {
      double x = -JA1 + (i + 0.5) * dx; double lo = Math.Max(-JB1, (x - W) / rho), hi = Math.Min(JB1, (x + W) / rho); if (hi <= lo) continue; double dy = (hi - lo) / NY; double inner = 0;
      for (int j = 0; j < NY; j++) { double y = lo + (j + 0.5) * dy; inner += (JB1 - Math.Abs(y)) * H4(x - y * rho, w) * dy; }
      I += (JA1 - Math.Abs(x)) * inner * dx;
    }
    double Phimax = JA1 * JB1 * H4(0, w); Aeff = I / Phimax;
    double norm = JA1 * JB1; double twoX = 2 * Xu;
    Ccont = twoX * I / (norm * norm);
    Cbound = twoX * (I + Phimax * (2 * Math.Sqrt(A0) + 1 + 2 / lam0)) / (norm * norm);
  }
  static long ba_, bb_;
  static void Cert(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); double xlo = double.Parse(a[3]), xhi = double.Parse(a[4]); double J0m = double.Parse(a[5]);
    double Ln = Math.Log(D), L2 = Ln * Ln; long J0 = (long)(J0m * D);
    int nmaxA = (int)Math.Sqrt(xhi * L2 / Math.Log(2)) + 3, nmaxB = (int)Math.Sqrt(xhi * L2 / Math.Log(l)) + 3;
    var LA = Levels(2, D, nmaxA); var LB = Levels(l, D, nmaxB);
    int viol = 0; double maxcc = 0, maxratio = 0; double bestBound = 1e9; string bestS = ""; int tot = 0, ok = 0; double worstBound = 0; string worstS = "";
    var pairBest = new Dictionary<string, double>(); var pairWorst = new Dictionary<string, double>();
    for (int i = 0; i < nmaxA; i++) for (int k = 0; k < nmaxB; k++) {
      if (LA[i].J < 1 || LB[k].J < 1) continue;
      double lnu = (double)i * i * Math.Log(2), lnv = (double)k * k * Math.Log(l);
      double UAu = Ratio(LA[i].U + 1, LA[i].step), UBu = Math.Exp(BigInteger.Log(LB[k].U + 1) - BigInteger.Log(LA[i].step));
      double lnTA = 0, lnTB = 0;
      for (double jj = J0; jj <= (double)LA[i].J + 1e-9; jj *= 1.35) {
        long JA = (long)jj; double lnX = lnu + Math.Log(JA + UAu); double xr = lnX / L2; if (xr < xlo || xr > xhi) continue;
        double JBd = Math.Floor(Math.Exp(lnX - lnv) + UBu * Math.Exp(lnu - lnv)); long JB = (long)JBd; if (JB < J0 || JB > (double)LB[k].J) continue;
        if (JA > 4000000 || JB > 4000000) continue;
        double rho = Math.Exp(lnv - lnu); double Cb, Cc, A0, lam0, Aeff;
        double Xu = Math.Exp(lnX - lnu);
        if (rho >= 1) CertOne(JA + 1, JB + 1, rho, UAu, UBu, Xu, lnTA, lnTB, out Cb, out Cc, out A0, out lam0, out Aeff);
        else { double rho2 = 1 / rho; CertOne(JB + 1, JA + 1, rho2, UBu * rho2, UAu * rho2, Xu * rho2, lnTB, lnTA, out Cb, out Cc, out A0, out lam0, out Aeff); }
        double lam2, cc2; double Ccheck = Cmodel(lnTA, lnTB, lnu, lnv, UAu, UBu, JA, JB, lnX, out lam2, out cc2); if (cc2 > Cb + 1e-3) viol++; if (cc2 > maxcc) maxcc = cc2; double rr = cc2 / Cb; if (rr > maxratio) maxratio = rr;
        tot++; if (Cb < 8.0 / 3 - 0.1) ok++; if (Cb < bestBound) { bestBound = Cb; bestS = $"n={i + 1} m={k + 1} JA={JA} JB={JB} Ccont={Cc:F3} bound={Cb:F3} A0={A0:F1} lam0={lam0:E2} Aeff={Aeff:F1}"; }
        if (Cb > worstBound) { worstBound = Cb; worstS = $"n={i + 1} m={k + 1} JA={JA} JB={JB} Ccont={Cc:F3} bound={Cb:F3} A0={A0:F1} lam0={lam0:E2} Aeff={Aeff:F1}"; }
        string key = $"({i + 1},{k + 1})"; if (!pairWorst.ContainsKey(key) || Cb > pairWorst[key]) pairWorst[key] = Cb; if (!pairBest.ContainsKey(key) || Cb < pairBest[key]) pairBest[key] = Cb;
      }
    }
    // per D: is there a pair all of whose heights have bound < 8/3 - 0.1 ?
    int goodPairs = 0; foreach (var kv in pairWorst) if (kv.Value < 8.0 / 3 - 0.1) goodPairs++;
    Console.WriteLine($"CHECK D={D} l={l}: lattice sum (Cmodel) exceeds certificate in {viol} of {tot} combos; max lattice sum {maxcc:F4}; max ratio sum/bound {maxratio:F3}");
    Console.WriteLine($"D={D} l={l}: combos={tot} bound<8/3-0.1: {ok}; pairs={pairWorst.Count}, pairs with ALL heights bound<8/3-0.1: {goodPairs}; best bound {bestBound:F3} [{bestS}]; worst bound {worstBound:F3} [{worstS}]");
  }
}

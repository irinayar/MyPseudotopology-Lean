using System;
using System.Collections.Generic;
using System.Numerics;
// Two-level certificate. Model M_2: top level exact clusters (m,n), second level exact digits (alpha,beta), rest uniform.
// Rigorous (hand proof, not part of the article): S_2 <= Main1 + Err,
//   Main1 = I_Phi1 + Phi1max (2 sqrt(A0) + 1 + 2/lambda0)        [Theorem X2, Phi1(x,y) = c_A c_B I_2(x u - y v)],
//   Err   = Psimax* e_2 S_w,  e_2 = 3 sqrt(A2*) + 1 + 1/lambda2*   [Lemma X1' for translates],  S_w <= I_w + (JA+1)(JB+1)(2 sqrt(A0)+1+2/lambda0).
// Usage: nonres cert2 D l n m JA JB
partial class P {
  static double Lam1sw(double JA, double JB, double rho, double W) { // first minimum, any rho>0 (swap if rho<1)
    long a, b; if (rho >= 1) return Lam1(JA, JB, rho, W, out a, out b); return Lam1(JB, JA, 1 / rho, W / rho, out a, out b); }
  static double AreaBox(double JA, double JB, double rho, double W) { // area of {|x|<JA,|y|<JB,|x - y rho|<W}, rho>=1 assumed
    int NX = 20000; double dx = 2 * JA / NX, A = 0; for (int i = 0; i < NX; i++) { double x = -JA + (i + 0.5) * dx; double lo = Math.Max(-JB, (x - W) / rho), hi = Math.Min(JB, (x + W) / rho); if (hi > lo) A += (hi - lo) * dx; } return A; }
  static void Cert2(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); int n = int.Parse(a[3]), m = int.Parse(a[4]); long JA = long.Parse(a[5]), JB = long.Parse(a[6]);
    int nA = n + 1, nB = m + 1; var LA = Levels(2, D, nA); var LB = Levels(l, D, nB);
    int iA = n - 1, iB = m - 1; int jA = iA - 1; while (jA >= 0 && LA[jA].J < 1) jA--; int jB = iB - 1; while (jB >= 0 && LB[jB].J < 1) jB--;
    if (jA < 0 || jB < 0) { Console.WriteLine("no second level"); return; }
    // all lengths in units of the A top step u
    double lnu = BigInteger.Log(LA[iA].step); Func<BigInteger, double> U = x => Math.Exp(BigInteger.Log(x + 1) - lnu); Func<BigInteger, double> S = x => Math.Exp(BigInteger.Log(x) - lnu);
    double rho = S(LB[iB].step), UA0 = U(LA[iA].U), UB0 = U(LB[iB].U), wA = S(LA[jA].step), wB = S(LB[jB].step), hA2 = U(LA[jA].U), hB2 = U(LB[jB].U);
    double JA1 = (double)LA[jA].J, JB1 = (double)LB[jB].J; double Xu = JA + UA0;
    double W1 = 2 * (UA0 + UB0), W2 = 2 * (hA2 + hB2);
    double[] w2 = { 2 * hA2, 2 * hA2, 2 * hB2, 2 * hB2 }; double H0 = H4(0, w2);
    // swap roles if rho < 1 (swap A and B everywhere)
    double Ja = JA, Jb = JB; double rr = rho; double wa = wA, wb = wB, J1a = JA1, J1b = JB1;
    if (rho < 1) { Ja = JB; Jb = JA; rr = 1 / rho; wa = wB / rho; wb = wA / rho; J1a = JB1; J1b = JA1; W1 = W1 / rho; W2 = W2 / rho; Xu = Xu / rho; H0 = H0 * rho; }
    // note: after swapping, lengths are in units of the (former) B step; hulls enter only through W1, W2 and H0 (H0 rescaled).
    double JA_ = Ja + 1, JB_ = Jb + 1;
    // top-level strip body K0
    double A0 = AreaBox(JA_, JB_, rr, W1) * 1.001; double lam0 = Lam1sw(JA_, JB_, rr, W1);
    double e1 = 2 * Math.Sqrt(A0) + 1 + 2 / lam0;
    // I_2(z): table
    double bw = 2 * J1b + 1, aw = 2 * J1a + 1; int NZ = 200; var T = new double[NZ + 1];
    for (int k = 0; k <= NZ; k++) { double z = W1 * k / NZ; int NA = 20000; double da = 2 * aw / NA, s = 0;
      for (int i = 0; i < NA; i++) { double al = -aw + (i + 0.5) * da; double be = (z + al * wa) / wb; double cb = bw - Math.Abs(be); if (cb <= 0) continue; s += (aw - Math.Abs(al)) * cb * da; }
      T[k] = s / wb; }
    Func<double, double> I2 = z => { z = Math.Abs(z); if (z >= W1) return 0; double t = z / W1 * NZ; int k = (int)t; if (k >= NZ) return T[NZ]; double f = t - k; return T[k] * (1 - f) + T[k + 1] * f; };
    // I_Phi1 and I_w
    int NX = 6000; double dx = 2 * JA_ / NX, I1 = 0, Iw = 0; int NY = 48;
    for (int i = 0; i < NX; i++) { double x = -JA_ + (i + 0.5) * dx; double lo = Math.Max(-JB_, (x - W1) / rr), hi = Math.Min(JB_, (x + W1) / rr); if (hi <= lo) continue; double dy = (hi - lo) / NY; double inner = 0, innerw = 0;
      for (int j = 0; j < NY; j++) { double y = lo + (j + 0.5) * dy; double cb = JB_ - Math.Abs(y); inner += cb * I2(x - y * rr) * dy; innerw += cb * dy; }
      double ca = JA_ - Math.Abs(x); I1 += ca * inner * dx; Iw += ca * innerw * dx; }
    double Phi1max = JA_ * JB_ * I2(0); double Main1 = I1 + Phi1max * e1;
    // second level
    double rho2 = wb / wa; double A2 = AreaBox(aw, bw, rho2 >= 1 ? rho2 : 1 / rho2, 1.0) ; // placeholder replaced below
    {
      // area of {|al|<aw,|be|<bw,|al wa - be wb|<W2} in units of wa
      double Wp = W2 / wa; if (rho2 >= 1) A2 = AreaBox(aw, bw, rho2, Wp); else A2 = AreaBox(bw, aw, 1 / rho2, Wp / rho2);
    }
    A2 *= 1.001; double lam2 = Lam1sw(2 * aw, 2 * bw, rho2, 2 * W2 / wa);
    double e2 = 3 * Math.Sqrt(A2) + 1 + 1 / lam2; double Psimax = aw * bw * H0;
    double Sw = Iw + JA_ * JB_ * e1; double Err = Psimax * e2 * Sw;
    double massA = JA_ * aw, massB = JB_ * bw; double norm = massA * massA * massB * massB;
    double C2cont = 2 * Xu * I1 / norm, C2rig = 2 * Xu * (Main1 + Err) / norm;
    double C1main = 2 * Xu * Main1 / norm;
    Console.WriteLine($"D={D} l={l} n={n} m={m} J'=({JA},{JB}) rho={rho:F4}: top A0={A0:F0} lam0={lam0:E2} | second level J1=({JA1},{JB1}) A2*={A2:F0} lam2*={lam2:E2} e2={e2:F1} | C_cont2={C2cont:F4}  main(top lattice)={C1main:F4}  rigorous two-level bound={C2rig:F4}  (err part {2 * Xu * Err / norm:F4})");
  }
}

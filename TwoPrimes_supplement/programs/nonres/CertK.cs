using System;
using System.Collections.Generic;
using System.Numerics;
// K-level certificate. Levels 0 (top clusters) .. K-1 exact, the rest uniform.  Recursion (multi-stage recursion):
//   F_k(z) <= I_k(z) + E_k,  E_K = 0,  E_k = aw_k^2 I_{k+1}(0) e_k + E_{k+1} (Iw_k + aw_k^2 e_k)   (k = K-1..1)
//   S <= I_0 + Phi0max e_0 + E_1 (Iw_0 + (J_P+1)(J_Q+1) e_0)
// Usage: nonres certk D l n m JA JB K
partial class P {
  static double AreaGen(double awA, double awB, double wA, double wB, double W) { // area of {|a|<awA,|b|<awB,|a wA - b wB|<W}, a in units A, b in units B
    double rho = wB / wA; if (rho >= 1) return AreaBox(awA, awB, rho, W / wA); return AreaBox(awB, awA, 1 / rho, W / wB); }
  static double IwGen(double awA, double awB, double wA, double wB, double W) { // integral of (awA-|a|)(awB-|b|) over the body
    double rho = wB / wA; bool sw = rho < 1; double JAx = sw ? awB : awA, JBx = sw ? awA : awB, r = sw ? 1 / rho : rho, Wx = sw ? W / wB : W / wA;
    int NX = 6000, NY = 48; double dx = 2 * JAx / NX, s = 0;
    for (int i = 0; i < NX; i++) { double x = -JAx + (i + 0.5) * dx; double lo = Math.Max(-JBx, (x - Wx) / r), hi = Math.Min(JBx, (x + Wx) / r); if (hi <= lo) continue; double dy = (hi - lo) / NY, inner = 0;
      for (int j = 0; j < NY; j++) { double y = lo + (j + 0.5) * dy; inner += (JBx - Math.Abs(y)) * dy; } s += (JAx - Math.Abs(x)) * inner * dx; }
    return s; }
  static double Jker(double z, double awA, double awB, double wA, double wB) { // (1/wB) int (awA-|a|)(awB-|(z + a wA)/wB|) da
    int NA = 20000; double da = 2 * awA / NA, s = 0;
    for (int i = 0; i < NA; i++) { double al = -awA + (i + 0.5) * da; double cb = awB - Math.Abs((z + al * wA) / wB); if (cb <= 0) continue; s += (awA - Math.Abs(al)) * cb * da; }
    return s / wB; }
  static void CertK(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); int n = int.Parse(a[3]), m = int.Parse(a[4]); long JA0 = long.Parse(a[5]), JB0 = long.Parse(a[6]); int K = int.Parse(a[7]);
    var LA = Levels(2, D, n + 1); var LB = Levels(l, D, m + 1); int iA = n - 1, iB = m - 1;
    // ball lists: level 0 = top
    var la = new List<int> { iA }; for (int j = iA - 1; j >= 0; j--) if (LA[j].J >= 1) la.Add(j); var lb = new List<int> { iB }; for (int j = iB - 1; j >= 0; j--) if (LB[j].J >= 1) lb.Add(j);
    if (K > la.Count || K > lb.Count) { Console.WriteLine($"only {Math.Min(la.Count, lb.Count)} levels available"); return; }
    bool swap = BigInteger.Log(LB[iB].step) < BigInteger.Log(LA[iA].step);      // P = ball with the smaller top step
    var LP = swap ? LB : LA; var LQ = swap ? LA : LB; var lp = swap ? lb : la; var lq = swap ? la : lb; double JP0 = swap ? JB0 : JA0, JQ0 = swap ? JA0 : JB0;
    double lnu = BigInteger.Log(LP[lp[0]].step);
    var wP = new double[K]; var wQ = new double[K]; var JP = new double[K]; var JQ = new double[K]; var hP = new double[K]; var hQ = new double[K];
    for (int k = 0; k < K; k++) { var p = LP[lp[k]]; var q = LQ[lq[k]]; wP[k] = Math.Exp(BigInteger.Log(p.step) - lnu); wQ[k] = Math.Exp(BigInteger.Log(q.step) - lnu); JP[k] = (k == 0 ? JP0 : (double)p.J); JQ[k] = (k == 0 ? JQ0 : (double)q.J);
      hP[k] = Math.Exp(BigInteger.Log(p.U + 1) - lnu); hQ[k] = Math.Exp(BigInteger.Log(q.U + 1) - lnu); }
    double Xu = JP0 + hP[0];
    // ranges: aw_k = J'+1 (top) or 2J+1 ; widths W_k = 2(hullBelow_P[k] + hullBelow_Q[k])
    var awP = new double[K]; var awQ = new double[K]; var W = new double[K];
    for (int k = 0; k < K; k++) { awP[k] = (k == 0) ? JP[0] + 1 : 2 * JP[k] + 1; awQ[k] = (k == 0) ? JQ[0] + 1 : 2 * JQ[k] + 1; W[k] = 2 * (hP[k] + hQ[k]); }
    double[] wd = { 2 * hP[K - 1], 2 * hP[K - 1], 2 * hQ[K - 1], 2 * hQ[K - 1] };
    // M_k = prod_{j>=k} (awP_j awQ_j)^2 for k>=1 ; M_K = 1 (note: M_k defined for exact levels k..K-1)
    var M = new double[K + 2]; M[K] = 1; for (int k = K - 1; k >= 1; k--) M[k] = M[k + 1] * awP[k] * awP[k] * awQ[k] * awQ[k];
    // I_k(0) (units 1/u): I_K(0) = H_low(0); I_k(0) = M_{k+1} * Jker(0,...) for 1<=k<=K-1
    Func<int, double> I0val = k => { if (k >= K) return Hn(0, wd); return M[k + 1] * Jker(0, awP[k], awQ[k], wP[k], wQ[k]); };
    // errors e_k and Iw_k
    var e = new double[K]; var Iw = new double[K]; var lam = new double[K]; var Ak = new double[K];
    for (int k = 0; k < K; k++) {
      double A = AreaGen(awP[k], awQ[k], wP[k], wQ[k], W[k]) * 1.001; Ak[k] = A;
      if (k == 0) { double rho = wQ[0] / wP[0]; lam[0] = Lam1sw(awP[0], awQ[0], rho, W[0] / wP[0]); e[0] = 2 * Math.Sqrt(A) + 1 + 2 / lam[0]; }
      else { double rho = wQ[k] / wP[k]; lam[k] = Lam1sw(2 * awP[k], 2 * awQ[k], rho, 2 * W[k] / wP[k]); e[k] = 3 * Math.Sqrt(A) + 1 + 1 / lam[k]; }
      Iw[k] = IwGen(awP[k], awQ[k], wP[k], wQ[k], W[k]);
    }
    // recursion
    double Ek = 0; var Eks = new double[K + 1]; Eks[K] = 0;
    for (int k = K - 1; k >= 1; k--) { double cm = awP[k] * awQ[k]; Ek = cm * I0val(k + 1) * e[k] + Ek * (Iw[k] + cm * e[k]); Eks[k] = Ek; if (Environment.GetEnvironmentVariable("DBG") != null) Console.WriteLine($"  level {k}: I_k(0)={I0val(k):E3} E_k={Ek:E3} ratio E_k/I_k(0)={Ek / I0val(k):E3}  Iw_k={Iw[k]:E3} cm*e_k={cm * e[k]:E3} I_{k + 1}(0)={I0val(k + 1):E3} cm={cm:E3}"); }
    // top: I_0 = int int c c I_1(x u - y v) ; I_1(z) = M_2 * Jker(z) (K>=2) or H_low (K=1)
    double JPp = awP[0], JQp = awQ[0]; double rr = wQ[0] / wP[0]; double W0 = W[0];
    int NZ = 200; var T = new double[NZ + 1];
    for (int i = 0; i <= NZ; i++) { double z = W0 * i / NZ; T[i] = (K >= 2) ? M[2] * Jker(z, awP[1], awQ[1], wP[1], wQ[1]) : Hn(z, wd); }
    Func<double, double> I1 = z => { z = Math.Abs(z); if (z >= W0) return 0; double t = z / W0 * NZ; int k = (int)t; if (k >= NZ) return T[NZ]; double f = t - k; return T[k] * (1 - f) + T[k + 1] * f; };
    int NX = 6000, NY = 48; double dx = 2 * JPp / NX, I0 = 0, Iw0 = 0;
    for (int i = 0; i < NX; i++) { double x = -JPp + (i + 0.5) * dx; double lo = Math.Max(-JQp, (x * wP[0] - W0) / wQ[0]), hi = Math.Min(JQp, (x * wP[0] + W0) / wQ[0]); if (hi <= lo) continue; double dy = (hi - lo) / NY, inner = 0, innerw = 0;
      for (int j = 0; j < NY; j++) { double y = lo + (j + 0.5) * dy; double cb = JQp - Math.Abs(y); inner += cb * I1(x * wP[0] - y * wQ[0]) * dy; innerw += cb * dy; }
      double ca = JPp - Math.Abs(x); I0 += ca * inner * dx; Iw0 += ca * innerw * dx; }
    double Phi0max = JPp * JQp * I1(0); double E1 = (K >= 2) ? Eks[1] : 0;
    double Stot = I0 + Phi0max * e[0] + E1 * (Iw0 + JPp * JQp * e[0]);
    double massP = JPp, massQ = JQp; for (int k = 1; k < K; k++) { massP *= awP[k]; massQ *= awQ[k]; }
    double norm = massP * massP * massQ * massQ; double Ccont = 2 * Xu * I0 / norm, Crig = 2 * Xu * Stot / norm, Ctop = 2 * Xu * (I0 + Phi0max * e[0]) / norm;
    Console.WriteLine($"D={D} l={l} (n,m)=({n},{m}) J'=({JA0},{JB0}) K={K}: C_cont={Ccont:F4}  top-lattice part={Ctop:F4}  RIGOROUS K-level bound={Crig:F4}   (levels' A_k*: {string.Join(", ", Array.ConvertAll(Ak, x => x.ToString("E1")))}; e_k: {string.Join(", ", Array.ConvertAll(e, x => x.ToString("E1")))})");
  }
}

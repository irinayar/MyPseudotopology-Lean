using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
// Merged-stage certificate: all levels of both balls sorted by step; consecutive weights of different balls with ln-ratio <= T are paired into a 2D stage,
// the others are 1D stages. Same recursion as certk (multi-stage recursion), with e = 1 for 1D stages.   Usage: nonres certm D l n m JA JB Stages T
partial class P {
  class Stg { public bool hasP, hasQ; public double awP, awQ, wP, wQ, W; public double hRemP, hRemQ; }
  static void CertM(string[] a) {
    long D = long.Parse(a[1]); int l = int.Parse(a[2]); int n = int.Parse(a[3]), m = int.Parse(a[4]); long JA0 = long.Parse(a[5]), JB0 = long.Parse(a[6]); int S = int.Parse(a[7]); double Tcut = double.Parse(a[8], System.Globalization.CultureInfo.InvariantCulture);
    var LA = Levels(2, D, n + 1); var LB = Levels(l, D, m + 1); int iA = n - 1, iB = m - 1;
    var la = new List<int> { iA }; for (int j = iA - 1; j >= 0; j--) if (LA[j].J >= 1) la.Add(j); var lb = new List<int> { iB }; for (int j = iB - 1; j >= 0; j--) if (LB[j].J >= 1) lb.Add(j);
    bool swap = BigInteger.Log(LB[iB].step) < BigInteger.Log(LA[iA].step);
    var LP = swap ? LB : LA; var LQ = swap ? LA : LB; var lp = swap ? lb : la; var lq = swap ? la : lb; double JP0 = swap ? JB0 : JA0, JQ0 = swap ? JA0 : JB0;
    double lnu = BigInteger.Log(LP[lp[0]].step);
    var el = new List<(int b, int k, double ln)>(); for (int k = 0; k < lp.Count; k++) el.Add((0, k, BigInteger.Log(LP[lp[k]].step))); for (int k = 0; k < lq.Count; k++) el.Add((1, k, BigInteger.Log(LQ[lq[k]].step)));
    el = el.OrderByDescending(x => x.ln).ToList();
    var stages = new List<Stg>();
    Func<int, double> hullBelowP = k => Math.Exp(BigInteger.Log(LP[lp[k]].U + 1) - lnu); Func<int, double> hullBelowQ = k => Math.Exp(BigInteger.Log(LQ[lq[k]].U + 1) - lnu);
    Func<int, double> stepP = k => Math.Exp(BigInteger.Log(LP[lp[k]].step) - lnu); Func<int, double> stepQ = k => Math.Exp(BigInteger.Log(LQ[lq[k]].step) - lnu);
    stages.Add(new Stg { hasP = true, hasQ = true, awP = JP0 + 1, awQ = JQ0 + 1, wP = 1.0, wQ = stepQ(0), hRemP = hullBelowP(0), hRemQ = hullBelowQ(0) });
    var rem = el.Where(x => !((x.b == 0 && x.k == 0) || (x.b == 1 && x.k == 0))).ToList(); int pos = 0;
    while (pos < rem.Count && stages.Count < S) {
      var e1 = rem[pos]; Stg st = new Stg(); bool pair = false;
      if (pos + 1 < rem.Count) { var e2 = rem[pos + 1]; if (e2.b != e1.b && e1.ln - e2.ln <= Tcut) pair = true; }
      Action<(int b, int k, double ln)> addDigit = x => {
        if (x.b == 0) { st.hasP = true; st.awP = 2 * (double)LP[lp[x.k]].J + 1; st.wP = stepP(x.k); st.hRemP = hullBelowP(x.k); }
        else { st.hasQ = true; st.awQ = 2 * (double)LQ[lq[x.k]].J + 1; st.wQ = stepQ(x.k); st.hRemQ = hullBelowQ(x.k); } };
      addDigit(e1); if (pair) { addDigit(rem[pos + 1]); pos += 2; } else pos += 1;
      var prev = stages[stages.Count - 1]; if (!st.hasP) st.hRemP = prev.hRemP; if (!st.hasQ) st.hRemQ = prev.hRemQ; stages.Add(st);
    }
    int Sn = stages.Count; foreach (var st in stages) st.W = 2 * (st.hRemP + st.hRemQ);
    var last = stages[Sn - 1]; double[] wd = { 2 * last.hRemP, 2 * last.hRemP, 2 * last.hRemQ, 2 * last.hRemQ };
    double Xu = JP0 + hullBelowP(0);
    var M = new double[Sn + 2]; M[Sn] = 1; for (int s = Sn - 1; s >= 1; s--) { double f = 1; if (stages[s].hasP) f *= stages[s].awP * stages[s].awP; if (stages[s].hasQ) f *= stages[s].awQ * stages[s].awQ; M[s] = M[s + 1] * f; }
    Func<int, double, double> Jk = (s, z) => { var st = stages[s]; if (st.hasP && st.hasQ) return Jker(z, st.awP, st.awQ, st.wP, st.wQ); double aw = st.hasP ? st.awP : st.awQ, w = st.hasP ? st.wP : st.wQ; double c = aw - Math.Abs(z / w); return c > 0 ? c / w : 0; };
    Func<int, double> I0val = s => { if (s >= Sn) return Hn(0, wd); return M[s + 1] * Jk(s, 0); };
    var e = new double[Sn]; var Iw = new double[Sn]; var Ak = new double[Sn]; var cm = new double[Sn];
    for (int s = 0; s < Sn; s++) { var st = stages[s];
      if (st.hasP && st.hasQ) { double A = AreaGen(st.awP, st.awQ, st.wP, st.wQ, st.W) * 1.001; Ak[s] = A; double rho = st.wQ / st.wP;
        if (s == 0) { double lam = Lam1sw(st.awP, st.awQ, rho, st.W / st.wP); e[s] = 2 * Math.Sqrt(A) + 1 + 2 / lam; } else { double lam = Lam1sw(2 * st.awP, 2 * st.awQ, rho, 2 * st.W / st.wP); e[s] = 3 * Math.Sqrt(A) + 1 + 1 / lam; }
        Iw[s] = IwGen(st.awP, st.awQ, st.wP, st.wQ, st.W); cm[s] = st.awP * st.awQ; }
      else { double aw = st.hasP ? st.awP : st.awQ, w = st.hasP ? st.wP : st.wQ; double len = Math.Min(2 * aw, 2 * st.W / w); Ak[s] = len; e[s] = 1; double hw = Math.Min(aw, st.W / w); Iw[s] = 2 * (aw * hw - hw * hw / 2); cm[s] = aw; }
    }
    double Ek = 0; var Eks = new double[Sn + 1];
    for (int s = Sn - 1; s >= 1; s--) { Ek = cm[s] * I0val(s + 1) * e[s] + Ek * (Iw[s] + cm[s] * e[s]); Eks[s] = Ek; if (Environment.GetEnvironmentVariable("DBG") != null) Console.WriteLine("  stage " + s + ": I_s(0)=" + I0val(s).ToString("E3") + " E_s=" + Ek.ToString("E3") + " E_s/I_s(0)=" + (Ek / I0val(s)).ToString("E3") + " Iw_s=" + Iw[s].ToString("E3") + " cm*e_s=" + (cm[s] * e[s]).ToString("E3") + " W/w=" + (stages[s].W / (stages[s].hasP ? stages[s].wP : stages[s].wQ)).ToString("E3") + " A_s=" + Ak[s].ToString("E3")); }
    double JPp = stages[0].awP, JQp = stages[0].awQ, rr = stages[0].wQ / stages[0].wP, W0 = stages[0].W; int NZ = 200; var T = new double[NZ + 1];
    for (int i = 0; i <= NZ; i++) { double z = W0 * i / NZ; T[i] = (Sn >= 2) ? M[2] * Jk(1, z) : Hn(z, wd); }
    Func<double, double> I1 = z => { z = Math.Abs(z); if (z >= W0) return 0; double t = z / W0 * NZ; int k = (int)t; if (k >= NZ) return T[NZ]; double f = t - k; return T[k] * (1 - f) + T[k + 1] * f; };
    int NX = 6000, NY = 48; double dx = 2 * JPp / NX, I0 = 0, Iw0 = 0;
    for (int i = 0; i < NX; i++) { double x = -JPp + (i + 0.5) * dx; double lo = Math.Max(-JQp, (x - W0) / rr), hi = Math.Min(JQp, (x + W0) / rr); if (hi <= lo) continue; double dy = (hi - lo) / NY, inner = 0, innerw = 0;
      for (int j = 0; j < NY; j++) { double y = lo + (j + 0.5) * dy; double cb = JQp - Math.Abs(y); inner += cb * I1(x - y * rr) * dy; innerw += cb * dy; } double ca = JPp - Math.Abs(x); I0 += ca * inner * dx; Iw0 += ca * innerw * dx; }
    double Phi0max = JPp * JQp * I1(0); double E1 = (Sn >= 2) ? Eks[1] : 0; double Stot = I0 + Phi0max * e[0] + E1 * (Iw0 + JPp * JQp * e[0]);
    double massP = 1, massQ = 1; foreach (var st in stages) { if (st.hasP) massP *= st.awP; if (st.hasQ) massQ *= st.awQ; }
    double norm = massP * massP * massQ * massQ; double Ccont = 2 * Xu * I0 / norm, Crig = 2 * Xu * Stot / norm, Ctop = 2 * Xu * (I0 + Phi0max * e[0]) / norm;
    string desc = string.Join(" ", stages.Select((st, s) => (st.hasP && st.hasQ ? "2D" : (st.hasP ? "P" : "Q")) + "[A=" + Ak[s].ToString("E1") + ",e=" + e[s].ToString("E1") + "]"));
    Console.WriteLine("D=" + D + " l=" + l + " (n,m)=(" + n + "," + m + ") J=(" + JA0 + "," + JB0 + ") stages=" + Sn + " T=" + Tcut + ": C_cont=" + Ccont.ToString("F4") + " top=" + Ctop.ToString("F4") + " RIGOROUS=" + Crig.ToString("F4") + "   stages: " + desc);
  }
}

using System;
using System.Collections.Generic;
using System.Text;
// One-prime ball U_{p,1/D} cap [0,X] (strict, all scales) enumerated by maximal-jump rule; energy of A=U_3, B=U_2.
public static class Energy2 {
  // next element >= k of {x : ||x/q|| < 1/D for all q in qs, x<=lim}; returns -1 if none <= lim
  static long Next(long k, long[] qs, int D, long lim) {
    while (k <= lim) {
      long best = k; bool failed = false;
      for (int i = 0; i < qs.Length; i++) {
        long q = qs[i];
        long T = (q - 1) / D;               // allowed residues: s<=T or s>=q-T
        long s = k % q;
        if (s > T && s < q - T) { failed = true; long kp = k + q - T - s; if (kp > best) best = kp; }
      }
      if (!failed) return k;
      k = best;
    }
    return -1;
  }
  public static long[] Ball(int p, int D, long X) {
    var qs = new List<long>(); 
    for (int n = 1; ; n++) {
      double lg = n * (double)n * Math.Log(p);
      if (lg > Math.Log((double)D * X) + 1) break;
      long q = 1; for (int i = 0; i < n * n; i++) q *= p; qs.Add(q);
    }
    var res = new List<long>(); long k = 0;
    while (true) { k = Next(k, qs.ToArray(), D, X); if (k < 0) break; res.Add(k); k++; }
    return res.ToArray();
  }
  public static bool InBall(long x, int p, int D, long X) {
    long ax = Math.Abs(x); 
    for (int n = 1; ; n++) {
      double lg = n * (double)n * Math.Log(p); if (lg > Math.Log((double)D * (ax + 1)) + 1) break;
      long q = 1; for (int i = 0; i < n * n; i++) q *= p; long r = ax % q; long m = Math.Min(r, q - r);
      if ((double)D * m >= q) return false;
    }
    return true;
  }
  static long Count(long[] sortedA, HashSet<long> setA, long s) { long c = 0; foreach (long a in sortedA) { if (a + s > sortedA[sortedA.Length - 1]) break; if (setA.Contains(a + s)) c++; } return c; }
  public static string Run(int D, long X) {
    long[] A = Ball(3, D, X), B = Ball(2, D, X);
    var sA = new HashSet<long>(A); var sB = new HashSet<long>(B);
    // candidate shifts s in [0,X]: need P_p(s) < 2/D for both p  (difference of two ball elements)
    int D2 = D / 2; // 2/D radius -> strict 1/(D/2) ; use exact D2 when D even
    var cand = Ball(3, D2, X);
    var candS = new List<long>(); foreach (long s in cand) if (InBall(s, 2, D2, X)) candS.Add(s);
    double E = 0; // use double for big counts; also keep exact in decimal via System.Numerics-free long if fits
    System.Numerics.BigInteger Eb = 0;
    foreach (long s in candS) {
      long ra = Count(A, sA, s), rb = Count(B, sB, s);
      System.Numerics.BigInteger term = (System.Numerics.BigInteger)ra * rb; if (s > 0) term *= 2; Eb += term;
    }
    double a = A.Length, b = B.Length; E = (double)Eb;
    double C = (2.0 * X + 1) * E / (a * a * b * b);
    return "D=" + D + " X=" + X + " a=" + A.Length + " b=" + B.Length + " cand=" + candS.Count + " E=" + Eb + " ab/(2X+1)=" + (a * b / (2.0 * X + 1)).ToString("G5") + " C_X=" + C.ToString("G6");
  }
  public static string Grid(int D, double lo, double hi, int steps) {
    var sb=new System.Text.StringBuilder();
    for (int j=0;j<=steps;j++){
      long X=(long)Math.Round(lo*Math.Pow(hi/lo,(double)j/steps));
      long[] A=Ball(3,D,X), B=Ball(2,D,X); var sA=new HashSet<long>(A); var sB=new HashSet<long>(B);
      var cand=Ball(3,D/2,X); System.Numerics.BigInteger Eb=0;
      foreach(long s in cand){ if(!InBall(s,2,D/2,X)) continue; long ra=Count(A,sA,s), rb=Count(B,sB,s); var t=(System.Numerics.BigInteger)ra*rb; if(s>0) t*=2; Eb+=t; }
      double a=A.Length,b=B.Length,Xd=X; double C=(2*Xd+1)*(double)Eb/(a*a*b*b); double lam=a*b/(2*Xd+1);
      double Cb=(2*Xd+1)*((Xd+1)*(Xd+1)+Xd*(Xd+1)*(2*Xd+1)/3)/Math.Pow(Xd+1,4);
      sb.AppendLine("D="+D+" X="+X+" lam="+lam.ToString("G5")+" C="+C.ToString("G6")+" excess="+(C-1/lam-Cb).ToString("F4")+" logDX/ln2="+(Math.Log(D*Xd)/Math.Log(2)).ToString("F2")+" logDX/ln3="+(Math.Log(D*Xd)/Math.Log(3)).ToString("F2"));
      Console.WriteLine(sb.ToString().Split('\n')[sb.ToString().Split('\n').Length-2]);
    }
    return sb.ToString();
  }
}

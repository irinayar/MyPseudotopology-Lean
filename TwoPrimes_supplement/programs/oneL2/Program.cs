using System;
using System.Collections.Generic;
using System.Numerics;
// Exact Fourier integral of the one-sided ball energy.  A+ = {t in T_N : 0 <= t <= X} (digit model), alpha(theta) = sum e(a theta).
// Prints cumulative I(M) = int_{|theta|<=M/b} |alpha|^2 |beta|^2 dtheta against the envelope P+_env(M), b = max hull; and P_c-based C.
// Usage: oneL2 D pA nTopA pB nTopB X [step_per_b=40]
class P {
  static List<double> Ball(int p, long D, int nTop, long X, out long hull, out long Jp) {
    var Y = new List<long> { 0 }; long U = 0;
    for (int k = 1; k < nTop; k++) {
      BigInteger q = BigInteger.Pow(p, k * k), qp = BigInteger.Pow(p, (k - 1) * (k - 1)); long J = (long)((q - 1) / (D * qp)); if (J < 1) continue; long w = (long)qp;
      var Z = new List<long>(Y.Count * (int)(2 * J + 1)); for (long j = -J; j <= J; j++) foreach (var y in Y) Z.Add(y + j * w); Y = Z; U += J * w;
    }
    Y.Sort();
    BigInteger Q = BigInteger.Pow(p, nTop * nTop), QP = BigInteger.Pow(p, (nTop - 1) * (nTop - 1)); long Jn = (long)((Q - 1) / (D * QP)); long q0 = (long)QP;
    Jp = Math.Min(Jn, (X + U) / q0); var A = new List<double>(); hull = 0;
    for (long j = 0; j <= Jp; j++) { long off = j * q0; foreach (var y in Y) { long v = y + off; if (v >= 0 && v <= X) { A.Add(v); if (v > hull) hull = v; } } }
    return A;
  }
  static void Main(string[] a) {
    long D = long.Parse(a[0]); int pA = int.Parse(a[1]), nA = int.Parse(a[2]), pB = int.Parse(a[3]), nB = int.Parse(a[4]); long X = long.Parse(a[5]); int spb = a.Length > 6 ? int.Parse(a[6]) : 40;
    long hA, hB, JA, JB; var A = Ball(pA, D, nA, X, out hA, out JA); var B = Ball(pB, D, nB, X, out hB, out JB);
    Console.WriteLine($"D={D} X={X} |A+|={A.Count} hull a={hA} J'={JA}; |B+|={B.Count} hull b={hB} J'={JB}");
    double aa = Math.Min(hA, hB), bb = Math.Max(hA, hB); double s = aa / bb; double Penv = (1 - s / 3) / bb; // int_R sinc^2 sinc^2
    double[] Ms = { 0.25, 0.5, 1, 2, 4, 8, 16 }; double Mmax = Ms[Ms.Length - 1];
    int K = (int)(Mmax * spb); double dth = (Mmax / bb) / K;
    double[] f = new double[K + 1]; double[] g = new double[K + 1];
    var ax = A.ToArray(); var bx = B.ToArray();
    for (int k = 0; k <= K; k++) {
      double th = k * dth, c1 = 0, s1 = 0, c2 = 0, s2 = 0; double w = 2 * Math.PI * th;
      foreach (var x in ax) { double ph = w * x; c1 += Math.Cos(ph); s1 += Math.Sin(ph); }
      foreach (var x in bx) { double ph = w * x; c2 += Math.Cos(ph); s2 += Math.Sin(ph); }
      double na = ax.Length, nb = bx.Length; f[k] = ((c1 * c1 + s1 * s1) / (na * na)) * ((c2 * c2 + s2 * s2) / (nb * nb));
      double xa = Math.PI * aa * th, xb = Math.PI * bb * th; double sa = xa == 0 ? 1 : Math.Sin(xa) / xa, sb = xb == 0 ? 1 : Math.Sin(xb) / xb; g[k] = sa * sa * sb * sb;
    }
    double If = 0, Ig = 0; int mi = 0; double na2 = A.Count, nb2 = B.Count;
    for (int k = 1; k <= K; k++) {
      If += 2 * 0.5 * (f[k] + f[k - 1]) * dth; Ig += 2 * 0.5 * (g[k] + g[k - 1]) * dth; // factor 2: both signs of theta
      if (mi < Ms.Length && Math.Abs(k * dth * bb - Ms[mi]) < 1e-9) {
        Console.WriteLine($"M={Ms[mi]}: I_exact={If * bb:F5}/b (C-units 2bI = {2 * bb * If:F5})  I_env={Ig * bb:F5}/b (2bI = {2 * bb * Ig:F5})  full-line P+env b = {Penv * bb:F5} (C_env={2 * (1 - s / 3):F5})  rel.diff(I_exact vs full-line env)={(If - Penv) / Penv:F5}");
        mi++;
      }
    }
    Console.WriteLine($"PRINC (2X+1)*I(16/b) = {(2.0 * X + 1) * If:F5}");
    Console.WriteLine($"diag 1/lambda-type term (2b)/(|A||B|) = {2 * bb / (na2 * nb2):E3}");
  }
}

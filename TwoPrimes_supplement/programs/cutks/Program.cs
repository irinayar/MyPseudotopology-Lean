using System;
using System.Collections.Generic;
using System.Numerics;
// Test of Theorem L1c: symmetric ball A = T_N cap [-X,X] (digit model, top level n, step q = p^((n-1)^2), lower set Y = T_{n-1}):
// sup |F_A - uniform[-h,h]| <= 5/(4 J' - 2), h = max A, J' = min(J_n, floor((X+U')/q)).
// Usage: cutks D p nTop nSamples
class P {
  static void Main(string[] a) {
    long D = long.Parse(a[0]); int p = int.Parse(a[1]); int nTop = int.Parse(a[2]); int ns = int.Parse(a[3]);
    var Y = new List<long> { 0 }; long U = 0;
    for (int k = 1; k < nTop; k++) {
      BigInteger q = BigInteger.Pow(p, k * k), qp = BigInteger.Pow(p, (k - 1) * (k - 1)); long J = (long)((q - 1) / (D * qp)); if (J < 1) continue; long w = (long)qp;
      var Z = new List<long>(Y.Count * (int)(2 * J + 1)); for (long j = -J; j <= J; j++) foreach (var y in Y) Z.Add(y + j * w); Y = Z; U += J * w;
    }
    Y.Sort();
    BigInteger Q = BigInteger.Pow(p, nTop * nTop), QP = BigInteger.Pow(p, (nTop - 1) * (nTop - 1)); long Jn = (long)((Q - 1) / (D * QP)); long q0 = (long)QP;
    Console.WriteLine($"D={D} p={p} top level n={nTop}: step q={q0} J_n={Jn} |Y|={Y.Count} U'={U} (U'/q={(double)U / q0:F4})");
    var rng = new Random(int.Parse(Environment.GetEnvironmentVariable("SEED") ?? "7")); double worst = 0, worstJ = 0, worst1 = 0; int cnt = 0; double worstRatio = 0;
    for (int s = 0; s < ns; s++) {
      long Jcap = Math.Min(Jn, 20000000L / Y.Count / 2); if (Jcap < 1) Jcap = 1; long Jp = 1 + (long)(rng.NextDouble() * Jcap); double f = rng.NextDouble(); if (rng.NextDouble() < 0.4) { double[] ed = { 0.0, 0.01, 0.05, 0.5, 0.95, 0.99, 1.0 }; f = ed[rng.Next(ed.Length)]; }
      long X = Jp * q0 + (long)((f - 0.5) * q0) ; // X around Jp*q +- q/2
      if (X <= 0) continue;
      long Jc = Math.Min(Jn, (X + U) / q0); if (Jc < 1) continue;
      // build A
      var A = new List<long>();
      for (long j = -Jc; j <= Jc; j++) { long off = j * q0; int lo = Y.BinarySearch(-X - off); if (lo < 0) lo = ~lo; for (int i = lo; i < Y.Count; i++) { long v = Y[i] + off; if (v > X) break; if (v >= -X) A.Add(v); } }
      A.Sort(); double h = A[A.Count - 1]; double M = A.Count; double ks = 0;
      for (int i = 0; i < A.Count; i++) { double g = (A[i] + h) / (2 * h); double fr = (i + 1) / M, fl = i / M; ks = Math.Max(ks, Math.Max(Math.Abs(fr - g), Math.Abs(fl - g))); }
      double bound = 5.0 / (4 * Jc - 2); double ratio = ks / bound; cnt++;
      { int i0 = A.BinarySearch(0L); if (i0 < 0) i0 = ~i0; double m1 = A.Count - i0; double ks1 = 0; for (int i = i0; i < A.Count; i++) { double g = A[i] / h; double fr = (i - i0 + 1) / m1, fl = (i - i0) / m1; ks1 = Math.Max(ks1, Math.Max(Math.Abs(fr - g), Math.Abs(fl - g))); } double b1 = 2 * bound + 2.0 / M; double r1 = ks1 / b1; if (r1 > worst1) worst1 = r1; }
      if (ratio > worstRatio) { worstRatio = ratio; worstJ = Jc; worst = ks; }
      if (s < 8) Console.WriteLine($"  X={X} (X/q={(double)X / q0:F3}) J'={Jc} |A|={A.Count} h/q={h / q0:F3} KS={ks:F5} bound={bound:F5} ratio={ratio:F3} KS*(2J'+1)={ks * (2 * Jc + 1):F3}");
    }
    Console.WriteLine($"samples={cnt}: max KS/bound = {worstRatio:F3} (at J'={worstJ}, KS={worst:F5}); one-sided max KS+/(2 bound + 2/|A|) = {worst1:F3}");
  }
}

using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

// Checks of the exact examples printed in the appendix of the TwoPrimes article.
class P {
  static BigInteger Pw(int b, int e) => BigInteger.Pow(b, e);
  static void Check(bool ok, string what) { Console.WriteLine((ok ? "OK   " : "FAIL ") + what); }
  // digit set T_N : levels n<=N, weight p^((n-1)^2), |d| <= floor(p^(2n-1)/D)
  static List<long> T(int p, int D, int N) { var s = new List<long> { 0 }; for (int n = 1; n <= N; n++) { long w = (long)Pw(p, (n - 1) * (n - 1)), J = (long)(Pw(p, 2 * n - 1) / D); var t = new List<long>(); foreach (var x in s) for (long d = -J; d <= J; d++) t.Add(x + d * w); s = t; } s.Sort(); return s; }
  static long Energy(List<long> A, List<long> B) { var h = new Dictionary<long, long>(); foreach (var a in A) foreach (var b in B) { h.TryGetValue(a - b, out var c); h[a - b] = c + 1; } return h.Values.Sum(c => c * c); }
  static void Main() {
    // cut energies: D=20, N=4 (p=2), M=3 (p=3), X=891
    var A = T(2, 20, 4); var B = T(3, 20, 3); var Y = T(2, 20, 3); var Z = T(3, 20, 2);
    long u = (long)Pw(2, 9), v = (long)Pw(3, 4), X = 891, U = Y.Max(), V = Z.Max();
    long J1 = Math.Min((long)(Pw(2, 7) / 20), (X + U) / u), J2 = Math.Min((long)(Pw(3, 5) / 20), (X + V) / v);
    var fa = new List<long>(); for (long j = 0; j <= J1; j++) foreach (var y in Y) fa.Add(j * u + y);
    var fb = new List<long>(); for (long j = 0; j <= J2; j++) foreach (var z in Z) fb.Add(j * v + z);
    var ca = A.Where(a => a >= 0 && a <= X).ToList(); var cb = B.Where(b => b >= 0 && b <= X).ToList();
    Console.WriteLine($"D=20 X=891: u={u} v={v} J'=({J1},{J2}) full |A|={A.Count} |B|={B.Count} E={Energy(A, B)}; filled |A|={fa.Count} |B|={fb.Count} E={Energy(fa, fb)}; cut |A|={ca.Count} |B|={cb.Count} E={Energy(ca, cb)}");
    // least dangerous fraction: {2,3}, N=69, M=55, K=9
    {
      BigInteger s = Pw(3, 2916), Bb = Pw(2, 4624), Q = Pw(3, 109);
      var astar = BigInteger.Parse("56315432342249049220074346"); var bstar = BigInteger.Parse("11844213708722456883529547");
      var acf = BigInteger.Parse("65611068146377812701339047"); var bcf = BigInteger.Parse("13799263904438599642302872");
      bool Danger(BigInteger a, BigInteger b) => BigInteger.Abs(b * Bb - a * s) * Q < 9 * a * (s + Bb);
      Check(Danger(astar, bstar), "dangerous-fraction a* dangerous"); Check(Danger(acf, bcf), "dangerous-fraction a_CF dangerous"); Check(astar < acf, "dangerous-fraction a* < a_CF");
      // Farey neighbours of b/a (written as x-values b/a around s/B): left < b*/a* < right with determinant 1
      BigInteger ln = BigInteger.Parse("11192530310150409297271772"), ld = BigInteger.Parse("53216887074206128059652779");
      BigInteger rn = BigInteger.Parse("651683398572047586257775"), rd = BigInteger.Parse("3098545268042921160421567");
      BigInteger det = rn * ld - ln * rd; Check(BigInteger.Abs(det) == 1, "dangerous-fraction neighbours determinant " + det);
      Check(ln + rn == bstar && ld + rd == astar, "dangerous-fraction mediant is (b*, a*)");
      bool Dr(BigInteger b, BigInteger a) => Danger(a, b);
      Check(!Dr(ln, ld) && !Dr(rn, rd), "dangerous-fraction neighbours not dangerous (interval inside them)");
      // ordinary convergents of B/s: first dangerous one
      BigInteger num = Bb, den = s, h1 = 1, h2 = 0, k1 = 0, k2 = 1; int idx = 0;
      while (!den.IsZero) { var q = BigInteger.DivRem(num, den, out var r); BigInteger h = q * h1 + h2, k = q * k1 + k2; h2 = h1; h1 = h; k2 = k1; k1 = k; idx++; if (Danger(h, k)) { Check(h == acf && k == bcf, $"dangerous-fraction first dangerous convergent #{idx} is a_CF"); break; } num = den; den = r; }
      Console.WriteLine($"dangerous-fraction a_CF/a* = {(double)acf / (double)astar:F10}");
    }
    // no square-root scale: {2,13}, N=360, M=187
    {
      BigInteger s = Pw(13, 34596), Bb = Pw(2, 128881), Q = Pw(13, 373);
      var lhs = (Bb * Q) * (Bb * Q); var t = s * Q + 9 * (s + Bb); var rhs = BigInteger.Pow(10, 100) * Q * t * t;
      Check(lhs > rhs, "square-root-scale (BQ)^2 > 10^100 Q (sQ+9(s+B))^2");
    }
    // N05: p=3, D=12, X=1626: Kolmogorov distance of the cut ball from the uniform law on [0,X]
    {
      var set = new List<long>(); for (long k = -1626; k <= 1626; k++) { long ak = Math.Abs(k); bool ok = true; for (int n = 1; ; n++) { var q = Pw(3, n * n); if (q > (ak + 2) * 12) break; var r = (long)(ak % q); var d = Math.Min(r, (long)q - r); if (d * 12 >= q) { ok = false; break; } } if (ok) set.Add(k); }
      double ks = 0; for (int i = 0; i < set.Count; i++) { double x = (set[i] + 1626.0) / 3252.0; ks = Math.Max(ks, Math.Max(Math.Abs((i + 1.0) / set.Count - x), Math.Abs((double)i / set.Count - x))); }
      Console.WriteLine($"N05: |set|={set.Count} max={set.Max()} KS={ks:F8}  230/11111={230.0 / 11111:F8}  230/271={230.0 / 271:F6}");
    }
    // table energies: energies of the table rows (full symmetric products)
    foreach (var (D, N, M) in new[] { (26, 4, 3), (30, 5, 4), (40, 5, 4) }) { var a = T(2, D, N); var b = T(3, D, M); Console.WriteLine($"table-energy D={D} ({N},{M}) |A|={a.Count} |B|={b.Count} E={Energy(a, b)}"); }
  }
}

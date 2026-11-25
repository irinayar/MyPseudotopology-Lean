using System;
using System.Collections.Generic;
using System.Linq;
// Direct check of the D=20, X=1656918 statistics for the pair {2,3}: A = {a in [0,X]: P_3(a) < 1/D}, B = {b: P_2(b) < 1/D}.
class P {
  static bool InBall(long k, int p, long D) { // P_p(k) < 1/D : for all n, ||k/p^(n^2)|| < 1/D, i.e. dist(k mod q, {0,q}) * D < q
    long q = 1; for (int n = 1; ; n++) { q *= (long)Math.Pow(p, 0) * 0 + 1; break; }
    for (int n = 1; n <= 6; n++) { long Q = 1; for (int i = 0; i < n * n; i++) Q *= p; if (Q > 4000000000000000000L / 2) break;
      long r = ((k % Q) + Q) % Q; long d = Math.Min(r, Q - r); if (d * D >= Q) return false; if (Q > 2 * Math.Abs(k) * D + 10) break; }
    return true;
  }
  static void Main() {
    long D = 20, X = 1656918; var A = new List<long>(); var B = new List<long>();
    for (long k = 0; k <= X; k++) { if (InBall(k, 3, D)) A.Add(k); if (InBall(k, 2, D)) B.Add(k); }
    Console.WriteLine($"|A|={A.Count} |B|={B.Count}");
    var rB = new Dictionary<long, long>(); foreach (var x in B) foreach (var y in B) { long d = x - y; if (d > 0) { rB.TryGetValue(d, out var c); rB[d] = c + 1; } }
    var rA = new Dictionary<long, long>(); foreach (var x in A) foreach (var y in A) { long d = x - y; if (d > 0 && rB.ContainsKey(d)) { rA.TryGetValue(d, out var c); rA[d] = c + 1; } }
    var terms = rA.Select(kv => (h: kv.Key, a: kv.Value, b: rB[kv.Key], pr: kv.Value * rB[kv.Key])).OrderByDescending(t => t.pr).ToList();
    long diag = (long)A.Count * B.Count; long pos = terms.Sum(t => t.pr); long E = diag + 2 * pos;
    Console.WriteLine($"positive shifts with nonzero term: {terms.Count}; E={E}; diagonal share={100.0 * diag / E:F4}%");
    long top8 = terms.Take(8).Sum(t => t.pr);
    Console.WriteLine($"top 8 sum={top8}; share 2*top8/E={100.0 * 2 * top8 / E:F4}%; positive-only share top8/E={100.0 * top8 / E:F4}%");
    foreach (var t in terms.Take(8)) Console.WriteLine($"  h={t.h} rA={t.a} rB={t.b} prod={t.pr}");
  }
}

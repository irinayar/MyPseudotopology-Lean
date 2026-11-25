using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
// Best "separated" subset G of digit levels of the two chains (each weight exceeds the cumulative range of all smaller chosen levels).
// For separated G, Z_G = 0 forces all digits 0, so P(Z=0) <= prod_G 1/(2J+1)  (positivity of the characteristic function).
// The resulting bound on C = (range size) * P(Z=0) is  range / prod_G (2J+1).  Report log of that bound for several D at the heights
// of both chains completed up to levels (N2, N3).
class S {
  record Lv(double logw, double logrange, double logsize);
  static List<Lv> Levels(int l, BigInteger D, int Nmax) {
    var r = new List<Lv>();
    for (int n = 1; n <= Nmax; n++) {
      BigInteger J = BigInteger.Pow(l, 2 * n - 1) / D; if (J == 0) continue;
      double lw = (n - 1) * (n - 1) * Math.Log(l);
      r.Add(new Lv(lw, lw + Math.Log(2.0 * (double)J + 0.0001), Math.Log(2.0 * (double)J + 1)));
    }
    return r;
  }
  static void Main() {
    foreach (var (ds, n2, n3) in new[] { ("20", 6, 5), ("60", 7, 5), ("1000", 9, 7), ("1000000", 12, 9) }) {
      BigInteger D = BigInteger.Parse(ds);
      var all = Levels(2, D, n2).Concat(Levels(3, D, n3)).OrderBy(v => v.logw).ToList();
      double totalLogSize = all.Sum(v => v.logsize);
      // range of the whole difference variable Z: about 2*max(range) ; use top two ranges
      double logRange = Math.Log(2.0) + all.Max(v => v.logrange);
      // DP: best[i] = max total logsize of a separated chain ending at level i (cumulative range approximated by 1.3 * range_i)
      int m = all.Count; var best = new double[m]; var prev = new int[m];
      for (int i = 0; i < m; i++) {
        best[i] = all[i].logsize; prev[i] = -1;
        for (int j = 0; j < i; j++) {
          // chain ending at j has cumulative range <= 1.3 * range_j ; need w_i > that
          if (all[i].logw > all[j].logrange + Math.Log(1.3) + Math.Log(1.0)) { double c = best[j] + all[i].logsize; if (c > best[i]) { best[i] = c; prev[i] = j; } }
        }
      }
      double bestG = best.Max();
      Console.WriteLine($"D={ds}: levels={m}, log prod over all levels={totalLogSize:F1}, log(range of Z)={logRange:F1}, best separated subset log prod={bestG:F1}; log of the resulting bound on C = {logRange - bestG:F1}");
    }
  }
}

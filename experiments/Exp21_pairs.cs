using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

public static class Pairs {
  // scale: Q = prime^(n^2), shift = 1 for the "k-1" chain (prime p), 0 for the "k" chain (prime q)
  struct Sc { public long Q; public int shift; public int prime; }

  static bool Ok(long k, Sc s, long d) {
    long v = k - s.shift;
    long r = ((v % s.Q) + s.Q) % s.Q;
    long m = r < s.Q - r ? r : s.Q - r;
    return d * m < s.Q;
  }

  static long Gcd(long a, long b) { while (b != 0) { long t = a % b; a = b; b = t; } return a; }

  public static string Run(int p, int q, long X, int dd, long LIM) {
    long d = dd;
    var sc = new List<Sc>();
    int[] prs = new int[] { p, q };
    int[] shs = new int[] { 1, 0 };
    for (int c = 0; c < 2; c++) {
      for (long n = 1; ; n++) {
        double lg = n * n * Math.Log(prs[c]);
        if (lg > Math.Log((double)X * d) + 1e-9) break;
        long Q = 1; for (long i = 0; i < n * n; i++) Q *= prs[c];
        if (Q > X * d) break;
        Sc s0 = new Sc(); s0.Q = Q; s0.shift = shs[c]; s0.prime = prs[c];
        sc.Add(s0);
      }
    }
    sc = sc.OrderBy(s => s.Q).ToList();
    int J = sc.Count;
    // prefix with lcm <= LIM
    long L = 1; int jp = 0;
    long lp = 1, lq = 1; // chain maxima
    for (int j = 0; j < J; j++) {
      long nlp = lp, nlq = lq;
      if (sc[j].prime == p) nlp = Math.Max(lp, sc[j].Q); else nlq = Math.Max(lq, sc[j].Q);
      long nl = nlp * nlq;
      if (nl > LIM) break;
      lp = nlp; lq = nlq; L = nl; jp = j + 1;
    }
    var counts = new long[J + 1];
    counts[0] = X;
    // residues mod L satisfying first j tests, j<=jp
    // compute for each residue the number of prefix tests passed
    long[] passed = new long[L];
    for (long r = 0; r < L; r++) {
      int c = 0;
      while (c < jp && Ok(r, sc[c], d)) c++;
      passed[r] = c;
    }
    for (int j = 1; j <= jp; j++) {
      long cnt = 0;
      for (long r = 0; r < L; r++) if (passed[r] >= j) {
        long r1 = r == 0 ? L : r;
        if (r1 <= X) cnt += (X - r1) / L + 1;
      }
      counts[j] = cnt;
    }
    long witness = long.MaxValue;
    for (long r = 0; r < L; r++) {
      if (passed[r] < jp) continue;
      long r1 = r == 0 ? L : r;
      for (long k = r1; k <= X; k += L) {
        int j = jp;
        while (j < J && Ok(k, sc[j], d)) { j++; counts[j]++; }
        // counts[j] holds survivors of j tests; we incremented on pass
        if (j == J && k < witness) witness = k;
      }
    }
    // counts above prefix were incremented once per surviving test passed (cumulative): fine
    var sb = new StringBuilder();
    sb.Append("p=" + p + " q=" + q + " X=" + X + " delta=1/" + dd + " L=" + L + " J=" + J + " jp=" + jp + "\n");
    sb.Append("  scales: " + string.Join(",", sc.Select(s => s.Q + (s.shift == 1 ? "'" : ""))) + "\n");
    sb.Append("  A_j:    " + string.Join(" ", counts.Skip(1)) + "\n");
    var rat = new List<string>();
    for (int j = 1; j <= J; j++) rat.Add(counts[j - 1] == 0 ? "-" : ((double)counts[j] / counts[j - 1]).ToString("0.000"));
    sb.Append("  ratios: " + string.Join(" ", rat) + "\n");
    sb.Append("  N=" + counts[J] + "  min witness k=" + (witness == long.MaxValue ? "none<=X" : witness.ToString()) + "\n");
    return sb.ToString();
  }
}

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Text;

public static class InvTest2 {
  static BigInteger ModInv(BigInteger a, BigInteger m) {
    BigInteger r0 = m, r1 = ((a % m) + m) % m, s0 = 0, s1 = 1;
    while (!r1.IsZero) { BigInteger q = r0 / r1; BigInteger t = r0 - q * r1; r0 = r1; r1 = t; t = s0 - q * s1; s0 = s1; s1 = t; }
    return ((s0 % m) + m) % m;
  }
  static bool Good(BigInteger v, BigInteger Q, int D) {
    BigInteger r = BigInteger.Remainder(v, Q); BigInteger m = BigInteger.Min(r, Q - r); return D * m < Q;
  }
  public static string Run(int D, BigInteger K, int nb, int nt) {
    long Mb = 1L << (nb * nb); long Mt = 1; for (int i = 0; i < nt * nt; i++) Mt *= 3;
    var scB = new List<long>(); for (int i = 1; i <= nb; i++) scB.Add(1L << (i * i));
    var scT = new List<long>(); for (int i = 1; i <= nt; i++) { long q = 1; for (int j = 0; j < i * i; j++) q *= 3; scT.Add(q); }
    var bin = new List<long>(); var binSet = new HashSet<long>();
    for (long a = 0; a < Mb; a++) { bool ok = true; foreach (long Q in scB) { long r = a % Q; long m = r < Q - r ? r : Q - r; if (D * m >= Q) { ok = false; break; } } if (ok) { bin.Add(a); binSet.Add(a); } }
    var ter = new List<long>();
    for (long b = 0; b < Mt; b++) { bool ok = true; foreach (long Q in scT) { long r = b % Q; long m = r < Q - r ? r : Q - r; if (D * m >= Q) { ok = false; break; } } if (ok) ter.Add(b); }
    var sb = new StringBuilder();
    sb.Append("D=" + D + ": |S_bin|=" + bin.Count + " |S_ter|=" + ter.Count + "\n");
    // closure of S_bin under k -> k^{-1}
    int inS = 0, odd = 0; var invMap = new Dictionary<long, long>();
    foreach (long a in bin) {
      BigInteger k = 1 + a; if (k.IsEven) continue; odd++;
      long ap = (long)((ModInv(k, Mb) - 1 + Mb) % Mb); invMap[a] = ap;
      if (binSet.Contains(ap)) inS++;
    }
    sb.Append("  inversion k->k^-1 mod 2^" + (nb * nb) + ": odd-k elements=" + odd + ", mapped into S_bin=" + inS + "\n");
    // negation k-1 -> -(k-1) is always a symmetry of ||.||; check S_bin closed under a->-a
    int negIn = 0; foreach (long a in bin) if (binSet.Contains((Mb - a) % Mb)) negIn++;
    sb.Append("  negation a->-a: mapped into S_bin=" + negIn + " of " + bin.Count + "\n");
    // remaining scales
    var rest = new List<KeyValuePair<BigInteger, int>>(); BigInteger limit = K * D;
    for (int i = nb + 1; ; i++) { BigInteger Q = BigInteger.Pow(2, i * i); if (Q > limit) break; rest.Add(new KeyValuePair<BigInteger, int>(Q, 2)); }
    for (int i = nt + 1; ; i++) { BigInteger Q = BigInteger.Pow(3, i * i); if (Q > limit) break; rest.Add(new KeyValuePair<BigInteger, int>(Q, 3)); }
    BigInteger M = (BigInteger)Mb * Mt; BigInteger inv = ModInv((BigInteger)Mb % Mt, Mt);
    Func<long, long, BigInteger> crt = (a, b) => {
      BigInteger k0 = 1 + a; BigInteger t = (((b - k0) % Mt + Mt) % Mt) * inv % Mt; return k0 + (BigInteger)Mb * t; };
    Func<BigInteger, bool> full = (k) => {
      foreach (var s in rest) { BigInteger v = s.Value == 2 ? k - 1 : k; if (!Good(v, s.Key, D)) return false; } return true; };
    // survivors
    var surv = new List<BigInteger>();
    foreach (long a in bin) foreach (long b in ter) {
      BigInteger c = crt(a, b);
      for (BigInteger k = (c.IsZero ? M : c); k <= K; k += M) if (full(k)) surv.Add(k);
    }
    surv.Sort();
    sb.Append("  survivors up to K: " + surv.Count + "\n");
    // inversion-image test
    int imgInS = 0, selfFixed = 0; long imgCand = 0, imgSurv = 0;
    foreach (BigInteger ks in surv) {
      long a = (long)BigInteger.Remainder(ks - 1, Mb); long b = (long)BigInteger.Remainder(ks, Mt);
      BigInteger kinv = ModInv(BigInteger.Remainder(ks, Mb), Mb); long ap = (long)((kinv - 1 + Mb) % Mb);
      if (!binSet.Contains(ap)) continue; imgInS++; if (ap == a) { selfFixed++; continue; }
      BigInteger c = crt(ap, b);
      for (BigInteger k = (c.IsZero ? M : c); k <= K; k += M) { imgCand++; if (full(k)) { imgSurv++; } }
    }
    sb.Append("  inversion images of survivors lying in S_bin: " + imgInS + "; candidates in those classes: " + imgCand + "; survivors among them: " + imgSurv + " (classes with a'=a excluded: " + selfFixed + ")\n");
    // baseline: random sample of classes with same size
    sb.Append("  baseline survivor rate = " + surv.Count + " / total candidates (see counts above)\n");
    return sb.ToString();
  }
}

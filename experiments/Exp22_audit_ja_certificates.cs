using System;
using System.Collections.Generic;
using System.Numerics;
using System.Text;

public static class AuditJA2 {
  // exact P_l(m) = sup_n ||m / l^(n^2)||, returned as (num, den) with den = l^(n^2)
  public static string PNorm(BigInteger m, int l) {
    m = BigInteger.Abs(m);
    BigInteger bestN = 0, bestD = 1;
    for (int n = 1; ; n++) {
      BigInteger Q = BigInteger.Pow(l, n * n);
      BigInteger r = BigInteger.Remainder(m, Q);
      BigInteger mn = BigInteger.Min(r, Q - r);
      if (mn * bestD > bestN * Q) { bestN = mn; bestD = Q; }
      if (Q > 2 * m + 2 && n > 2) break;
    }
    BigInteger g = BigInteger.GreatestCommonDivisor(bestN, bestD);
    if (g.IsZero) g = 1;
    return (bestN / g).ToString() + "/" + (bestD / g).ToString();
  }

  static BigInteger ModInv(BigInteger a, BigInteger m) {
    BigInteger g = m, x = 0, y = 1, aa = a % m;
    BigInteger r0 = m, r1 = aa, s0 = 0, s1 = 1;
    while (!r1.IsZero) {
      BigInteger q = r0 / r1;
      BigInteger t = r0 - q * r1; r0 = r1; r1 = t;
      t = s0 - q * s1; s0 = s1; s1 = t;
    }
    return ((s0 % m) + m) % m;
  }

  // exact minimum check: does any k in [1, K] satisfy P_2(k-1) < 1/D and P_3(k) < 1/D ?
  public static string FiniteMin(int D, BigInteger K, int nb, int nt, int s2, int s3) {
    // binary prefix: scales 2^(i^2), i=1..nb ; ternary prefix: 3^(i^2), i=1..nt
    long Mb = 1L << (nb * nb);
    long Mt = 1; for (int i = 0; i < nt * nt; i++) Mt *= 3;
    var bin = new List<long>();
    var scB = new List<long>(); for (int i = 1; i <= nb; i++) scB.Add(1L << (i * i));
    for (long a = 0; a < Mb; a++) {
      bool ok = true;
      foreach (long Q in scB) { long r = a % Q; long m = r < Q - r ? r : Q - r; if (D * m >= Q) { ok = false; break; } }
      if (ok) bin.Add(a);
    }
    var ter = new List<long>();
    var scT = new List<long>(); for (int i = 1; i <= nt; i++) { long q = 1; for (int j = 0; j < i * i; j++) q *= 3; scT.Add(q); }
    for (long b = 0; b < Mt; b++) {
      bool ok = true;
      foreach (long Q in scT) { long r = b % Q; long m = r < Q - r ? r : Q - r; if (D * m >= Q) { ok = false; break; } }
      if (ok) ter.Add(b);
    }
    BigInteger M = (BigInteger)Mb * Mt;
    BigInteger inv = ModInv((BigInteger)Mb % Mt, Mt);   // Mb^{-1} mod Mt
    var rest = new List<KeyValuePair<BigInteger, int>>(); // remaining active scales: (Q, prime)
    BigInteger limit = K * D;
    for (int i = nb + 1; ; i++) { BigInteger Q = BigInteger.Pow(2, i * i); if (Q > limit) break; rest.Add(new KeyValuePair<BigInteger, int>(Q, 2)); }
    for (int i = nt + 1; ; i++) { BigInteger Q = BigInteger.Pow(3, i * i); if (Q > limit) break; rest.Add(new KeyValuePair<BigInteger, int>(Q, 3)); }
    long classes = 0, cands = 0, surv = 0; BigInteger first = -1;
    foreach (long a in bin) foreach (long b in ter) {
      // k = 1 + a (mod 2^nb^2), k = b (mod 3^nt^2)
      BigInteger k0 = s2 + a;
      // solve k = k0 + Mb * t, with k0 + Mb t = b mod Mt -> t = (b - k0) * inv mod Mt
      BigInteger t = (((b + s3 - k0) % Mt + Mt) % Mt) * inv % Mt;
      BigInteger c = k0 + (BigInteger)Mb * t;      // 0 <= c < M
      classes++;
      for (BigInteger k = (c.IsZero ? M : c); k <= K; k += M) {
        cands++;
        bool ok = true;
        foreach (var s in rest) {
          BigInteger v = s.Value == 2 ? k - s2 : k - s3;
          BigInteger r = BigInteger.Remainder(v, s.Key);
          BigInteger m = BigInteger.Min(r, s.Key - r);
          if (D * m >= s.Key) { ok = false; break; }
        }
        if (ok) { surv++; if (first < 0 || k < first) first = k; }
      }
    }
    var sb = new StringBuilder();
    sb.Append("D=" + D + " binary residues=" + bin.Count + " ternary residues=" + ter.Count + " classes=" + classes + " modulus=" + M + " candidates=" + cands);
    sb.Append(" rest scales=" + rest.Count + " survivors(strict)=" + surv + " first=" + first);
    return sb.ToString();
  }
}

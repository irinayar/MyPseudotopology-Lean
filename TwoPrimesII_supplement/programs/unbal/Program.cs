using System;
using System.Collections.Generic;
using System.Numerics;

// unbal: window heights with far-apart top steps, and the bound Gamma_D there.
// Primes p < q.  The SMALLER step is u = q^((n-1)^2) (level n of q), the larger v = p^((m-1)^2) (level m of p), v >= K D u.
// Heights: D v <= X < min(q^(n^2), p^(m^2)) / D.
// usage: unbal p q K x D1 [D2 ...]       (D may be given as 1eNN; it is moved up until coprime to pq)
//        unbal list p q K Dlo Dhi        (all small D with such a height of size below 10^18, for exact tests)
class P {
  static BigInteger Pw(int b, long e) => BigInteger.Pow(b, (int)e);
  static BigInteger MaxT(int p, BigInteger D, int N) { BigInteger s = 0; for (int n = 1; n <= N; n++) { BigInteger J = Pw(p, 2L * n - 1) / D; s += J * Pw(p, (long)(n - 1) * (n - 1)); } return s; }
  static double Ln(BigInteger a) => BigInteger.Log(a);
  static double Ratio(BigInteger a, BigInteger b) => a.IsZero ? 0 : Math.Exp(Ln(BigInteger.Abs(a)) - Ln(b)) * a.Sign;

  // Gamma_D from the exact geometry; returns (Gamma upper, Ccont upper, term sqrt, term lambda)
  static (double gam, double cc, double tA, double tL, double lamA) Gamma(BigInteger D, int p, int q, int n, int m, BigInteger X, out BigInteger JA, out BigInteger JB) {
    BigInteger u = Pw(q, (long)(n - 1) * (n - 1)), v = Pw(p, (long)(m - 1) * (m - 1));
    BigInteger UA = MaxT(q, D, n - 1), UB = MaxT(p, D, m - 1);
    BigInteger ja = BigInteger.Min(Pw(q, 2L * n - 1) / D, (X + UA) / u), jb = BigInteger.Min(Pw(p, 2L * m - 1) / D, (X + UB) / v); JA = ja; JB = jb;
    BigInteger JAl = ja, JBl = jb;
    BigInteger W = 2 * (UA + UB);
    BigInteger P1 = u * (JA + 1), P2 = v * (JB + 1), Pm = BigInteger.Min(P1, P2), Q = BigInteger.Max(P1, P2);
    // C_cont between C0 - 2XW/Q^2 and C0
    double c0 = 2.0 / 3.0 * Ratio(X, Q) * (3.0 - Ratio(Pm, Q));
    double cl = c0 - 2.0 * Ratio(X, Q) * Ratio(W, Q);
    // area A0 = (4 Pm W - (W-Q+Pm)_+^2 + (W-Pm-Q)_+^2)/(uv)
    BigInteger a1 = BigInteger.Max(0, W - Q + Pm), a2 = BigInteger.Max(0, W - Pm - Q);
    BigInteger areaNum = 4 * Pm * W - a1 * a1 + a2 * a2;
    double lnA0 = Ln(areaNum) - Ln(u) - Ln(v);
    BigInteger h = BigInteger.Min(UA, UB), hp = BigInteger.Max(UA, UB);
    // H(0) = (3h'-h)/(6h'^2) ;  A_eff = Ccont (JA+1)(JB+1)/(2 X H0), lower bound with cl
    double lnH0 = Ln(3 * hp - h) - Math.Log(6) - 2 * Ln(hp);
    double lnAeff = Math.Log(cl) + Ln(JA + 1) + Ln(JB + 1) - Math.Log(2) - Ln(X) - lnH0;
    // lambda0' : min over (1,0) and the convergents (p_k,q_k) of v/u of max(m/(JA+1), n/(JB+1), |mu-nv|/W)
    double best = double.PositiveInfinity;
    void Try(BigInteger mm, BigInteger nn) {
      if (mm.IsZero && nn.IsZero) return;
      double g1 = mm.IsZero ? double.NegativeInfinity : Ln(mm) - Ln(JAl + 1);
      double g2 = nn.IsZero ? double.NegativeInfinity : Ln(nn) - Ln(JBl + 1);
      BigInteger d = BigInteger.Abs(mm * u - nn * v);
      double g3 = d.IsZero ? double.NegativeInfinity : Ln(d) - Ln(W);
      double g = Math.Max(g1, Math.Max(g2, g3)); if (g < best) best = g;
    }
    Try(1, 0); Try(0, 1);
    BigInteger num = v, den = u, p0 = 0, p1 = 1, q0 = 1, q1 = 0;
    while (!den.IsZero) {
      BigInteger a = BigInteger.DivRem(num, den, out var r);
      BigInteger pk = a * p1 + p0, qk = a * q1 + q0;   // pk/qk -> v/u : m = pk (steps u), n = qk (steps v)
      Try(pk, qk);
      p0 = p1; p1 = pk; q0 = q1; q1 = qk; num = den; den = r;
      if (pk > JAl && qk > JBl) break;
    }
    double tA = Math.Exp(Math.Log(2) + 0.5 * lnA0 - lnAeff) + Math.Exp(-lnAeff);
    double tL = Math.Exp(Math.Log(2) - best - lnAeff);
    return (c0 * (1 + tA + tL), c0, tA, tL, Math.Exp(best + lnAeff));
  }


  // C_model = 2X sum (JA+1-|m|)(JB+1-|n|) H(mu-nv) / ((JA+1)(JB+1))^2 , H the density of four uniforms
  static double Model(BigInteger D, int p, int q, int n, int m, BigInteger X, BigInteger JA, BigInteger JB) {
    BigInteger u = Pw(q, (long)(n - 1) * (n - 1)), v = Pw(p, (long)(m - 1) * (m - 1));
    BigInteger UA = MaxT(q, D, n - 1), UB = MaxT(p, D, m - 1), W = 2 * (UA + UB);
    double a = Ratio(UA, UB), b = 1.0, w = 2 * (a + b); int[] c2 = { 1, 2, 1 };
    double H(double z) { double s = 0; z = -Math.Abs(z); for (int i = 0; i <= 2; i++) for (int j = 0; j <= 2; j++) { double y = z + w - 2 * i * a - 2 * j * b; if (y > 0) s += ((i + j) % 2 == 0 ? 1 : -1) * c2[i] * c2[j] * y * y * y; } return s / (96 * a * a * b * b); }
    long ja = (long)JA, jb = (long)JB; double sum = 0;
    for (long k = -jb; k <= jb; k++) {
      BigInteger c = k * v;
      long lo = (long)BigInteger.Max(-ja, (c - W) / u - 1), hi = (long)BigInteger.Min(ja, (c + W) / u + 1);
      for (long mm = lo; mm <= hi; mm++) { double z = Ratio(mm * u - c, UB); if (Math.Abs(z) >= w) continue; sum += (double)(ja + 1 - Math.Abs(mm)) * (jb + 1 - Math.Abs(k)) * H(z); }
    }
    double norm = (double)(ja + 1) * (jb + 1);
    return 2.0 * sum / (norm * norm) * Ratio(X, UB);
  }

  static bool Search(int p, int q, BigInteger D, BigInteger K, double x, out int n, out int m, out BigInteger X, int span) {
    double L = Ln(D), a = Math.Log(p), b = Math.Log(q);
    int s0 = (int)Math.Ceiling(L * Math.Sqrt(x / b));
    for (int s = s0; s < s0 + span; s++) {
      BigInteger u = Pw(q, (long)s * s);
      int t = (int)Math.Floor(s * Math.Sqrt(b / a));
      for (int tt = Math.Max(1, t - 1); tt <= t + 6; tt++) {
        BigInteger v = Pw(p, (long)tt * tt);
        if (v < K * D * u) continue;
        BigInteger lo = D * v, hi = BigInteger.Min(Pw(q, (long)(s + 1) * (s + 1)), Pw(p, (long)(tt + 1) * (tt + 1))) / D - 1;
        if (lo > hi) continue;
        n = s + 1; m = tt + 1; X = BigInteger.Min(hi, lo * 3); return true;
      }
    }
    n = m = 0; X = 0; return false;
  }

  static void Main(string[] a) {
    if (a[0] == "at") { int p0 = int.Parse(a[1]), q0 = int.Parse(a[2]); BigInteger D0 = BigInteger.Parse(a[3]); int n0 = int.Parse(a[4]), m0 = int.Parse(a[5]); BigInteger X0 = BigInteger.Parse(a[6]); var g = Gamma(D0, p0, q0, n0, m0, X0, out BigInteger ja, out BigInteger jb); Console.WriteLine($"{ja} {jb} {g.cc:F5} {g.gam:F5} {Model(D0, p0, q0, n0, m0, X0, ja, jb):F5}"); return; }
    if (a[0] == "list") {
      int p = int.Parse(a[1]), q = int.Parse(a[2]); long K = long.Parse(a[3]); int Dlo = int.Parse(a[4]), Dhi = int.Parse(a[5]);
      for (int D = Dlo; D <= Dhi; D++) {
        if (D % p == 0 && IsPow(D, p) || IsPow(D, q)) continue;
        for (int n = 2; n <= 7; n++) for (int m = 2; m <= 9; m++) {
          BigInteger u = Pw(q, (long)(n - 1) * (n - 1)), v = Pw(p, (long)(m - 1) * (m - 1));
          if (v < (BigInteger)K * D * u) continue;
          BigInteger lo = D * v, hi = BigInteger.Min(Pw(q, (long)n * n), Pw(p, (long)m * m)) / D - 1;
          if (lo > hi || lo > BigInteger.Pow(10, 15)) continue;
          Console.WriteLine($"D={D} n={n}(q) m={m}(p) u={u} v={v} rho/D={(double)v / (double)u / D:F2} X in [{lo},{hi}]");
        }
      }
      return;
    }
    {
      int p = int.Parse(a[0]), q = int.Parse(a[1]); long K = long.Parse(a[2]); double x = double.Parse(a[3], System.Globalization.CultureInfo.InvariantCulture);
      for (int i = 4; i < a.Length; i++) {
        BigInteger D = a[i].StartsWith("1e") ? BigInteger.Pow(10, int.Parse(a[i].Substring(2))) : BigInteger.Parse(a[i]);
        while (!(BigInteger.GreatestCommonDivisor(D, p * q).IsOne)) D++;
        if (!Search(p, q, D, K, x, out int n, out int m, out BigInteger X, 400)) { Console.WriteLine($"D~{a[i]}: no height found"); continue; }
        var r = Gamma(D, p, q, n, m, X, out BigInteger JA, out BigInteger JB);
        BigInteger u = Pw(q, (long)(n - 1) * (n - 1)), v = Pw(p, (long)(m - 1) * (m - 1));
        double L = Ln(D);
        bool ok = v >= K * D * u && X >= D * v && X < Pw(q, (long)n * n) / D && X < Pw(p, (long)m * m) / D && JA >= D && JB >= D;
        Console.WriteLine($"D={a[i]} n={n} m={m} ln(v/u)/lnD={(Ln(v) - Ln(u)) / L:F3} lnX/ln^2D={Ln(X) / (L * L):F3} checks={ok} Ccont<={r.cc:F5} sqrtTerm={r.tA:E2} lamTerm={r.tL:E2} Gamma<={r.gam:F5}");
      }
    }
  }
  static bool IsPow(int D, int p) { long x = 1; while (x < D) x *= p; return x == D; }
}

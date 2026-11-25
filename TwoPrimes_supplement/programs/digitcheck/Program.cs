using System;
using System.Collections.Generic;
using System.Numerics;

// Check of the digit-set model of the symmetric one-prime ball (r=1/m):
//  (1) direct definition  {k : |k|<=K, P_p(k)<1/m}  versus the digit set
//  (2) autocorrelation r_A(h) versus product formula prod_n (2J_n+1-|delta_n|)
class D {
  static void Main(string[] a) {
    long p = long.Parse(a[0]), m = long.Parse(a[1]); long K = long.Parse(a[2]);
    // direct set
    var lv = new List<long>(); for (long n = 1; ; n++) { BigInteger q = BigInteger.Pow(p, (int)(n * n)); if (q > (BigInteger)m * K) break; lv.Add((long)q); }
    var direct = new HashSet<long>();
    for (long k = -K; k <= K; k++) { bool ok = true; foreach (long q in lv) { long r = ((k % q) + q) % q; long d = Math.Min(r, q - r); if (m * d >= q) { ok = false; break; } } if (ok) direct.Add(k); }
    Console.WriteLine($"direct |A_sym| (|k|<={K}) = {direct.Count}");
    // digit model: levels n>=1; weights w_n = q_{n-1}; J_n = largest j with |j| < rho_n = q_n/(m q_{n-1}) minus boundary; here use J_n = ceil(rho_n)-1
    var qs = new List<long> { 1 }; foreach (long q in lv) qs.Add(q);
    var Js = new List<long>(); var ws = new List<long>();
    for (int n = 1; n < qs.Count; n++) {
      // rho = q_n / (m q_{n-1}); J = ceil(rho)-1 for non-integer rho
      BigInteger num = qs[n], den = (BigInteger)m * qs[n - 1];
      long J = (long)((num - 1) / den); // largest integer strictly below rho (rho not integer or integer)
      if (J > 0) { Js.Add(J); ws.Add(qs[n - 1]); }
    }
    Console.WriteLine("digit ranges J_n (weights): " + string.Join(", ", Js.ConvertAll(x => x.ToString())) + "   weights " + string.Join(", ", ws.ConvertAll(x => x.ToString())));
    BigInteger cnt = 1; foreach (long J in Js) cnt *= (2 * J + 1);
    Console.WriteLine($"digit model size = {cnt}");
    // top level cut by K: the last digit is limited by K, handled by comparing only for the complete model:
    var model = new HashSet<long> { 0 };
    for (int i = 0; i < Js.Count; i++) { var nx = new HashSet<long>(); foreach (long x in model) for (long j = -Js[i]; j <= Js[i]; j++) nx.Add(x + j * ws[i]); model = nx; }
    long mx = 0; foreach (long x in model) mx = Math.Max(mx, Math.Abs(x));
    Console.WriteLine($"model max |k| = {mx}; model == direct (within |k|<={K}): {SetEq(model, direct, K)}");
    // autocorrelation at a given h
    if (a.Length > 3) {
      long h = long.Parse(a[3]); long c = 0; foreach (long x in model) if (model.Contains(x + h)) c++;
      // product formula via balanced digits of h in the weights
      long rem = h; BigInteger prod = 1; var digs = new List<long>();
      for (int i = Js.Count - 1; i >= 0; i--) { long w = ws[i]; long d = (long)Math.Round((double)rem / w); rem -= d * w; digs.Insert(0, d); prod *= (2 * Js[i] + 1 - Math.Abs(d)) > 0 ? (2 * Js[i] + 1 - Math.Abs(d)) : 0; }
      Console.WriteLine($"h={h}: r_A(h) direct={c}; balanced digits={string.Join(",", digs)} remainder={rem}; product formula={prod}");
    }
  }
  static bool SetEq(HashSet<long> a, HashSet<long> b, long K) { foreach (long x in a) if (Math.Abs(x) <= K && !b.Contains(x)) return false; foreach (long x in b) if (!a.Contains(x)) return false; return true; }
}

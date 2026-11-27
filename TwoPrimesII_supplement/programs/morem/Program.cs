using System;
using System.Collections.Generic;
using System.Globalization;
using System.Linq;
using System.Numerics;
using System.Threading.Tasks;

// morem: checks for TwoPrimesII, heights X = M v with a general number M of top clusters.
//   energy p q D s t M...  : exact energy of the balls from the definition of the metrics (FFT), against the two-sided bounds
//   kappa  p q D s t Mmax  : Phi_j, kappa_M, the transfer inequalities and the small-conductor bound
//   cert                   : independent recomputation of the three low-conductor certificates and of the elementary bound
//   qp     q D s           : the exact conductor masses of the q-digit set against direct counting
class P {
  static CultureInfo CI = CultureInfo.InvariantCulture;
  static BigInteger Pow(int p, int e) => BigInteger.Pow(p, e);

  static List<(long w, long J)> Digits(int p, int D, int levels) {
    var L = new List<(long, long)>();
    for (int n = 1; n <= levels; n++) L.Add(((long)Pow(p, (n - 1) * (n - 1)), (long)(Pow(p, 2 * n - 1) / D)));
    return L;
  }
  static List<long> Set(List<(long w, long J)> L) {
    var S = new List<long> { 0 };
    foreach (var (w, J) in L) { var T = new List<long>(); foreach (var x in S) for (long j = -J; j <= J; j++) T.Add(x + j * w); S = T; }
    return S;
  }
  // k lies in B_p(1/D), directly from sup_n || k / p^{n^2} || < 1/D
  static bool InBall(long k, int p, int D) {
    for (int n = 1; ; n++) {
      BigInteger m = Pow(p, n * n);
      if (m > (BigInteger)k * D * 2 + 2) return true;      // then ||k/m|| = k/m < 1/D, and so for all larger n
      long mm = (long)m, r = k % mm; if (2 * r > mm) r = mm - r;
      if ((long)D * r >= mm) return false;
    }
  }
  static void FFT(Complex[] a, bool inv) {
    int n = a.Length;
    for (int i = 1, j = 0; i < n; i++) { int bit = n >> 1; for (; (j & bit) != 0; bit >>= 1) j ^= bit; j |= bit; if (i < j) (a[i], a[j]) = (a[j], a[i]); }
    var root = new Complex[n / 2];
    for (int k = 0; k < n / 2; k++) { double ang = (inv ? 2 : -2) * Math.PI * k / n; root[k] = new Complex(Math.Cos(ang), Math.Sin(ang)); }
    for (int len = 2; len <= n; len <<= 1) {
      int step = n / len, half = len / 2;
      Parallel.For(0, n / len, b => { int i = b * len; for (int k = 0; k < half; k++) { var x = a[i + k]; var y = a[i + k + half] * root[k * step]; a[i + k] = x + y; a[i + k + half] = x - y; } });
    }
    if (inv) for (int i = 0; i < n; i++) a[i] /= n;
  }
  // E = #{a - b = a' - b'}
  static BigInteger Energy(List<int> A, List<int> B, int X, out double err) {
    int n = 1; while (n < 2 * X + 2) n <<= 1;
    var fa = new Complex[n]; var fb = new Complex[n];
    foreach (var x in A) fa[x] = 1; foreach (var x in B) fb[x] = 1;
    FFT(fa, false); FFT(fb, false);
    for (int i = 0; i < n; i++) fa[i] *= Complex.Conjugate(fb[i]);
    FFT(fa, true);
    BigInteger E = 0; err = 0; long tot = 0;
    for (int i = 0; i < n; i++) { double r = Math.Round(fa[i].Real); err = Math.Max(err, Math.Abs(fa[i].Real - r)); long c = (long)r; E += (BigInteger)c * c; tot += c; }
    if (tot != (long)A.Count * B.Count) throw new Exception("correlation total wrong");
    return E;
  }
  // law of y+z modulo m (probabilities)
  static double[] Law(long m, IEnumerable<(long w, long J)> digits) {
    var f = new double[m]; f[0] = 1;
    foreach (var (w, J) in digits) {
      if (J == 0) continue;
      long N = 2 * J + 1, step = w % m; if (step == 0) continue;
      var g = new double[m];
      // orbits of x -> x + step
      long a = step, b = m; while (b != 0) (a, b) = (b, a % b);
      long orbits = a, len = m / orbits;
      Parallel.For(0L, orbits, o => {
        var idx = new long[len]; long x = o; for (long i = 0; i < len; i++) { idx[i] = x; x += step; if (x >= m) x -= m; }
        long full = N / len, rest = N % len; double all = 0; for (long i = 0; i < len; i++) all += f[idx[i]];
        // value at position i: sum over j in [-J, J] of f[i - j]
        long start = ((-J) % len + len) % len;   // i - j for j = J is i - J
        double win = 0; for (long k = 0; k < rest; k++) win += f[idx[(start + k) % len]];
        for (long i = 0; i < len; i++) {
          g[idx[i]] = (full * all + win) / N;
          win += f[idx[(start + i + rest) % len]] - f[idx[(start + i) % len]];
        }
      });
      f = g;
    }
    return f;
  }
  // Phi_j for j = 1..H: m * sum_r (average of law(r + l v), l<j)^2
  static double[] PhiList(double[] law, long vm, int Hmax) {
    long m = law.Length; var f = new double[m];
    Parallel.For(0L, m, i => f[i] = law[(long)((UInt128)(ulong)i * (ulong)vm % (ulong)m)]);
    var win = new double[m]; var Phi = new double[Hmax + 1];
    for (int j = 1; j <= Hmax; j++) {
      int jj = j; object gate = new object(); double tot = 0;
      Parallel.For(0, 64, () => 0.0, (c, st, acc) => {
        long lo = m * c / 64, hi = m * (c + 1) / 64;
        for (long i = lo; i < hi; i++) { long k = (i + jj - 1) % m; win[i] += f[k]; acc += win[i] * win[i]; }
        return acc;
      }, acc => { lock (gate) tot += acc; });
      Phi[j] = m * tot / ((double)j * j);
    }
    return Phi;
  }
  static double K0(int M) => M * (2.0 * M * M + 1) / 3;
  static double KappaM(double[] Phi, int M) {
    double s = 0; for (int j = 1; j < M; j++) s += 2.0 * j * j * Phi[j]; s += (double)M * M * Phi[M];
    return s / K0(M);
  }

  static void EnergyMode(string[] a) {
    int p = int.Parse(a[1]), q = int.Parse(a[2]), D = int.Parse(a[3]), s = int.Parse(a[4]), t = int.Parse(a[5]);
    long u = (long)Pow(q, s * s), v = (long)Pow(p, t * t);
    var yd = Digits(q, D, s); var zd = Digits(p, D, t);
    var Y = Set(yd); var Z = Set(zd);
    var law = Law(u, yd.Concat(zd));
    for (int ai = 6; ai < a.Length; ai++) {
      int M = int.Parse(a[ai]); long X = M * v;
      bool admissible = v >= 20 * D * u && (BigInteger)D * X < Pow(q, (s + 1) * (s + 1)) && (BigInteger)D * X < Pow(p, (t + 1) * (t + 1));
      var A = new List<int>(); var B = new List<int>();
      for (long k = 0; k <= X; k++) { if (InBall(k, q, D)) A.Add((int)k); if (InBall(k, p, D)) B.Add((int)k); }
      var E = Energy(A, B, (int)X, out double err);
      double C = (2.0 * X + 1) * (double)E / ((double)A.Count * A.Count * (double)B.Count * B.Count);
      bool sizeB = B.Count == (long)M * Z.Count + 1;
      // two-sided bounds: K^- and K^+ with coefficients (M-1-|m|)(M-eps-|m|) and (M+1-|m|)(M+eps-|m|), eps = 3/D
      var f = new double[u]; for (long i = 0; i < u; i++) f[i] = law[(long)((BigInteger)i * v % u)];
      double eps = 3.0 / D;
      double Auto(long m) { double sum = 0; long mm = ((m % u) + u) % u; for (long i = 0; i < u; i++) sum += f[i] * f[(i + mm) % u]; return sum; }
      double lo = 0, up = 0, mid = 0;
      for (int m = -M; m <= M; m++) {
        double ac = u * Auto(m); int am = Math.Abs(m);
        double cp = Math.Max(0, M + 1 - am) * Math.Max(0, M + eps - am);
        double cm = Math.Max(0, M - 1 - am) * Math.Max(0, M - eps - am);
        double w = am < M ? (double)(M - am) * (M - am) : 0;
        up += cp * ac; lo += cm * ac; mid += w * ac;
      }
      double pref = (double)v / u * ((double)Y.Count * Y.Count * Z.Count * Z.Count / u);
      double Elo = pref * lo, Eup = pref * up, kappaM = mid / K0(M);
      Console.WriteLine(string.Format(CI, "p={0} q={1} D={2} s={3} t={4} M={5} admissible={6} |A|={7} |B|={8} |B|=M|Z|+1:{9} E={10} C={11:F6} (4/3)kappaM={12:F6} C/(4/3 kappaM)-1={13:E2} lower<=E:{14} E<=upper:{15} fftErr={16:E1}",
        p, q, D, s, t, M, admissible, A.Count, B.Count, sizeB, E, C, 4.0 / 3 * kappaM, C / (4.0 / 3 * kappaM) - 1, Elo <= (double)E * (1 + 1e-9), (double)E <= Eup * (1 + 1e-9), err));
    }
  }

  static void KappaMode(string[] a) {
    int p = int.Parse(a[1]), q = int.Parse(a[2]), D = int.Parse(a[3]), s = int.Parse(a[4]), t = int.Parse(a[5]), Mmax = int.Parse(a[6]);
    long u = (long)Pow(q, s * s); BigInteger v = Pow(p, t * t); long vm = (long)(v % u);
    var dig = Digits(q, D, s).Concat(Digits(p, D, t).Select(d => (w: (long)(Pow((int)p, 0) * d.w), d.J))).ToList();
    var law = Law(u, dig);
    var Phi = PhiList(law, vm, Mmax);
    double kappa = u * law.Sum(x => x * x);
    var km = new double[Mmax + 1]; for (int M = 1; M <= Mmax; M++) km[M] = KappaM(Phi, M);
    double worstA = 0, worstB = 0;
    for (int H = 1; H <= Mmax; H++)
      for (int j = 1; j <= Mmax; j++) {
        double c = (double)(j + H - 1) / j; worstA = Math.Max(worstA, Phi[j] / (c * c * Phi[H]));
        double h = H - 1; worstB = Math.Max(worstB, km[j] / ((1 + 3 * h / j + 4 * h * h / ((double)j * j)) * Phi[H]));
      }
    Console.WriteLine(string.Format(CI, "p={0} q={1} D={2} s={3} t={4} u={5} kappa={6:F6} max Phi_j/bound={7:F6} max kappa_M/bound={8:F6}", p, q, D, s, t, u, kappa, worstA, worstB));
    Console.Write(" M, kappa_M, Phi_M:");
    foreach (int M in new[] { 1, 2, 5, 10, 20, 40, 80, 160, 320, 640 }) if (M <= Mmax) Console.Write(string.Format(CI, "  ({0}, {1:F6}, {2:F6})", M, km[M], Phi[M]));
    Console.WriteLine();
    // small conductors Q = q^a
    double worstQ = 0;
    for (int e = 1; e <= s * s; e++) {
      long Q = (long)Pow(q, e); if (Q > 3000000) break;
      var lq = Law(Q, dig); var Pq = PhiList(lq, (long)(v % Q), Math.Min(Mmax, 80));
      foreach (int M in new[] { 10, 20, 40, 80 }) if (M <= Mmax) { double L = KappaM(Pq, M) - 1; double bnd = Math.PI * Math.PI * Q * (double)Q / (4.0 * M * M); worstQ = Math.Max(worstQ, L / bnd); }
    }
    Console.WriteLine(string.Format(CI, " max L_Q / (pi^2 Q^2 / 4M^2) = {0:F6}", worstQ));
  }

  static BigInteger Gcd(BigInteger a, BigInteger b) => BigInteger.GreatestCommonDivisor(a, b);
  static string Sci(BigInteger num, BigInteger den) {
    double lg = BigInteger.Log10(num) - BigInteger.Log10(den); double e = Math.Floor(lg); return string.Format(CI, "{0:F11}e{1}", Math.Pow(10, lg - e), e);
  }
  static void Cert() {
    var cases = new (int D, int s, int t, int a, int[] I)[] { (100, 9, 12, 14, new[] { 9, 10, 11, 12 }), (360, 13, 17, 14, new[] { 16, 17 }), (1000, 13, 17, 16, new[] { 16, 17 }) };
    foreach (var c in cases) {
      long Q = (long)Pow(3, c.a); BigInteger v = Pow(2, c.t * c.t), u = Pow(3, c.s * c.s);
      bool hyp = v >= 20 * c.D * u && (BigInteger)c.D * c.D * v < Pow(3, (c.s + 1) * (c.s + 1)) && (BigInteger)c.D * c.D * v < Pow(2, (c.t + 1) * (c.t + 1));
      double expo = (Math.Log(c.D) + c.t * c.t * Math.Log(2)) / (Math.Log(c.D) * Math.Log(c.D));
      var cnt = new long[Q]; cnt[0] = 1; BigInteger N = 1; var ord = new long[Q];
      foreach (int j in c.I) {
        long J = (long)(Pow(2, 2 * j - 1) / c.D), len = 2 * J + 1; N *= len;
        long w = (long)(Pow(2, (j - 1) * (j - 1)) % Q);
        for (long i = 0, x = 0; i < Q; i++) { ord[i] = cnt[x]; x += w; if (x >= Q) x -= Q; }
        long full = len / Q, rest = len % Q; long all = 0; foreach (var y in ord) all += y;
        long start = ((-J) % Q + Q) % Q; long win = 0; for (long k = 0; k < rest; k++) win += ord[(start + k) % Q];
        var res = cnt;
        for (long i = 0, x = 0; i < Q; i++) { res[x] = checked(full * all + win); win += ord[(start + i + rest) % Q] - ord[(start + i) % Q]; x += w; if (x >= Q) x -= Q; }
        // res is cnt
      }
      long vm = (long)(v % Q);
      var b = ord; for (long i = 0, x = 0; i < Q; i++) { b[i] = cnt[x]; x += vm; if (x >= Q) x -= Q; }
      // T = sum_i b_i sum_{|m|<D} (D-|m|)^2 b_{i+m}, by the second difference of the weights
      int D = c.D; long B(long i) => b[((i % Q) + Q) % Q];
      Int128 Direct(long i) { Int128 s = 0; for (int m = 1 - D; m <= D - 1; m++) s += (Int128)(long)(D - Math.Abs(m)) * (D - Math.Abs(m)) * B(i + m); return s; }
      Int128 prev = Direct(-1), cur = Direct(0);
      Int128 S = 0; for (int m = 1 - D; m <= D - 1; m++) S += B(m);
      BigInteger T = 0; Int128 chunk = 0;
      for (long i = 0; i < Q; i++) {
        chunk += (Int128)b[i] * cur; if ((i & 1023) == 1023 || i == Q - 1) { T += (BigInteger)chunk; chunk = 0; }
        Int128 next = 2 * cur - prev + 2 * S - (Int128)4 * D * B(i) + B(i - D) + B(i + D);
        S += B(i + D) - B(i - D + 1);
        prev = cur; cur = next;
      }
      if (cur != Direct(0)) throw new Exception("recurrence does not close");
      BigInteger k0 = (BigInteger)D * (2 * (BigInteger)D * D + 1) / 3;
      BigInteger num = Q * T - k0 * N * N, den = k0 * N * N; var g = Gcd(num, den); num /= g; den /= g;
      Console.WriteLine(string.Format(CI, "D={0} (s,t)=({1},{2}) Q=3^{3} hypotheses={4} lnX/ln^2D={5:F9} N={6} L_Q <= {7}/{8} = {9}", c.D, c.s, c.t, c.a, hyp, expo, N, num, den, Sci(num, den)));
    }
    // elementary bound (LC) at D = 100, (s,t) = (9,12)
    Console.Write("LC bound, D=100 t=12:");
    for (int e = 4; e <= 12; e++) {
      BigInteger Q = Pow(3, e); BigInteger bn = 0, bd = 1; bool first = true;
      for (int j = 1; j <= 12; j++) {
        BigInteger N = 2 * (Pow(2, 2 * j - 1) / 100) + 1, r = N % Q, num = r * (Q - r), den = N * N;
        for (int i = 1; i <= 12; i++) { if (i == j) continue; BigInteger Ni = 2 * (Pow(2, 2 * i - 1) / 100) + 1; if (Q * Q < 4 * Ni * Ni) { num *= Q * Q; den *= 4 * Ni * Ni; } }
        if (first || num * bd < bn * den) { bn = num; bd = den; first = false; }
      }
      Console.Write(" 3^" + e + ": " + (bn == 0 ? "0" : Sci(bn, bd)) + ";");
    }
    Console.WriteLine();
  }

  static void QP(string[] a) {
    int q = int.Parse(a[1]), D = int.Parse(a[2]), s = int.Parse(a[3]);
    var dig = Digits(q, D, s); var Y = Set(dig);
    double worst = 0;
    for (int e = 1; e <= s * s; e++) {
      long mod = (long)Pow(q, e); int k = (int)Math.Ceiling(Math.Sqrt(e) - 1e-12);
      long w = (long)Pow(q, (k - 1) * (k - 1)), d = (long)Pow(q, e - (k - 1) * (k - 1)), N = 2 * dig[k - 1].J + 1, r = N % d;
      double H = 1; for (int j = 0; j < k - 1; j++) H *= 2 * dig[j].J + 1;
      double formula = w / H * (1 + (double)r * (d - r) / ((double)N * N));
      var cnt = new Dictionary<long, long>(); foreach (var y in Y) { long x = ((y % mod) + mod) % mod; cnt[x] = cnt.GetValueOrDefault(x) + 1; }
      double direct = 0; foreach (var c in cnt.Values) direct += (double)c * c; direct *= (double)mod / ((double)Y.Count * Y.Count);
      worst = Math.Max(worst, Math.Abs(formula / direct - 1));
    }
    Console.WriteLine($"qp q={q} D={D} s={s} |Y|={Y.Count} layers={s * s} max relative difference={worst.ToString("E2", CI)}");
  }

  static void Main(string[] a) {
    if (a[0] == "energy") EnergyMode(a);
    else if (a[0] == "kappa") KappaMode(a);
    else if (a[0] == "cert") Cert();
    else if (a[0] == "qp") QP(a);
  }
}

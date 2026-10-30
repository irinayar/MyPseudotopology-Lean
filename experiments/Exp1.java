public class Exp1 {
  static double pk(long k) {
    double best = 0;
    for (int ell = 2; ell <= 3; ell++) {
      long c = 1;
      for (int n = 0; ; n++) {
        long r = k % c;
        double v = Math.min(r, c - r) / (double) c;
        if (v > best) best = v;
        if (c > 2 * k) break;
        long nn = (long) (n + 1) * (n + 1);
        long cc = 1; for (long i = 0; i < nn; i++) cc *= ell;
        c = cc;
      }
    }
    return best;
  }
  public static void main(String[] a) {
    double[] ds = {0.4, 0.3, 0.2, 0.1, 0.05};
    long[] Ns = {1000L, 10000L, 100000L, 1000000L, 10000000L, 100000000L};
    long[] cnt = new long[ds.length];
    int j = 0;
    long maxN = Ns[Ns.length - 1];
    System.out.println("N, delta, count(B_delta ∩ [0,N]), density, d_N(delta), heuristic (2delta)^d, proven bound L^-d");
    for (long k = 0; k <= maxN; k++) {
      double p = pk(k);
      for (int i = 0; i < ds.length; i++) if (p < ds[i]) cnt[i]++;
      if (k == Ns[j]) {
        for (int i = 0; i < ds.length; i++) {
          double N = k, d = ds[i];
          long dN = 2 + (long) Math.floor(Math.sqrt(Math.log(N / d) / Math.log(2))) + (long) Math.floor(Math.sqrt(Math.log(N / d) / Math.log(3)));
          long L = (long) Math.floor(1 / d) + 1;
          double dens = cnt[i] / (N + 1);
          System.out.printf("%d, %.2f, %d, %.5f, %d, %.3e, %.3e%n", k, d, cnt[i], dens, dN, Math.pow(2 * d, dN), Math.pow(L, -dN));
        }
        j++;
        if (j == Ns.length) break;
      }
    }
  }
}

public class Exp4 {
  static long dN(double N, double d) {
    return 2 + (long) Math.floor(Math.sqrt(Math.log(N / d) / Math.log(2))) + (long) Math.floor(Math.sqrt(Math.log(N / d) / Math.log(3)));
  }
  public static void main(String[] a) {
    System.out.println("delta, L, first N with 400*L^d < 100*N (covering bound non-vacuous), first N with L^-d >= N^-1/2 (density >= 1/sqrt N)");
    for (double d : new double[]{0.4, 0.3, 0.2, 0.1, 0.05}) {
      long L = (long) Math.floor(1 / d) + 1;
      double n1 = -1, n2 = -1;
      for (double e = 2; e <= 400; e += 0.05) {
        double N = Math.pow(10, e);
        long dd = dN(N, d);
        double logL = Math.log10(L);
        if (n1 < 0 && Math.log10(400) + dd * logL < 2 + e) n1 = e;
        if (n2 < 0 && -dd * logL >= -0.5 * e) n2 = e;
        if (n1 > 0 && n2 > 0) break;
      }
      System.out.printf("%.2f, %d, 10^%.1f, 10^%.1f%n", d, L, n1, n2);
    }
  }
}

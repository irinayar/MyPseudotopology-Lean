import java.util.*;
public class Exp1b {
  public static void main(String[] a) {
    double[] ds = {0.1, 0.05};
    long maxN = 100000000L;
    for (double d : ds) {
      List<Long> L = new ArrayList<>();
      for (long k = 0; k <= maxN; k++) if (Exp1.pk(k) < d) L.add(k);
      System.out.println("delta=" + d + " count=" + L.size());
      System.out.println(L.size() > 120 ? L.subList(0, 40) + " ... " + L.subList(L.size()-10, L.size()) : L);
    }
  }
}

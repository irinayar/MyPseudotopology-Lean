/** Exp11: strictly lacunary integers for both chains: g >= 1 such that for l in {2,3} and every n >= 1,
 *  l^(n^2) divides g, or g <= eps * l^(n^2)  (eps = a/b, exact test: b*g <= a*q). Lists all such g up to K. */
public class Exp11 {
    static boolean ok(long g, long base, long a, long b) {
        for (long n = 1; ; n++) {
            long q = 1; for (long i = 0; i < n * n; i++) q = Math.multiplyExact(q, base);
            boolean div = (g % q == 0);
            boolean negl = Math.multiplyExact(b, g) <= Math.multiplyExact(a, q);
            if (!div && !negl) return false;
            if (negl) return true;      // q large: every later scale is also negligible
        }
    }
    public static void main(String[] args) {
        long K = Long.parseLong(args[0]), a = Long.parseLong(args[1]), b = Long.parseLong(args[2]);
        long count = 0, max = 0; StringBuilder top = new StringBuilder();
        for (long g = 1; g <= K; g++) if (ok(g, 2, a, b) && ok(g, 3, a, b)) { count++; max = g; if (count <= 30) top.append(g + " "); }
        System.out.println("eps=" + a + "/" + b + "  count=" + count + "  largest=" + max + "  first: " + top);
    }
}

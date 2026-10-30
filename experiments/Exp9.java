import java.math.BigInteger;
/** Exp9: exact value of P(k) = max over l in {2,3} of sup_n ||k/l^(n^2)|| as a reduced fraction (scales until l^(n^2) > 10k). */
public class Exp9 {
    public static void main(String[] args) {
        for (String arg : args) {
            long k = Long.parseLong(arg);
            BigInteger bestNum = BigInteger.ZERO, bestDen = BigInteger.ONE; String where = "";
            for (int l : new int[]{2, 3}) {
                for (int n = 1; ; n++) {
                    BigInteger q = BigInteger.valueOf(l).pow(n * n), K = BigInteger.valueOf(k);
                    BigInteger r = K.mod(q), s = r.min(q.subtract(r));
                    if (s.multiply(bestDen).compareTo(bestNum.multiply(q)) > 0) { bestNum = s; bestDen = q; where = "base " + l + ", n=" + n; }
                    if (q.compareTo(K.multiply(BigInteger.TEN)) > 0) break;
                }
            }
            BigInteger g = bestNum.gcd(bestDen);
            System.out.println("P(" + k + ") = " + bestNum.divide(g) + "/" + bestDen.divide(g) + "  (attained at " + where + ")  < 1/10: " + (bestNum.multiply(BigInteger.TEN).compareTo(bestDen) < 0));
        }
    }
}

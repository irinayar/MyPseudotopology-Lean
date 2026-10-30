import java.util.*;

/** Exp10: "rays" and "complete intervals" inside B_delta for S={2,3} (exact integer test, delta=a/b).
 *  For c in B_delta (multiples of 6 up to K): R(c) = max R with k*c in B_delta for all 1<=k<=R (cap CAP).
 *  Also, for each c, the largest q such that q*c in B_delta and k*c in B_delta for all 1<=k<=q (complete interval ending at a multiple).
 *  This tests whether Außenhofer–de la Barrera Mayoral's Proposition 4.1 pattern (k*b_j in V for |k|<=b_{j+1}/(8m b_j)) can occur. */
public class Exp10 {
    static boolean small(long k, long base, long a, long b) {
        for (long n = 1; ; n++) {
            long e = n * n; long q = 1;
            for (long i = 0; i < e; i++) q = Math.multiplyExact(q, base);
            long r = k % q; long s = Math.min(r, q - r);
            if (Math.multiplyExact(b, s) >= Math.multiplyExact(a, q)) return false;
            if (q > 2 * k) return true;
        }
    }
    static boolean inB(long k, long a, long b) { return small(k, 2, a, b) && small(k, 3, a, b); }
    public static void main(String[] args) {
        long K = Long.parseLong(args[0]), a = Long.parseLong(args[1]), b = Long.parseLong(args[2]);
        int CAP = Integer.parseInt(args[3]);
        List<Long> els = new ArrayList<>();
        for (long k = 6; k <= K; k += 6) if (inB(k, a, b)) els.add(k);
        System.out.println("delta=" + a + "/" + b + " K=" + K + " |B|=" + els.size());
        int[] hist = new int[CAP + 2]; long bestC = 0; int bestR = 0;
        for (long c : els) {
            int R = 1;
            while (R < CAP && c * (R + 1) <= K && inB(c * (R + 1), a, b)) R++;
            hist[R]++;
            if (R > bestR) { bestR = R; bestC = c; }
        }
        StringBuilder sb = new StringBuilder("R(c) histogram (R: count): ");
        for (int r = 1; r <= Math.min(CAP, 12); r++) sb.append(r + ":" + hist[r] + " ");
        System.out.println(sb);
        System.out.println("largest R(c) = " + bestR + " at c=" + bestC);
        // complete intervals: for each c, scan q = 2.. while all k*c (k<=q) in B; record maximum q with q*c in B
        int bestQ = 1; long bestQc = 0;
        for (long c : els) {
            int q = 1;
            while (q < CAP && c * (q + 1) <= K && inB(c * (q + 1), a, b)) q++;
            if (q > bestQ) { bestQ = q; bestQc = c; }
        }
        System.out.println("complete multiples chain c,2c,...,qc all in B_delta: max q = " + bestQ + " at c=" + bestQc);
    }
}

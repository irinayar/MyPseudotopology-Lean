// Independent brute-force check (C#, double precision) of the exhaustive enumeration for ||h||_inf <= H:
// for every (h1, h2) in [-H, H]^2 put h0 = nearest integer to -(h1 alpha + h2 beta) and report every h = (h0, h1, h2) with
// 1 <= ||h||_inf <= H and |h.v| ||h||_inf^2 <= THR (THR = 0.6 > 1/4 leaves a margin for the rounding error of doubles; the candidates are
// then tested exactly in Python).  alpha = sqrt(log2/log3), beta = sqrt(log2/log5).
using System;
using System.Collections.Generic;
public static class BF {
    public static string Run(int H, double thr) {
        double L2 = Math.Log(2.0), L3 = Math.Log(3.0), L5 = Math.Log(5.0);
        double al = Math.Sqrt(L2 / L3), be = Math.Sqrt(L2 / L5);
        var sb = new System.Text.StringBuilder();
        long cnt = 0;
        for (int h1 = -H; h1 <= H; h1++) {
            double a1 = h1 * al;
            for (int h2 = -H; h2 <= H; h2++) {
                double s = a1 + h2 * be;
                double r = Math.Round(s);
                double d = Math.Abs(s - r);
                int h0 = (int)(-r);
                int m = Math.Max(Math.Abs(h0), Math.Max(Math.Abs(h1), Math.Abs(h2)));
                if (m < 1 || m > H) continue;
                if (d * (double)m * (double)m <= thr) { sb.Append(h0).Append(' ').Append(h1).Append(' ').Append(h2).Append('\n'); cnt++; }
            }
        }
        return sb.ToString();
    }
}

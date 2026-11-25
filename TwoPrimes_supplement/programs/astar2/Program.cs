using System;
using System.Collections.Generic;
using System.Numerics;
using System.Text;

// astar2: level-pair screen with the common-height range (corrected version of the scan).
// For a pair (N,M): s<=B the two top steps; at a height X the smaller step has range J_small=floor(X/s);
// the best case for the screen is the largest admissible X: X_max(L)=min(e^{x2 L^2}, min(p^{N^2},q^{M^2})/D), so
// D*J_small ~ Q_eff(L)=min(D e^{x2 L^2}, min(p^{N^2},q^{M^2}))/s.
// A rational a/b (a>=b coprime, a<=D/2) is dangerous if Q_eff |bB-as| < K a (s+B).  Convergents of B/s suffice when
// 2K (D/2)^2 (s+B) <= Q_eff B (Legendre); otherwise the pair is "unverified" at that L.
// usage: astar2 p q Nmax K x0off x2off [Lstep] [Nmin]
class P
{
    static double Ln(BigInteger x)
    {
        if (x.IsZero) return double.NegativeInfinity;
        long bits = (long)x.GetBitLength();
        if (bits < 1000) return Math.Log((double)x);
        int sh = (int)(bits - 900);
        return Math.Log((double)(x >> sh)) + sh * Math.Log(2.0);
    }
    static void Main(string[] a)
    {
        int p = int.Parse(a[0]), q = int.Parse(a[1]); int Nmax = int.Parse(a[2]);
        int K = int.Parse(a[3]); double x0off = double.Parse(a[4]), x2off = double.Parse(a[5]);
        double Lstep = a.Length > 6 ? double.Parse(a[6]) : 0.1; int Nmin = a.Length > 7 ? int.Parse(a[7]) : 1;
        double al = Math.Log(p), be = Math.Log(q);
        double AS = 1 / Math.Sqrt(al) + 1 / Math.Sqrt(be), c = 0.25 * (1 / al + 1 / be);
        double xS = Math.Pow((AS + Math.Sqrt(AS * AS - 4 * c)) / 2, 2);
        double x0 = xS + x0off, x2 = xS + x2off;
        Console.WriteLine("pair " + p + "," + q + " xS=" + xS.ToString("F4") + " window [" + x0.ToString("F3") + "," + x2.ToString("F3") + "] K=" + K + " Nmax=" + Nmax);
        double Lstart = 30, Lcap = Nmax * Math.Sqrt(al / (x2 + 0.2)) * 0.98;
        int G = (int)Math.Floor((Lcap - Lstart) / Lstep) + 1;
        bool[] cov = new bool[G]; bool[] covAny = new bool[G];
        int unverified = 0, usableCount = 0, dangerousCount = 0, feasible = 0;
        double minMargin = 1e9; string minTxt = "";
        for (int N = Nmin; N <= Nmax; N++)
        {
            int M0 = (int)Math.Floor(N * Math.Sqrt(al / be));
            while ((double)(M0 + 1) * (M0 + 1) * be <= (double)N * N * al) M0++;
            while (M0 > 1 && (double)M0 * M0 * be > (double)N * N * al) M0--;
            for (int M = Math.Max(1, M0); M <= M0 + 1; M++)
            {
                if (M < 2 || N < 2) continue;
                double lnu = (double)(N - 1) * (N - 1) * al, lnv = (double)(M - 1) * (M - 1) * be;
                double hi = Math.Min((double)N * N * al, (double)M * M * be), lo = Math.Max(lnu, lnv);
                // admissible L range on the grid
                List<int> Ls = new List<int>(); 
                for (int g = 0; g < G; g++) { double L = Lstart + g * Lstep; double a1 = Math.Max(lo + L + 1, x0 * L * L), b1 = Math.Min(hi - L - 1, x2 * L * L); if (a1 <= b1) Ls.Add(g); }
                if (Ls.Count == 0) continue; feasible++;
                BigInteger u = BigInteger.Pow(p, (N - 1) * (N - 1)), v = BigInteger.Pow(q, (M - 1) * (M - 1));
                BigInteger s, B; if (u <= v) { s = u; B = v; } else { s = v; B = u; }
                double lns = Ln(s), lnB = Ln(B), lnsB = Ln(s + B);
                double lnCap = hi; // min(p^{N^2}, q^{M^2}) in logs
                double maxL = Lstart + Ls[Ls.Count - 1] * Lstep; double capA = maxL - Math.Log(2.0) + 1;
                // convergents with ln a <= maxL - ln 2 + 1
                var lna = new List<double>(); var gk = new List<double>();
                BigInteger num = B, den = s, h1 = 1, h2 = 0, k1 = 0, k2 = 1;
                while (!den.IsZero)
                {
                    BigInteger r; BigInteger aq = BigInteger.DivRem(num, den, out r);
                    BigInteger h = aq * h1 + h2, k = aq * k1 + k2; h2 = h1; h1 = h; k2 = k1; k1 = k;
                    double lh = Ln(h); if (lh > capA) break;
                    BigInteger diff = BigInteger.Abs(k * B - h * s);
                    double gval = diff.IsZero ? double.PositiveInfinity : Math.Log(K) + lh + lnsB - Ln(diff);
                    lna.Add(lh); gk.Add(gval); num = den; den = r;
                }
                foreach (int g in Ls)
                {
                    double L = Lstart + g * Lstep; double lnD = L; double lnLim = L - Math.Log(2.0);
                    double lnQeff = Math.Min(lnD + x2 * L * L, lnCap) - lns;
                    double Gmax = double.NegativeInfinity; for (int i = 0; i < lna.Count && lna[i] <= lnLim; i++) if (gk[i] > Gmax) Gmax = gk[i];
                    bool danger = lnQeff < Gmax;
                    double lnLeg = Math.Log(2.0 * K) + 2 * lnLim + lnsB - lnB; bool legOK = lnLeg <= lnQeff;
                    covAny[g] = true;
                    if (!danger && legOK) { cov[g] = true; usableCount++; double mg = lnQeff - lnLeg; if (mg < minMargin) { minMargin = mg; minTxt = "N=" + N + " M=" + M + " L=" + L.ToString("F1"); } }
                    else if (danger) dangerousCount++; else unverified++;
                }
            }
        }
        var sb = new StringBuilder(); bool inGap = false; double gs = 0; int ngap = 0;
        for (int g = 0; g < G; g++)
        {
            double L = Lstart + g * Lstep;
            if (!cov[g] && !inGap) { inGap = true; gs = L; }
            if (cov[g] && inGap) { inGap = false; sb.Append("[" + gs.ToString("F1") + "," + (L - Lstep).ToString("F1") + "] "); ngap++; }
        }
        if (inGap) { sb.Append("[" + gs.ToString("F1") + "," + (Lstart + (G - 1) * Lstep).ToString("F1") + "] "); ngap++; }
        Console.WriteLine("feasible pairs " + feasible + "; (pair,L) usable " + usableCount + ", dangerous " + dangerousCount + ", unverified (Legendre fails) " + unverified);
        Console.WriteLine("L grid " + Lstart + ".." + Lcap.ToString("F1") + " step " + Lstep + ": uncovered intervals " + ngap + " " + sb.ToString());
        Console.WriteLine("smallest Legendre margin (ln Q_eff - ln bound) among usable: " + minMargin.ToString("F2") + " (" + minTxt + ")");
    }
}

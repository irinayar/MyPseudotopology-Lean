using System;
using System.Collections.Generic;
using System.IO;
using System.Numerics;
using System.Text;

// Reproducible window / forced-free-digit statistics for the note "From Claude at 2026-10-27 12:54".
// Forced digits: for scale p^(n*n), ||(x)/p^(n*n)|| < 1/D forces the top t digits of x mod p^(n*n)
// (digit positions n*n-t .. n*n-1) to be all 0 or all p-1, where t = floor(log_p D).
public static class WinStats {
  static int Digits(BigInteger v, int p) { int c = 0; while (!v.IsZero) { v /= p; c++; } return c; }
  static int DigitAt(BigInteger v, int p, int pos) { return (int)BigInteger.Remainder(v / BigInteger.Pow(p, pos), p); }
  static int Tlen(int D, int p) { int t = 0; BigInteger q = 1; while (q * p <= D) { q *= p; t++; } return t; }
  // returns "forced/total/free" and fills window types per scale
  public static string Stats(BigInteger x, int p, int D, List<string> types) {
    int L = Digits(x, p); int t = Tlen(D, p);
    var forced = new HashSet<int>();
    for (int n = 1; n * n - t < L + 0; n++) {
      int top = n * n - 1, bot = n * n - t; if (bot < 0) bot = 0;
      for (int j = bot; j <= top && j < L; j++) forced.Add(j);
      if (types != null && n * n <= L) {
        int d = DigitAt(x, p, top);   // top digit of the residue mod p^(n*n)
        types.Add(n + ":" + (d == 0 ? "L" : "H"));
      }
    }
    return forced.Count + "/" + L + "/" + (L - forced.Count);
  }
  static string Split(BigInteger x, int p, int D, int nmax) {
    // count low / high at scale p^(nmax*nmax)
    int d = DigitAt(x, p, nmax * nmax - 1); return d == 0 ? "L" : (d == p - 1 ? "H" : "?");
  }
  public static void Main(string[] args) {
    string dir = args[0];
    var sb = new StringBuilder();
    var ws = new List<KeyValuePair<int, BigInteger>>();
    ws.Add(new KeyValuePair<int, BigInteger>(100, BigInteger.Parse(JumpJA.Run(100, 100000000).Split('=')[2].Split(' ')[0])));
    ws.Add(new KeyValuePair<int, BigInteger>(200, BigInteger.Parse(JumpJA.Run(200, 100000000).Split('=')[2].Split(' ')[0])));
    ws.Add(new KeyValuePair<int, BigInteger>(500, BigInteger.Parse("6207496413615241618428036085462998253569")));
    foreach (var w in ws) {
      sb.AppendLine("D=" + w.Key + " k=" + w.Value);
      sb.AppendLine("  binary k-1: forced/total/free = " + Stats(w.Value - 1, 2, w.Key, null) + "  (t=" + Tlen(w.Key, 2) + " bits per window)");
      sb.AppendLine("  ternary k:  forced/total/free = " + Stats(w.Value, 3, w.Key, null) + "  (t=" + Tlen(w.Key, 3) + " trits per window)");
      int v2 = 0; BigInteger a = w.Value - 1; while (a.IsEven) { a /= 2; v2++; }
      int v3 = 0; BigInteger b = w.Value; while (BigInteger.Remainder(b, 3).IsZero) { b /= 3; v3++; }
      sb.AppendLine("  v2(k-1)=" + v2 + " v3(k)=" + v3);
    }
    foreach (string nm in new string[] { "surv_D50.txt", "surv_D60.txt" }) {
      var ks = new List<BigInteger>();
      foreach (string ln in File.ReadAllLines(Path.Combine(dir, nm))) if (ln.Trim().Length > 0) ks.Add(BigInteger.Parse(ln.Trim()));
      var binSeen = new HashSet<string>(); var terSeen = new HashSet<string>();
      int bl = 0, bh = 0, tl = 0, th = 0, bo = 0, to = 0;
      BigInteger mb = BigInteger.Pow(2, 25), mt = BigInteger.Pow(3, 16);
      foreach (BigInteger k in ks) {
        BigInteger rb = BigInteger.Remainder(k - 1, mb), rt = BigInteger.Remainder(k, mt);
        if (binSeen.Add(rb.ToString())) { string c = Split(rb, 2, 0, 5); if (c == "L") bl++; else if (c == "H") bh++; else bo++; }
        if (terSeen.Add(rt.ToString())) { string c = Split(rt, 3, 0, 4); if (c == "L") tl++; else if (c == "H") th++; else to++; }
      }
      sb.AppendLine(nm + ": survivors=" + ks.Count + "; distinct binary prefixes mod 2^25 of k-1: " + binSeen.Count + " (top bit of scale 2^25: low " + bl + ", high " + bh + ", other " + bo + "); distinct ternary prefixes mod 3^16: " + terSeen.Count + " (top trit of scale 3^16: low " + tl + ", high " + th + ", other " + to + ")");
      int rawL = 0, rawH = 0;
      foreach (BigInteger k in ks) { string c = Split(BigInteger.Remainder(k - 1, mb), 2, 0, 5); if (c == "L") rawL++; else rawH++; }
      sb.AppendLine("   raw (not de-duplicated) binary n=5: low " + rawL + ", high " + rawH);
    }
    Console.Write(sb.ToString());
  }
}

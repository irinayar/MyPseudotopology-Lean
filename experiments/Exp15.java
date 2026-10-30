import java.io.*; import java.math.*; import java.util.*;
/** Exp15: by decade of k, among the exact-E list (gens_K1e10.csv) with E<level, mean of ||kx|| and fraction with ||kx||>0.05.
 *  Tests the weak form ||h_i x|| -/-> 0 along generators of fixed profile size with growing size (centres). */
public class Exp15 {
  static final MathContext MC=new MathContext(80);
  static BigDecimal nrm(BigDecimal v){ BigDecimal f=v.subtract(new BigDecimal(v.setScale(0,RoundingMode.FLOOR).toBigInteger())); BigDecimal g=BigDecimal.ONE.subtract(f); return f.compareTo(g)<0?f:g; }
  public static void main(String[] a) throws Exception {
    double lv=Double.parseDouble(a[1]);
    ArrayList<Long> K=new ArrayList<>(); try(BufferedReader br=new BufferedReader(new FileReader(a[0]))){ br.readLine(); String ln; while((ln=br.readLine())!=null){ String[] f=ln.split(","); if(Double.parseDouble(f[3])<lv) K.add(Long.parseLong(f[0])); } }
    String[] nm={"sqrt2-1","phi-1","pi-3","e-2","1/5","1/7","1/11","1/9(H)","1/4(H)"};
    BigDecimal[] xs={new BigDecimal(2).sqrt(MC).subtract(BigDecimal.ONE),BigDecimal.ONE.add(new BigDecimal(5).sqrt(MC)).divide(new BigDecimal(2),MC).subtract(BigDecimal.ONE),
      new BigDecimal("0.14159265358979323846264338327950288419716939937510582097494459230781640628620899"),new BigDecimal("0.71828182845904523536028747135266249775724709369995957496696762772407663035354759"),
      new BigDecimal(1).divide(new BigDecimal(5),MC),new BigDecimal(1).divide(new BigDecimal(7),MC),new BigDecimal(1).divide(new BigDecimal(11),MC),new BigDecimal(1).divide(new BigDecimal(9),MC),new BigDecimal("0.25")};
    System.out.println("E<"+lv+": "+K.size()+" generators; per decade [10^d,10^(d+1)): count | mean ||kx|| | frac>0.05");
    for(int d=5; d<=9; d++){ long lo=(long)Math.pow(10,d), hi=lo*10; ArrayList<Long> S=new ArrayList<>(); for(long k:K) if(k>=lo&&k<hi) S.add(k);
      StringBuilder sb=new StringBuilder("decade "+d+" n="+S.size()+":");
      for(int i=0;i<xs.length;i++){ double sum=0; int big=0; for(long k:S){ double v=nrm(new BigDecimal(k).multiply(xs[i],MC)).doubleValue(); sum+=v; if(v>0.05)big++; } sb.append(String.format("  %s %.3f/%.2f",nm[i],S.isEmpty()?0:sum/S.size(),S.isEmpty()?0:(double)big/S.size())); }
      System.out.println(sb); }
  }
}

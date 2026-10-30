import java.io.*; import java.util.*;
/** Exp16: survivors of the Lipschitz constraints. E_C = { x : ||kx|| <= C P(k) for all k }.
 *  Intersect, for every listed k (P<0.12, k<=1e10, increasing), the set {x in [0,1): ||kx|| <= C P(k)}; report the number of
 *  surviving intervals and their rational approximations. Usage: java Exp16 gens.csv C */
public class Exp16 {
  static double pk(long k){ double m=0; for(long base: new long[]{2,3}) for(long n=1;;n++){ long q=1; boolean big=false; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/base){big=true;break;} q*=base; } double t=0; if(!big){ long r=k%q; long s=Math.min(r,q-r); t=(double)s/(double)q;} if(t>m)m=t; if(big||q>2*k)break; } return m; }
  static String rat(double x, int maxq){ // best rational approx with denominator <= maxq by continued fraction
    long h0=0,h1=1,k0=1,k1=0; double y=x; long a=(long)Math.floor(y); h0=a; k0=1; long hp=1,kp=0; double f=y-a; long hh=a,kk=1;
    long H1=1,K1=0,H2=a,K2=1; for(int i=0;i<30;i++){ if(f<1e-12)break; y=1/f; long b=(long)Math.floor(y); f=y-b; long H=b*H2+H1,K=b*K2+K1; if(K>maxq)break; H1=H2;K1=K2;H2=H;K2=K; }
    return H2+"/"+K2; }
  public static void main(String[] a) throws Exception {
    double C=Double.parseDouble(a[1]);
    ArrayList<Long> K=new ArrayList<>(); try(BufferedReader br=new BufferedReader(new FileReader(a[0]))){ br.readLine(); String ln; while((ln=br.readLine())!=null) K.add(Long.parseLong(ln.split(",")[0])); }
    Collections.sort(K);
    ArrayList<double[]> cur=new ArrayList<>(); cur.add(new double[]{0,1});
    long[] marks={10000,100000,1000000,10000000,100000000,1000000000,10000000000L}; int mi=0;
    for(long k: K){
      double c=C*pk(k); if(c>=0.5) continue;
      ArrayList<double[]> nxt=new ArrayList<>();
      for(double[] iv: cur){ long j0=(long)Math.floor(k*iv[0]-c), j1=(long)Math.ceil(k*iv[1]+c);
        for(long j=j0;j<=j1;j++){ double lo=Math.max(iv[0],(j-c)/k), hi=Math.min(iv[1],(j+c)/k); if(lo<=hi) nxt.add(new double[]{lo,hi}); } }
      // merge touching
      nxt.sort((p,q)->Double.compare(p[0],q[0])); ArrayList<double[]> m=new ArrayList<>(); for(double[] iv: nxt){ if(!m.isEmpty() && iv[0]<=m.get(m.size()-1)[1]+1e-15) m.get(m.size()-1)[1]=Math.max(m.get(m.size()-1)[1],iv[1]); else m.add(iv); }
      cur=m;
      while(mi<marks.length && k>=marks[mi]){ double meas=0; for(double[] iv:cur) meas+=iv[1]-iv[0]; System.out.printf("C=%.0f after k<=%d: intervals=%d measure=%.3e%n",C,marks[mi],cur.size(),meas); mi++; }
      if(cur.size()>2000000){ System.out.println("too many intervals"); return; }
    }
    double meas=0; for(double[] iv:cur) meas+=iv[1]-iv[0];
    System.out.printf("FINAL C=%.0f intervals=%d measure=%.3e%n",C,cur.size(),meas);
    int shown=0; for(double[] iv: cur){ double mid=(iv[0]+iv[1])/2; if(shown<60){ System.out.printf("  [%.10f, %.10f] width %.2e ~ %s%n",iv[0],iv[1],iv[1]-iv[0],rat(mid,5000)); shown++; } }
  }
}

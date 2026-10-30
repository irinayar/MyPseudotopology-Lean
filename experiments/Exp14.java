import java.io.*; import java.util.*;
/** Exp14: for each modulus q, minimum of P(k) over listed k (multiples of 6, P<0.12, k<=1e10) with q not dividing k.
 *  If q Z is P-open then this minimum is bounded below by a positive delta(q) for ALL k; if not, it should keep decreasing as K grows. */
public class Exp14 {
  static double pk(long k){ double m=0; for(long base: new long[]{2,3}) for(long n=1;;n++){ long q=1; boolean big=false; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/base){big=true;break;} q*=base; } double t=0; if(!big){ long r=k%q; long s=Math.min(r,q-r); t=(double)s/(double)q;} if(t>m)m=t; if(big||q>2*k)break; } return m; }
  public static void main(String[] a) throws Exception {
    ArrayList<Long> K=new ArrayList<>(); ArrayList<Double> P=new ArrayList<>();
    try(BufferedReader br=new BufferedReader(new FileReader(a[0]))){ br.readLine(); String ln; while((ln=br.readLine())!=null){ long k=Long.parseLong(ln.split(",")[0]); K.add(k); P.add(pk(k)); } }
    int N=K.size(); Integer[] idx=new Integer[N]; for(int i=0;i<N;i++)idx[i]=i; Arrays.sort(idx,(x,y)->Long.compare(K.get(x),K.get(y)));
    long[] qs={4,5,7,8,9,10,11,12,13,16,17,18,19,23,25,27,29,31,32,37,41,43,64,81,97};
    long[] cut={1000000L,10000000L,100000000L,1000000000L,10000000000L};
    System.out.println("N="+N+"  columns: q | min P(k) over {q does not divide k, k<=cut} for cut=1e6,1e7,1e8,1e9,1e10");
    for(long q: qs){ StringBuilder sb=new StringBuilder(String.format("q=%-3d |",q)); for(long c: cut){ double m=9; for(int i=0;i<N;i++){ long k=K.get(i); if(k>c)continue; if(k%q!=0 && P.get(i)<m) m=P.get(i);} sb.append(String.format(" %.5f",m)); } System.out.println(sb); }
    double all[]=new double[cut.length]; StringBuilder sb=new StringBuilder("all   |"); for(long c: cut){ double m=9; for(int i=0;i<N;i++) if(K.get(i)<=c && P.get(i)<m) m=P.get(i); sb.append(String.format(" %.5f",m)); } System.out.println(sb);
  }
}

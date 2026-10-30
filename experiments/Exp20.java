import java.util.*;
/** Exp20: survival counts A_j(X): number of k in [1,X] passing the first j active constraints, ordered by denominator
 *  (constraints: ||(k-1)/2^(n^2)|| < delta and ||k/3^(m^2)|| < delta, only denominators <= X/delta). Prints ratios A_j/A_{j-1}. */
public class Exp20 {
  static boolean ok(long x, long q, double d){ long r=((x%q)+q)%q; long s=Math.min(r,q-r); return (double)s/(double)q<d; }
  public static void main(String[] a){
    long X=Long.parseLong(a[0]); double d=Double.parseDouble(a[1]);
    ArrayList<long[]> cons=new ArrayList<>(); // {q, base}
    for(long n=1;;n++){ long q=1; boolean big=false; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/2){big=true;break;} q*=2; } if(big||q>X/d)break; cons.add(new long[]{q,2}); }
    for(long m=1;;m++){ long q=1; boolean big=false; for(long i=0;i<m*m;i++){ if(q>Long.MAX_VALUE/3){big=true;break;} q*=3; } if(big||q>X/d)break; cons.add(new long[]{q,3}); }
    cons.sort((u,v)->Long.compare(u[0],v[0]));
    int J=cons.size(); long[] cnt=new long[J+1];
    for(long k=1;k<=X;k++){ int j=0; while(j<J){ long q=cons.get(j)[0]; long base=cons.get(j)[1]; long x=(base==2)?k-1:k; if(!ok(x,q,d))break; j++; } for(int i=0;i<=j;i++) cnt[i]++; }
    System.out.printf("X=%d delta=%.3f active constraints J=%d%n",X,d,J);
    for(int j=1;j<=J;j++) System.out.printf("  j=%d q=%d (base %d): A_j=%d  ratio=%.3f%n",j,cons.get(j-1)[0],cons.get(j-1)[1],cnt[j],cnt[j-1]==0?0.0:(double)cnt[j]/cnt[j-1]);
  }
}

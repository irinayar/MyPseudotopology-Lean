import java.util.*;
/** Exp19: independence check. Count k<=L with P_3(k)<delta and P_2(k-1)<delta, compare with |V||U|/L (and with the shifted
 *  count for several shifts t). */
public class Exp19 {
  static boolean small(long k, long base, double delta){
    for(long n=1;;n++){ long q=1; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/base) return true; q*=base; }
      long r=((k%q)+q)%q; long s=Math.min(r,q-r); if((double)s/(double)q>=delta) return false; if(q>2*Math.abs(k)+2) return true; } }
  public static void main(String[] a){
    long L=Long.parseLong(a[0]); double d=Double.parseDouble(a[1]);
    long cu=0,cv=0; long[] both=new long[8]; int[] ts={1,2,3,5,7,11,13,17};
    for(long k=0;k<=L;k++){
      boolean v=small(k,3,d); boolean u=small(k,2,d); if(u)cu++; if(v)cv++;
      if(v){ for(int i=0;i<ts.length;i++) if(small(k-ts[i],2,d)) both[i]++; } }
    System.out.printf("delta=%.3f L=%d |U|=%d |V|=%d  predicted |V∩(U+t)| ~ %.1f%n",d,L,cu,cv,(double)cu*cv/L);
    for(int i=0;i<ts.length;i++) System.out.printf("   t=%d actual=%d ratio=%.2f%n",ts[i],both[i],both[i]/((double)cu*cv/L)); }
}

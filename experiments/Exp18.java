import java.util.*;
/** Exp18: smallest positive k with P_3(k) < delta and P_2(k-1) < delta (the t=1 witness of the joint approximation property). */
public class Exp18 {
  static boolean small(long k, long base, double delta){
    for(long n=1;;n++){ long q=1; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/base) return true; q*=base; }
      long r=k%q; if(r<0) r+=q; long s=Math.min(r,q-r); if((double)s/(double)q>=delta) return false; if(q>2*Math.abs(k)) return true; } }
  public static void main(String[] a){
    long L=Long.parseLong(a[0]);
    double[] ds={0.3,0.25,0.2,0.15,0.12,0.1,0.08,0.07,0.06,0.05,0.04,0.035,0.03,0.025,0.02};
    for(double d: ds){ long found=-1; long cnt=0; long first3=-1;
      for(long k=3;k<=L;k+=3){ if(small(k,3,d)){ if(small(k-1,2,d)){ cnt++; if(found<0) found=k; } } }
      System.out.println("delta="+d+"  smallest k = "+found+"  (number of witnesses up to "+L+": "+cnt+")"); }
  }
}

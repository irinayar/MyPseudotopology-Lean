import java.util.*;
/** Exp17: covering test (J): is every t in [-T,T] equal to u - v with P_2(u)<delta (u in U) and P_3(v)<delta (v in V)?
 *  U, V are enumerated up to L (u,v >= 0 and also allow negative: U and V are symmetric, so u - v = u + (-v) covers t = u - v for
 *  u in U, v in V, both signs). Usage: java Exp17 L T delta */
public class Exp17 {
  static boolean small(long k, long base, double delta){ // sup_n ||k/base^(n^2)|| < delta (exact enough for doubles)
    for(long n=1;;n++){ long q=1; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/base) return true; q*=base; }
      long r=k%q; long s=Math.min(r,q-r); if((double)s/(double)q>=delta) return false; if(q>2*k) return true; } }
  public static void main(String[] a){
    int L=Integer.parseInt(a[0]); int T=Integer.parseInt(a[1]); double delta=Double.parseDouble(a[2]);
    BitSet Ub=new BitSet(L+T+2); ArrayList<Integer> V=new ArrayList<>(); int cu=0;
    for(int k=0;k<=L+T;k++){ if(small(k,2,delta)){ Ub.set(k); cu++; } }
    for(int k=0;k<=L;k++){ if(small(k,3,delta)) V.add(k); }
    System.out.println("delta="+delta+" L="+L+" |U|="+cu+" |V|="+V.size());
    // t in [0,T]: need u in U, v in V with u - v = t (v >= 0, u = t+v) or u + v' = t with negative combos: u - v = t, u,v may be negative; by symmetry
    // enumerate v in V (v>=0 or v<0): u = t+v must be in U (U symmetric: u>=0 means u in Ub; u<0 means -u in Ub)
    boolean[] cov=new boolean[T+1]; int covered=0; ArrayList<Integer> miss=new ArrayList<>();
    for(int t=0;t<=T;t++){
      boolean ok=false;
      for(int v: V){ long u=(long)t+v; if(u<=L+T && Ub.get((int)u)){ ok=true; break; }
                     long u2=(long)t-v; long au=Math.abs(u2); if(au<=L+T && Ub.get((int)au)){ ok=true; break; } }
      cov[t]=ok; if(ok)covered++; else if(miss.size()<30) miss.add(t); }
    System.out.println("covered "+covered+" of "+(T+1)+"; first uncovered t: "+miss);
  }
}

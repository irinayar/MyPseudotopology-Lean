using System; using System.Collections.Generic; using System.Numerics;
public static class PairE {
  // ---- scales
  static long[] Scales(int p, int D, long X) { var l=new List<long>(); BigInteger lim=(BigInteger)D*X; for(int n=1;;n++){ BigInteger q=BigInteger.Pow(p,n*n); if(q>lim) break; l.Add((long)q);} return l.ToArray(); }
  // intervals at scale q for pair condition with shift h: x mod q in S and (x+h) mod q in S
  static List<long[]> Pair(long q, long T, long h) {
    var S=new List<long[]>(); S.Add(new long[]{0,T+1}); S.Add(new long[]{q-T,q});
    var Sh=new List<long[]>(); long hm=h%q;
    foreach(var iv in S){ long len=iv[1]-iv[0]; long u=((iv[0]-hm)%q+q)%q; if(u+len<=q) Sh.Add(new long[]{u,u+len}); else { Sh.Add(new long[]{u,q}); Sh.Add(new long[]{0,u+len-q}); } }
    var res=new List<long[]>();
    foreach(var a in S) foreach(var b in Sh){ long lo=Math.Max(a[0],b[0]), hi=Math.Min(a[1],b[1]); if(lo<hi) res.Add(new long[]{lo,hi}); }
    return res;
  }
  sealed class Ctx { public long[] q; public List<long[]>[] iv; public Dictionary<long,long>[] memo; public long[] R; }
  static long F(Ctx c,int n,long Y){
    if(n==0) return Y; if(Y<=0) return 0;
    long v0; if(c.memo[n].TryGetValue(Y,out v0)) return v0;
    long q=c.q[n-1]; long a=Y/q, t=Y%q; long res=a*Rn(c,n);
    foreach(var iv in c.iv[n]) res+=F(c,n-1,Math.Min(t,iv[1]))-F(c,n-1,Math.Min(t,iv[0]));
    c.memo[n][Y]=res; return res;
  }
  static long Rn(Ctx c,int n){ if(c.R[n]>=0) return c.R[n]; long r=0; foreach(var iv in c.iv[n]) r+=F(c,n-1,iv[1])-F(c,n-1,iv[0]); c.R[n]=r; return r; }
  public static long Pairs(int p,int D,long h,long X,long[] qs){
    int N=qs.Length; var c=new Ctx(); c.q=qs; c.iv=new List<long[]>[N+1]; c.memo=new Dictionary<long,long>[N+1]; c.R=new long[N+1];
    for(int n=1;n<=N;n++){ c.iv[n]=Pair(qs[n-1],(qs[n-1]-1)/D,h); c.memo[n]=new Dictionary<long,long>(); c.R[n]=-1; }
    return F(c,N,X-h+1);
  }
  // ---- candidate shifts: x in [1,X] with ||x/q||<1/D2 for all q for p=3 and p=2
  static bool Ok(long x,int p,int D2,long X){ for(int n=1;;n++){ BigInteger q=BigInteger.Pow(p,n*n); if(q>(BigInteger)D2*X) break; long ql=(long)q; long r=x%ql; long m=Math.Min(r,ql-r); if((long)D2*m>=ql) return false; } return true; }
  static long Next(long k,long[] qs,int D,long lim){
    while(k<=lim){ long best=k; bool failed=false;
      for(int i=0;i<qs.Length;i++){ long q=qs[i]; long T=(q-1)/D; long s=k%q; if(s>T&&s<q-T){failed=true; long kp=k+q-T-s; if(kp>best)best=kp;} }
      if(!failed) return k; k=best; }
    return -1; }
  public static string Run(int D,long X){
    long[] q3=Scales(3,D,X), q2=Scales(2,D,X);
    long a=Pairs(3,D,0,X,q3), b=Pairs(2,D,0,X,q2);
    int D2=D/2; long[] c3=Scales(3,D2,X); BigInteger off=0; long cand=0;
    long k=1;
    while(true){ k=Next(k,c3,D2,X); if(k<0) break; if(Ok(k,2,D2,X)){ cand++; long r3=Pairs(3,D,k,X,q3), r2=Pairs(2,D,k,X,q2); off+=(BigInteger)r3*r2; } k++; }
    BigInteger E=(BigInteger)a*b+2*off;
    double lam=(double)a*(double)b/(2.0*X+1); double C=(double)((2*(BigInteger)X+1)*E)/((double)a*a*(double)b*b);
    return "D="+D+" X="+X+" a="+a+" b="+b+" cand="+cand+" E="+E+" lam="+lam.ToString("F6")+" C="+C.ToString("F9");
  }
  // largest element <= X of the one-prime ball (reverse jump)
  public static long MaxElem(int p,int D,long X){ long[] qs=Scales(p,D,X); long x=X;
    while(x>=0){ long best=x; bool failed=false; for(int i=0;i<qs.Length;i++){ long q=qs[i]; long T=(q-1)/D; long s=x%q; if(s>T&&s<q-T){failed=true; long xp=x-(s-T); if(xp<best)best=xp;} } if(!failed) return x; x=best; }
    return -1; }
}

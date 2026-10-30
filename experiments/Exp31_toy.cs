using System; using System.Collections.Generic; using System.Numerics;
public static class Toy {
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
  static long[] QsN(int p,int N){ var l=new long[N]; for(int n=1;n<=N;n++){ long q=1; for(int i=0;i<n*n;i++) q*=p; l[n-1]=q;} return l; }
  public static long Full(int p,int D,long h,long[] qs){
    int N=qs.Length; var c=new Ctx(); c.q=qs; c.iv=new List<long[]>[N+1]; c.memo=new Dictionary<long,long>[N+1]; c.R=new long[N+1];
    for(int n=1;n<=N;n++){ c.iv[n]=Pair(qs[n-1],(qs[n-1]-1)/D,h); c.memo[n]=new Dictionary<long,long>(); c.R[n]=-1; }
    return Rn(c,N);
  }
  public static string RunToy(int D,int N,int M,double Lmax,int pts){
    long[] q2=QsN(2,N), q3=QsN(3,M);
    long Q2=q2[N-1], Q3=q3[M-1];
    double s2=Full(2,D,0,q2), s3=Full(3,D,0,q3);
    var all=new List<long>(); all.AddRange(q2); all.AddRange(q3);
    long lim=(long)Lmax; int D2=D/2;
    var hs=new List<long>(); var gs=new List<double>();
    long k=1;
    while(true){ k=Next(k,all.ToArray(),D2,lim); if(k<0) break;
      long c2=Full(2,D,k,q2); long c3=Full(3,D,k,q3);
      double g=((double)Q2*c2/(s2*s2))*((double)Q3*c3/(s3*s3));
      if(g>0){ hs.Add(k); gs.Add(g);} k++; }
    var sb=new System.Text.StringBuilder();
    double diagG=((double)Q2/s2)*((double)Q3/s3);
    sb.AppendLine("TOY D="+D+" N="+N+" M="+M+" q2="+Q2+" q3="+Q3+" d2="+(s2/Q2).ToString("G4")+" d3="+(s3/Q3).ToString("G4")+" diagGamma="+diagG.ToString("G5")+" nshifts="+hs.Count+" Lmax="+Lmax.ToString("G4"));
    double qmax=Math.Max(Q2,Q3); double mx10=-1,mn10=1e9,mx30=-1,mn30=1e9;
    for(int j=0;j<=pts;j++){
      double L=qmax/4.0*Math.Pow(Lmax/(qmax/4.0),(double)j/pts); if(L<2) L=2; double Lr=Math.Floor(L);
      double S0=0; for(int i=0;i<hs.Count;i++){ if(hs[i]>=Lr) break; double d=Lr-hs[i]; S0+=gs[i]*d*d; }
      double off=2*S0; double diag=Lr*Lr*diagG; double A0=Lr*Lr+(Lr-1)*Lr*(2*Lr-1)/3.0;
      double ro=off/A0; if(Lr>=10*qmax){ if(ro>mx10)mx10=ro; if(ro<mn10)mn10=ro;} if(Lr>=30*qmax){ if(ro>mx30)mx30=ro; if(ro<mn30)mn30=ro;} if(j%10==0||j==pts) sb.AppendLine("L="+Lr.ToString("F0")+" L/qmax="+(Lr/qmax).ToString("F3")+" rho_total="+((diag+off)/A0).ToString("F5")+" diag/A0="+(diag/A0).ToString("G4")+" off/A0="+(off/A0).ToString("F5")+" (rho_off+1-diagonal baseline: offBase="+((Lr-1)*Lr*(2*Lr-1)/3.0/A0).ToString("F4")+")");
    }
    sb.AppendLine("SUMMARY D="+D+" N="+N+" M="+M+" off/A0 over L>=10q: min="+mn10.ToString("F4")+" max="+mx10.ToString("F4")+" ; over L>=30q: min="+mn30.ToString("F4")+" max="+mx30.ToString("F4"));
    return sb.ToString();
  }
  static void OnePrime(int p,int D,long[] qs,List<long> rs,List<double> gs,out double dinv){
    long Q=qs[qs.Length-1]; double s=Full(p,D,0,qs); dinv=(double)Q/s; int D2=D/2; long k=1;
    while(true){ k=Next(k,qs,D2,Q-1); if(k<0) break; long c=Full(p,D,k,qs); if(c>0){ rs.Add(k); gs.Add((double)Q*c/(s*s)); } k++; }
  }
  static double Rho1(List<long> rs,List<double> gs,double dinv,long Q,double L){
    double off=0; for(double h0=Q; h0<L; h0+=Q){ double d0=L-h0; off+=dinv*d0*d0; } for(int i=0;i<rs.Count;i++){ double sum=0; for(double h=rs[i]; h<L; h+=Q){ double d=L-h; sum+=d*d; } off+=gs[i]*sum; }
    double A0=L*L+(L-1)*L*(2*L-1)/3.0; return (L*L*dinv+2*off)/A0; }
  public static string RunDecomp(int D,int N,int M,double Lmax,int pts){
    long[] q2=QsN(2,N), q3=QsN(3,M); long Q2=q2[N-1], Q3=q3[M-1];
    var r2=new List<long>(); var g2=new List<double>(); var r3=new List<long>(); var g3=new List<double>(); double di2,di3;
    OnePrime(2,D,q2,r2,g2,out di2); OnePrime(3,D,q3,r3,g3,out di3);
    double s2=Full(2,D,0,q2), s3=Full(3,D,0,q3);
    var all=new List<long>(); all.AddRange(q2); all.AddRange(q3); int D2=D/2;
    var hs=new List<long>(); var gs=new List<double>(); long k=1;
    while(true){ k=Next(k,all.ToArray(),D2,(long)Lmax); if(k<0) break; long c2=Full(2,D,k,q2), c3=Full(3,D,k,q3); double g=((double)Q2*c2/(s2*s2))*((double)Q3*c3/(s3*s3)); if(g>0){hs.Add(k);gs.Add(g);} k++; }
    var sb=new System.Text.StringBuilder(); double qmax=Math.Max(Q2,Q3); double diagG=di2*di3;
    sb.AppendLine("DECOMP D="+D+" N="+N+" M="+M+" shifts2="+r2.Count+" shifts3="+r3.Count+" mixed="+hs.Count+" Lmax="+Lmax.ToString("G4"));
    double maxM10=-1, maxM30=-1; 
    for(int j=0;j<=pts;j++){
      double L=Math.Floor(qmax/4.0*Math.Pow(Lmax/(qmax/4.0),(double)j/pts)); if(L<2) L=2;
      double S0=0; for(int i=0;i<hs.Count;i++){ if(hs[i]>=L) break; double d=L-hs[i]; S0+=gs[i]*d*d; }
      double A0=L*L+(L-1)*L*(2*L-1)/3.0; double rho=(L*L*diagG+2*S0)/A0;
      double rho2=Rho1(r2,g2,di2,Q2,L), rho3=Rho1(r3,g3,di3,Q3,L); double Mx=rho-rho2-rho3+1;
      if(L>=10*qmax && Mx>maxM10) maxM10=Mx; if(L>=30*qmax && Mx>maxM30) maxM30=Mx;
      if(j%10==0||j==pts) sb.AppendLine("L/q="+(L/qmax).ToString("F2")+" rho="+rho.ToString("F5")+" rho2-1="+(rho2-1).ToString("G4")+" rho3-1="+(rho3-1).ToString("G4")+" mixed M="+Mx.ToString("G4")+" M/(rho-1)="+(Mx/(rho-1)).ToString("G3"));
    }
    sb.AppendLine("SUMMARY-DECOMP D="+D+" N="+N+" M="+M+" max mixed M over L>=10q: "+maxM10.ToString("G4")+" ; over L>=30q: "+maxM30.ToString("G4"));
    return sb.ToString();
  }
}


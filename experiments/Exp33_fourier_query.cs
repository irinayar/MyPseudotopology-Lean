using System; using System.Collections.Generic; using System.Numerics;
public static class FQ {
  // Fourier coefficient query: amplitude |sum_{x in S_N} e(jx/Q)| / s for one prime, via cumulative-phase recursion
  sealed class Ctx { public int N; public BigInteger Q; public BigInteger j; public long[] q; public long[][] iv; public Dictionary<long,Complex>[] memo; public Complex[] R; public bool[] hasR; }
  static Complex E(BigInteger numer, BigInteger Q){ // e(numer/Q) = exp(2 pi i numer/Q), numer reduced mod Q exactly
    BigInteger r=((numer%Q)+Q)%Q; double ang=2*Math.PI*(double)r/(double)Q; return new Complex(Math.Cos(ang),Math.Sin(ang)); }
  static Complex Gmod(BigInteger a, BigInteger u, BigInteger Q){ // sum_{b=0}^{a-1} e(u/Q)^b
    u=((u%Q)+Q)%Q; if(u.IsZero) return new Complex((double)a,0);
    BigInteger twoQ=2*Q; double A=Math.PI*(double)((a*u)%twoQ)/(double)Q; double sn=Math.Sin(A);
    BigInteger uu=BigInteger.Min(u,Q-u); double d=Math.Sin(Math.PI*(double)uu/(double)Q); // sin(pi u/Q) = sin(pi uu/Q) for u in (0,Q)
    double ph=Math.PI*(double)((((a-1)*u)%twoQ))/(double)Q; return new Complex(Math.Cos(ph),Math.Sin(ph))*(sn/d); }
  static Complex F(Ctx c,int n,long Y){
    if(Y<=0) return Complex.Zero;
    if(n==0) return Gmod(Y,c.j,c.Q);
    Complex v; if(c.memo[n].TryGetValue(Y,out v)) return v;
    long q=c.q[n-1]; long a=Y/q, t=Y%q; Complex res=Complex.Zero;
    if(a>0) res=Gmod(a,c.j*q,c.Q)*Rn(c,n);
    Complex part=Complex.Zero; for(int i=0;i<c.iv[n].Length;i+=2){ part+=F(c,n-1,Math.Min(t,c.iv[n][i+1]))-F(c,n-1,Math.Min(t,c.iv[n][i])); }
    res+=E(c.j*a*q,c.Q)*part; c.memo[n][Y]=res; return res; }
  static Complex Rn(Ctx c,int n){ if(c.hasR[n]) return c.R[n]; Complex r=Complex.Zero; for(int i=0;i<c.iv[n].Length;i+=2) r+=F(c,n-1,c.iv[n][i+1])-F(c,n-1,c.iv[n][i]); c.R[n]=r; c.hasR[n]=true; return r; }
  public static double[] Query(int p,int N,int D,BigInteger j){ // returns {c_j, s}
    var c=new Ctx(); c.N=N; c.q=new long[N]; for(int n=1;n<=N;n++){ BigInteger q=BigInteger.Pow(p,n*n); c.q[n-1]=(long)q; }
    c.Q=c.q[N-1]; c.j=j; c.iv=new long[N+1][]; c.memo=new Dictionary<long,Complex>[N+1]; c.R=new Complex[N+1]; c.hasR=new bool[N+1];
    for(int n=1;n<=N;n++){ long qn=c.q[n-1]; long T=(qn-1)/D; c.iv[n]=new long[]{0,T+1,qn-T,qn}; c.memo[n]=new Dictionary<long,Complex>(); }
    Complex R=Rn(c,N); // count s by j=0 query
    var c0=new Ctx(); c0.N=N; c0.q=c.q; c0.Q=c.Q; c0.j=BigInteger.Zero; c0.iv=c.iv; c0.memo=new Dictionary<long,Complex>[N+1]; for(int n=1;n<=N;n++) c0.memo[n]=new Dictionary<long,Complex>(); c0.R=new Complex[N+1]; c0.hasR=new bool[N+1];
    double s=Rn(c0,N).Real; double amp=R.Magnitude/s; return new double[]{amp*amp,s,amp}; }
  public static string Test(){
    var sb=new System.Text.StringBuilder();
    foreach(var cfg in new int[][]{ new int[]{2,4,10}, new int[]{3,3,20}, new int[]{2,3,12}}){ int p=cfg[0],N=cfg[1],D=cfg[2];
      long Q=1; for(int i=0;i<N*N;i++) Q*=p; var qs=new List<long>(); for(int n=1;n<=N;n++){ long q=1; for(int i=0;i<n*n;i++) q*=p; qs.Add(q);} var S=new List<long>();
      for(long s2=0;s2<Q;s2++){ bool ok=true; foreach(long q in qs){ long r=s2%q; long m=Math.Min(r,q-r); if((long)D*m>=q){ok=false;break;} } if(ok) S.Add(s2);} 
      double maxerr=0; foreach(long j in new long[]{0,1,3,7,100,1234,Q/3,Q-37,Q/2+1}){ double re=0,im=0; foreach(long x in S){ double ang=2*Math.PI*(double)((j*x)%Q)/Q; re+=Math.Cos(ang); im+=Math.Sin(ang);} double cd=(re*re+im*im)/((double)S.Count*S.Count); double cq=Query(p,N,D,j)[0]; maxerr=Math.Max(maxerr,Math.Abs(cd-cq)); }
      sb.AppendLine("test p="+p+" N="+N+" D="+D+" s="+S.Count+" max|c_direct-c_query|="+maxerr.ToString("E2")); }
    return sb.ToString(); }
}

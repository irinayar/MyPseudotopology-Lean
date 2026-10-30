using System; using System.Collections.Generic; using System.Numerics; using System.Threading.Tasks;
public sealed class FQ2 {
  int N; long Q; long[] q; long[][] iv; double s;
  sealed class Ctx { public long j; public Dictionary<long,Complex>[] memo; public Complex[] R; public bool[] has; }
  public FQ2(int p,int Nn,int D){ N=Nn; q=new long[N]; for(int n=1;n<=N;n++){ BigInteger v=BigInteger.Pow(p,n*n); q[n-1]=(long)v; } Q=q[N-1]; iv=new long[N+1][];
    for(int n=1;n<=N;n++){ long qn=q[n-1]; long T=(qn-1)/D; iv[n]=new long[]{0,T+1,qn-T,qn}; }
    s=Eval0(); }
  public double S{ get{return s;} } public long Period{ get{return Q;} }
  double Eval0(){ var c=New(0); return Rn(c,N).Real; }
  Ctx New(long j){ var c=new Ctx(); c.j=j; c.memo=new Dictionary<long,Complex>[N+1]; for(int n=1;n<=N;n++) c.memo[n]=new Dictionary<long,Complex>(); c.R=new Complex[N+1]; c.has=new bool[N+1]; return c; }
  static Complex E(BigInteger numer, long Q){ BigInteger r=BigInteger.Remainder(numer,Q); if(r.Sign<0) r+=Q; double ang=2*Math.PI*(double)r/(double)Q; return new Complex(Math.Cos(ang),Math.Sin(ang)); }
  Complex Gmod(long a, BigInteger u){ u=BigInteger.Remainder(u,Q); if(u.Sign<0) u+=Q; if(u.IsZero) return new Complex((double)a,0);
    BigInteger twoQ=2*(BigInteger)Q; BigInteger au=(BigInteger)a*u; double A=Math.PI*(double)BigInteger.Remainder(au,twoQ)/(double)Q; double sn=Math.Sin(A);
    BigInteger uu=BigInteger.Min(u,Q-u); double d=Math.Sin(Math.PI*(double)uu/(double)Q); BigInteger am=(BigInteger)(a-1)*u; double ph=Math.PI*(double)BigInteger.Remainder(am,twoQ)/(double)Q; return new Complex(Math.Cos(ph),Math.Sin(ph))*(sn/d); }
  Complex F(Ctx c,int n,long Y){ if(Y<=0) return Complex.Zero; if(n==0) return Gmod(Y,c.j);
    Complex v; if(c.memo[n].TryGetValue(Y,out v)) return v; long qq=q[n-1]; long a=Y/qq, t=Y%qq; Complex res=Complex.Zero;
    if(a>0) res=Gmod(a,(BigInteger)c.j*qq)*Rn(c,n);
    Complex part=Complex.Zero; for(int i=0;i<iv[n].Length;i+=2) part+=F(c,n-1,Math.Min(t,iv[n][i+1]))-F(c,n-1,Math.Min(t,iv[n][i]));
    res+=E((BigInteger)c.j*a*qq,Q)*part; c.memo[n][Y]=res; return res; }
  Complex Rn(Ctx c,int n){ if(c.has[n]) return c.R[n]; Complex r=Complex.Zero; for(int i=0;i<iv[n].Length;i+=2) r+=F(c,n-1,iv[n][i+1])-F(c,n-1,iv[n][i]); c.R[n]=r; c.has[n]=true; return r; }
  public double C(long j){ var c=New(j); Complex R=Rn(c,N); double a=R.Magnitude/s; return a*a; }
}
public static class FullB {
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger g=m, x=0, y=1, aa=((a%m)+m)%m; BigInteger r0=m, r1=aa, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  public static string Run(int D,int N,int M,long X,double heavyCut){
    var f2=new FQ2(2,N,D); var f3=new FQ2(3,M,D); long Q2=f2.Period, Q3=f3.Period; BigInteger NN=(BigInteger)Q2*Q3; long E=(long)(NN/X);
    BigInteger i3=Inv(Q3,Q2), i2=Inv(Q2,Q3); // j = e*inv(q3) mod q2 ; k = e*inv(q2) mod q3
    int nth=Environment.ProcessorCount; double[] partial=new double[nth], heavy=new double[nth]; long[] cnt=new long[nth];
    var hv=new List<string>[nth]; for(int i=0;i<nth;i++) hv[i]=new List<string>();
    Parallel.For(0,nth,delegate(int t){ var g2=new FQ2(2,N,D); var g3=new FQ2(3,M,D);
      for(long e=1+t;e<=E;e+=nth){ long j=(long)(((BigInteger)e*i3)%Q2); long k=(long)(((BigInteger)e*i2)%Q3); double c2=g2.C(j), c3=g3.C(k); double pr=c2*c3; partial[t]+=pr; cnt[t]++; if(pr>=heavyCut){ heavy[t]+=pr; long jj=j>Q2/2?j-Q2:j, kk=k>Q3/2?k-Q3:k; hv[t].Add("e="+e+" j="+jj+" k="+kk+" prod="+pr.ToString("G4")); } } });
    double one=0,hvs=0; long ne=0; for(int t=0;t<nth;t++){ one+=partial[t]; hvs+=heavy[t]; ne+=cnt[t]; }
    double B1=2*one; double Hv=2*hvs; // e and -e symmetric
    double m2=(Q2/f2.S-1)/(Q2-1), m3=(Q3/f3.S-1)/(Q3-1); double pred=2.0*E*m2*m3;
    var sb=new System.Text.StringBuilder(); sb.AppendLine("D="+D+" (N,M)=("+N+","+M+") X="+X+" q2="+Q2+" q3="+Q3+" s2="+f2.S+" s3="+f3.S+" window E="+E+" pairs="+(2*ne)+" B-1="+B1.ToString("G8")+" (heavy>= "+heavyCut+": "+Hv.ToString("G6")+" ; rest "+(B1-Hv).ToString("G6")+")  independent-model total n*m2*m3="+pred.ToString("G6")+"  ratio (B-1)/model="+(B1/pred).ToString("G5"));
    var all=new List<string>(); for(int t=0;t<nth;t++) all.AddRange(hv[t]); all.Sort(); int shown=0; foreach(var s0 in all){ if(shown++<12) sb.AppendLine("  "+s0); }
    return sb.ToString(); }
}

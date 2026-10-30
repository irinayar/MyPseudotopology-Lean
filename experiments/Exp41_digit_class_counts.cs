using System; using System.Numerics; using System.Threading.Tasks;
public static class DigCount {
  static void MaxDigit(long j,int p,int N,out int T,out long mx){
    long[] q=new long[N+1]; q[0]=1; for(int n=1;n<=N;n++){ BigInteger v=BigInteger.Pow(p,n*n); q[n]=(long)v; }
    long Q=q[N]; if(j>Q/2) j-=Q; T=0; mx=0; long x=j;
    for(int n=N;n>=1;n--){ long al=q[n]/q[n-1]; long r=((x%al)+al)%al; if(r*2>al) r-=al; if(r!=0){ T++; if(Math.Abs(r)>mx) mx=Math.Abs(r); } x=(x-r)/al; } }
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  static double Vectors(int p,int N,int R){ double v=1; for(int n=1;n<=N;n++){ long al=(long)Math.Pow(p,2*n-1); double cnt=Math.Min((double)al,2.0*R+1); v*=cnt; } return v; }
  public static string Run(int N,int M,long X,int[] Rs){
    long Q2=(long)Math.Pow(2,N*N), Q3=(long)Math.Pow(3,M*M); BigInteger NN=(BigInteger)Q2*Q3; long E=(long)(NN/X); BigInteger i3=Inv(Q3,Q2), i2=Inv(Q2,Q3);
    int nth=Environment.ProcessorCount; int nr=Rs.Length; long[][] cnt=new long[nth][]; for(int t=0;t<nth;t++) cnt[t]=new long[nr];
    Parallel.For(0,nth,delegate(int t){ for(long e=1+t;e<=E;e+=nth){ long j=(long)(((BigInteger)e*i3)%Q2); long k=(long)(((BigInteger)e*i2)%Q3); int T2,T3; long m2,m3; MaxDigit(j,2,N,out T2,out m2); MaxDigit(k,3,M,out T3,out m3); long mx=Math.Max(m2,m3); for(int a=0;a<nr;a++) if(mx<=Rs[a]) cnt[t][a]+=2; } });
    string res="(N,M)=("+N+","+M+") X="+X+" window pairs (e!=0) = "+(2*E)+"\n";
    for(int a=0;a<nr;a++){ long c=0; for(int t=0;t<nth;t++) c+=cnt[t][a]; double nv=Vectors(2,N,Rs[a])*Vectors(3,M,Rs[a]); double expct=(nv-1)*(2.0*E)/(double)((double)Q2*Q3); res+="  all digits <= "+Rs[a]+": observed "+c+"  expected (random) "+expct.ToString("G5")+"  ratio "+(c/expct).ToString("G4")+"\n"; }
    return res; }
}

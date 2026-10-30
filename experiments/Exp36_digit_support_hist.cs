using System; using System.Numerics; using System.Threading.Tasks;
public static class DigHist {
  // balanced mixed-radix digits of j mod Q, q_n=p^(n^2): j = sum r_n Q/q_n ; returns count of nonzero digits and max |digit|
  static void Digits(long j,int p,int N,out int T,out long mx){
    long[] q=new long[N+1]; q[0]=1; for(int n=1;n<=N;n++){ BigInteger v=BigInteger.Pow(p,n*n); q[n]=(long)v; }
    long Q=q[N]; if(j>Q/2) j-=Q; T=0; mx=0; long x=j;
    for(int n=N;n>=1;n--){ long al=q[n]/q[n-1]; long r=((x%al)+al)%al; if(r>al/2 || (r*2>al)) r-=al; if(r!=0){ T++; if(Math.Abs(r)>mx) mx=Math.Abs(r); } x=(x-r)/al; }
  }
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  public static string Run(int D,int N,int M,long X){
    var f2=new FQ2(2,N,D); var f3=new FQ2(3,M,D); long Q2=f2.Period, Q3=f3.Period; BigInteger NN=(BigInteger)Q2*Q3; long E=(long)(NN/X);
    BigInteger i3=Inv(Q3,Q2), i2=Inv(Q2,Q3); int nth=Environment.ProcessorCount; int TM=16;
    double[][] byT=new double[nth][]; double[][] byMx=new double[nth][]; long[][] cT=new long[nth][];
    for(int t=0;t<nth;t++){ byT[t]=new double[TM]; byMx[t]=new double[4]; cT[t]=new long[TM]; }
    Parallel.For(0,nth,delegate(int t){ var g2=new FQ2(2,N,D); var g3=new FQ2(3,M,D);
      for(long e=1+t;e<=E;e+=nth){ long j=(long)(((BigInteger)e*i3)%Q2); long k=(long)(((BigInteger)e*i2)%Q3); double pr=g2.C(j)*g3.C(k);
        int T2,T3; long m2,m3; Digits(j,2,N,out T2,out m2); Digits(k,3,M,out T3,out m3); int T=Math.Min(T2+T3,TM-1); long mx=Math.Max(m2,m3);
        byT[t][T]+=2*pr; cT[t][T]+=2; int b=mx<=10?0:(mx<=40?1:(mx<=200?2:3)); byMx[t][b]+=2*pr; } });
    var sb=new System.Text.StringBuilder(); sb.AppendLine("D="+D+" ("+N+","+M+") X="+X+" window pairs="+(2*E));
    double tot=0; for(int T=0;T<TM;T++){ double s=0; long c=0; for(int t=0;t<nth;t++){ s+=byT[t][T]; c+=cT[t][T]; } tot+=s; if(c>0) sb.AppendLine("  T="+T+" pairs="+c+" mass="+s.ToString("G5")+" mean="+(s/c).ToString("G3")); }
    double[] mm=new double[4]; for(int b=0;b<4;b++) for(int t=0;t<nth;t++) mm[b]+=byMx[t][b];
    sb.AppendLine("  total B-1="+tot.ToString("G6")+"  by max digit: <=10: "+mm[0].ToString("G4")+"  11..40: "+mm[1].ToString("G4")+"  41..200: "+mm[2].ToString("G4")+"  >200: "+mm[3].ToString("G4"));
    return sb.ToString(); }
}

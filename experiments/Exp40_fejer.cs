using System; using System.Numerics; using System.Threading.Tasks;
public static class Fejer {
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  public static string Run(int D,long X,double[] c2,double[] c3){
    long Q2=c2.Length, Q3=c3.Length; long NN=Q2*Q3; long E=NN/X; long i3=(long)Inv(Q3,Q2), i2=(long)Inv(Q2,Q3);
    double[] v=new double[NN]; long j=0,k=0; for(long e=0;e<NN;e++){ v[e]=c2[j]*c3[k]; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; }
    double[] w=new double[E+1]; for(long a=0;a<=E;a++) w[a]=1.0-(double)a/(E+1);
    int nth=Environment.ProcessorCount; long chunk=(NN+nth-1)/nth; double[] mx=new double[nth], mr=new double[nth]; long[] arg=new long[nth];
    Parallel.For(0,nth,delegate(int t){ long s=t*chunk, en=Math.Min(NN,s+chunk); double best=0,bestr=0; long ba=0; for(long x=s;x<en;x++){ double r=v[x]; double sr=0; for(long a=1;a<=E;a++){ long p=x+a; if(p>=NN) p-=NN; long m=x-a; if(m<0) m+=NN; sr+=w[a]*(v[p]+v[m]); } double tot=r+sr; if(tot>best){best=tot; ba=x;} } mx[t]=best; arg[t]=ba; mr[t]=bestr; });
    double b=0; long ab=0; for(int t=0;t<nth;t++) if(mx[t]>b){b=mx[t]; ab=arg[t];}
    double at0=v[0]; for(long a=1;a<=E;a++) at0+=w[a]*(v[a]+v[NN-a]);
    return "D="+D+" N="+NN+" X="+X+" E="+E+"  Fejer-weighted window sum at 0 = "+at0.ToString("G8")+"   sup over all centers = "+b.ToString("G8")+" at x="+ab; }
}

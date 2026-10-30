using System; using System.Numerics; using System.Threading.Tasks;
public static class Cascade {
  // kappa(r) for the quartic window radius a=1/D: [15 g(s)/16]^2, s=2 pi r/D, g(s)=16(3(sin s - s cos s) - s^2 sin s)/s^5
  static double Kappa(long r,int D){ if(r==0) return 1.0; double s=2*Math.PI*r/D; double g; if(Math.Abs(s)<0.05){ double s2=s*s; g=16.0/15.0*(1-s2/14.0+s2*s2/504.0); } else { g=16.0*(3*(Math.Sin(s)-s*Math.Cos(s))-s*s*Math.Sin(s))/Math.Pow(s,5); } double k=15.0*g/16.0; return k*k; }
  public static double[] Build(int p,int nPrefix,int N,int D){
    double[] c=SmoothB.Coef(p,nPrefix,D,true,p==2); long Qprev=c.Length;
    for(int n=nPrefix+1;n<=N;n++){ long Q=(long)Math.Pow(p,n*n); long al=Q/Qprev; double[] cn=new double[Q]; long P=Qprev; long half=al/2;
      Parallel.For(0,(int)Math.Min(Q,int.MaxValue/1)>0?64:64,delegate(int t){ long chunk=(Q+63)/64; long s=t*chunk, e=Math.Min(Q,s+chunk);
        for(long j=s;j<e;j++){ long l0=(j+half)/al; // nearest coarse index
          double sum=0; for(int d=-3;d<=3;d++){ long l=l0+d; long r=j-al*l; long lm=((l%P)+P)%P; sum+=Kappa(r,D)*c[lm]; } cn[j]=sum; } });
      c=cn; Qprev=Q; }
    return c; }
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  public static string Mass(int D,double[] c2,double[] c3,long[] Xs,string tag){
    long Q2=c2.Length,Q3=c3.Length; BigInteger NN=(BigInteger)Q2*Q3; long i3=(long)Inv(Q3,Q2), i2=(long)Inv(Q2,Q3); string res="";
    foreach(long X in Xs){ long E=(long)(NN/X); int nth=Environment.ProcessorCount; double[] part=new double[nth]; double[] mx=new double[nth]; double[] dense=new double[nth];
      Parallel.For(0,nth,delegate(int t){ long j=(long)(((BigInteger)(1+t)*i3)%Q2), k=(long)(((BigInteger)(1+t)*i2)%Q3); long sj=(long)(((BigInteger)nth*i3)%Q2), sk=(long)(((BigInteger)nth*i2)%Q3);
        for(long e=1+t;e<=E;e+=nth){ double v=c2[j]*c3[k]; part[t]+=v; if(v>mx[t]) mx[t]=v; j+=sj; if(j>=Q2) j-=Q2; k+=sk; if(k>=Q3) k-=Q3; } });
      double s=0,m=0; for(int t=0;t<nth;t++){ s+=part[t]; if(mx[t]>m) m=mx[t]; }
      double zero=c2[0]*c3[0]; res+="  "+tag+" D="+D+" X="+X+" E="+E+"  c2(0)c3(0)="+zero.ToString("G8")+"  B = zero + 2*sum = "+(zero+2*s).ToString("G8")+"  (B-1="+(zero+2*s-1).ToString("G6")+", max pair "+m.ToString("G3")+")\n"; }
    return res; }
}

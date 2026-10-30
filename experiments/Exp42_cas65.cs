using System; using System.Numerics; using System.Threading.Tasks;
public static class Cas65 {
  static double Kappa(long r,int D){ if(r==0) return 1.0; if(r<0) r=-r; double s=2*Math.PI*r/D; double g; if(s<0.05){ double s2=s*s; g=16.0/15.0*(1-s2/14.0+s2*s2/504.0); } else { g=16.0*(3*(Math.Sin(s)-s*Math.Cos(s))-s*s*Math.Sin(s))/Math.Pow(s,5); } double k=15.0*g/16.0; return k*k; }
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  // top level: c(j) = sum_{d=-3..3} kappa(j - al*(l0+d)) * cprev[(l0+d) mod P]
  public static string Run(int D,int N,int M,long[] Xs,int n0=4,int m0=2){
    // arrays one level below the top
    double[] c2p=Cascade.Build(2,n0,N-1,D); double[] c3p=Cascade.Build(3,m0,M-1,D);
    long P2=c2p.Length, P3=c3p.Length; long Q2=(long)Math.Pow(2,N*N); long Q3=(long)Math.Pow(3,M*M); long al2=Q2/P2, al3=Q3/P3;
    int T2=(int)(4*al2), T3=(int)(4*al3); double[] ktab2=new double[T2], ktab3=new double[T3]; for(int r=0;r<T2;r++) ktab2[r]=Kappa(r,D); for(int r=0;r<T3;r++) ktab3[r]=Kappa(r,D);
    BigInteger NN=(BigInteger)Q2*Q3; long i3=(long)Inv(Q3,Q2), i2=(long)Inv(Q2,Q3); string res="";
    Func<long,double> C2=delegate(long j){ long l0=(j+al2/2)/al2; double s=0; for(int d=-3;d<=3;d++){ long l=l0+d; long r=j-al2*l; if(r<0) r=-r; long lm=l%P2; if(lm<0) lm+=P2; s+=ktab2[r]*c2p[lm]; } return s; };
    Func<long,double> C3=delegate(long k){ long l0=(k+al3/2)/al3; double s=0; for(int d=-3;d<=3;d++){ long l=l0+d; long r=k-al3*l; if(r<0) r=-r; long lm=l%P3; if(lm<0) lm+=P3; s+=ktab3[r]*c3p[lm]; } return s; };
    double zero=C2(0)*C3(0);
    foreach(long X in Xs){ long E=(long)(NN/X); int chunks=256; long cs=(E+chunks-1)/chunks; double[] part=new double[chunks]; double[] mx=new double[chunks];
      var sw=System.Diagnostics.Stopwatch.StartNew();
      Parallel.For(0,chunks,delegate(int c){ long s=1+c*cs, e1=Math.Min(E,(long)(c+1)*cs); if(s>e1) return; long j=(long)(((BigInteger)s*i3)%Q2), k=(long)(((BigInteger)s*i2)%Q3); double acc=0, m=0;
        for(long e=s;e<=e1;e++){ long jb=j>Q2/2?j-Q2:j; long kb=k>Q3/2?k-Q3:k; double v=C2(jb<0?jb+Q2:jb)*C3(kb<0?kb+Q3:kb); acc+=v; if(v>m) m=v; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; } part[c]=acc; mx[c]=m; });
      double sTot=0,mTot=0; for(int c=0;c<chunks;c++){ sTot+=part[c]; if(mx[c]>mTot) mTot=mx[c]; }
      res+="(N,M)=("+N+","+M+") D="+D+" X="+X+" E="+E+"  c2(0)c3(0)="+zero.ToString("G8")+"  B-1 = "+(zero-1+2*sTot).ToString("G7")+"  max pair "+mTot.ToString("G3")+"   ["+Math.Round(sw.Elapsed.TotalSeconds,1)+" s]\n"; }
    return res; }
}

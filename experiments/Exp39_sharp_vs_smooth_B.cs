using System; using System.Numerics; using System.Threading.Tasks;
public static class SmoothB {
  static void FFT(Complex[] a){ int n=a.Length; for(int i=1,j=0;i<n;i++){ int bit=n>>1; for(;(j&bit)!=0;bit>>=1) j^=bit; j^=bit; if(i<j){ Complex t=a[i]; a[i]=a[j]; a[j]=t; } }
    for(int len=2;len<=n;len<<=1){ double ang=-2*Math.PI/len; Complex wl=new Complex(Math.Cos(ang),Math.Sin(ang)); for(int i=0;i<n;i+=len){ Complex w=Complex.One; for(int j=0;j<len/2;j++){ Complex u=a[i+j], v=a[i+j+len/2]*w; a[i+j]=u+v; a[i+j+len/2]=u-v; w*=wl; } } } }
  static double W(double t,double a){ double z=t/a; if(Math.Abs(z)>=1) return 0; double v=1-z*z; return v*v; }
  static double[] Weights(int p,int n,int D,bool smooth){ long[] q=new long[n+1]; for(int k=1;k<=n;k++) q[k]=(long)Math.Pow(p,k*k); long Q=q[n]; double[] f=new double[Q];
    for(long x=0;x<Q;x++){ double v=1; for(int k=1;k<=n;k++){ long r=x%q[k]; if(r>q[k]/2) r-=q[k]; if(smooth){ v*=W((double)r/q[k],1.0/D); } else { long T=(q[k]-1)/D; if(Math.Abs(r)>T) v=0; } if(v==0) break; } f[x]=v; } return f; }
  public static double[] Coef(int p,int n,int D,bool smooth,bool pow2){ double[] f=Weights(p,n,D,smooth); long Q=f.Length; double S=0; for(long x=0;x<Q;x++) S+=f[x]; double[] c=new double[Q];
    if(pow2){ Complex[] a=new Complex[Q]; for(long x=0;x<Q;x++) a[x]=f[x]; FFT(a); for(long j=0;j<Q;j++) c[j]=a[j].Magnitude*a[j].Magnitude/(S*S); }
    else { int cnt=0; for(long x=0;x<Q;x++) if(f[x]!=0) cnt++; long[] xs=new long[cnt]; double[] fs=new double[cnt]; int t=0; for(long x=0;x<Q;x++) if(f[x]!=0){ xs[t]=x; fs[t]=f[x]; t++; }
      double[] cs=new double[Q], sn=new double[Q]; for(long i=0;i<Q;i++){ cs[i]=Math.Cos(2*Math.PI*i/Q); sn[i]=Math.Sin(2*Math.PI*i/Q); }
      Parallel.For(0,(int)Q,delegate(int j){ double re=0,im=0; for(int i=0;i<cnt;i++){ long idx=((long)j*xs[i])%Q; re+=fs[i]*cs[idx]; im+=fs[i]*sn[idx]; } c[j]=(re*re+im*im)/(S*S); }); }
    return c; }
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  public static string Run(int D,int N,int M,long[] Xs){
    double[][] c2=new double[2][], c3=new double[2][]; for(int s=0;s<2;s++){ c2[s]=Coef(2,N,D,s==1,true); c3[s]=Coef(3,M,D,s==1,false); }
    long Q2=c2[0].Length, Q3=c3[0].Length; BigInteger NN=(BigInteger)Q2*Q3; BigInteger i3=Inv(Q3,Q2), i2=Inv(Q2,Q3);
    string res="D="+D+" ("+N+","+M+") q2="+Q2+" q3="+Q3+"  sum c (rho): sharp "+Sum(c2[0]).ToString("G5")+"/"+Sum(c3[0]).ToString("G5")+"  smooth "+Sum(c2[1]).ToString("G5")+"/"+Sum(c3[1]).ToString("G5")+"\n";
    foreach(long X in Xs){ long E=(long)(NN/X); double[] tot=new double[2]; double[] mx=new double[2];
      for(long e=1;e<=E;e++){ long j=(long)(((BigInteger)e*i3)%Q2); long k=(long)(((BigInteger)e*i2)%Q3); for(int s=0;s<2;s++){ double pr=c2[s][j]*c3[s][k]; tot[s]+=2*pr; if(pr>mx[s]) mx[s]=pr; } }
      res+="  X="+X+" window E="+E+"  B-1 sharp="+tot[0].ToString("G5")+" (max pair "+mx[0].ToString("G3")+")   smooth(a=1/D)="+tot[1].ToString("G5")+" (max pair "+mx[1].ToString("G3")+")\n"; }
    return res; }
  static double Sum(double[] a){ double s=0; foreach(double v in a) s+=v; return s; }
}

using System; using System.Numerics; using System.Threading.Tasks;
public static class Msq {
  static void FFT(Complex[] a,bool inv){ int n=a.Length; for(int i=1,j=0;i<n;i++){ int bit=n>>1; for(;(j&bit)!=0;bit>>=1) j^=bit; j^=bit; if(i<j){ Complex t=a[i]; a[i]=a[j]; a[j]=t; } }
    for(int len=2;len<=n;len<<=1){ double ang=(inv?2:-2)*Math.PI/len; Complex wl=new Complex(Math.Cos(ang),Math.Sin(ang)); for(int i=0;i<n;i+=len){ Complex w=Complex.One; for(int j=0;j<len/2;j++){ Complex u=a[i+j], v=a[i+j+len/2]*w; a[i+j]=u+v; a[i+j+len/2]=u-v; w*=wl; } } } if(inv) for(int i=0;i<n;i++) a[i]/=n; }
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  public static string Run(int D,long X,double[] c2,double[] c3){
    long Q2=c2.Length, Q3=c3.Length; long NN=Q2*Q3; long E=NN/X; long W=2*E+1; long i3=(long)Inv(Q3,Q2), i2=(long)Inv(Q2,Q3);
    // autocorrelations: A2(d)=sum_j c2(j)c2(j+d) via FFT; A3 directly
    Complex[] f=new Complex[Q2]; for(long j=0;j<Q2;j++) f[j]=c2[j]; FFT(f,false); for(long j=0;j<Q2;j++) f[j]=f[j]*Complex.Conjugate(f[j]); FFT(f,true); double[] A2=new double[Q2]; for(long j=0;j<Q2;j++) A2[j]=f[j].Real;
    double[] A3=new double[Q3]; Parallel.For(0,(int)Q3,delegate(int d){ double s=0; for(int k=0;k<Q3;k++){ int kk=k+d; if(kk>=Q3) kk-=(int)Q3; s+=c3[k]*c3[kk]; } A3[d]=s; });
    double rhs=0; for(long d=-2*E; d<=2*E; d++){ long a=Math.Abs(d); long d2=(long)((((BigInteger)d*i3)%Q2+Q2)%Q2); long d3=(long)((((BigInteger)d*i2)%Q3+Q3)%Q3); rhs+=(double)(W-a)*A2[d2]*A3[d3]; } rhs/=NN;
    // LHS by sliding
    int nth=Environment.ProcessorCount; long chunk=(NN+nth-1)/nth; double[] acc=new double[nth];
    Parallel.For(0,nth,delegate(int t){ long start=t*chunk, end=Math.Min(NN,start+chunk); if(start>=end) return; long e0=start-E; long j=(long)((((BigInteger)e0*i3)%Q2+Q2)%Q2), k=(long)((((BigInteger)e0*i2)%Q3+Q3)%Q3);
      double[] buf=new double[W]; double sum=0; long bp=0; for(long i=0;i<W;i++){ double v=c2[j]*c3[k]; buf[i]=v; sum+=v; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; }
      double a=sum*sum; for(long x=start+1;x<end;x++){ double v=c2[j]*c3[k]; sum+=v-buf[bp]; buf[bp]=v; bp++; if(bp==W) bp=0; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; a+=sum*sum; } acc[t]=a; });
    double lhs=0; for(int t=0;t<nth;t++) lhs+=acc[t]; lhs/=NN;
    double mean=(double)W*Sum(c2)*Sum(c3)/NN;
    return "D="+D+" X="+X+" E="+E+"  mean-square over centers: sliding="+lhs.ToString("G8")+"  CRT-factorized formula="+rhs.ToString("G8")+"  (mean sum)^2="+(mean*mean).ToString("G5")+"  d=0 term="+((double)W*A2[0]*A3[0]/NN).ToString("G4"); }
  static double Sum(double[] a){ double s=0; foreach(double v in a) s+=v; return s; }
}

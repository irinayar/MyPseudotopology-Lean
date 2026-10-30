using System; using System.Numerics;
public static class SmoothChk {
  static void FFT(Complex[] a){ int n=a.Length; for(int i=1,j=0;i<n;i++){ int bit=n>>1; for(;(j&bit)!=0;bit>>=1) j^=bit; j^=bit; if(i<j){ Complex t=a[i]; a[i]=a[j]; a[j]=t; } }
    for(int len=2;len<=n;len<<=1){ double ang=-2*Math.PI/len; Complex wl=new Complex(Math.Cos(ang),Math.Sin(ang)); for(int i=0;i<n;i+=len){ Complex w=Complex.One; for(int j=0;j<len/2;j++){ Complex u=a[i+j], v=a[i+j+len/2]*w; a[i+j]=u+v; a[i+j+len/2]=u-v; w*=wl; } } } }
  static double W(double t,double a){ double z=t/a; if(Math.Abs(z)>=1) return 0; double v=1-z*z; return v*v; }
  public static string Run(int p,int n,int D){
    long[] q=new long[n+1]; for(int k=1;k<=n;k++) q[k]=(long)Math.Pow(p,k*k); long Q=q[n], P=q[n-1], al=Q/P; double a=1.0/(2*D);
    Complex[] f=new Complex[Q]; double S=0,T=0; for(long x=0;x<Q;x++){ double v=1; for(int k=1;k<=n;k++){ long r=x%q[k]; if(r>q[k]/2) r-=q[k]; v*=W((double)r/q[k],a); if(v==0) break; } f[x]=v; S+=v; T+=v*v; }
    double rho=Q*T/(S*S); FFT(f); double[] c=new double[Q]; for(long J=0;J<Q;J++) c[J]=f[J].Magnitude*f[J].Magnitude/(S*S);
    double tot=0; for(long J=0;J<Q;J++) tot+=c[J];
    string res="p="+p+" n="+n+" D="+D+" alpha="+al+" rho="+rho.ToString("G6")+" sum c="+tot.ToString("G6")+" max c="+Math.Max(c[0],0).ToString("G4")+"\n";
    foreach(int R in new int[]{1,2,3,5,8,12,20,40}){ if(R>=al/2) continue; double tail=0; for(long l=0;l<P;l++) for(long r=-al/2+1;r<=al/2;r++){ if(Math.Abs(r)>R){ long J=(((al*l+r)%Q)+Q)%Q; tail+=c[J]; } }
      double bound=35.0*D*D*D/18.0*rho/((double)R*R*R); res+="  R="+R+" tail="+tail.ToString("G4")+" bound="+bound.ToString("G4")+" ratio="+(tail/bound).ToString("G3")+"\n"; }
    return res; }
}

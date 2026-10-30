using System; using System.Collections.Generic; using System.Numerics;
public static class AliasChk {
  static bool Good(long x,long q,int D){ long T=(q-1)/D; long r=((x%q)+q)%q; return r<=T || r>=q-T; }
  public static string Run(int p,int n,int D){
    long[] q=new long[n+1]; for(int k=1;k<=n;k++) q[k]=(long)Math.Pow(p,k*k); long Q=q[n], P=q[n-1], al=Q/P;
    List<long> S=new List<long>(); List<long> Sp=new List<long>();
    for(long x=0;x<Q;x++){ bool g=true; for(int k=1;k<=n;k++) if(!Good(x,q[k],D)){g=false;break;} if(g) S.Add(x); }
    for(long y=0;y<P;y++){ bool g=true; for(int k=1;k<n;k++) if(!Good(y,q[k],D)){g=false;break;} if(g) Sp.Add(y); }
    long s=S.Count, sp=Sp.Count; long T=(Q-1)/D; long m=2*T+1; long K=m/P; long u=s-K*sp;
    double[] c=new double[Q]; for(long J=0;J<Q;J++){ Complex f=Complex.Zero; foreach(long x in S){ double ang=2*Math.PI*((J*x)%Q)/Q; f+=new Complex(Math.Cos(ang),Math.Sin(ang)); } c[J]=f.Magnitude*f.Magnitude/((double)s*s); }
    double d=(double)s/Q; double maxerr=0;
    for(long r=-al/2;r<=al/2 && r<al/2+1;r++){ if(r==al/2 && al%2==0) continue; double sum=0; for(long l=0;l<P;l++){ long J=(((al*l+r)%Q)+Q)%Q; sum+=c[J]; } double mu=d*sum;
      double GK,GK1; if(r==0){GK=K;GK1=K+1;} else { double z=Math.PI*r/al; GK=Math.Sin(K*z)/Math.Sin(z); GK1=Math.Sin((K+1)*z)/Math.Sin(z); }
      double form=((sp-u)*GK*GK+u*GK1*GK1)/(al*(double)s); maxerr=Math.Max(maxerr,Math.Abs(mu-form)); }
    return "p="+p+" n="+n+" D="+D+" Q="+Q+" P="+P+" alpha="+al+" s="+s+" s_prev="+sp+" K="+K+" u="+u+" max|mu-formula| over r = "+maxerr.ToString("E3"); }
}

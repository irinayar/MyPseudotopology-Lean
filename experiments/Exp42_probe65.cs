using System; using System.Numerics; using System.Text;
public static class Probe65 {
  static double Kappa(long r,int D){ if(r==0) return 1.0; if(r<0) r=-r; double s=2*Math.PI*r/D; double g; if(s<0.05){ double s2=s*s; g=16.0/15.0*(1-s2/14.0+s2*s2/504.0); } else { g=16.0*(3*(Math.Sin(s)-s*Math.Cos(s))-s*s*Math.Sin(s))/Math.Pow(s,5); } double k=15.0*g/16.0; return k*k; }
  public static string Run(int D,int N,int M,int n0,int m0,long[] js,long[] ks,int tmax){
    double[] c2p=Cascade.Build(2,n0,N-1,D); double[] c3p=Cascade.Build(3,m0,M-1,D); long P2=c2p.Length,P3=c3p.Length; long Q2=(long)Math.Pow(2,N*N), Q3=(long)Math.Pow(3,M*M); long al2=Q2/P2, al3=Q3/P3;
    Func<long,double> C2=delegate(long j){ j=((j%Q2)+Q2)%Q2; long l0=(j+al2/2)/al2; double s=0; for(int d=-3;d<=3;d++){ long l=l0+d; long r=j-al2*l; long lm=((l%P2)+P2)%P2; s+=Kappa(r,D)*c2p[lm]; } return s; };
    Func<long,double> C3=delegate(long k){ k=((k%Q3)+Q3)%Q3; long l0=(k+al3/2)/al3; double s=0; for(int d=-3;d<=3;d++){ long l=l0+d; long r=k-al3*l; long lm=((l%P3)+P3)%P3; s+=Kappa(r,D)*c3p[lm]; } return s; };
    StringBuilder sb=new StringBuilder(); for(int i=0;i<js.Length;i++){ BigInteger e=(BigInteger)js[i]*Q3+(BigInteger)ks[i]*Q2; sb.AppendLine("direction (j0,k0)=("+js[i]+","+ks[i]+") e0="+e); for(int t=1;t<=tmax;t++){ double w=C2(js[i]*t)*C3(ks[i]*t); BigInteger et=e*t; sb.AppendLine("   t="+t+" e="+et+" weight c2*c3 = "+w.ToString("G6")+"  c2="+C2(js[i]*t).ToString("G5")+" c3="+C3(ks[i]*t).ToString("G5")); } }
    return sb.ToString(); }
}

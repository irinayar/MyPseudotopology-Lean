using System; using System.Collections.Generic;
public static class Bmass {
  static List<long> Good(int p,int N,int D){ var res=new List<long>(); long Q=1; for(int i=0;i<N*N;i++) Q*=p; var qs=new List<long>(); for(int n=1;n<=N;n++){ long q=1; for(int i=0;i<n*n;i++) q*=p; qs.Add(q);} 
    for(long s=0;s<Q;s++){ bool ok=true; foreach(long q in qs){ long r=s%q; long m=Math.Min(r,q-r); if((long)D*m>=q){ok=false;break;} } if(ok) res.Add(s);} return res; }
  static double[] Coef(List<long> S,long Q){ var c=new double[Q]; double s=S.Count; for(long j=0;j<Q;j++){ double re=0,im=0; foreach(long x in S){ double ang=2*Math.PI*(double)((j*x)%Q)/Q; re+=Math.Cos(ang); im+=Math.Sin(ang);} c[j]=(re*re+im*im)/(s*s);} return c; }
  public static string Run(int D,int N,int M,long[] Xs){
    var S2=Good(2,N,D); var S3=Good(3,M,D); long Q2=1,Q3=1; for(int i=0;i<N*N;i++)Q2*=2; for(int i=0;i<M*M;i++)Q3*=3;
    var c2=Coef(S2,Q2); var c3=Coef(S3,Q3);
    var sb=new System.Text.StringBuilder(); sb.AppendLine("D="+D+" q2="+Q2+" q3="+Q3+" s2="+S2.Count+" s3="+S3.Count+" sumc2="+Sum(c2).ToString("G6")+" (expect q/s="+((double)Q2/S2.Count).ToString("G6")+")");
    foreach(long X in Xs){ double B=0; double w=1.0/X;
      for(long j=0;j<Q2;j++){ if(c2[j]<1e-300) continue; double t=-(double)j/Q2; t-=Math.Floor(t); // want k/Q3 near t (mod 1) so that j/Q2+k/Q3 near integer
        double kc=t*Q3; long k0=(long)Math.Floor(kc-w*Q3)-1; long k1=(long)Math.Ceiling(kc+w*Q3)+1;
        for(long k=k0;k<=k1;k++){ long kk=((k%Q3)+Q3)%Q3; double th=(double)j/Q2+(double)kk/Q3; double d=Math.Abs(th-Math.Round(th)); if(d<=w) B+=c2[j]*c3[kk]; } }
      sb.AppendLine("X="+X+" B_X="+B.ToString("F9")); }
    return sb.ToString(); }
  static double Sum(double[] a){ double s=0; foreach(double v in a) s+=v; return s; }
}

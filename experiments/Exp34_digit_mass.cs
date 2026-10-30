using System; using System.Collections.Generic;
public static class DigB {
  static List<long> Good(int p,int N,int D){ var res=new List<long>(); long Q=1; for(int i=0;i<N*N;i++) Q*=p; var qs=new List<long>(); for(int n=1;n<=N;n++){ long q=1; for(int i=0;i<n*n;i++) q*=p; qs.Add(q);} 
    for(long s=0;s<Q;s++){ bool ok=true; foreach(long q in qs){ long r=s%q; long m=Math.Min(r,q-r); if((long)D*m>=q){ok=false;break;} } if(ok) res.Add(s);} return res; }
  static double[] Coef(List<long> S,long Q){ var c=new double[Q]; double s=S.Count; for(long j=0;j<Q;j++){ double re=0,im=0; foreach(long x in S){ double ang=2*Math.PI*(double)((j*x)%Q)/Q; re+=Math.Cos(ang); im+=Math.Sin(ang);} c[j]=(re*re+im*im)/(s*s);} return c; }
  // frequencies whose balanced mixed-radix digits all satisfy |r_n|<=R  (level 1 digit in {0,1}, level 2 in -3..4 for p=2 radix 8; general: (-alpha/2, alpha/2])
  static HashSet<long> Freqs(int p,int N,int R){ long[] q=new long[N+1]; for(int n=1;n<=N;n++){ long v=1; for(int i=0;i<n*n;i++) v*=p; q[n]=v;} long Q=q[N];
    var set=new HashSet<long>(); var cur=new List<long>(); cur.Add(0);
    for(int n=1;n<=N;n++){ long alpha=(n==1)?q[1]:q[n]/q[n-1]; long lo=-(alpha-1)/2, hi=alpha/2; if(lo<-R) lo=-R; if(hi>R) hi=R; long w=Q/q[n];
      var nxt=new List<long>(); foreach(long a in cur) for(long r=lo;r<=hi;r++){ long v=((a+r*w)%Q+Q)%Q; nxt.Add(v);} cur=nxt; }
    foreach(long a in cur) set.Add(a); return set; }
  public static string Run(int D,int N,int M,long X,int[] Rs){
    var S2=Good(2,N,D); var S3=Good(3,M,D); long Q2=1,Q3=1; for(int i=0;i<N*N;i++)Q2*=2; for(int i=0;i<M*M;i++)Q3*=3;
    var c2=Coef(S2,Q2); var c3=Coef(S3,Q3); var sb=new System.Text.StringBuilder(); double w=1.0/X;
    sb.AppendLine("D="+D+" q2="+Q2+" q3="+Q3+" X="+X);
    foreach(int R in Rs){ var U=Freqs(2,N,R); var V=Freqs(3,M,R); double B=0; long pairs=0;
      foreach(long j in U){ double t=-(double)j/Q2; t-=Math.Floor(t); double kc=t*Q3; long k0=(long)Math.Floor(kc-w*Q3)-1, k1=(long)Math.Ceiling(kc+w*Q3)+1;
        for(long k=k0;k<=k1;k++){ long kk=((k%Q3)+Q3)%Q3; if(!V.Contains(kk)) continue; double th=(double)j/Q2+(double)kk/Q3; double d=Math.Abs(th-Math.Round(th)); if(d<=w){ B+=c2[j]*c3[kk]; pairs++; } } }
      sb.AppendLine("R="+R+" |U|="+U.Count+" |V|="+V.Count+" matched pairs="+pairs+" B_R="+B.ToString("F9")); }
    return sb.ToString(); }
}

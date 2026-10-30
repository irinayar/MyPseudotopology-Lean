using System; using System.Collections.Generic; using System.Numerics;
public static class DigBig {
  static long[] Qs(int p,int N){ var q=new long[N+1]; for(int n=1;n<=N;n++){ long v=1; for(int i=0;i<n*n;i++) v*=p; q[n]=v;} return q; }
  static List<long> Freqs(int p,int N,int R,int RT){ var q=Qs(p,N); long Q=q[N]; var cur=new List<long>(); cur.Add(0);
    for(int n=1;n<=N;n++){ long alpha=(n==1)?q[1]:q[n]/q[n-1]; long lo=-(alpha-1)/2, hi=alpha/2; int rr=(n==N)?RT:R; if(lo<-rr) lo=-rr; if(hi>rr) hi=rr; long w=Q/q[n];
      var nxt=new List<long>(cur.Count*(int)(hi-lo+1)); foreach(long a in cur) for(long r=lo;r<=hi;r++){ long v=(a+r*w)%Q; if(v<0) v+=Q; nxt.Add(v);} cur=nxt; }
    return cur; }
  public static string Run(int D,int N,int M,long X,int R,int RT,double minw){
    var sb=new System.Text.StringBuilder(); long[] q2=Qs(2,N), q3=Qs(3,M); long Q2=q2[N], Q3=q3[M];
    var U=Freqs(2,N,R,RT); var V=Freqs(3,M,R,RT); sb.AppendLine("D="+D+" N="+N+" M="+M+" X="+X+" R="+R+" RT="+RT+" |U|="+U.Count+" |V|="+V.Count);
    // sort V by key = frac(-b/Q3) ; query u=frac(a/Q2): need frac(a/Q2 + b/Q3) near 0
    int nv=V.Count; var keys=new double[nv]; var idx=new int[nv]; for(int i=0;i<nv;i++){ double t=-(double)V[i]/Q3; t-=Math.Floor(t); keys[i]=t; idx[i]=i; }
    Array.Sort(keys,idx); double w=1.0/X*(1+1e-6)+1e-15; var found=new List<long[]>();
    foreach(long a in U){ double u=(double)a/Q2; double lo=u-w, hi=u+w; for(int shift=-1;shift<=1;shift++){ double l=lo+shift, h=hi+shift; int pos=Array.BinarySearch(keys,l); if(pos<0) pos=~pos; while(pos>0 && keys[pos-1]>=l) pos--; for(;pos<nv && keys[pos]<=h;pos++){ long b=V[idx[pos]]; BigInteger e=(BigInteger)a*Q3+(BigInteger)b*Q2; BigInteger N2=(BigInteger)Q2*Q3; BigInteger er=e%N2; if(er<0) er+=N2; BigInteger er2=BigInteger.Min(er,N2-er); if(er2*X<=N2) found.Add(new long[]{a,b}); } } }
    // dedupe
    var seen=new HashSet<string>(); var list=new List<long[]>(); foreach(var f in found){ string k=f[0]+","+f[1]; if(seen.Add(k)) list.Add(f); }
    double B=0; var rows=new List<string>(); foreach(var f in list){ long a=f[0], b=f[1]; double c2=FQ.Query(2,N,D,a)[0], c3=FQ.Query(3,M,D,b)[0]; double pr=c2*c3; B+=pr; if(pr>=minw){ long ja=a>Q2/2?a-Q2:a, kb=b>Q3/2?b-Q3:b; rows.Add("j="+ja+" k="+kb+" c2="+c2.ToString("G4")+" c3="+c3.ToString("G4")+" product="+pr.ToString("G5")); } }
    sb.AppendLine("matched pairs (incl zero)="+list.Count+"  partial B (sum of exact product weights)="+B.ToString("F9"));
    foreach(var r in rows) sb.AppendLine(r); return sb.ToString(); }
}

using System; using System.Collections.Generic; using System.Text;
public static class Boxes2 {
  // enumerate j values (mod Q) for balanced mixed-radix digit vectors with |r_n|<=R_n (R<0: all), returns list of j in [0,Q)
  static void Enum(int p,int n,int[] R,long[] q,List<long> outj){
    long Q=q[n]; long[] cur=new long[]{0};
    for(int l=1;l<=n;l++){ long al=q[l]/q[l-1]; long unit=Q/q[l]; int rr=R[l-1]; List<long> digs=new List<long>(); long lo=-(al-1)/2, hi=al/2; // balanced range: r in (-al/2, al/2]
      for(long r=-(al/2); r<=al/2; r++){ if(r*2<=-al) continue; if(rr>=0 && Math.Abs(r)>rr) continue; digs.Add(r); }
      long[] nxt=new long[cur.Length*digs.Count]; int t=0; foreach(long c in cur) foreach(long r in digs){ long v=(c+r*unit)%Q; if(v<0) v+=Q; nxt[t++]=v; } cur=nxt; lo=hi; }
    outj.AddRange(cur); }
  public static double Refined(int N,int M,long X,int[] R,int logB){
    long[] q2=new long[N+1], q3=new long[M+1]; q2[0]=1; q3[0]=1; for(int n=1;n<=N;n++) q2[n]=(long)Math.Pow(2,n*n); for(int m=1;m<=M;m++) q3[m]=(long)Math.Pow(3,m*m);
    int[] R2=new int[N], R3=new int[M]; for(int i=0;i<N;i++) R2[i]=R[i]; for(int i=0;i<M;i++) R3[i]=R[N+i];
    List<long> J=new List<long>(), K=new List<long>(); Enum(2,N,R2,q2,J); Enum(3,M,R3,q3,K);
    long B=1L<<logB; int[] nu=new int[B], nw=new int[B]; long Q2=q2[N], Q3=q3[M];
    foreach(long j in J){ long b=(long)((double)j/Q2*B); if(b>=B) b=B-1; nu[b]++; }
    foreach(long k in K){ long w=(Q3-k)%Q3; long b=(long)((double)w/Q3*B); if(b>=B) b=B-1; nw[b]++; }
    double s=0; for(long b=0;b<B;b++) if(nu[b]!=0&&nw[b]!=0) s+=(double)nu[b]*nw[b]; return s*2.0*B/X - 2.0*B/X; }
}
public static class BoxRun2 {
  static string Name(int[] R,int N){ StringBuilder sb=new StringBuilder(); for(int l=0;l<R.Length;l++){ sb.Append(R[l]<0?"*":R[l].ToString()); if(l<R.Length-1) sb.Append(l==N-1?" | ":","); } return sb.ToString(); }
  public static string Run(int N,int M,long X,int nRandom,int seed,int logB){
    Boxes b=new Boxes(N,M,X); int L=b.L; StringBuilder sb=new StringBuilder(); sb.AppendLine("(N,M)=("+N+","+M+") X="+X+" E="+b.E+" refined expectation with coarse overlap, bins 2^"+logB);
    int[] vals=new int[]{0,1,2,3,5,8,13,21,34,55,89,144,-1}; Random rng=new Random(seed); int used=0,tries=0; List<double> zr=new List<double>(), zi=new List<double>(); double s2r=0,s2i=0; List<string> outl=new List<string>();
    while(used<nRandom && tries<400000){ tries++; int[] box=new int[L]; for(int i=0;i<L;i++) box[i]=vals[rng.Next(vals.Length)]; double ex0=b.Expected(box); if(ex0<30||ex0>5e5) continue;
      double exr=Boxes2.Refined(N,M,X,box,logB); if(exr<30) continue; long ob=b.Count(box); double zI=(ob-ex0)/Math.Sqrt(ex0); double zR=(ob-exr)/Math.Sqrt(exr); zr.Add(zR); zi.Add(zI); s2r+=zR*zR; s2i+=zI*zI; used++; if(Math.Abs(zR)>4) outl.Add("  ["+Name(box,N)+"] obs="+ob+" indep-exp="+ex0.ToString("G5")+" refined-exp="+exr.ToString("G5")+" z_refined="+zR.ToString("F2")); }
    zr.Sort(); zi.Sort(); sb.AppendLine("random boxes used="+used+"  independent model: mean z^2="+(s2i/used).ToString("G4")+" [min "+zi[0].ToString("F1")+", max "+zi[zi.Count-1].ToString("F1")+"]   refined model: mean z^2="+(s2r/used).ToString("G4")+" [min "+zr[0].ToString("F1")+", max "+zr[zr.Count-1].ToString("F1")+"]");
    sb.AppendLine("refined outliers |z|>4: "+outl.Count); for(int i=0;i<outl.Count&&i<25;i++) sb.AppendLine(outl[i]); return sb.ToString(); }
}
public static class BoxRun3 {
  public static string Cubes(int N,int M,long X){
    Boxes b=new Boxes(N,M,X); int L=b.L; System.Text.StringBuilder sb=new System.Text.StringBuilder(); sb.AppendLine("cubes (N,M)=("+N+","+M+") X="+X);
    foreach(int R in new int[]{1,2,3,5,8,12,20,40}){ int[] box=new int[L]; for(int i=0;i<L;i++) box[i]=R; long ob=b.Count(box); double e0=b.Expected(box); double e16=Boxes2.Refined(N,M,X,box,16), e20=Boxes2.Refined(N,M,X,box,20), e24=Boxes2.Refined(N,M,X,box,24);
      sb.AppendLine("  R="+R+" obs="+ob+"  indep="+e0.ToString("G5")+"  refined(2^16)="+e16.ToString("G5")+"  refined(2^20)="+e20.ToString("G5")+"  refined(2^24)="+e24.ToString("G5")); }
    return sb.ToString(); }
}

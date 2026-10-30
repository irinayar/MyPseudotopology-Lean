using System; using System.Collections.Generic; using System.Numerics; using System.Threading.Tasks; using System.Text;
public sealed class Boxes {
  public int L; public int N, M; public long E; public double Ntot; public double[] alpha; public ushort[][] dig; public long[] jj, kk; public long Q2, Q3;
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  static void Digits(long j,int p,int n,ushort[][] dig,int off,long idx,double[] alpha,long[] q){
    long Q=q[n]; if(j>Q/2) j-=Q; long x=j; for(int l=n;l>=1;l--){ long al=q[l]/q[l-1]; long r=((x%al)+al)%al; if(r*2>al) r-=al; dig[off+l-1][idx]=(ushort)Math.Abs(r); x=(x-r)/al; } }
  public Boxes(int N_,int M_,long X){
    N=N_; M=M_; L=N+M; Q2=(long)Math.Pow(2,N*N); Q3=(long)Math.Pow(3,M*M); BigInteger NN=(BigInteger)Q2*Q3; Ntot=(double)Q2*(double)Q3; E=(long)(NN/X);
    long[] q2=new long[N+1], q3=new long[M+1]; q2[0]=1; q3[0]=1; for(int n=1;n<=N;n++) q2[n]=(long)Math.Pow(2,n*n); for(int m=1;m<=M;m++) q3[m]=(long)Math.Pow(3,m*m);
    alpha=new double[L]; for(int n=1;n<=N;n++) alpha[n-1]=q2[n]/q2[n-1]; for(int m=1;m<=M;m++) alpha[N+m-1]=q3[m]/q3[m-1];
    dig=new ushort[L][]; for(int l=0;l<L;l++) dig[l]=new ushort[E]; jj=new long[E]; kk=new long[E];
    BigInteger i3=Inv(Q3,Q2), i2=Inv(Q2,Q3); int nth=Environment.ProcessorCount;
    Parallel.For(0,nth,delegate(int t){ long j=(long)(((BigInteger)(1+t)*i3)%Q2), k=(long)(((BigInteger)(1+t)*i2)%Q3); long sj=(long)(((BigInteger)nth*i3)%Q2), sk=(long)(((BigInteger)nth*i2)%Q3);
      for(long e=1+t;e<=E;e+=nth){ long idx=e-1; jj[idx]=j; kk[idx]=k; Digits(j,2,N,dig,0,idx,alpha,q2); Digits(k,3,M,dig,N,idx,alpha,q3); j+=sj; if(j>=Q2) j-=Q2; k+=sk; if(k>=Q3) k-=Q3; } }); }
  public double Vectors(int[] R){ double v=1; for(int l=0;l<L;l++){ double c=(R[l]<0)?alpha[l]:Math.Min(alpha[l],2.0*R[l]+1); v*=c; } return v; }
  public long Count(int[] R){ long[] part=new long[64]; int nth=64; long chunk=(E+nth-1)/nth; Parallel.For(0,nth,delegate(int t){ long s=t*chunk, e=Math.Min(E,s+chunk); long c=0; for(long i=s;i<e;i++){ bool ok=true; for(int l=0;l<L;l++){ if(R[l]>=0 && dig[l][i]>R[l]){ ok=false; break; } } if(ok) c++; } part[t]=c; }); long tot=0; foreach(long c in part) tot+=c; return 2*tot; }
  public double Expected(int[] R){ return (Vectors(R)-1)*2.0*E/Ntot; }
}
public static class BoxRun {
  static string Name(int[] R){ StringBuilder sb=new StringBuilder(); for(int l=0;l<R.Length;l++){ sb.Append(R[l]<0?"*":R[l].ToString()); if(l<R.Length-1) sb.Append(l==4?" | ":","); } return sb.ToString(); }
  public static string Run(int N,int M,long X,int nRandom,int seed){
    Boxes b=new Boxes(N,M,X); int L=b.L; StringBuilder sb=new StringBuilder(); sb.AppendLine("(N,M)=("+N+","+M+") X="+X+" E="+b.E+" levels: binary 1..N then ternary 1..M ; digit bound per level (* = free)");
    int[] vals=new int[]{0,1,2,3,5,8,13,21,34,55,89,144,-1}; int[] Rs=new int[]{0,1,2,4,8,16,32,64};
    // F1: single-level restriction, others free
    sb.AppendLine("F1 single-level bound (others free): level R observed expected z");
    for(int l=0;l<L;l++) foreach(int R in Rs){ int[] box=new int[L]; for(int i=0;i<L;i++) box[i]=-1; box[l]=R; double ex=b.Expected(box); if(ex<20||b.Vectors(box)>=b.Vectors(AllFree(L))) continue; long ob=b.Count(box); sb.AppendLine("  L"+(l+1)+" R="+R+" obs="+ob+" exp="+ex.ToString("G6")+" z="+((ob-ex)/Math.Sqrt(ex)).ToString("F2")); }
    // F2: coarse-small / fine-wide and reverse, per prime
    sb.AppendLine("F2 profile boxes: name observed expected z");
    int[][] prof=new int[][]{ new int[]{1,2,4,8,16,16,16,16,16}, new int[]{16,16,16,16,1,16,16,16,2}, new int[]{4,4,4,4,4,-1,-1,-1,-1}, new int[]{-1,-1,-1,-1,-1,4,4,4,4}, new int[]{2,3,5,8,13,2,3,5,8}, new int[]{13,8,5,3,2,8,5,3,2}, new int[]{1,1,1,1,-1,1,1,1,-1}, new int[]{-1,-1,-1,-1,2,-1,-1,-1,2}, new int[]{3,5,8,13,21,34,55,89,144}, new int[]{144,89,55,34,21,13,8,5,3}, new int[]{30,30,30,30,30,3,3,3,3}, new int[]{3,3,3,3,3,30,30,30,30} };
    foreach(int[] p in prof){ int[] box=new int[L]; for(int i=0;i<L;i++) box[i]=(i<p.Length)?p[i]:-1; double ex=b.Expected(box); long ob=b.Count(box); sb.AppendLine("  ["+Name(box)+"] obs="+ob+" exp="+ex.ToString("G6")+" z="+((ob-ex)/Math.Sqrt(Math.Max(ex,1e-9))).ToString("F2")); }
    // F4: random boxes
    Random rng=new Random(seed); List<double> zs=new List<double>(); List<string> outl=new List<string>(); int used=0, tries=0; double sumZ2=0; int cntBigExcess=0;
    while(used<nRandom && tries<200000){ tries++; int[] box=new int[L]; for(int i=0;i<L;i++) box[i]=vals[rng.Next(vals.Length)]; double ex=b.Expected(box); if(ex<30||ex>2e6) continue; long ob=b.Count(box); double z=(ob-ex)/Math.Sqrt(ex); zs.Add(z); sumZ2+=z*z; used++; if(Math.Abs(z)>3.5||ob>1.3*ex+10) outl.Add("  ["+Name(box)+"] obs="+ob+" exp="+ex.ToString("G6")+" z="+z.ToString("F2")); if(ob>1.1*ex) cntBigExcess++; }
    zs.Sort(); sb.AppendLine("F4 random boxes (expected 30..2e6): used="+used+" mean z^2="+(sumZ2/Math.Max(1,used)).ToString("G4")+"  min z="+zs[0].ToString("F2")+" max z="+zs[zs.Count-1].ToString("F2")+"  boxes with obs>1.1*exp: "+cntBigExcess);
    sb.AppendLine("outliers (|z|>3.5 or obs>1.3 exp+10), up to 40:"); for(int i=0;i<outl.Count&&i<40;i++) sb.AppendLine(outl[i]); sb.AppendLine("  total outliers="+outl.Count);
    return sb.ToString(); }
  static int[] AllFree(int L){ int[] a=new int[L]; for(int i=0;i<L;i++) a[i]=-1; return a; }
}

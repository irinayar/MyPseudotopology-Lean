using System; using System.Collections.Generic; using System.Numerics; using System.Text;
public static class Struct {
  static long Gcd(long a,long b){ a=Math.Abs(a); b=Math.Abs(b); while(b!=0){ long t=a%b; a=b; b=t; } return a; }
  public static string Run(int N,int M,long X,int Rmax,int D,double[] c2,double[] c3){
    Boxes bx=new Boxes(N,M,X); int L=bx.L; long Q2=bx.Q2, Q3=bx.Q3; StringBuilder sb=new StringBuilder();
    List<long> idxs=new List<long>(); for(long i=0;i<bx.E;i++){ bool ok=true; for(int l=0;l<L;l++) if(bx.dig[l][i]>Rmax){ ok=false; break; } if(ok) idxs.Add(i); }
    sb.AppendLine("X="+X+" E="+bx.E+": positive window pairs with all digits <= "+Rmax+": "+idxs.Count+" (x2 with conjugates)");
    // group by primitive direction
    Dictionary<string,List<long>> groups=new Dictionary<string,List<long>>(); Dictionary<string,long[]> prim=new Dictionary<string,long[]>();
    foreach(long i in idxs){ long j=bx.jj[i], k=bx.kk[i]; if(j>Q2/2) j-=Q2; if(k>Q3/2) k-=Q3; long g=Gcd(j,k); if(g==0) g=1; long j0=j/g,k0=k/g; if(j0<0||(j0==0&&k0<0)){ j0=-j0; k0=-k0; } string key=j0+","+k0; if(!groups.ContainsKey(key)){ groups[key]=new List<long>(); prim[key]=new long[]{j0,k0}; } groups[key].Add(i); }
    List<string> keys=new List<string>(groups.Keys); keys.Sort(delegate(string a,string b){ return groups[b].Count.CompareTo(groups[a].Count); });
    int fam=0, single=0; double wFam=0, wSingle=0;
    sb.AppendLine("direction (j0,k0) | e0=j0*q3+k0*q2 | #pairs | multiples t | weights c2*c3 of the pairs (smooth cascade, D="+D+") | max digit");
    foreach(string key in keys){ List<long> g=groups[key]; long j0=prim[key][0], k0=prim[key][1]; BigInteger e0=(BigInteger)j0*Q3+(BigInteger)k0*Q2; double w=0; StringBuilder ts=new StringBuilder(); StringBuilder ws=new StringBuilder(); int mxd=0;
      foreach(long i in g){ long j=bx.jj[i], k=bx.kk[i]; double pr=c2[bx.jj[i]]*c3[bx.kk[i]]; w+=pr; long jb=j>Q2/2?j-Q2:j; long gg=Gcd(jb,k>Q3/2?k-Q3:k); ts.Append(gg+" "); if(ws.Length<90) ws.Append(pr.ToString("G3")+" "); for(int l=0;l<L;l++) mxd=Math.Max(mxd,bx.dig[l][i]); }
      if(g.Count>=2){ fam+=g.Count; wFam+=w; } else { single++; wSingle+=w; }
      if(g.Count>=2 || w>0.02) sb.AppendLine("  ("+j0+","+k0+") e0="+e0+" n="+g.Count+" t="+ts.ToString().Trim()+" w="+ws.ToString().Trim()+" total="+w.ToString("G4")+" maxdig="+mxd); }
    sb.AppendLine("pairs in multi-member directions: "+fam+" (weight "+wFam.ToString("G4")+"), singletons: "+single+" (weight "+wSingle.ToString("G4")+") [positive e only; double for conjugates]");
    return sb.ToString(); }
}

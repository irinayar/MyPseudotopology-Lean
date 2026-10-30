using System; using System.Text;
public static class Overlap {
  public static string Run(int D,double[] c2,double[] c3,long[] Xs,int[] logBs,double actual20){
    long Q2=c2.Length,Q3=c3.Length; double r2=0,r3=0; for(long j=0;j<Q2;j++) r2+=c2[j]; for(long k=0;k<Q3;k++) r3+=c3[k]; StringBuilder sb=new StringBuilder();
    sb.AppendLine("D="+D+" rho2="+r2.ToString("G6")+" rho3="+r3.ToString("G6")+"  rho2*rho3="+(r2*r3).ToString("G5")+"  floor 2*rho2*rho3/X for X: ");
    foreach(long X in Xs) sb.AppendLine("   X="+X+" floor="+(2*r2*r3/X).ToString("G5"));
    foreach(int lb in logBs){ long B=1L<<lb; double[] wu=new double[B], ww=new double[B];
      for(long j=0;j<Q2;j++){ long b=(long)((double)j/Q2*B); if(b>=B) b=B-1; wu[b]+=c2[j]; }
      for(long k=0;k<Q3;k++){ long w=(Q3-k)%Q3; long b=(long)((double)w/Q3*B); if(b>=B) b=B-1; ww[b]+=c3[k]; }
      double s=0; for(long b=0;b<B;b++) s+=wu[b]*ww[b]; sb.Append("  bins 2^"+lb+": collision S="+s.ToString("G6")+" (S/(rho2 rho3/B)="+(s/(r2*r3/B)).ToString("G4")+")  predicted B-1:");
      foreach(long X in Xs) sb.Append("  X="+X+": "+(2.0*B*s/X-2.0*B/X).ToString("G5")); sb.AppendLine(); }
    return sb.ToString(); }
}

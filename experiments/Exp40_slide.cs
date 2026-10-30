using System; using System.Numerics; using System.Threading.Tasks;
public static class Slide {
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  // sliding-window sums of c2[j(e)]*c3[k(e)] over all centers x in Z/N, window |e-x|<=E
  public static string Run(int D,int N,int M,long X,bool smooth,double[] c2,double[] c3){
    long Q2=c2.Length, Q3=c3.Length; long NN=Q2*Q3; long E=NN/X; long W=2*E+1;
    long i3=(long)Inv(Q3,Q2), i2=(long)Inv(Q2,Q3);
    int nth=Environment.ProcessorCount; long chunk=(NN+nth-1)/nth; double[] mx=new double[nth]; long[] arg=new long[nth]; long[] above=new long[nth]; double[] atZero=new double[1];
    double thr=1.0; // count centers whose window sum exceeds thr
    Parallel.For(0,nth,delegate(int t){ long start=t*chunk, end=Math.Min(NN,start+chunk); if(start>=end) return; long e0=start-E; // first e in buffer
      long j=(long)((((BigInteger)e0*i3)%Q2+Q2)%Q2), k=(long)((((BigInteger)e0*i2)%Q3+Q3)%Q3);
      double[] buf=new double[W]; double sum=0; long bp=0;
      for(long i=0;i<W;i++){ double v=c2[j]*c3[k]; buf[i]=v; sum+=v; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; }
      // window now covers e in [start-E, start+E]; center=start
      double best=sum; long barg=start; long ab=0; if(sum>thr) ab++;
      for(long x=start+1;x<end;x++){ double v=c2[j]*c3[k]; sum+=v-buf[bp]; buf[bp]=v; bp++; if(bp==W) bp=0; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; if(sum>best){best=sum; barg=x;} if(sum>thr) ab++; }
      mx[t]=best; arg[t]=barg; above[t]=ab; });
    double best2=0; long barg2=0; long ab2=0; for(int t=0;t<nth;t++){ if(mx[t]>best2){best2=mx[t]; barg2=arg[t];} ab2+=above[t]; }
    // value at center 0
    double z=0; { long e0=-E; long j=(long)((((BigInteger)e0*i3)%Q2+Q2)%Q2), k=(long)((((BigInteger)e0*i2)%Q3+Q3)%Q3); for(long i=0;i<W;i++){ z+=c2[j]*c3[k]; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; } }
    long cen=barg2; if(cen>NN/2) cen-=NN;
    return "D="+D+" ("+N+","+M+") "+(smooth?"smooth":"sharp")+" X="+X+" E="+E+"  window at 0 (B)="+z.ToString("G5")+"  sup over centers="+best2.ToString("G5")+" at x="+cen+"  fraction of centers with sum>1: "+((double)ab2/NN).ToString("G3")+"  mean sum="+((2*E+1)*Sum(c2)*Sum(c3)/NN).ToString("G4"); }
  static double Sum(double[] a){ double s=0; foreach(double v in a) s+=v; return s; }
}

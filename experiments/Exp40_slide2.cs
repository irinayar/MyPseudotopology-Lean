using System; using System.Numerics; using System.Threading.Tasks;
public static class Slide2 {
  static BigInteger Inv(BigInteger a, BigInteger m){ BigInteger r0=m, r1=((a%m)+m)%m, t0=0, t1=1; while(!r1.IsZero){ BigInteger qq=r0/r1; BigInteger r2=r0-qq*r1; r0=r1; r1=r2; BigInteger t2=t0-qq*t1; t0=t1; t1=t2; } return ((t0%m)+m)%m; }
  // split each atom weight into heavy (>=eta) and light (<eta); sliding-window sums of each
  public static string Run(int D,long X,double eta,double[] c2,double[] c3){
    long Q2=c2.Length, Q3=c3.Length; long NN=Q2*Q3; long E=NN/X; long W=2*E+1; long i3=(long)Inv(Q3,Q2), i2=(long)Inv(Q2,Q3);
    int nth=Environment.ProcessorCount; long chunk=(NN+nth-1)/nth; double[] mxL=new double[nth], mxH=new double[nth]; long[] aL=new long[nth], aH=new long[nth]; double[] sumL=new double[nth]; double[] sumH=new double[nth]; long[] nH=new long[nth];
    Parallel.For(0,nth,delegate(int t){ long start=t*chunk, end=Math.Min(NN,start+chunk); if(start>=end) return; long e0=start-E;
      long j=(long)((((BigInteger)e0*i3)%Q2+Q2)%Q2), k=(long)((((BigInteger)e0*i2)%Q3+Q3)%Q3);
      double[] bl=new double[W], bh=new double[W]; double sl=0, sh=0; long bp=0;
      for(long i=0;i<W;i++){ double v=c2[j]*c3[k]; if(v>=eta){ bh[i]=v; sh+=v; } else { bl[i]=v; sl+=v; } j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; }
      double ml=sl, mh=sh; long al=start, ah=start; double accL=sl, accH=sh; long cnt=1; long nh=0;
      for(long x=start+1;x<end;x++){ double v=c2[j]*c3[k]; double nl=0,nhh=0; if(v>=eta) nhh=v; else nl=v; sl+=nl-bl[bp]; sh+=nhh-bh[bp]; bl[bp]=nl; bh[bp]=nhh; bp++; if(bp==W) bp=0; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3;
        if(sl>ml){ml=sl; al=x;} if(sh>mh){mh=sh; ah=x;} accL+=sl; accH+=sh; cnt++; if(sh>0.5) nh++; }
      mxL[t]=ml; mxH[t]=mh; aL[t]=al; aH[t]=ah; sumL[t]=accL/cnt; sumH[t]=accH/cnt; nH[t]=nh; });
    double ml2=0,mh2=0; long al2=0,ah2=0; double mL=0,mH=0; long nh2=0; for(int t=0;t<nth;t++){ if(mxL[t]>ml2){ml2=mxL[t];al2=aL[t];} if(mxH[t]>mh2){mh2=mxH[t];ah2=aH[t];} mL+=sumL[t]/nth; mH+=sumH[t]/nth; nh2+=nH[t]; }
    // value at center 0, split
    double z0L=0,z0H=0; { long e0=-E; long j=(long)((((BigInteger)e0*i3)%Q2+Q2)%Q2), k=(long)((((BigInteger)e0*i2)%Q3+Q3)%Q3); for(long i=0;i<W;i++){ double v=c2[j]*c3[k]; if(v>=eta) z0H+=v; else z0L+=v; j+=i3; if(j>=Q2) j-=Q2; k+=i2; if(k>=Q3) k-=Q3; } }
    return "D="+D+" X="+X+" E="+E+" eta="+eta+" | at 0: heavy="+z0H.ToString("G4")+" light="+z0L.ToString("G4")+" | light: mean="+mL.ToString("G4")+" sup="+ml2.ToString("G4")+" (sup/mean="+(ml2/mL).ToString("G3")+") | heavy: mean="+mH.ToString("G3")+" sup="+mh2.ToString("G4")+" at x="+(ah2>NN/2?ah2-NN:ah2)+"  #centers with heavy>0.5: "+nh2; }
}

using System; using System.Collections.Generic; using System.Numerics;
public static class ZoneMass {
  static double Sinc2(double x){ if(x==0) return 1; double v=Math.Sin(Math.PI*x)/(Math.PI*x); return v*v; }
  public static string Run(int D,int Nmax,int Rmax,double K){
    var sb=new System.Text.StringBuilder(); var rows=new List<string>(); var vals=new List<double>(); var valsEnd=new List<double>();
    BigInteger[] P2=new BigInteger[Nmax+2], P3=new BigInteger[Nmax+2]; for(int n=0;n<=Nmax+1;n++){ P2[n]=BigInteger.Pow(2,n*n); P3[n]=BigInteger.Pow(3,n*n); }
    for(int N=3;N<=Nmax;N++) for(int M=2;M<=Nmax;M++){
      double l2=N*N*Math.Log10(2), l3=M*M*Math.Log10(3); double lq=Math.Max(l2,l3); double lnext=Math.Min((N+1)*(N+1)*Math.Log10(2),(M+1)*(M+1)*Math.Log10(3))-Math.Log10(D); double lxlo=lq+Math.Log10(K); if(lnext<=lxlo) continue;
      double Sstart=0,Send=0; string best=""; double bw=0;
      for(int n=1;n<=N;n++){ BigInteger qn=P2[n]; double ln=BigInteger.Log10(qn); double an=(n==1)?2:Math.Pow(2,2*n-1); double rmaxn=Math.Min(Rmax,an/2);
        for(int m=1;m<=M;m++){ BigInteger qm=P3[m]; double lm=BigInteger.Log10(qm); double am=(m==1)?3:Math.Pow(3,2*m-1); double kmax=Math.Min(Rmax,am/2); if(ln+lm<lxlo) continue; // need qn*qm >= X
          for(int r=1;r<=rmaxn;r++){ BigInteger num=BigInteger.Multiply(r,qm); BigInteger k0=-(BigInteger.Divide(num*2+qn,qn*2));
            for(int d=-1;d<=1;d++){ BigInteger k=k0+d; if(k.IsZero || (double)BigInteger.Abs(k)>kmax) continue; BigInteger e=BigInteger.Abs(num+k*qn); if(e.IsZero) continue;
              double lInv=ln+lm-BigInteger.Log10(e); double w=Sinc2(2.0*r/D)*Sinc2(2.0*(double)k/D);
              if(lInv>=lxlo){ Sstart+=2*w; if(w>bw){bw=w; best="(n="+n+",m="+m+",r="+r+",k="+k+",1/th=1e"+lInv.ToString("F1")+")";} } if(lInv>=lnext) Send+=2*w; } } } }
      vals.Add(Sstart); valsEnd.Add(Send); rows.Add("N="+N+" M="+M+" zone 1e"+lxlo.ToString("F1")+"..1e"+lnext.ToString("F1")+" S_single(start)="+Sstart.ToString("G4")+" S_single(end)="+Send.ToString("G4")+" top "+best+" w="+bw.ToString("G3"));
    }
    sb.AppendLine("D="+D+" K="+K+" Rmax="+Rmax+" pairs="+vals.Count);
    var idx=new List<int>(); for(int i=0;i<vals.Count;i++) idx.Add(i); idx.Sort(delegate(int a,int b){ return vals[b].CompareTo(vals[a]); });
    for(int t=0;t<Math.Min(8,idx.Count);t++) sb.AppendLine(rows[idx[t]]);
    var sorted=new List<double>(vals); sorted.Sort(); int cnt=sorted.Count; sb.AppendLine("quantiles of S_single(start): median="+sorted[cnt/2].ToString("G3")+" 90%="+sorted[(int)(cnt*0.9)].ToString("G3")+" max="+sorted[cnt-1].ToString("G3")+" ; #pairs with S>0.001: "+sorted.FindAll(delegate(double v){return v>0.001;}).Count);
    var se=new List<double>(valsEnd); se.Sort(); sb.AppendLine("S_single(end): max="+se[cnt-1].ToString("G3")+" ; #pairs with S>0.001: "+se.FindAll(delegate(double v){return v>0.001;}).Count);
    return sb.ToString(); }
}


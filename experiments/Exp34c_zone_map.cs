using System; using System.Collections.Generic; using System.Numerics;
public static class Zone {
  static double Sinc2(double x){ if(x==0) return 1; double v=Math.Sin(Math.PI*x)/(Math.PI*x); return v*v; }
  public static string Run(int D,int Nmax,int J,double K,double wmin){
    var sb=new System.Text.StringBuilder(); sb.AppendLine("D="+D+" J="+J+" K="+K+" wmin="+wmin+"  (N,M): zone [K*qmax, min(next)/D] in log10, polluted-at-top resonances (j,k,weight,log10(1/theta))");
    int total=0, polluted=0, pollutedAny=0;
    for(int N=3;N<=Nmax;N++){ BigInteger q2=BigInteger.Pow(2,N*N); double l2=N*N*Math.Log10(2);
      for(int M=2;M<=Nmax;M++){ BigInteger q3=BigInteger.Pow(3,M*M); double l3=M*M*Math.Log10(3);
        double lq=Math.Max(l2,l3); double lnext=Math.Min((N+1)*(N+1)*Math.Log10(2),(M+1)*(M+1)*Math.Log10(3))-Math.Log10(D);
        double lxlo=lq+Math.Log10(K); if(lnext<=lxlo) continue; total++;
        var res=new List<string>(); bool top=false, any=false;
        for(int j=1;j<=J;j++){ // k near -j*q3/q2
          BigInteger num=BigInteger.Multiply(j,q3); BigInteger kk=-(BigInteger.Divide(num*2+q2,q2*2)); // round(-j q3/q2)
          for(int d=-1;d<=1;d++){ BigInteger k=kk+d; if(BigInteger.Abs(k)>J*4) continue; BigInteger e=BigInteger.Abs(num+k*q2); if(e.IsZero) continue;
            double le=BigInteger.Log10(e)-l2-l3; // log10 theta
            double w=Sinc2(2.0*j/D)*Sinc2(2.0*(double)k/D); if(w<wmin) continue; double lInvTheta=-le;
            if(lInvTheta>=lxlo) any=true;
            if(lInvTheta>=lnext){ top=true; res.Add("("+j+","+k+",w="+w.ToString("G2")+",1/th=1e"+lInvTheta.ToString("F1")+")"); } } }
        if(any) pollutedAny++; if(top){ polluted++; if(polluted<=40) sb.AppendLine("N="+N+" M="+M+" zone 1e"+lxlo.ToString("F1")+"..1e"+lnext.ToString("F1")+" : "+string.Join(" ",res.ToArray())); } } }
    sb.AppendLine("pairs with nonempty zone: "+total+" ; with a resonance (weight>=wmin) in window somewhere in the zone: "+pollutedAny+" ; polluted through the whole zone (in window even at the zone top): "+polluted);
    return sb.ToString(); }
}

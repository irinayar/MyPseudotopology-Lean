using System; using System.Collections.Generic; using System.Numerics;
public static class DigitCount {
  static Dictionary<string,BigInteger> memo;
  static BigInteger F(int p,int D,int n,BigInteger y){
    if(n==0) return y;
    string key=n+":"+y; BigInteger v; if(memo.TryGetValue(key,out v)) return v;
    BigInteger q=BigInteger.Pow(p,n*n), T=(q-1)/D, a=BigInteger.Divide(y,q), t=y-a*q;
    BigInteger R=F(p,D,n-1,T+1)+F(p,D,n-1,q)-F(p,D,n-1,q-T);
    BigInteger r=a*R+F(p,D,n-1,BigInteger.Min(t,T+1))+F(p,D,n-1,BigInteger.Max(t,q-T))-F(p,D,n-1,q-T);
    memo[key]=r; return r;
  }
  public static BigInteger Count(int p,int D,BigInteger X){
    memo=new Dictionary<string,BigInteger>();
    int N=0; while(BigInteger.Pow(p,(N+1)*(N+1))<=D*X) N++;
    return F(p,D,N,X+1);
  }
  public static string Run(){
    var sb=new System.Text.StringBuilder();
    int[][] chk=new int[][]{ new int[]{20,9}, new int[]{10,9}, new int[]{20,8}, new int[]{10,8}};
    foreach(var c in chk){ BigInteger X=BigInteger.Pow(10,c[1]); sb.AppendLine("D="+c[0]+" X=1e"+c[1]+" a="+Count(3,c[0],X)+" b="+Count(2,c[0],X)); }
    int[] Ds={20,50,100,200,500};
    foreach(int D in Ds){ for(int e=6;e<=60;e++){ BigInteger X=BigInteger.Pow(10,e); BigInteger a=Count(3,D,X), b=Count(2,D,X);
        double lam=Math.Exp(BigInteger.Log(a)+BigInteger.Log(b)-BigInteger.Log(2*X+1));
        if(lam>=10){ sb.AppendLine("D="+D+" first lambda>=10 at X=1e"+e+" lambda="+lam.ToString("F3")); break; } } }
    return sb.ToString();
  }
}

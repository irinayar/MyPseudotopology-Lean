import java.io.*; import java.util.*;
/** Exp16b: as Exp16, then classify final intervals by nearest rational a/q (q<=Q) and distance. */
public class Exp16b {
  static double pk(long k){ double m=0; for(long base: new long[]{2,3}) for(long n=1;;n++){ long q=1; boolean big=false; for(long i=0;i<n*n;i++){ if(q>Long.MAX_VALUE/base){big=true;break;} q*=base; } double t=0; if(!big){ long r=k%q; long s=Math.min(r,q-r); t=(double)s/(double)q;} if(t>m)m=t; if(big||q>2*k)break; } return m; }
  public static void main(String[] a) throws Exception {
    double C=Double.parseDouble(a[1]); int Q=Integer.parseInt(a[2]); double far=Double.parseDouble(a[3]);
    ArrayList<Long> K=new ArrayList<>(); try(BufferedReader br=new BufferedReader(new FileReader(a[0]))){ br.readLine(); String ln; while((ln=br.readLine())!=null) K.add(Long.parseLong(ln.split(",")[0])); }
    Collections.sort(K);
    ArrayList<double[]> cur=new ArrayList<>(); cur.add(new double[]{0,1});
    for(long k: K){ double c=C*pk(k); if(c>=0.5) continue; ArrayList<double[]> nxt=new ArrayList<>();
      for(double[] iv: cur){ long j0=(long)Math.floor(k*iv[0]-c), j1=(long)Math.ceil(k*iv[1]+c); for(long j=j0;j<=j1;j++){ double lo=Math.max(iv[0],(j-c)/k), hi=Math.min(iv[1],(j+c)/k); if(lo<=hi) nxt.add(new double[]{lo,hi}); } }
      nxt.sort((p,q)->Double.compare(p[0],q[0])); ArrayList<double[]> m=new ArrayList<>(); for(double[] iv: nxt){ if(!m.isEmpty() && iv[0]<=m.get(m.size()-1)[1]+1e-15) m.get(m.size()-1)[1]=Math.max(m.get(m.size()-1)[1],iv[1]); else m.add(iv); }
      cur=m; if(cur.size()>3000000){ System.out.println("too many at k="+k); return; } }
    System.out.println("C="+C+" final intervals="+cur.size());
    TreeMap<Integer,Integer> byQ=new TreeMap<>(); int exotic=0; ArrayList<String> ex=new ArrayList<>();
    for(double[] iv: cur){ double mid=(iv[0]+iv[1])/2; double best=9; int bq=0; long bp=0; for(int q=1;q<=Q;q++){ long p=Math.round(mid*q); double d=Math.abs(mid-(double)p/q); if(d<best-1e-18){best=d;bq=q;bp=p;} }
      if(best<far){ // reduce fraction
        long g=gcd(bp,bq); int qq=(int)(bq/g); byQ.merge(qq,1,Integer::sum); } else { exotic++; if(ex.size()<40) ex.add(String.format("%.12f (nearest %d/%d dist %.2e, width %.1e)",mid,bp,bq,best,iv[1]-iv[0])); } }
    System.out.println("near-rational (dist<"+far+", q<="+Q+") by reduced denominator: "+byQ);
    System.out.println("exotic survivors (dist>="+far+"): "+exotic); for(String s: ex) System.out.println("   "+s);
  }
  static long gcd(long x,long y){ x=Math.abs(x); while(y!=0){ long t=x%y; x=y; y=t;} return x==0?1:x; }
}

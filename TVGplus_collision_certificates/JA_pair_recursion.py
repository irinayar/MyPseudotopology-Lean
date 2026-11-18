
from pathlib import Path
from functools import lru_cache
import json,time
root=Path(r'C:\Users\Irina\OneDrive\Documents\Irina\MyPseudotopology')
work=root/'tmp/mixed_prime_research'
def pair_counter(p,D,h):
 assert D>=2 and h>=0
 @lru_cache(None)
 def modulus(n):return p**(n*n)
 def cyclic_interval(start,length,q):
  assert 0<length<=q
  start%=q
  if start+length<=q:return [(start,start+length)]
  return [(0,start+length-q),(start,q)]
 @lru_cache(None)
 def allowed(n):
  q=modulus(n);T=(q-1)//D;L=2*T+1
  I=cyclic_interval(-T,L,q);J=cyclic_interval(-T-h,L,q)
  K=[]
  for l,u in I:
   for v,w in J:
    a,b=max(l,v),min(u,w)
    if a<b:K.append((a,b))
  K.sort();out=[]
  for l,u in K:
   if out and l<=out[-1][1]:out[-1]=(out[-1][0],max(u,out[-1][1]))
   else:out.append((l,u))
  return tuple(out)
 @lru_cache(None)
 def full(n):
  if n==0:return 1
  return sum(prefix(n-1,u)-prefix(n-1,l) for l,u in allowed(n))
 @lru_cache(None)
 def prefix(n,Y):
  if Y<=0:return 0
  if n==0:return Y
  a,r=divmod(Y,modulus(n))
  return a*full(n)+sum(prefix(n-1,min(r,u))-prefix(n-1,min(r,l)) for l,u in allowed(n))
 def count(X):
  if h>X:return 0
  n=0
  while modulus(n+1)<=D*X:n+=1
  return prefix(n,X-h+1)
 count.stats=lambda: {'prefix_states':prefix.cache_info().currsize,'period_states':full.cache_info().currsize,'mask_states':allowed.cache_info().currsize}
 return count
def norm_good(k,p,D):
 n=1
 while p**(n*n)<=D*abs(k):
  q=p**(n*n);r=k%q
  if D*min(r,q-r)>=q:return False
  n+=1
 return True
def mixed_candidates(D,X):
 assert D%2==0
 d=D//2;qs=[]
 for p in (2,3):
  n=1
  while p**(n*n)<=d*X:qs.append(p**(n*n));n+=1
 qs=sorted(qs);k=0;steps=0
 while k<=X:
  steps+=1;best=k;failed=False
  for q in qs:
   T=(q-1)//d;s=k%q
   if T<s<q-T:failed=True;best=max(best,k+q-T-s)
  if failed:k=best
  else:yield k;k+=1
def validate():
 cases=0
 for p in (2,3,5):
  for D in (2,3,4,10,20,50):
   for X in (0,1,7,31,100,300):
    A={k for k in range(X+1) if norm_good(k,p,D)}
    for h in sorted({0,1,2,X//3,X//2,X}):
     got=pair_counter(p,D,h)(X);want=sum(x+h in A for x in A)
     assert got==want,(p,D,X,h,got,want)
     cases+=1
 return cases
if __name__=='__main__':
 start=time.monotonic()
 cases=validate();print('Exact pair-recursion small checks',cases,flush=True)
 rows=[]
 for D,X in [(20,2**18),(20,2**20),(20,10**9)]:
  a,b=pair_counter(3,D,0)(X),pair_counter(2,D,0)(X)
  E=0;candidate_count=0;nonzero_pairs=0;terms=[]
  for h in mixed_candidates(D,X):
   candidate_count+=1
   ra,rb=pair_counter(3,D,h)(X),pair_counter(2,D,h)(X)
   term=ra*rb*(1 if h==0 else 2);E+=term
   if term:nonzero_pairs+=1;terms.append((h,ra,rb))
  row={'D':D,'X':X,'a':a,'b':b,'energy':str(E),'candidate_shifts':candidate_count,'nonzero_shift_terms_including_zero':nonzero_pairs,'C_numerator':str((2*X+1)*E),'C_denominator':str((a*b)**2),'C_approx':(2*X+1)*E/(a*b)**2,'off_diagonal_energy':str(E-a*b)}
  rows.append(row)
  print(json.dumps(row),flush=True)
  (work/f'JA_pair_terms_D{D}_X{X}.json').write_text(json.dumps(terms),encoding='utf-8')
 (work/'JA_pair_recursion_results.json').write_text(json.dumps({'small_direct_checks':cases,'rows':rows,'elapsed_seconds':time.monotonic()-start},indent=2),encoding='utf-8')
 print('DONE seconds',time.monotonic()-start,flush=True)

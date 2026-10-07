import random, math
from math import isqrt
def iroot(n,p):
    lo,hi=0,1<<(n.bit_length()//p+2)
    while lo+1<hi:
        m=(lo+hi)//2
        if m**p<=n: lo=m
        else: hi=m
    return lo
def check(n):
    k=iroot(n,6); b=k; w=8*k+8; h0=32*k*k+64; s=(n-h0)//(2*k); h=n-2*k*s; h1=16*k*k+64
    L=s-w-2; u=(L-h1)//k; L2=u-w-2; ell=isqrt(L2)//8; t=L2//ell; J=ell-1
    rem=L-h1-k*u
    ok=dict(
      k256=k>=256, k6=k**6<=n<2*k**6, s=(4*s>=k**5 and s<=k**5), u=(16*u>=k**4 and u<=k**4),
      t=k*k<=t<=16*k*k, h=h<=33*k*k, h1=h1<=17*k*k, smku=s-k*u<=18*k*k, rem=0<=rem<k,
      tl=t>=16*ell+32, tw=t+w+10<=u, hw=h1+w+10<=s, hub=h>=h0,
      deferred=s*s-k*k*(u*(u-w)-6)<=51*s*k*k)
    # E3 with real harmonic bounds
    Hb=1+math.log(b*b); Hl=1+math.log(max(J,1))
    E=(n*n*k*k+n*n*b*b+n*n*t+n**3/(k*b*t)+n*n*k*Hb+n*n*b*Hl+n*n*k/b*Hb*Hl)
    ok['E3']=E<=35*n**(7/3)
    return ok, E/n**(7/3)
rng=random.Random(3); worst=0; bad=[]
ns=[2**48,2**48+1,257**6-1,257**6,2*256**6-1]+[rng.randrange(2**48,2**200) for _ in range(3000)]+[(m**6) for m in range(256,4000,37)]+[(2*m**6-1) for m in range(256,4000,37)]
for n in ns:
    ok,r=check(n); worst=max(worst,r)
    f=[key for key,v in ok.items() if not v]
    if f: bad.append((n.bit_length(),f))
print(len(ns),"cases; failures:",len(bad),bad[:8]); print("max E3/n^(7/3) =",round(worst,2))

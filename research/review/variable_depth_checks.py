from fractions import Fraction as F
import random, sys, itertools
import os; sys.path.insert(0,os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','variable_depth'))
import verify_variable_depth as V
H={}
def harm(k):
    if k not in H: H[k]=sum((F(1,i) for i in range(1,k+1)),F())
    return H[k]
# 1. productive identity 2*sum_x d(z,x) = 4n floor(n^2/4)
for n in range(1,40):
    c=n//2
    s=sum(abs(i-c)+abs(j-c) for i in range(n) for j in range(n))
    assert 2*s==4*n*(n*n//4)<=n**3,(n)
print("identity ok")
# 2. H_{b^2}/b <1 for b>=3 (to 60), <=1/2 for b>=16
for b in range(3,61):
    h=harm(b*b); assert h<b
    if b>=16: assert 2*h<=b
print("harmonic ok")
# 3. recurrence with REAL harmonic numbers, real sides: simulate W_{i+1}=9b n^2+rho W_i (worst case equality)
rng=random.Random(1)
worst=F(0)
for trial in range(3000):
    r=rng.randrange(1,40)
    bs=[rng.choice([16,16,17,20,32,64,100]) for _ in range(r)]
    h=F(rng.randrange(0,300),rng.randrange(1,7))
    w=F(18*bs[0]); mid=F(0)
    for i in range(1,r):
        mid+=harm(bs[i]**2)*w
        w=9*bs[i]+harm(bs[i]**2)/bs[i]*w
    lhs=mid+h*w; S=sum(b*b for b in bs)
    assert lhs<=27*S+18*h*h
    worst=max(worst,lhs/(27*S+18*h*h))
print("recurrence ok, worst ratio",float(worst))
# 4. geometry at the edge of admissibility and random n
cnt=0
for L in list(range(2,40))+[60,90]:
    base=(1<<20)*16**(L+3)
    for n in [base,base+1,base*2-1,(1<<20)*17**(L+3)-1,(1<<20)*17**(L+3)]+[rng.randrange(base,base*1000) for _ in range(20)]:
        V.geometry(n,L); cnt+=1
print("geometry ok",cnt)
# below threshold must be rejected
try: V.geometry((1<<20)*16**5-1,2); print("NO REJECT")
except ValueError: print("below threshold rejected")

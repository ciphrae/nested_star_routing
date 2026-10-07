#!/usr/bin/env python3
"""Exact-integer checks of candidate rounded three-level dimensions.
The universal estimates are proved in the notes; these are finite tests.
"""
from __future__ import annotations
import argparse,json,math,random
from pathlib import Path


def root_floor(n:int,power:int)->int:
    lo=0;hi=1<<((n.bit_length()+power-1)//power)
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**power<=n:lo=mid
        else:hi=mid
    return lo


def dimensions(n:int)->dict:
    if n<2**48:raise ValueError('candidate asymptotic range starts at 2^48')
    k=root_floor(n,6);w=8*k+8;h0=32*k*k+64
    s=(n-h0)//(2*k);h=n-2*k*s
    h1=16*k*k+64;L=s-w-2;u=(L-h1)//k;delta=L-h1-k*u
    L2=u-w-2;ell=math.isqrt(L2)//8;t=L2//ell;J=ell-1
    assert k>=256 and k**6<=n<=(2*k**6)
    assert 4*s>=k**5 and s<=k**5
    assert 16*u>=k**4 and u<=k**4
    assert k*k<=t<=16*k*k
    assert 0<=delta<k and 2*k*s<=n and k*u<=s
    assert h<=33*k*k and h1<=17*k*k and s-k*u<=18*k*k
    assert t>=16*ell+32 and ell>=2 and ell*t<=L2
    assert t+w+10<=u and h1+w+10<=s and k*k<=s
    assert J<=k*k
    # Rounding/strip/marker area inequality used in the middle cost account.
    lost=s*s-k*k*(u*(u-w)-6)
    assert lost<=51*s*k*k
    return {'n':str(n),'k':k,'large_side':s,'middle_hub_side':h1,
            'small_side':u,'leaf_block_side':t,'leaf_pairs':J,'middle_fringe':delta}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output');a=ap.parse_args()
    rng=random.Random(730026);values={2**48}
    for k in [256,257,300,511,512,1024,4096,65536,10**9,10**18]:
        values.update([k**6,k**6+1,(k+1)**6-1])
    for bits in range(48,241):
        values.add((1<<bits)+rng.randrange(1<<bits))
    rows=[dimensions(n) for n in sorted(values)]
    result={'all_passed':True,'cases':len(rows),
            'scope':'Finite exact-integer parameter tests; not a proof of routing or a universal theorem.',
            'results':rows}
    if a.output:Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
if __name__=='__main__':main()

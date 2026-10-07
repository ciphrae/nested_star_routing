#!/usr/bin/env python3
"""Exact exhaustive checks of the running-maximum credit lemma.

States contain source returns, real admissions, and historical nonnegative
credit maxima. This tests a finite counter abstraction, not puzzle moves.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def check(population: tuple[int,...], budget: int) -> dict:
    j=len(population);h=sum((Fraction(1,i) for i in range(1,j+1)),Fraction())
    zero=(0,)*j;start=(zero,zero,zero)
    seen={start};todo=deque([start]);transitions=0;largest_peak_sum=0
    while todo:
        S,D,peak=todo.popleft()
        credit=tuple(S[i]-D[i] for i in range(j))
        active=[i for i in range(j) if S[i]<population[i]]
        assert sum(credit)<=budget
        assert sum(peak)<=j+budget*h
        for i in active:
            assert len(active)*(peak[i]-1)<=budget
        largest_peak_sum=max(largest_peak_sum,sum(peak))
        least=min((credit[i] for i in active),default=0)
        for i in range(j):
            for input_real,output_real in product((0,1),repeat=2):
                if input_real==output_real==0:continue  # identical counter state
                if input_real and D[i]==population[i]:continue
                if output_real and S[i]==population[i]:continue
                if not input_real and (i not in active or credit[i]!=least):continue
                ns=list(S);nd=list(D)
                ns[i]+=output_real;nd[i]+=input_real
                nc=tuple(ns[a]-nd[a] for a in range(j))
                if sum(nc)>budget:continue
                np=tuple(max(peak[a],nc[a]) for a in range(j))
                nxt=(tuple(ns),tuple(nd),np);transitions+=1
                assert sum(np)<=j+budget*h
                if nxt not in seen:seen.add(nxt);todo.append(nxt)
    return {'population':population,'total_credit_cap':budget,'states':len(seen),
            'transitions':transitions,'largest_observed_sum_of_peaks':largest_peak_sum,
            'proved_allowance':str(j+budget*h)}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output');a=ap.parse_args()
    cases=[(p,b) for p in [(1,),(2,),(1,1),(2,2),(1,2,3),(2,2,2),(1,1,1,1),(2,2,2,2)] for b in range(5)]
    rows=[check(p,b) for p,b in cases]
    result={'scope':'Exhaustive finite counter model, not a universal or physical-slide proof.',
            'cases':len(rows),'states':sum(r['states'] for r in rows),
            'transitions':sum(r['transitions'] for r in rows),'all_passed':True,'results':rows}
    if a.output:Path(a.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
if __name__=='__main__':main()

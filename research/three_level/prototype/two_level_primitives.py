#!/usr/bin/env python3
"""Independent one-board replay of the ordinary nested algorithm.

Adjacent walks and fixed gate words are expanded literally. Three-cycles
and even sorting permutations use their proved exact endpoint effects and
200*side-per-cycle upper bounds. These are finite regression tests, not a
universal proof or a Lean check.
"""
from __future__ import annotations
import argparse, json, random, time
from collections import Counter

REFILL='RDLUR'
IDLE='RDLDDRUULDRUULDDRDL'
PRODUCTIVE='DDDRULURDDLUUURDLDRUULDDRULDD'


def elbow(r0,c,r,f):
    return [(y,c) for y in range(r0,r+1)]+[(r,x) for x in range(c+1,f+1)]


def parity(values):
    seen=set(); sign=0
    for x in range(len(values)):
        if x in seen: continue
        y=x; length=0
        while y not in seen:
            seen.add(y); length+=1; y=values[y]
        sign^=(length-1)&1
    return sign


class Board:
    def __init__(self,n):
        self.n=n; self.a=list(range(n*n)); self.pos=self.a.copy()
        self.blank_label=n*n-1; self.blank=n*n-1
        self.cost=0; self.slides=0; self.cycles=0; self.sorts=0
    def swap(self,x,y):
        ax,ay=self.a[x],self.a[y]
        self.a[x],self.a[y]=ay,ax; self.pos[ax],self.pos[ay]=y,x
    def move(self,y):
        x=self.blank; n=self.n
        assert abs(x//n-y//n)+abs(x%n-y%n)==1,(x,y)
        self.swap(x,y); self.blank=y; self.cost+=1; self.slides+=1
    def walk(self,path):
        assert self.blank==path[0],(self.blank,path[0])
        for x in path[1:]: self.move(x)
    def word(self,code,view):
        r=c=0; assert self.blank==view(r,c)
        for d in code:
            dr,dc={'U':(-1,0),'D':(1,0),'L':(0,-1),'R':(0,1)}[d]
            r+=dr; c+=dc; self.move(view(r,c))
    def cycle(self,points,square):
        assert len(set(points))==3 and self.blank not in points
        assert all(square.contains(x) for x in [self.blank,*points])
        x,y,z=points
        self.swap(x,y); self.swap(x,z) # old x goes to y, old y to z
        self.cost+=200*square.side; self.cycles+=1
    def double(self,e,q,u,v,square):
        assert len({e,q,u,v})==4 and self.blank not in {e,q,u,v}
        assert all(square.contains(x) for x in [self.blank,e,q,u,v])
        self.swap(e,q); self.swap(u,v)
        self.cost+=400*square.side; self.cycles+=2
    def arrange(self,cells,prescribed,free,square):
        cells=sorted(cells); free=sorted(free)
        assert self.blank not in cells and square.contains(self.blank)
        assert all(square.contains(x) for x in cells)
        assert set(prescribed).isdisjoint(free)
        assert set(prescribed)|set(free)==set(cells)
        old=[self.a[x] for x in cells]
        remaining=sorted(set(old)-set(prescribed.values()))
        assert len(remaining)==len(free)
        want=dict(prescribed); want.update(zip(free,remaining))
        lookup={v:i for i,v in enumerate(old)}
        perm=[lookup[want[x]] for x in cells]
        if parity(perm):
            assert len(free)>=2,'odd fully prescribed endpoint'
            x,y=free[:2]; want[x],want[y]=want[y],want[x]
        assert parity([lookup[want[x]] for x in cells])==0
        for x in cells: self.a[x]=want[x]; self.pos[want[x]]=x
        self.cost+=200*square.side*len(cells); self.sorts+=1


class View:
    def __init__(self,board,side,origin=(0,0),sr=1,sc=1):
        self.B=board; self.side=side; self.r,self.c=origin; self.sr=sr; self.sc=sc
    def cell(self,r,c):
        rr=self.r+self.sr*r; cc=self.c+self.sc*c
        assert 0<=rr<self.B.n and 0<=cc<self.B.n,(rr,cc)
        return rr*self.B.n+cc
    def local(self,x):
        return self.sr*(x//self.B.n-self.r), self.sc*(x%self.B.n-self.c)
    def contains(self,x):
        r,c=self.local(x); return 0<=r<self.side and 0<=c<self.side
    def sub(self,r,c,side):
        x=self.cell(r,c)
        return View(self.B,side,divmod(x,self.B.n),self.sr,self.sc)
    def path(self,points): return [self.cell(*x) for x in points]


class Spoke:
    def __init__(self,view,y0,ci,yi,f):
        self.view=view; self.ci=ci; self.y0=y0; self.yi=yi; self.f=f
        self.I=view.path(elbow(y0,ci,yi,f))
        self.O=view.path(elbow(y0,ci+3,yi-3,f))
        self.D=view.cell(y0-1,ci+2); self.C=view.cell(y0-1,ci+1)
        self.gates={}; self.S=0; self.Dcount=0; self.Hinputs=0; self.Hreturns=0
    def endpoint_word(self,B,word,column):
        B.word(word,lambda r,c:self.view.cell(self.yi-r,column+c))
    def hub_word(self,B):
        B.word(PRODUCTIVE,lambda r,c:self.view.cell(self.y0-c,self.ci+3-r))


class Inner:
    def __init__(self,parent):
        self.p=parent; self.B=parent.B; self.v=parent.view.sub(parent.w+2,2,parent.L)
        self.hub=self.v.sub(0,0,parent.t); t=parent.t; ell=parent.ell
        self.P=self.v.cell(t//2,t//2+1); self.E=self.v.cell(t//2,t//2)
        self.entry=self.v.cell(0,0); self.live=set(); self.accepted=set(); self.tokens={}
        self.spokes=[]; self.goal={}; self.blocks=[]; self.services=0; self.productive=0; self.refills=0
        for i in range(1,ell):
            sp=Spoke(self.v,t-1,t-8*i,i*t+5,ell*t-2)
            for j in range(1,ell):
                block=self.v.sub(i*t,j*t,t)
                reservoir={block.cell(r,c) for r in [1,3,4,6,*range(8,t)] for c in range(t)}
                core={block.cell(r,c) for r in range(8,t) for c in range(t)}
                U={self.B.a[x] for x in core}; self.live.update(U)
                gate={'block':block,'reservoir':reservoir,'core':core,'U':U,'F':set(),
                      'column':j*t+t//2,'spoke':sp}
                col=gate['column']; gate['ai']=sp.I.index(self.v.cell(sp.yi,col)); gate['bi']=sp.O.index(self.v.cell(sp.yi-3,col))
                for label in core: self.goal[label]=gate
                sp.gates[gate['ai']]=gate; self.blocks.append(gate)
                for x in reservoir-core:self.tokens[self.B.a[x]]='early'
            for x in sp.I[1:]:
                assert self.B.a[x] not in self.tokens
                self.tokens[self.B.a[x]]='early'
            sp.population=sum(len(g['U']) for g in sp.gates.values())
            sp.early=sum(1 for x in sp.I[1:])+4*t*(ell-1)
            self.spokes.append(sp)
    def access(self,sp):
        t=self.p.t; y=t-3; ci=sp.ci
        return self.v.path([(r,0) for r in range(y+1)]+[(y,c) for c in range(1,ci+1)]+[(y+1,ci),(y+2,ci)])
    def park(self,sp):
        if self.B.blank==sp.I[0]:return
        old=next((x for x in self.spokes if self.B.blank==x.I[0]),None)
        if old:self.B.walk(list(reversed(self.access(old))))
        assert self.B.blank==self.entry
        self.B.walk(self.access(sp))
    def unpark(self):
        sp=next(x for x in self.spokes if self.B.blank==x.I[0])
        self.B.walk(list(reversed(self.access(sp))))
    def stage(self,gate,label,target):
        src=self.B.pos[label]
        assert src in gate['reservoir'] and target in gate['reservoir']
        if src!=target:
            third=next(x for x in gate['reservoir'] if x not in (src,target))
            self.B.cycle([src,target,third],gate['block'])
    def replace(self,e,q,u,v):
        old=self.B.a[q]; incoming=self.B.a[e]
        assert old not in self.live and old not in self.accepted
        assert incoming not in self.tokens and incoming not in self.live and incoming not in self.accepted
        if old in self.tokens:self.tokens[incoming]=self.tokens.pop(old)
        self.B.double(e,q,u,v,self.p.view)
    def service(self,sp,real):
        B=self.B; self.park(sp); incoming=B.a[self.P]
        assert incoming not in self.tokens
        if real:
            assert incoming not in self.accepted and self.goal[incoming]['spoke'] is sp
        else:assert incoming not in self.live and incoming not in self.accepted
        ready=[g for g in sp.gates.values() if B.a[sp.O[g['bi']]] in self.accepted and self.goal[B.a[sp.O[g['bi']]]] is g]
        gate=min(ready,key=lambda g:g['bi']) if ready else None
        ai=gate['ai'] if gate else len(sp.I)-1; bi=gate['bi'] if gate else len(sp.O)-1
        B.cycle([self.P,sp.D,self.E],self.hub)
        for d in range(1,ai+1):
            refill=sp.gates.get(d)
            if refill and B.a[sp.I[d]] not in self.live and refill['U']:
                h=B.a[sp.I[d]]; assert h in self.tokens and h not in self.accepted
                label=next(iter(refill['U'])); col=refill['column']
                self.stage(refill,label,self.v.cell(sp.yi+1,col))
                B.word(REFILL,lambda r,c:self.v.cell(sp.yi+r,col-1+c))
                refill['U'].remove(label); self.refills+=1
            else:B.move(sp.I[d])
        col=gate['column'] if gate else sp.f
        if gate:
            x=B.a[sp.O[bi]]; assert x in self.accepted and x not in gate['F']
            assert len(gate['F'])<len(gate['core'])
            if gate['U']:label=next(iter(gate['U'])); gate['U'].remove(label)
            else:label=next(B.a[z] for z in gate['reservoir'] if B.a[z] not in gate['F'])
            self.stage(gate,label,self.v.cell(sp.yi-1,col+1))
            sp.endpoint_word(B,PRODUCTIVE,col); gate['F'].add(x); self.productive+=1
        else:
            h=B.a[sp.O[bi]]
            assert h not in self.accepted and h not in self.live and h not in self.tokens
            self.tokens[h]='full'; sp.endpoint_word(B,IDLE,col)
        for d in range(bi-1,-1,-1):B.move(sp.O[d])
        sp.hub_word(B); B.cycle([sp.C,self.P,self.E],self.hub)
        out=B.a[self.P]; original=out in self.live
        if original:self.live.remove(out); sp.S+=1
        else:
            tag=self.tokens.pop(out)
            assert tag=='early' or sp.S==sp.population,('full inner token crossed original',sp.S,sp.population)
            if sp.S<sp.population:sp.Hreturns+=1; assert sp.Hreturns<=sp.early
        if real:self.accepted.add(incoming); sp.Dcount+=1
        else:sp.Hinputs+=1
        assert sp.Dcount<=sp.population
        self.services+=1
        return out,original
    def run(self,real,need_original):
        incoming=self.B.a[self.P]
        if real:sp=self.goal[incoming]['spoke']
        else:sp=min((x for x in self.spokes if x.S<x.population),key=lambda x:x.S-x.Dcount)
        out,original=self.service(sp,real)
        while need_original and not original:
            sp=min((x for x in self.spokes if x.S<x.population),key=lambda x:x.S-x.Dcount)
            out,original=self.service(sp,False)
        return out,original
    def drain(self):
        assert not self.live
        for sp in self.spokes:
            used=0
            while any(self.B.a[z] in self.accepted for z in sp.O):
                self.service(sp,False); used+=1
                assert used<=2*(len(sp.O)-1)+1
        assert self.productive==len(self.goal)


class Parent:
    def __init__(self,B,view,w,ell,t,marked):
        self.B=B; self.view=view; self.w=w; self.ell=ell; self.t=t; self.L=view.side-w-2
        self.V={view.cell(r,c) for r in range(w,view.side) for c in range(view.side)}
        self.goals=self.V-marked; self.m=len(self.goals)
        self.inner=Inner(self); self.oc=set(self.inner.live)
        originals={B.a[x] for x in self.goals}
        self.OR=originals-self.oc; self.HG={B.a[x] for x in self.V if B.a[x] in marked}
        self.FC=set(); self.FR=set(); self.M=len(self.oc); self.reserve=len(self.OR); self.g=len(self.HG)
        self.b=self.inner.entry; self.c=self.inner.P; self.u=view.cell(w,6); self.v=view.cell(w,7)
        self.protected={self.b,self.c,self.u,self.v}; self.counts=Counter(); self.cost=0
        assert self.g>=6
    def connector(self):
        r,c=self.view.local(self.B.blank); w=self.w
        return self.view.path([(r,x) for x in range(c,0,-1)]+[(y,1) for y in range(r+1,w+3)]+[(w+2,2)])
    def helper(self):return next(x for x in self.HG if self.B.pos[x] not in self.protected)
    def wrapper(self,e,real,need):
        B=self.B; route=self.connector(); old_blank=B.blank; seed=B.a[self.c]; entry=B.a[self.b]
        B.walk(route); square=self.view.sub(0,0,self.t+self.w+10)
        B.double(e,self.c,self.u,self.v,square)
        out,original=self.inner.run(real,need); self.inner.unpark()
        B.double(e,self.c,self.u,self.v,square); B.walk(list(reversed(route)))
        assert B.blank==old_blank and B.a[e]==out and B.a[self.c]==seed and B.a[self.b]==entry
        return out
    def request(self,e,kind):
        B=self.B; before=B.cost; incoming=B.a[e]; old_blank=B.blank
        assert e not in self.V and old_blank not in self.V
        assert all(incoming not in role for role in (self.oc,self.OR,self.HG,self.FC,self.FR))
        if kind=='core':
            assert incoming in self.inner.goal
            out=self.wrapper(e,True,bool(self.oc))
            if not self.oc:
                if self.OR and out not in self.OR:
                    self.inner.replace(e,B.pos[next(iter(self.OR))],self.u,self.v);out=B.a[e];self.counts['correction']+=1
                elif not self.OR and out not in self.HG:
                    assert out in self.FR
                    self.inner.replace(e,B.pos[self.helper()],self.u,self.v);out=B.a[e];self.counts['rescue']+=1
        elif kind=='helper' and self.oc:
            out=self.wrapper(e,False,True)
        elif kind=='reserve' and not self.OR and self.oc:
            h=self.helper();self.inner.replace(e,B.pos[h],self.u,self.v)
            out=self.wrapper(e,False,True);self.counts['reserve_staging']+=1
        else:
            assert kind in ('helper','reserve')
            if kind=='helper':assert self.OR
            chosen=next(iter(self.OR)) if self.OR else self.helper()
            self.inner.replace(e,B.pos[chosen],self.u,self.v);out=B.a[e];self.counts['direct']+=1
        if self.oc or self.OR:assert out in self.oc or out in self.OR
        else:assert out in self.HG
        if out in self.oc:self.oc.remove(out);self.counts['EC']+=1
        elif out in self.OR:self.OR.remove(out);self.counts['ER']+=1
        else:self.HG.remove(out)
        if kind=='core':self.FC.add(incoming);self.counts['AC']+=1
        elif kind=='reserve':self.FR.add(incoming);self.counts['AR']+=1
        else:self.HG.add(incoming)
        assert B.blank==old_blank and B.a[e]==out
        assert len(self.inner.live)==len(self.oc) and len(self.inner.accepted)==len(self.FC)
        E=self.counts['EC']+self.counts['ER']; A=self.counts['AC']+self.counts['AR']
        assert 0<=E-A<=4*B.n+4 and self.counts['ER']>=self.counts['AR']
        assert len(self.HG)==self.g+E-A>=6
        assert all(B.a[x] in self.HG for x in self.protected)
        self.counts['requests']+=1;self.cost+=B.cost-before
        return out
    def verify(self):
        roles=[self.oc,self.OR,self.HG,self.FC,self.FR]
        assert self.inner.live==self.oc and self.inner.accepted==self.FC
        assert sum(map(len,roles))==len(set.union(*roles))==len(self.V)
        assert set.union(*roles)=={self.B.a[x] for x in self.V}
    def finish(self):
        B=self.B;before=B.cost
        assert not self.oc and not self.OR and len(self.FC)+len(self.FR)==self.m
        route=self.connector();B.walk(route)
        first=self.inner.spokes[0];self.inner.park(first)
        self.inner.drain();self.inner.unpark()
        for g in self.inner.blocks:
            block=g['block']; r,c=self.inner.v.local(block.cell(0,0))
            access=self.inner.v.path([(y,0) for y in range(r+1)]+[(r,x) for x in range(1,c+1)])
            B.walk(access)
            cells={block.cell(y,x) for y in range(self.t) for x in range(self.t)}-{B.blank}
            B.arrange(cells,{x:x for x in g['core']},cells-g['core'],block)
            B.walk(list(reversed(access)))
        B.walk(list(reversed(route)))
        core=set(self.inner.goal); cells=self.V-core
        B.arrange(cells,{x:x for x in self.goals-core},cells-self.goals,self.view)
        assert all(B.a[x]==x for x in self.goals)
        self.cost+=B.cost-before


class Run:
    def __init__(self,k=1,ell=2,t=64,seed=125):
        self.k=k;self.w=8*k+8;self.s=ell*t+self.w+2;self.h=32*k*k+64
        self.n=2*k*self.s+self.h;self.o=k*self.s;self.B=Board(self.n)
        B=self.B;n=self.n;o=self.o;h=self.h;s=self.s;w=self.w
        self.hub=View(B,h,(o,o));self.P=self.hub.cell(h//2,h//2+1);self.E=self.hub.cell(h//2,h//2)
        self.marked={r*n+c for r in range(n) for c in range(n) if o<=r<o+h or o<=c<o+h or c==n-1}
        self.frames=[]
        for fr in (False,True):
            for fc in (False,True):
                bank=View(B,n,(n-1 if fr else 0,n-1 if fc else 0),-1 if fr else 1,-1 if fc else 1)
                for r in range(k):
                    for c in range(k):
                        view=bank.sub(o+h+r*s,o+h+c*s,s)
                        self.marked.update(view.cell(y,x) for y in range(w) for x in range(s))
                        self.marked.update(view.cell(y,x) for y,x in [(w+2,2),(w+2+t//2,2+t//2+1),(w,6),(w,7),(w,8),(w,9)])
                        j=r*k+c;sp=Spoke(bank,o+h-1,o+h-8-8*j,o+h+r*s+8*c+5,o+h+c*s+4)
                        self.frames.append((view,sp))
        # Begin at a provably reachable prepared configuration: move the blank
        # through marked cells, then apply even permutations inside R and S.
        sp=self.frames[0][1];target=sp.I[0]
        while B.blank//n>target//n:B.move(B.blank-n)
        while B.blank%n>target%n:B.move(B.blank-1)
        rng=random.Random(seed)
        for group in [self.marked-{B.blank},set(range(n*n))-self.marked]:
            cells=sorted(group);perm=list(range(len(cells)));rng.shuffle(perm)
            if parity(perm):perm[0],perm[1]=perm[1],perm[0]
            old=[B.a[x] for x in cells]
            for i,x in enumerate(cells):B.a[x]=old[perm[i]];B.pos[B.a[x]]=x
        self.parents=[];self.spokes=[];self.destination={};self.tokens={};self.main_services=0;self.drain_services=0
        for view,sp in self.frames:
            p=Parent(B,view,w,ell,t,self.marked);sp.parent=p;sp.population=p.m
            self.parents.append(p);self.spokes.append(sp)
            for x in p.goals:self.destination[x]=sp
            for label in p.HG:self.tokens[label]='early'
            for x in sp.I[1:]:
                assert B.a[x] in self.marked and B.a[x] not in self.tokens
                self.tokens[B.a[x]]='early'
            sp.early=len(sp.I)-1+p.g
        self.start_cost=B.cost;self.start_slides=B.slides
    def access(self,sp):
        o=self.o;h=self.h;n=self.n
        r,c=divmod(sp.I[0],n)
        row=o+2 if r==o else o+h-3
        # Common parking corner in the hub; corridor then a two-edge stub.
        points=[(o+2,o)]
        step=1 if row>=o+2 else -1
        points.extend((y,o) for y in range(o+2+step,row+step,step))
        points.extend((row,x) for x in range(o+1,c+1))
        step=1 if r>row else -1
        points.extend((y,c) for y in range(row+step,r+step,step))
        return [y*n+x for y,x in points]
    def park(self,sp):
        if self.B.blank==sp.I[0]:return
        old=next(x for x in self.spokes if self.B.blank==x.I[0])
        self.B.walk(list(reversed(self.access(old))));self.B.walk(self.access(sp))
    def service(self,sp,real,drain=False):
        B=self.B;self.park(sp);incoming=B.a[self.P];p=sp.parent
        assert (incoming not in self.marked)==real
        if real:assert self.destination[incoming] is sp
        productive=B.a[sp.O[-1]] not in self.marked
        B.cycle([self.P,sp.D,self.E],self.hub)
        for d in range(1,len(sp.I)):
            if d==len(sp.I)-1 and B.a[sp.I[d]] in self.marked and (p.oc or p.OR):
                p.request(sp.I[d],'helper')
            B.move(sp.I[d])
        if productive:
            x=B.a[sp.O[-1]];assert self.destination[x] is sp
            p.request(sp.O[-1],'core' if x in p.inner.goal else 'reserve')
        else:
            h=B.a[sp.O[-1]];assert h not in self.tokens
            self.tokens[h]='full'
        sp.endpoint_word(B,IDLE,sp.f)
        for x in reversed(sp.O[:-1]):B.move(x)
        sp.hub_word(B);B.cycle([sp.C,self.P,self.E],self.hub)
        out=B.a[self.P]
        if out not in self.marked:sp.S+=1
        else:
            tag=self.tokens.pop(out)
            assert tag=='early' or sp.S==sp.population,('full root token crossed original',sp.S,sp.population)
            if sp.S<sp.population:sp.Hreturns+=1;assert sp.Hreturns<=sp.early
        if real:sp.Dcount+=1
        elif not drain:sp.Hinputs+=1;assert sp.Hinputs<=sp.early+1
        assert sp.S<=sp.population and sp.Dcount<=sp.population and sp.S-sp.Dcount<=1
        assert sum(x.S-x.Dcount for x in self.spokes)==int(out not in self.marked)
    def verify(self):
        for sp in self.spokes:
            p=sp.parent;p.verify()
            inward=sum(self.B.a[z] not in self.marked for z in sp.I[1:])
            outward=sum(self.B.a[z] not in self.marked for z in sp.O)
            assert len(p.oc)+len(p.OR)+inward+sp.S==p.m
            assert sp.Dcount==len(p.FC)+len(p.FR)+outward
    def run(self):
        B=self.B
        while any(s.S<s.population for s in self.spokes) or B.a[self.P] not in self.marked:
            real=B.a[self.P] not in self.marked
            if real:sp=self.destination[B.a[self.P]]
            else:
                active=[s for s in self.spokes if s.S<s.population]
                negative=[s for s in active if s.S<s.Dcount]
                sp=(negative or active)[0]
            self.service(sp,real);self.main_services+=1
            if self.main_services%1000==0:self.verify()
            assert self.main_services<=sum(s.population+s.early+1 for s in self.spokes)
        self.verify()
        for sp in self.spokes:
            count=0
            while any(B.a[x] not in self.marked for x in sp.O):
                self.service(sp,False,True);count+=1;self.drain_services+=1
                assert count<=2*(len(sp.O)-1)+1
        self.verify()
        for sp in self.spokes:
            self.park(sp);B.walk(sp.I[:-1]);sp.parent.finish();B.walk(list(reversed(sp.I[:-1])))
        # Return to the hub, then use its marked row and the last column.
        sp=next(x for x in self.spokes if B.blank==x.I[0])
        B.walk(list(reversed(self.access(sp))))
        row=B.blank//self.n
        while B.blank%self.n<self.n-1:B.move(B.blank+1)
        while B.blank//self.n<self.n-1:B.move(B.blank+self.n)
        assert all(B.a[x]==x for x in range(self.n*self.n) if x not in self.marked)
        B.arrange(self.marked-{B.blank},{x:x for x in self.marked-{B.blank}},set(),View(B,self.n))
        assert B.a==list(range(self.n*self.n))
        for p in self.parents:
            delta=sum(sum(p.view.local(x)) for x in p.goals)
            harmonic=sum(1/i for i in range(1,p.ell))
            budget=2*delta+100000*(self.s**2*p.t+self.s**3/p.t+self.s**2*self.k+self.s*(4*self.n+5)*harmonic)
            assert p.cost<=budget
            assert p.counts['direct']+p.counts['reserve_staging']+p.counts['correction']+p.counts['rescue']<=2*p.reserve+4*self.n+4
        return {'n':self.n,'k':self.k,'parent_side':self.s,'inner_side':self.parents[0].t,
                'inner_spokes_per_parent':self.parents[0].ell-1,'real_tiles':len(self.destination),
                'root_main_services':self.main_services,'root_drain_services':self.drain_services,
                'inner_services':sum(p.inner.services for p in self.parents),
                'inner_refills':sum(p.inner.refills for p in self.parents),
                'request_cases':dict(sum((p.counts for p in self.parents),Counter())),
                'expanded_adjacent_slides':B.slides-self.start_slides,'proved_three_cycle_macro_calls':B.cycles,
                'even_sort_macros':B.sorts,'charged_length_upper_bound':B.cost-self.start_cost,
                'exact_target_reached':True,'single_board_single_blank':True}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--ell',type=int,default=2);parser.add_argument('--k',type=int,default=1)
    parser.add_argument('--seed',type=int,default=125);parser.add_argument('--output')
    args=parser.parse_args();start=time.monotonic()
    t=16*args.ell+32
    result={'status':'passed','scope':'Finite one-board integration replay. Gate words and walks expanded; proved three-cycle/even-permutation endpoint macros are not expanded. Not a universal proof.','result':Run(k=args.k,ell=args.ell,t=t,seed=args.seed).run(),'seconds':round(time.monotonic()-start,3)}
    text=json.dumps(result,indent=2)
    if args.output:open(args.output,'w').write(text+'\n')
    print(text)

if __name__=='__main__':main()

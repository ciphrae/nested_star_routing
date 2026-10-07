#!/usr/bin/env python3
"""Three-level one-board research replay; not a universal proof.

Walks and 5/19/29-slide gate words are literal. Three-cycles and even
sorting use exact endpoint macros and conservative proved slide receipts.
The compact test sizes are NOT the asymptotic scale choice.
"""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
import random
import time
from two_level_primitives import Board, View, Spoke, Inner, Run, parity, IDLE


def side_of(w_in,fanouts,ell,t):
    if not fanouts: return ell*t+w_in+2
    f=fanouts[0]
    return w_in+2+(8*f*f+16)+f*side_of(8*f+8,fanouts[1:],ell,t)


def harmonic(j: int) -> float:
    return sum(1.0/a for a in range(1, j+1))


class LeafInner(Inner):
    def __init__(self, parent):
        super().__init__(parent)
        self.productive_lane_cost = 0
        self.max_credit = [0]*len(self.spokes)
        self.max_total_credit = 0
        self.max_pre_retire_helpers = [0]*len(self.spokes)
        self.retire_active_counts = [None]*len(self.spokes)

    def notify_replace(self, old: int, incoming: int, q: int) -> None:
        assert old not in self.live and old not in self.accepted
        assert incoming not in self.tokens and incoming not in self.live and incoming not in self.accepted
        if old in self.tokens:
            self.tokens[incoming] = self.tokens.pop(old)

    def replace(self, e, q, u, v):
        self.notify_replace(self.B.a[q], self.B.a[e], q)
        self.B.double(e, q, u, v, self.p.view)

    def service(self, sp, real):
        ready = [g for g in sp.gates.values()
                 if self.B.a[sp.O[g['bi']]] in self.accepted
                 and self.goal[self.B.a[sp.O[g['bi']]]] is g]
        if ready:
            g = min(ready, key=lambda x:x['bi'])
            self.productive_lane_cost += g['ai']+g['bi']
        active_before = sum(x.S<x.population for x in self.spokes)
        was_active = sp.S<sp.population
        result = super().service(sp, real)
        self.track(sp, was_active, active_before)
        return result

    def track(self, sp, was_active, active_before):
        for i, x in enumerate(self.spokes):
            self.max_credit[i] = max(self.max_credit[i], x.S-x.Dcount)
        self.max_total_credit = max(self.max_total_credit, sum(x.S-x.Dcount for x in self.spokes))
        i = self.spokes.index(sp)
        if was_active:
            self.max_pre_retire_helpers[i] = sp.Hinputs
        if was_active and sp.S == sp.population:
            self.retire_active_counts[i] = active_before

    def finish_cells(self):
        B=self.B
        for g in self.blocks:
            block=g['block']; r,c=self.v.local(block.cell(0,0))
            access=self.v.path([(y,0) for y in range(r+1)]+[(r,x) for x in range(1,c+1)])
            B.walk(access)
            cells={block.cell(y,x) for y in range(self.p.t) for x in range(self.p.t)}-{B.blank}
            B.arrange(cells,{x:x for x in g['core']},cells-g['core'],block)
            B.walk(list(reversed(access)))

    def check_extra(self):
        j=len(self.spokes); b=self.max_total_credit
        assert sum(self.max_credit) <= j+b*harmonic(j)+1e-8
        for i,sp in enumerate(self.spokes):
            rank=self.retire_active_counts[i]
            if rank is not None:
                assert self.max_credit[i] <= 1+b/rank+1e-8
                assert self.max_pre_retire_helpers[i] <= sp.early+self.max_credit[i]+1e-8


class Node:
    """Source-first parent request, with a leaf or a nested-star router."""
    def __init__(self, B, view, w, excluded, *, ell, t, fanout=None, hub=None, sub=()):
        self.B=B; self.view=view; self.w=w; self.ell=ell; self.L=view.side-w-2
        self.V={view.cell(r,c) for r in range(w,view.side) for c in range(view.side)}
        self.goals=self.V-excluded; self.m=len(self.goals)
        self.t=hub if fanout is not None else t
        self.inner=(StarInner(self,fanout,ell,t,hub,excluded,sub) if fanout is not None else LeafInner(self))
        assert set(self.inner.goal)<=self.goals
        self.oc=set(self.inner.live)
        originals={B.a[x] for x in self.goals}
        assert self.oc<=originals
        self.OR=originals-self.oc
        self.HG={B.a[x] for x in self.V-self.goals}
        self.FC=set();self.FR=set();self.M=len(self.oc);self.reserve=len(self.OR);self.g=len(self.HG)
        self.b=self.inner.entry;self.c=self.inner.P;self.u=view.cell(w,6);self.v=view.cell(w,7)
        self.protected={self.b,self.c,self.u,self.v};self.counts=Counter();self.cost=0;self.max_lead=0
        assert self.g>=6 and all(B.a[x] in self.HG for x in self.protected)

    def connector(self):
        r,c=self.view.local(self.B.blank);w=self.w
        return self.view.path([(r,x) for x in range(c,0,-1)]+[(y,1) for y in range(r+1,w+3)]+[(w+2,2)])

    def helper(self):
        return next(x for x in self.HG if self.B.pos[x] not in self.protected)

    def wrapper(self,e,real,need):
        B=self.B;route=self.connector();old_blank=B.blank;seed=B.a[self.c];entry=B.a[self.b]
        B.walk(route);square=self.view.sub(0,0,self.t+self.w+10)
        assert square.side<=self.view.side
        B.double(e,self.c,self.u,self.v,square)
        out,original=self.inner.run(real,need);self.inner.unpark()
        B.double(e,self.c,self.u,self.v,square);B.walk(list(reversed(route)))
        assert B.blank==old_blank and B.a[e]==out and B.a[self.c]==seed and B.a[self.b]==entry
        return out

    def notify_helper_replace(self,old,incoming,q):
        assert old in self.HG and all(incoming not in role for role in (self.oc,self.OR,self.HG,self.FC,self.FR))
        # Ancestor substitutions occur while this node is paused.
        # A parking/seed helper may change identity, but must stay a helper.
        self.inner.notify_replace(old,incoming,q)
        self.HG.remove(old);self.HG.add(incoming)

    def request(self,e,kind):
        B=self.B;before=B.cost;incoming=B.a[e];old_blank=B.blank
        assert e not in self.V and old_blank not in self.V
        assert all(incoming not in role for role in (self.oc,self.OR,self.HG,self.FC,self.FR))
        before_sources=bool(self.oc or self.OR)
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
        if before_sources:assert out in self.oc or out in self.OR
        else:assert out in self.HG
        if out in self.oc:self.oc.remove(out);self.counts['EC']+=1
        elif out in self.OR:self.OR.remove(out);self.counts['ER']+=1
        else:self.HG.remove(out)
        if kind=='core':self.FC.add(incoming);self.counts['AC']+=1
        elif kind=='reserve':self.FR.add(incoming);self.counts['AR']+=1
        else:self.HG.add(incoming)
        assert B.blank==old_blank and B.a[e]==out
        assert len(self.inner.live)==len(self.oc) and len(self.inner.accepted)==len(self.FC)
        E=self.counts['EC']+self.counts['ER'];A=self.counts['AC']+self.counts['AR']
        assert E-A>=0 and self.counts['ER']>=self.counts['AR']
        assert len(self.HG)==self.g+E-A>=6
        assert all(B.a[x] in self.HG for x in self.protected)
        self.max_lead=max(self.max_lead,E-A)
        self.counts['requests']+=1;self.cost+=B.cost-before
        return out

    def verify(self):
        roles=[self.oc,self.OR,self.HG,self.FC,self.FR]
        assert self.inner.live==self.oc and self.inner.accepted==self.FC
        assert sum(map(len,roles))==len(set.union(*roles))==len(self.V)
        assert set.union(*roles)=={self.B.a[x] for x in self.V}
        if isinstance(self.inner,StarInner):self.inner.verify()

    def finish(self):
        B=self.B;before=B.cost
        assert not self.oc and not self.OR and len(self.FC)+len(self.FR)==self.m
        route=self.connector();B.walk(route)
        self.inner.park(self.inner.spokes[0]);self.inner.drain();self.inner.unpark()
        self.inner.finish_cells()
        B.walk(list(reversed(route)))
        core=set(self.inner.goal);cells=self.V-core
        B.arrange(cells,{x:x for x in self.goals-core},cells-self.goals,self.view)
        assert all(B.a[x]==x for x in self.goals)
        self.cost+=B.cost-before
        self.inner.check_extra()
        assert self.counts['direct']+self.counts['reserve_staging']+self.counts['correction']+self.counts['rescue']<=2*self.reserve+self.max_lead
        assert self.inner.max_total_credit<=self.max_lead+1


class StarInner:
    """One corner-rooted pair per child, with recursive child requests."""
    def __init__(self,parent,fanout,ell,t,hub,inherited_excluded,sub=()):
        self.p=parent;self.B=parent.B;self.v=parent.view.sub(parent.w+2,2,parent.L)
        self.hub=self.v.sub(0,0,hub);self.P=self.v.cell(hub//2,hub//2+1);self.E=self.v.cell(hub//2,hub//2)
        self.entry=self.v.cell(0,0);self.live=set();self.accepted=set();self.tokens={}
        self.spokes=[];self.goal={};self.children=[];self.services=0;self.productive=0;self.refills=0
        self.productive_lane_cost=0;self.max_total_credit=0
        w=8*fanout+8;side=side_of(w,list(sub),ell,t)
        hc=8*sub[0]*sub[0]+16 if sub else None;tc=hc if sub else t
        assert parent.L==hub+fanout*side
        # The parent's auxiliary labels occupying these cells are the children's helpers.
        reserved=set(inherited_excluded)
        frames=[]
        for r in range(fanout):
            for c in range(fanout):
                view=self.v.sub(hub+r*side,hub+c*side,side)
                reserved.update(view.cell(y,x) for y in range(w) for x in range(side))
                reserved.update(view.cell(y,x) for y,x in [(w+2,2),(w+2+tc//2,2+tc//2+1),(w,6),(w,7),(w,8),(w,9)])
                j=r*fanout+c
                sp=Spoke(self.v,hub-1,hub-8-8*j,hub+r*side+8*c+5,hub+c*side+4)
                frames.append((view,sp))
        for view,sp in frames:
            child=(Node(self.B,view,w,reserved,ell=ell,t=t,fanout=sub[0],hub=hc,sub=sub[1:]) if sub else Node(self.B,view,w,reserved,ell=ell,t=t))
            sp.parent=child;sp.population=child.m
            self.children.append(child);self.spokes.append(sp)
            self.live.update(child.oc|child.OR)
            for label in child.goals:self.goal[label]=sp
            for label in child.HG:
                assert label not in self.tokens
                self.tokens[label]='early'
            for x in sp.I[1:]:
                assert self.B.a[x] not in self.tokens and self.B.a[x] not in self.live
                self.tokens[self.B.a[x]]='early'
            sp.early=len(sp.I)-1+child.g
        self.max_credit=[0]*len(self.spokes)
        self.max_pre_retire_helpers=[0]*len(self.spokes)
        self.retire_active_counts=[None]*len(self.spokes)

    def access(self,sp):
        h=self.p.t;y=h-3;ci=sp.ci
        return self.v.path([(r,0) for r in range(y+1)]+[(y,c) for c in range(1,ci+1)]+[(y+1,ci),(y+2,ci)])
    park=Inner.park
    unpark=Inner.unpark
    track=LeafInner.track
    check_extra=LeafInner.check_extra

    def notify_replace(self,old,incoming,q):
        assert old not in self.live and old not in self.accepted
        assert incoming not in self.tokens and incoming not in self.live and incoming not in self.accepted
        if old in self.tokens:self.tokens[incoming]=self.tokens.pop(old)
        for child in self.children:
            if q in child.V:
                child.notify_helper_replace(old,incoming,q)
                break

    def replace(self,e,q,u,v):
        self.notify_replace(self.B.a[q],self.B.a[e],q)
        self.B.double(e,q,u,v,self.p.view)

    def service(self,sp,real):
        B=self.B;self.park(sp);incoming=B.a[self.P];child=sp.parent
        assert incoming not in self.tokens
        if real:assert incoming not in self.accepted and self.goal[incoming] is sp
        else:assert incoming not in self.live and incoming not in self.accepted
        productive=B.a[sp.O[-1]] in self.accepted
        active_before=sum(x.S<x.population for x in self.spokes);was_active=sp.S<sp.population
        B.cycle([self.P,sp.D,self.E],self.hub)
        for d in range(1,len(sp.I)):
            if d==len(sp.I)-1 and B.a[sp.I[d]] not in self.live and (child.oc or child.OR):
                assert B.a[sp.I[d]] in self.tokens
                child.request(sp.I[d],'helper');self.refills+=1
            B.move(sp.I[d])
        if productive:
            x=B.a[sp.O[-1]];assert self.goal[x] is sp
            child.request(sp.O[-1],'core' if x in child.inner.goal else 'reserve')
            self.productive+=1
            self.productive_lane_cost+=len(sp.I)+len(sp.O)-2
        else:
            h=B.a[sp.O[-1]];assert h not in self.tokens and h not in self.live
            self.tokens[h]='full'
        sp.endpoint_word(B,IDLE,sp.f)
        for x in reversed(sp.O[:-1]):B.move(x)
        sp.hub_word(B);B.cycle([sp.C,self.P,self.E],self.hub)
        out=B.a[self.P];original=out in self.live
        if original:self.live.remove(out);sp.S+=1
        else:
            tag=self.tokens.pop(out)
            assert tag=='early' or sp.S==sp.population,('full middle helper crossed original',sp.S,sp.population)
            if sp.S<sp.population:sp.Hreturns+=1;assert sp.Hreturns<=sp.early
        if real:self.accepted.add(incoming);sp.Dcount+=1
        else:sp.Hinputs+=1
        assert sp.S<=sp.population and sp.Dcount<=sp.population
        self.services+=1;self.track(sp,was_active,active_before)
        # Pointwise boundary bridge, before the next recursive call.
        lead=child.counts['EC']+child.counts['ER']-child.counts['AC']-child.counts['AR']
        inward=sum(B.a[z] in self.live for z in sp.I[1:])
        outward=sum(B.a[z] in self.accepted for z in sp.O)
        assert lead==(sp.S-sp.Dcount)+inward+outward
        return out,original

    def run(self,real,need_original):
        incoming=self.B.a[self.P]
        if real:sp=self.goal[incoming]
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
                self.service(sp,False);used+=1
                assert used<=2*(len(sp.O)-1)+1
        assert self.productive==len(self.goal)

    def verify(self):
        for sp in self.spokes:
            child=sp.parent;child.verify()
            inward=sum(self.B.a[z] in self.live for z in sp.I[1:])
            outward=sum(self.B.a[z] in self.accepted for z in sp.O)
            assert len(child.oc)+len(child.OR)+inward+sp.S==child.m
            assert sp.Dcount==len(child.FC)+len(child.FR)+outward

    def finish_cells(self):
        for sp in self.spokes:
            self.park(sp);self.B.walk(sp.I[:-1]);sp.parent.finish();self.B.walk(list(reversed(sp.I[:-1])))
        self.unpark()


class ThreeLevelRun(Run):
    def __init__(self,k=1,fanout=2,ell=2,t=10,seed=125,deeper=()):
        self.k=k;self.fanout=fanout;self.ell=ell;self.leaf_t=t
        self.w=8*k+8;child_w=8*fanout+8;child_side=ell*t+child_w+2
        middle_h=8*fanout*fanout+16
        self.deeper=tuple(deeper);self.s=side_of(self.w,[fanout,*self.deeper],ell,t)
        self.h=32*k*k+64;self.n=2*k*self.s+self.h;self.o=k*self.s;self.B=Board(self.n)
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
                        self.marked.update(view.cell(y,x) for y,x in [(w+2,2),(w+2+middle_h//2,2+middle_h//2+1),(w,6),(w,7),(w,8),(w,9)])
                        j=r*k+c
                        sp=Spoke(bank,o+h-1,o+h-8-8*j,o+h+r*s+8*c+5,o+h+c*s+4)
                        self.frames.append((view,sp))
        target=self.frames[0][1].I[0]
        while B.blank//n>target//n:B.move(B.blank-n)
        while B.blank%n>target%n:B.move(B.blank-1)
        rng=random.Random(seed)
        for group in [self.marked-{B.blank},set(range(n*n))-self.marked]:
            cells=sorted(group);perm=list(range(len(cells)));rng.shuffle(perm)
            if parity(perm):perm[0],perm[1]=perm[1],perm[0]
            old=[B.a[x] for x in cells]
            for i,x in enumerate(cells):B.a[x]=old[perm[i]];B.pos[B.a[x]]=x
        self.parents=[];self.spokes=[];self.destination={};self.tokens={};self.main_services=0;self.drain_services=0
        self.productive_lane_cost=0
        for view,sp in self.frames:
            p=Node(B,view,w,self.marked,ell=ell,t=t,fanout=fanout,hub=middle_h,sub=self.deeper)
            sp.parent=p;sp.population=p.m
            self.parents.append(p);self.spokes.append(sp)
            for x in p.goals:self.destination[x]=sp
            for label in p.HG:self.tokens[label]='early'
            for x in sp.I[1:]:
                assert B.a[x] in self.marked and B.a[x] not in self.tokens
                self.tokens[B.a[x]]='early'
            sp.early=len(sp.I)-1+p.g
        self.start_cost=B.cost;self.start_slides=B.slides

    def service(self,sp,real,drain=False):
        if self.B.a[sp.O[-1]] not in self.marked:
            self.productive_lane_cost+=len(sp.I)+len(sp.O)-2
        return super().service(sp,real,drain)

    def run(self,progress=False,max_root_services=None):
        B=self.B
        while any(s.S<s.population for s in self.spokes) or B.a[self.P] not in self.marked:
            real=B.a[self.P] not in self.marked
            if real:sp=self.destination[B.a[self.P]]
            else:
                active=[s for s in self.spokes if s.S<s.population]
                negative=[s for s in active if s.S<s.Dcount]
                sp=(negative or active)[0]
            self.service(sp,real);self.main_services+=1
            if self.main_services%2000==0:self.verify()
            if progress and self.main_services%10000==0:
                print(json.dumps({'root_services':self.main_services,'slides':B.slides}),flush=True)
            assert self.main_services<=sum(s.population+s.early+1 for s in self.spokes)
            if max_root_services is not None and self.main_services>=max_root_services:
                self.verify()
                return {"paused_at_root_services":self.main_services}
        self.verify()
        for sp in self.spokes:
            count=0
            while any(B.a[x] not in self.marked for x in sp.O):
                self.service(sp,False,True);count+=1;self.drain_services+=1
                assert count<=2*(len(sp.O)-1)+1
        self.verify()
        for sp in self.spokes:
            self.park(sp);B.walk(sp.I[:-1]);sp.parent.finish();B.walk(list(reversed(sp.I[:-1])))
        sp=next(x for x in self.spokes if B.blank==x.I[0])
        B.walk(list(reversed(self.access(sp))))
        while B.blank%self.n<self.n-1:B.move(B.blank+1)
        while B.blank//self.n<self.n-1:B.move(B.blank+self.n)
        assert all(B.a[x]==x for x in range(self.n*self.n) if x not in self.marked)
        B.arrange(self.marked-{B.blank},{x:x for x in self.marked-{B.blank}},set(),View(B,self.n))
        assert B.a==list(range(self.n*self.n))
        levels=[];nodes=list(self.parents)
        while nodes:
            levels.append(nodes)
            nodes=[c for x in nodes if isinstance(x.inner,StarInner) for c in x.inner.children]
        middles=[p.inner for p in self.parents]
        leaves=levels[-1]
        productive=[self.productive_lane_cost]+[sum(x.inner.productive_lane_cost for x in lv) for lv in levels]
        allstars=[x.inner for lv in levels for x in lv if isinstance(x.inner,StarInner)]
        for mid in allstars:
            j=len(mid.spokes);bp=mid.p.max_lead+1
            assert sum(mid.max_credit)<=j+bp*harmonic(j)+1e-8
            for i,sp in enumerate(mid.spokes):
                assert sp.parent.max_lead <= mid.max_credit[i]+len(sp.I)-1+len(sp.O)+2
        fans=[self.fanout,*self.deeper];ratios=[];sides=[]
        for d,lv in enumerate(levels):
            fp=self.k if d==0 else fans[d-1];r=0
            for x in lv:
                kids=x.inner.children if isinstance(x.inner,StarInner) else []
                excl=x.cost-sum(c.cost for c in kids)-x.inner.productive_lane_cost;sd=x.view.side;beta=x.max_lead+1
                if kids:
                    f=fans[d];form=sd*sd*(f*f+fp+1)+sd*beta*harmonic(f*f)
                else:
                    J=len(x.inner.spokes);form=sd*sd*self.leaf_t+sd**3/self.leaf_t+sd*sd*fp+sd*beta*max(1,harmonic(J))
                r=max(r,excl/form)
            ratios.append(round(r,1));sides.append(lv[0].view.side)
        self.depth_report=dict(levels=[len(lv) for lv in levels],stars_checked=len(allstars),exclusive_cost_over_formula=ratios,sides=sides,
            max_lead_by_level=[max(x.max_lead for x in lv) for lv in levels])
        assert sum(productive)<=self.n**3
        for p in self.parents:
            assert p.max_lead<=4*self.n+4
            mid=p.inner;j=len(mid.spokes);bp=p.max_lead+1
            assert sum(mid.max_credit)<=j+bp*harmonic(j)+1e-8
            # Each leaf request begins at a preceding middle service boundary;
            # at most two completed child requests add at most two to its lead.
            for i,sp in enumerate(mid.spokes):
                assert sp.parent.max_lead <= mid.max_credit[i]+len(sp.I)-1+len(sp.O)+2
        return {'n':self.n,'root_fanout_per_quadrant':self.k,'middle_fanout_per_side':self.fanout,
                'large_region_side':self.s,'small_region_side':leaves[0].view.side,'leaf_block_side':self.leaf_t,
                'large_regions':len(self.parents),'small_regions':len(leaves),
                'real_tiles':len(self.destination),'root_main_services':self.main_services,
                'root_drain_services':self.drain_services,'middle_services':sum(x.services for x in middles),
                'leaf_services':sum(c.inner.services for c in leaves),
                'expanded_adjacent_slides':B.slides-self.start_slides,
                'three_cycle_endpoint_macros':B.cycles,'even_sort_endpoint_macros':B.sorts,
                'charged_length_upper_bound':B.cost-self.start_cost,
                'productive_lane_cost_by_level':productive,'median_cubic_allowance':self.n**3,
                'large_request_cases':dict(sum((p.counts for p in self.parents),Counter())),
                'small_request_cases':dict(sum((c.counts for c in leaves),Counter())),
                'large_max_leads':[p.max_lead for p in self.parents],
                'middle_sum_max_credits':[sum(m.max_credit) for m in middles],'depth_report':self.depth_report,
                'exact_target_reached':True,'single_board_single_blank':True,
                'scope':'Finite replay with unexpanded, proved endpoint macros. Not a universal proof or fully expanded TAS path.'}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k',type=int,default=1);ap.add_argument('--fanout',type=int,default=2)
    ap.add_argument('--ell',type=int,default=2);ap.add_argument('--t',type=int,default=10)
    ap.add_argument('--seed',type=int,default=125);ap.add_argument('--deeper',type=int,nargs='*',default=[]);ap.add_argument('--output');ap.add_argument('--progress',action='store_true')
    args=ap.parse_args()
    if min(args.k,args.fanout)<1 or args.ell<2 or args.t<max(10,8*(args.ell-1)+2):
        ap.error('positive fanouts, ell >= 2 and t >= max(10,8*(ell-1)+2) required')
    start=time.monotonic()
    result=ThreeLevelRun(args.k,args.fanout,args.ell,args.t,args.seed,args.deeper).run(args.progress)
    result.update(seed=args.seed,seconds=round(time.monotonic()-start,3))
    text=json.dumps(result,indent=2)
    if args.output:Path(args.output).write_text(text+'\n')
    print(text)
if __name__=='__main__':main()

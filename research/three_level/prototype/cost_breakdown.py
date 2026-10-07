#!/usr/bin/env python3
"""Per-node exclusive cost breakdown for deep_replay.py (our addition, not upstream).

Attributes charged cost to the node that performs it, excluding nested child work,
split into request wrappers, middle services, reserve exchanges and finishing.
Used on 2026-10-04 to check that per-node cost has the shape of the analysis' eq. (17)
and does not grow with depth. Example: a depth-6 chain of fanout-1 stars.
"""
import argparse
from collections import defaultdict

import deep_replay as D

stack = []
cat = defaultdict(lambda: defaultdict(int))


def wrapcost(cls, name, label):
    f = getattr(cls, name)

    def g(self, *a, **k):
        B = self.B
        owner = self if isinstance(self, D.Node) else self.p
        stack.append([owner, label, B.cost, 0])
        try:
            return f(self, *a, **k)
        finally:
            o, l, c0, child = stack.pop()
            tot = B.cost - c0
            cat[id(o)][l] += tot - child
            if stack:
                stack[-1][3] += tot
    setattr(cls, name, g)


wrapcost(D.Node, 'request', 'request_other')
wrapcost(D.Node, 'finish', 'finish')
wrapcost(D.StarInner, 'service', 'service')
wrapcost(D.StarInner, 'replace', 'replace')
wrapcost(D.LeafInner, 'service', 'leaf_service')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--k', type=int, default=1)
    ap.add_argument('--fanout', type=int, default=1)
    ap.add_argument('--deeper', type=int, nargs='*', default=[1, 1, 1])
    ap.add_argument('--ell', type=int, default=2)
    ap.add_argument('--t', type=int, default=10)
    ap.add_argument('--seed', type=int, default=8)
    a = ap.parse_args()
    r = D.ThreeLevelRun(a.k, a.fanout, a.ell, a.t, a.seed, tuple(a.deeper))
    r.run()
    levels, nodes = [], list(r.parents)
    while nodes:
        levels.append(nodes)
        nodes = [c for x in nodes if isinstance(x.inner, D.StarInner) for c in x.inner.children]
    for d, lv in enumerate(levels):
        x = lv[0]
        s = x.view.side
        print(f"level {d} side {s} m={x.m} reserve={x.reserve} lead={x.max_lead} counts={dict(x.counts)}")
        if isinstance(x.inner, D.StarInner):
            print(f"    services={x.inner.services} productive={x.inner.productive}")
        print("    cost/s^2 by category:", {k: round(v / s / s, 1) for k, v in cat[id(x)].items()})


if __name__ == '__main__':
    main()

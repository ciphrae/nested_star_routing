#!/usr/bin/env python3
"""Arithmetic checks for a variable-depth sliding-puzzle research account.

This is NOT a puzzle solver, a Lean proof, or a test of universal physical
realization. All assertions use exact integer/rational arithmetic. The
underlying conditional analysis is in VARIABLE_DEPTH_ANALYSIS.md.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path
import random
from typing import Any

C0 = 1 << 20
MIN_BRANCH = 16


def integer_root(n: int, power: int) -> int:
    """Return floor(n**(1/power)) without floating-point conversions."""
    if n < 0 or power < 1:
        raise ValueError('Need n >= 0 and power >= 1')
    if n < 2:
        return n
    lo, hi = 0, 1 << ((n.bit_length() + power - 1) // power)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** power <= n:
            lo = mid
        else:
            hi = mid
    return hi if hi ** power <= n else lo


def harmonic(n: int) -> Fraction:
    if n < 0:
        raise ValueError('Negative harmonic index')
    return sum((Fraction(1, j) for j in range(1, n + 1)), Fraction())


def balanced_branches(n: int, layers: int) -> list[int]:
    """Mixed b/b+1 integer factors; avoid depth-compounded floor losses.

    layers includes the last row-shared local router. There are r=layers-1
    star subdivision stages, the first being the global root.
    """
    if n < 1 or layers < 2:
        raise ValueError('Need positive n and layers >= 2')
    r, p = layers - 1, layers + 3
    b = integer_root(n // C0, p)
    if b < MIN_BRANCH:
        raise ValueError('Depth too large: require n >= 2^20 * 16^(layers+3)')
    # q=(n/C0)^(1/p). Choose largest j for which
    # P=b^(r-j)*(b+1)^j <= q^r, by exact integer powers.
    lo, hi = 0, r + 1
    while lo + 1 < hi:
        j = (lo + hi) // 2
        prod = b ** (r - j) * (b + 1) ** j
        if C0 ** r * prod ** p <= n ** r:
            lo = j
        else:
            hi = j
    j = lo
    return [b + (((i + 1) * j) // r - (i * j) // r) for i in range(r)]


def geometry(n: int, layers: int) -> dict[str, Any]:
    """Exact scalar sizes only; does not construct grid paths or cells."""
    bs = balanced_branches(n, layers)
    r, p = len(bs), layers + 3
    k = bs[0]
    h0 = 32 * k * k + 64
    side = (n - h0) // (2 * k)
    actual_root_hub = n - 2 * k * side
    assert actual_root_hub >= h0
    sizes = [side]
    prod = k
    for i, b in enumerate(bs[1:], start=1):
        w = 8 * bs[i - 1] + 8
        hub = 16 * b * b + 64
        assert hub >= 8 * b * b + 16
        assert side >= hub + w + 10
        remainder = (side - w - 2 - hub) % b
        assert 0 <= remainder < b
        child = (side - w - 2 - hub) // b
        assert child >= 1 and b * child <= side
        side = child
        sizes.append(side)
        prod *= b
    incoming = 8 * bs[-1] + 8
    local = side - incoming - 2
    ell = isqrt(local) // 8
    assert ell >= 2
    t = local // ell
    assert t >= 16 * ell + 32
    assert t + incoming + 10 <= side
    assert 16 * side <= t * t  # Exact check of t >= 4 sqrt(side).
    assert t * t <= 256 * side
    assert (side - incoming - 2) >= side // 2
    assert (4 * side) ** p >= C0 ** r * n ** 4
    assert side ** p <= C0 ** r * n ** 4
    # Product is within one adjacent integer-ratio of q^r.
    b = min(bs)
    assert C0 ** r * prod ** p <= n ** r
    assert (C0 ** r * (prod * (b + 1)) ** p >= n ** r * b ** p)
    # Exact uniform scalar-account upper bound.
    numerator = (sum(x*x for x in bs) + t) * prod * t + n
    denominator = prod * t
    coeff = 2 * r + 20 * isqrt(C0)
    assert numerator ** p * C0 ** 2 <= (coeff * denominator) ** p * n ** 2
    return dict(n=str(n), layers=layers, branches=bs,
                region_sides=[str(x) for x in sizes], leaf_block_side=str(t),
                leaf_pairs=ell-1, scalar_geometry_passed=True)


def check_weighted_recurrence(bs: list[int], terminal_h: Fraction) -> None:
    """Check a worst-case recurrence with rho=1/2 and h_i=b_i/2.

    w_i = W_i/n^2; the area cap has already been applied. The analysis
    proves actual h_i=H_(b_i^2) <= b_i/2 for b_i >= 16.
    """
    if not bs or min(bs) < MIN_BRANCH or terminal_h < 0:
        raise ValueError('Invalid recurrence parameters')
    w = Fraction(18 * bs[0])
    middle = Fraction()
    for b in bs[1:]:
        middle += Fraction(b, 2) * w
        w = 9 * b + w / 2
    cost = middle + terminal_h * w
    bound = 27 * sum(b*b for b in bs) + 18 * terminal_h ** 2
    assert cost <= bound, (bs, terminal_h, cost, bound)


def run_checks() -> dict[str, Any]:
    exact_h = {}
    for b in (3, 4, 8, 16, 24, 32):
        h = harmonic(b*b)
        assert h < b
        if b >= MIN_BRANCH:
            assert 2*h <= b
        exact_h[str(b)] = {
            'rho_numerator': str((h/b).numerator),
            'rho_denominator': str((h/b).denominator),
            'rho_decimal_display_only': float(h/b),
        }
    rng = random.Random(12573)
    recurrence_cases = 0
    for length in (1, 2, 3, 4, 8, 16, 32, 64, 128):
        for _ in range(160):
            bs = [rng.randrange(16, 257) for _ in range(length)]
            q = Fraction(rng.randrange(0, 2000), rng.randrange(1, 50))
            check_weighted_recurrence(bs, q)
            recurrence_cases += 1
    geometry_rows = []
    for bits in (40, 44, 48, 64, 80, 100, 128, 192, 256, 384, 512):
        max_layers = (bits - 20)//4 - 3
        if max_layers < 2:
            continue
        chosen = sorted({2, max_layers, max(2, max_layers//2), min(3, max_layers), min(6, max_layers)})
        for L in chosen:
            for delta in (0, 1, 12345):
                geometry_rows.append(geometry((1 << bits) + delta, L))
    # Exact thresholds and non-power-of-two examples.
    for L in (2, 3, 4, 8, 16, 32, 64):
        for b in (16, 17, 31):
            n = C0 * b ** (L + 3)
            geometry_rows.append(geometry(n, L))
            geometry_rows.append(geometry(n + n//7 + 1, L))
    # Constant-branch adaptive stopping; intervals do not depend on depth.
    stop_cases = []
    b = 16
    K = 16*b*b + 8*b + 74
    low = 1 << 20
    high = b*low + K
    for bits in (30, 40, 60, 100, 200, 500, 1000, 2000, 4096):
        n = 1 << bits
        side = (n-(32*b*b+64))//(2*b)
        depth = 2
        while side > high:
            side = (side-K)//b
            depth += 1
        assert low <= side <= high
        stop_cases.append({'log2_n':bits, 'layers':depth,
                           'leaf_region_side':side})
    return {
        'status':'all_passed',
        'scope':'Exact scalar geometry and recurrence checks, not puzzle replay or a universal theorem.',
        'harmonic_ratios':exact_h,
        'weighted_recurrence_cases':recurrence_cases,
        'scalar_geometry_cases':len(geometry_rows),
        'largest_layers_checked':max(x['layers'] for x in geometry_rows),
        'geometry_examples':geometry_rows,
        'constant_branch_stop_cases':stop_cases,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--n', type=int)
    parser.add_argument('--layers', type=int)
    args = parser.parse_args()
    if (args.n is None) != (args.layers is None):
        parser.error('--n and --layers must be specified together')
    result = geometry(args.n, args.layers) if args.n is not None else run_checks()
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2)+'\n')
    summary = {k:v for k,v in result.items() if k not in ('geometry_examples','harmonic_ratios')}
    print(json.dumps(summary, indent=2))

if __name__ == '__main__':
    main()

# Three routing levels: construction and the seven-thirds target

## Status

There is a working finite, one-board prototype with three routing levels. There is also a proved harmonic bound for historical maximum credits; see `PEAK_CREDIT_LEMMA.md`.

The calculations below identify a seven-term cost account that would give

\[
n^3+O(n^{7/3}).
\]

**This document does not certify that universal puzzle bound.** The conditional cost implication and the scheduling lemma are separated from the remaining universal physical-composition obligation. No new Lean theorem or Lean build is supplied.

The prototype is useful evidence about a specific recursive implementation. A passed replay is not an extrapolation to all boards, all dimensions, or all rounding cases.

## 1. What changes physically

Use three transport systems:

1. The whole board's central hub has a pair of lanes to each large region.
2. Each large region has a corner hub and a separate pair of lanes to each smaller region inside it.
3. Each smaller region uses the existing row-shared local lanes to collect and distribute tiles among its final, smallest blocks.

Every occupied cell belongs to the same physical puzzle. A paused local router has a tile at its entry position, not its own blank. The one blank enters it through a reversible connection, does the requested work, and returns to the caller.

A main tile originating in a deepest block can pass through the small-region hub, the large-region hub, and the global hub before the reverse distribution stages lead to its destination block. These are stages of a tile's history, not one uninterrupted trip of the blank following that tile.

At every level, some ordinary labels have their exact positions deferred. They remain physical tiles. A label can be an auxiliary at one level while being an unexported source or an already received reserve goal at the preceding level. The implementation therefore tracks occurrence roles rather than assigning one permanent real/helper flag to a label throughout the hierarchy.

## 2. Dimensions and the candidate scales

Use the following notation, ignoring fixed numerical factors only in the approximate descriptions:

| Symbol | Meaning | Candidate scale |
|---|---|---|
| `n` | Whole-board side | `n` |
| `k` | Large regions along a side of one quadrant | `n^(1/6)` |
| `b` | Small regions along a side of a large region | `n^(1/6)` |
| `s` | Large-region side | `n^(5/6)` |
| `u` | Small-region side | `n^(2/3)` |
| `t` | Final block side | `n^(1/3)` |

There are `4k^2` large regions and `b^2` smaller regions per large region. The balanced choice is `b=k`. The outer hub has side proportional to `k^2`, and each middle hub has side proportional to `b^2`. The smallest routing hubs have side `t`.

The large regions do not undergo arbitrary side-`s` rearrangements once per main tile. Most long internal transport takes place on shared lanes. Operations spanning a whole large region are confined to its deferred labels and separately counted exceptions.

## 3. A corner-rooted middle layout

Here is a concrete geometry to use inside a large region. Coordinates point away from the global center; reflect both the geometry and moves in the other quadrants.

Remove the top entry strip of width `w0` and an additional two-cell margin. In the remaining local square, put a corner hub of side `h1`. Place a `b`-by-`b` grid of side-`u` children starting at local coordinate `(h1,h1)`.

For child row `r` and column `c`, where `0<=r,c<b`, set

\[
j=rb+c,\quad y_0=h_1-1,\quad
c_I=h_1-8-8j,\quad y_I=h_1+ru+8c+5,\quad f=h_1+cu+4.
\]

Its inward lane is the L-shaped path

\[
(y_0,c_I)\longrightarrow(y_I,c_I)\longrightarrow(y_I,f).
\]

The outward lane replaces `c_I` by `c_I+3` and `y_I` by `y_I-3`.

Use `h1>=8b^2+16` and reserve a strip of width `w1=8b+8` at the top of every child-row band. The proposed asymptotic scale choice below uses the larger `h1=16b^2+64`.

The vertical columns decrease and horizontal rows increase with `j`. A later vertical lies to the left of the earlier horizontal starts, and its horizontal lies below the earlier vertical ends. This is the same nested-L separation pattern as the supplied outer layout. Within a pair the three-cell offsets prevent a crossing. The eight-cell gaps leave room for the fixed gate frames.

The full inward-plus-outward length is

\[
a_{rc}+b_{rc}=2(r+c)u+16(c+j)+30.
\]

The child's near corner is `(h1+ru,h1+cu)`, measured from this local square's origin. Its doubled distance from that origin is `4h1+2(r+c)u`. The hub margin makes the displayed lane length no greater than that doubled distance. The large region's own near corner is still nearer the global center, so this also bounds the lane length by twice the appropriate large-corner-to-child-corner distance.

The local child strips contain the incoming/outgoing gates. The reversible connector reaches the child's parked entry and carrier within a square whose side is its hub side plus its incoming strip width and a fixed margin. Thus this connector is intended to cost `O(t+b)` for a leaf child and `O(b^2+k)` for a middle router, rather than a whole-region distance on every request.

## 4. The recursive interface implemented in the prototype

A region receives one external tile at a designated input position. The actual blank is at an adjacent external working position. On completion the blank must return to that position, the input position must contain the output tile, and all other external cells must be restored.

The input is either a fresh destination for the region or an auxiliary. An auxiliary-only request is allowed only while an old source remains. The output must be an old source whenever any remains; otherwise it must be an auxiliary. A previously accepted final is never the completed output.

The region's inventory has five disjoint roles:

- old sources associated with the internal routing core;
- old sources associated with the deferred reserve;
- auxiliaries supplied by the preceding level;
- received core destinations;
- received reserve destinations.

The existing seven-case parent policy is used with either a row-shared router or a corner-star router underneath it. A core request feeds the destination to its branch, then uses minimum-credit helper rounds until an old source returns when one is needed. Reserve requests use a direct auxiliary exchange. The late-input cases repair an inappropriate returned reserve final before the request completes.

The physical wrapper is still

\[
T\,R\,U\,R\,T^{-1},
\]

where `T` is the blank's connector walk, `R` is a double transposition involving the external input, local carrier, and two parity cells, and `U` is the local routing operation. The repeated double transposition and reversed connection restore the external working cells and the local parked seed.

### The new auxiliary-substitution issue

A large-region reserve exchange can replace an auxiliary physically inside a smaller region. Merely updating the large region's records is insufficient.

The prototype follows that replacement down to the owning child. It replaces the child-helper identity in the child's inventory and transfers any inward visit token, including its early/full tag. If the position lies deeper, the notification recurses. Source and accepted-destination records remain unchanged.

This includes a replacement at a paused child's entry or carrier seed. Those positions must contain helpers, but their helper identities need not be immutable across *ancestor* operations. The next wrapper reads the actual seed and restores that seed for its own duration.

These replacements happen only while the affected child is paused. No running local wrapper's captured seed is changed behind its back.

The finite implementation checks these rules. The universal proof still needs an explicit inductive substitution lemma for the entire recursive representation, including its protected-cell and external-frame conditions.

## 5. Productive travel still has one cubic allowance

Let `z` be a median cell of the board. For a main goal `x` deep in the hierarchy, write `cP` for its large region's near corner and `cQ` for its small region's near corner. All are ordered coordinate by coordinate along the same outward direction. Therefore

\[
\operatorname{dist}(z,x)=
\operatorname{dist}(z,c_P)+
\operatorname{dist}(c_P,c_Q)+
\operatorname{dist}(c_Q,x).
\]

Let

\[
D_P=\sum_{x\in\text{main goals of }P}\operatorname{dist}(c_P,x),
\qquad
D_Q=\sum_{x\in\text{main goals of }Q}\operatorname{dist}(c_Q,x).
\]

When there is one productive delivery per relevant goal at every level, the three productive lane accounts are bounded by

\[
\begin{array}{ll}
\text{outer:}& n^3-2\sum_P D_P,\\
\text{middle:}&2\sum_P D_P-2\sum_Q D_Q,\\
\text{leaf:}&2\sum_Q D_Q.
\end{array}
\]

The quantities cancel on addition. Deferred goals which do not enter a deeper system only leave unused nonnegative distance allowance.

This is a bound on productive **blank** travel. It is not a claim that every tile follows a shortest path. The actual service counts and exact lane receipts are still necessary to use this geometric identity.

## 6. The new lead calculation

Let `BP` bound a large region's external exports minus arrivals. The root argument gives `BP<=4n+4`.

Its middle scheduler has `J=b^2` child branches. Apply the historical-maximum lemma with total-credit cap `BP+1`. If `lambda_Q` is the lead allowance needed by child `Q`, the consequence proved in the companion note is

\[
\boxed{\sum_{Q\subset P}(\lambda_Q+1)
\le b^2(4s+5)+(B_P+1)H_{b^2}.}
\]

It is essential to sum these allowances before discarding the parent-child relationship. Using a separate `O(n)` worst-case allowance for every small region would introduce an unnecessarily large logarithmic term at the target exponent.

The smallest local router in a child contributes a lead-dependent allowance of the existing form

\[
O\bigl(u(\lambda_Q+1)H_J^{\rm leaf}\bigr),
\]

where the number of leaf lane pairs is at most `u/t`. Summing first over children and then over large regions gives

\[
O\left(n^2bH_J^{\rm leaf}
+n^2\frac{k}{b}H_{b^2}H_J^{\rm leaf}\right).
\]

There is a product of two harmonic factors, but it has a sufficiently small polynomial prefactor. It is not `n^(7/3)` times that product.

## 7. Proposed physical cost account

The source code tests the geometry and operational rule at finite sizes. The following are the uniform accounts to establish for that same construction.

### Work outside all large regions

Preparation, the outer hub operations, idle outer trips, finishing access, and final restoration of global helpers have the same form as in the supplied construction:

\[
O(n^2k^2).
\]

Only the placement of the six protected helper cells inside each large region changes. Their number does not grow with the number of grandchildren.

### Middle routing and large-region reserves

There are `b^2` middle pairs in a large region. A child's initial middle-level helper stock is six, and a middle inward lane has length `O(s)`. The early-return and drain allowances therefore total `O(sb^2)`. The main helper-round account adds `(BP+1)H_(b^2)`.

The middle hub side is `O(b^2)`. A wrapper costs `O(b^2+k)` per external request; there are at most twice the region's main population in such requests. Middle operations excluding work owned by the children are therefore expected to satisfy

\[
O\bigl(s^2(b^2+k)+s(B_P+1)H_{b^2}\bigr).
\]

The deferred area has size `O(s(b^2+k))`. Direct reserve exchanges and final reserve sorting are included in this expression. A parent's receipt must not count a child's complete operation again after that operation is already included in the child receipt.

### Leaf children

The supplied one-parent cost account has the form

\[
O\left(u^2t+\frac{u^3}{t}+u^2b
+u(\lambda_Q+1)H_J^{\rm leaf}\right)
\]

in addition to its productive distance charge. To reuse it here, its auxiliary-substitution hypotheses must be verified with the dynamic helper roles described above.

### The resulting seven terms

With `2ks<=n` and `bu<=s`, adding the proposed accounts produces

\[
\begin{aligned}
\mathcal E_3={}&n^2k^2+n^2b^2+n^2t+\frac{n^3}{kbt}\\
&+n^2kH_{b^2}
+n^2bH_J^{\rm leaf}
+n^2\frac{k}{b}H_{b^2}H_J^{\rm leaf}.
\end{aligned}
\]

**Conditional implication.** If a constant `C`, independent of dimension and board, bounds the excess physical cost of the completed construction by `C E3`, then the scale choice below proves a universal `n^3+O(n^(7/3))` bound. The arithmetic implication is established; the universal physical premise is not being silently assumed as already proved.

## 8. Why the balanced exponent is seven thirds

Write `k` on scale `n^a`, `b` on scale `n^d`, and `t` on scale `n^c`. The four main exponents are

\[
2+2a,\quad2+2d,\quad2+c,\quad3-a-d-c.
\]

They agree for

\[
a=d=1/6,\quad c=1/3,
\]

and their common value is `7/3`.

There is also a simple optimality statement for **this four-term account**, not for the puzzle itself. If all four exponents were at most `2+delta`, then

\[
a\le\delta/2,\quad d\le\delta/2,\quad c\le\delta,
\quad1\le a+d+c+\delta\le3\delta.
\]

Thus `delta>=1/3`. The balanced choice attains it.

The harmonic contributions at the balanced scales have sizes

\[
O(n^{13/6}\log n),\qquad O(n^{13/6}\log n),\qquad O(n^2(\log n)^2).
\]

Each is lower order than `n^(7/3)`.

## 9. An integer-rounded scale choice

The following is a candidate uniform geometry for `n>=2^48`. It differs from the deliberately small, exact-fit test dimensions used in the physical replay.

Set

\[
\begin{aligned}
k=b&=\lfloor n^{1/6}\rfloor,&w&=8k+8,\\
h_0&=32k^2+64,&s&=\left\lfloor\frac{n-h_0}{2k}\right\rfloor,\\
h&=n-2ks,&h_1&=16k^2+64,\\
L&=s-w-2,&u&=\left\lfloor\frac{L-h_1}{k}\right\rfloor,\\
L_2&=u-w-2,&\ell&=\lfloor\sqrt{L_2}/8\rfloor,\\
t&=\lfloor L_2/\ell\rfloor,&J_{\rm leaf}&=\ell-1.
\end{aligned}
\]

The middle remainder `L-h1-ku` is nonnegative and less than `k`; it belongs to that large region's deferred area.

Here `k>=256` and

\[
k^6\le n<2k^6,\quad k^5/4\le s\le k^5,
\quad k^4/16\le u\le k^4,
\quad k^2\le t\le16k^2.
\]

For the first inequality use `(k+1)^6 <= (257/256)^6 k^6 < 2k^6`. Floor losses and the hub/strip widths are smaller than half of each available dimension, giving the displayed lower bounds on `s` and `u`. In detail, `s >= n/(4k)`, `L-h1 >= s/2`, and `u >= s/(4k)` suffice. The leaf square has `L2>=u/2`. The standard floor estimates then give `8 sqrt(L2)-1 <= t <=16 sqrt(L2)`, implying the stated bounds on `t`.

Further useful inequalities are

\[
h\le33k^2,\quad h_1\le17k^2,\quad s-ku\le18k^2,
\]

\[
t\ge16\ell+32,\quad t+w+10\le u,\quad h_1+w+10\le s.
\]

They provide the hub separation, small-block spacing, and wrapper containment margins. Both harmonic indices are at most `k^2`, so

\[
H_{k^2},H_{J_{\rm leaf}}\le1+2\ln k\le3k.
\]

At `b=k`, the proposed error account therefore satisfies

\[
\begin{aligned}
\mathcal E_3
&\le(2+16+2+3+3+9)n^2k^2\\
&\le\boxed{35n^{7/3}}.
\end{aligned}
\]

The reciprocal term uses `n^3/(k^2 t)<=n^3/k^4<=2n^2k^2`. This last calculation is independent of any empirical fit.

For the middle deferred area, `w<=9k` and `s-ku<=18k^2` give

\[
s^2-k^2\bigl(u(u-w)-6\bigr)\le51sk^2.
\]

This prevents the middle workspace and its final restoration from contributing an unaccounted cubic term.

## 10. What the prototype verifies, and what it does not

`three_level_replay.py` implements the recursive source-first policy with literal tile identities on one board. It checks source/goal conservation, helper-token transfer, no early full-helper return, external blank restoration, lead identities, historical-maximum credit bounds, and exact final target equality.

All ordinary blank walks and the fixed 5-, 19-, and 29-slide words are expanded. Three-cycles and even sorting are implemented through their exact endpoint permutations with conservative slide receipts. They are not expanded to a complete raw slide sequence in this prototype.

The start is a reachable prepared configuration: a blank walk through the reserved set followed by even permutations within the reserved and unreserved sets. The prototype does not implement or test arbitrary-board preparation anew. The proposed proof would reuse the supplied preparation argument after verifying the new global reserved-set bound.

The compact finite layouts do not test all remainders in the candidate integer-rounded geometry. `check_scales.py` separately checks numerical parameter inequalities; it is not a board replay at those huge dimensions.

## 11. Remaining universal proof obligation

The next proof step is a single coherent recursive realization theorem, rather than more exponent manipulation. It must establish, simultaneously for every admissible board:

1. The source-first parent interface, with dynamic auxiliary substitutions that preserve every paused descendant's records and protected working cells.
2. The exact middle layout, all connector/frame disjointness, and arbitrary-dimension remainder ownership.
3. Finite completion of the actual interleaved request history, followed by all finishing operations on the same board.
4. A uniform physical receipt bounded by the seven terms, with child operations charged exactly once and all preparation/cleanup included.

The code and the new peak-credit lemma support this route and expose the required hypotheses. They do not replace this theorem. Until it is established, the uploaded `12/5` package remains the existing universal result, and `7/3` is the target supported by this extension's conditional account.

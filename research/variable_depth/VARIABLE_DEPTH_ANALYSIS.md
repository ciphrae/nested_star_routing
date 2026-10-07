# A variable number of routing layers

## Result and its exact status

The three-level peak-credit argument extends to an arbitrary finite hierarchy. After weighting each region's export-imbalance allowance by that region's side length, the inherited part contracts rather than growing by an unopposed product of harmonic sums.

The central new calculation is

\[
W_{i+1}\le 9b_i n^2+\frac{H_{b_i^2}}{b_i}W_i.
\]

Here `b_i` is the number of children per side at the next subdivision, and `W_i` is a size-weighted sum of the regions' historical export-lead allowances at depth `i`. For `b_i >= 16`, the multiplier is at most `1/2`. This gives a depth-uniform estimate, including unequal branching factors at different depths.

Under the explicit local physical-receipt assumptions in Section 5, the proposed excess move count is bounded by

\[
C n^2\left(\sum_{j=0}^{L-2}b_j^2+t+
\frac{n}{t\prod_{j=0}^{L-2}b_j}\right),                         \tag{1}
\]

with a constant `C` independent of `n`, the number `L` of routing layers, and the board. The leading productive charge remains at most `n^3`.

Optimizing the scalar expression in (1) gives the depth-dependent scale

\[
 n^2(L+3)n^{2/(L+3)}.                                      \tag{2}
\]

Thus this analysis supports a conditional `n^3 + O(n^2 log n)` target with logarithmically many constant-factor subdivisions. Logarithmic depth is an outcome of optimizing this account, not an imposed restriction. Slower-growing depths give other bounds described below.

**This is not a completed universal sliding-puzzle theorem.** The new weighted-credit estimates and the scalar-account optimization are mathematical deductions under their stated hypotheses. The physical composition premise in Section 5 is still to be proved for every admissible board and arbitrary depth. In particular, this work does not upgrade the three-level prototype's finite correctness checks into a universal theorem. No new Lean theorem or deeper physical-board replay is claimed.

## 1. Sources and the layer convention

The supplied sources are `THREE_LEVEL_CONSTRUCTION.md` and `PEAK_CREDIT_LEMMA.md` in the previous three-level research bundle. The relevant inputs are:

- The historical-maximum credit theorem, valid for every finite execution prefix.
- Its child-lead inequality, Section “Application to the next layer's export lead.”
- The proposed local physical accounts in Section 7 of `THREE_LEVEL_CONSTRUCTION.md`.
- The near-corner productive-distance cancellation in Section 5 of that note.

No external literature result is used to assert the new asymptotic target.

Count routing layers as in the earlier discussion:

- `L=1`: the original single-level, row-shared construction.
- `L=2`: a global star router followed by row-shared routers inside its regions.
- `L=3`: a global star, corner-star routers, and final row-shared routers.
- General `L>=2`: `r=L-1` star subdivision stages, then row-shared routers feeding the final blocks.

There are `r` per-side branching factors `b_0,...,b_(r-1)`. The global root uses `4 b_0^2` regions, one `b_0`-by-`b_0` array in each quadrant. Every later star region at stage `i` has `b_i^2` children. Its hub is near the corner facing the global center.

A region at depth `i` has side `s_v`. The leaf-region side is `m`; the final block side inside a leaf region is `t`. These are different quantities. With homogeneous dimensions at each depth, all leaf regions have the same `m` and `t`.

Ignoring reserved strips only for this informal size description,

\[
m\approx\frac{n}{2\prod_{j=0}^{r-1}b_j}.
\]

The later proofs use the inequality `m <= n/(2 product b_j)` or explicit rounded sizes, not an unqualified approximation.

## 2. The inherited lead bound

A region's external export lead is its number of old source labels exported minus its number of destination labels received. Let `lambda_v` be a nonnegative allowance valid throughout the completed-request prefixes of region `v`, and set

\[
\beta_v:=\lambda_v+1.
\]

Inside a parent region, a branch credit is

\[
C_j=S_j-D_j,
\]

where `S_j` counts original sources returned from the branch and `D_j` counts destinations admitted to it. A branch retires when all its originals have returned. A helper-input round chooses a minimum-credit unretired branch.

The previous peak-credit lemma states that, if the sum of the branch credits is bounded by `B`, then

\[
\sum_j\max(0,\hbox{all historical values of }C_j)
\le J+B H_J,
\quad H_J=\sum_{a=1}^J\frac1a.                             \tag{3}
\]

It is important that the maxima in (3) may occur at different times. A child needs an allowance for its complete history, not merely a simultaneous bound at one instant.

At completed branch-service boundaries, the child's actual export lead is its branch credit plus the numbers of its source and destination tiles still on the two connecting lanes. For a side-`s_v` parent, those two lane inventories total at most `4s_v+1`. At most two already-completed child requests occur between successive parent-service boundaries. This gives the previous bundle's bound

\[
\sum_{w\text{ child of }v}\beta_w
\le b_i^2(4s_v+5)+H_{b_i^2}\beta_v.                         \tag{4}
\]

Equation (4) is the input to the new argument. Its application to the puzzle remains contingent on the recursive representation maintaining the source-first and occurrence-inventory hypotheses. Ancestor replacements of auxiliary labels must preserve the counters and their early/full visit records; that requirement is not eliminated by this accounting argument.

## 3. Weight by the distance over which the allowance can cost moves

A large numerical lead allowance inside a small region is less expensive than the same allowance inside a large region. The local cost account charges a factor proportional to the local region side. Therefore define

\[
W_i:=\sum_{v\text{ at depth }i}s_v\beta_v.                  \tag{5}
\]

This is an accounting number, not a physical count of tiles currently in transit.

Regions at the same depth are disjoint, so

\[
\sum_{v\text{ at depth }i}s_v^2\le n^2.                    \tag{6}
\]

Every child of a stage-`i` parent has side at most `s_v/b_i`. Multiplying (4) by that upper bound gives

\[
\begin{aligned}
\sum_{w\text{ child of }v}s_w\beta_w
&\le\frac{s_v}{b_i}
 \left[b_i^2(4s_v+5)+H_{b_i^2}\beta_v\right]\\
&=4b_i s_v^2+5b_i s_v+
  \frac{H_{b_i^2}}{b_i}s_v\beta_v\\
&\le9b_i s_v^2+\frac{H_{b_i^2}}{b_i}s_v\beta_v.
\end{aligned}                                             \tag{7}
\]

The last step uses the integer side condition `s_v>=1`. Summing (7) and using (6) proves

\[
\boxed{W_{i+1}\le9b_i n^2+\rho_i W_i,
\qquad \rho_i:=H_{b_i^2}/b_i.}                              \tag{8}
\]

This is a finite-depth theorem about any tree satisfying (4), the child-size bounds, and disjointness. No convergence limit or termination assumption is needed.

### Why the multiplier is small

The inherited credit count is multiplied by a harmonic factor, but its cost is measured in a region at least `b_i` times smaller. The net multiplier is `H_(b_i^2)/b_i`, not `H_(b_i^2)`.

For example,

| `b` | `H_(b^2)/b` (display approximation) |
|---:|---:|
| 2 | 1.041667 |
| 3 | 0.942989 |
| 4 | 0.845182 |
| 8 | 0.592986 |
| 16 | 0.382772 |
| 32 | 0.234662 |

In fact the ratio is below one for all integers `b>=3`. One proof starts with `H_9<3` and notes that increasing `b` by one adds less than one to `H_(b^2)`, since

\[
H_{(b+1)^2}-H_{b^2}\le\frac{2b+1}{b^2+1}<1\quad(b>2).
\]

For a convenient uniform margin, use `b>=16`. The integral bound gives

\[
\frac{H_{b^2}}b\le\frac{1+2\ln b}b\le\frac12.             \tag{9}
\]

To justify the last inequality without a floating-point approximation, the function on the middle is decreasing for `b>=16`, and `ln 2 <= 3/4` gives `1+2 ln 16 <= 7 < 8`. The bound on `ln 2` follows by integrating the chord above the convex function `1/x` on `[1,2]`.

The special global-root argument supplies `lambda_v <= 4n+4` for each first-level region. There are `4b_0^2` such regions, each of side at most `n/(2b_0)`. Consequently

\[
W_1\le4b_0^2\frac{n}{2b_0}(4n+5)
\le18b_0 n^2.                                             \tag{10}
\]

## 4. A uniform bound even when branching factors vary

Write `w_i=W_i/n^2`. From (8)--(10), with `b_j>=16`,

\[
w_i\le18\sum_{j=0}^{i-1}2^{-(i-1-j)}b_j
\qquad(1\le i\le r).                                    \tag{11}
\]

The constant 18 is sufficient because the fresh term in (8) has coefficient 9. Induction proves (11).

A middle star at depth `i` has lead-dependent local allowance proportional to `s_v beta_v H_(b_i^2)`. Summed over all its regions, this is `H_(b_i^2) W_i`. Let

\[
S:=\sum_{j=0}^{r-1}b_j^2.
\]

Using `H_(b_i^2)<=b_i/2` and (11),

\[
\begin{aligned}
\frac1{n^2}\sum_{i=1}^{r-1}H_{b_i^2}W_i
&\le9\sum_{0\le j<i\le r-1}2^{-(i-1-j)}b_i b_j\\
&\le18 S.                                                \tag{12}
\end{aligned}
\]

For the last inequality, group terms by the positive index difference `d=i-j`. For every `d`, the Cauchy--Schwarz inequality gives

\[
\sum_j b_j b_{j+d}\le S,
\]

and the geometric weights sum to two. This step prevents a new factor of the number of layers.

Let `h` be the common harmonic factor of the terminal row-shared routers. Their total lead-dependent allowance is `h W_r`. Applying `2xy<=x^2+y^2` to (11),

\[
hw_r\le9S+18h^2.                                         \tag{13}
\]

Combining (12) and (13),

\[
\boxed{
\sum_{i=1}^{r-1}H_{b_i^2}W_i+hW_r
\le n^2(27S+18h^2).
}                                                         \tag{14}
\]

The number of row-shared terminal lane pairs is at most `m/t`. For `x=m/t>=1`,

\[
h\le1+\ln x,\qquad (1+\ln x)^2\le2x.                     \tag{15}
\]

For example the maximum of `(1+ln x)^2/x` over `x>=1` is `4/e<2`, attained at `x=e`. Empty lane sets have `h=0` and require no logarithm.

Therefore

\[
\boxed{
\sum_{i=1}^{r-1}H_{b_i^2}W_i+hW_r
\le n^2\left(27\sum_{j=0}^{r-1}b_j^2+36\frac mt\right).
}                                                         \tag{16}
\]

**The constants in (16) do not depend on depth.** All inherited harmonic terms fit within the same kinds of terms already needed for hub overhead and terminal routing. This is stronger than replacing each harmonic factor by `log n` and multiplying those estimates over the hierarchy.

## 5. The exact physical premise that is still required

The preceding section is an accounting theorem. To turn it into a sliding-puzzle theorem, prove a recursive region operation with one uniform constant `A` and these exclusive local receipts.

“Exclusive” means that a parent's receipt counts its own blank walks, gate words, staging, reserve exchanges, and reserve restoration, but not the work counted by a invoked child's receipt. The child is charged once, separately. The coefficient on a child's complete receipt must be one, not `A`.

For a middle star region `v` with side `s_v`, next branching `b_i`, and incoming strip parameter `b_(i-1)`, the intended nonproductive receipt is

\[
A\left[s_v^2(b_i^2+b_{i-1}+1)
+s_v\beta_v H_{b_i^2}\right].                              \tag{17}
\]

For a terminal region with side `m` and final block side `t`, it is

\[
A\left[m^2t+\frac{m^3}{t}+m^2b_{r-1}+m\beta_v h\right].    \tag{18}
\]

Global preparation, root operations, global idle trips, access, and final restoration of global helpers must fit `A n^2 b_0^2`, apart from productive lane travel.

Equations (17) and (18) are the all-depth version of the proposed three-level local accounts. They are **obligations**, not already proved physical theorems. They include the deferred-area and direct-exchange costs; deferring such costs until after the recurrence would leave an incomplete argument.

The other physical requirements are:

1. Every region must implement the same source-first external request interface, using the one actual blank and restoring its caller's external frame.
2. Replacing an auxiliary label while a descendant is paused must preserve all descendant records, visit tags, and protected-cell conditions. It must not change a running wrapper's captured seed.
3. The coordinate layout, connector paths, and reserve ownership must satisfy these interfaces at every depth, including rounding remainders.
4. Every finite request history must satisfy the counter hypotheses used in (3)--(4), and completed routing plus cleanup must give one legal path to the exact target.
5. The local constant `A` must be independent of depth. An estimate of the form `A * (local cost + all child costs)` would not be sufficient.

Subject to these premises, disjointness gives a contribution at most `A n^2 b_i^2` from the quadratic hub term at each stage. Incoming-strip and unit terms are absorbed using `b_i>=16`. Equations (16) and (18) absorb the lead costs. Since `m <= n/(2 product b_j)`, one obtains (1) with a new universal constant `C`.

### Preserving the leading coefficient

For a goal `x`, follow its nested near corners `z,c_1,...,c_r,x`. Coordinates move consistently outward, so

\[
\operatorname{dist}(z,x)=\operatorname{dist}(z,c_1)
+\sum_{i=1}^{r-1}\operatorname{dist}(c_i,c_{i+1})
+\operatorname{dist}(c_r,x).
\]

The productive lane costs telescope if there is exactly one productive delivery for each relevant goal at each stage. Goals deferred earlier need no later charge. The sum is at most

\[
2\sum_x\operatorname{dist}(z,x)
=4n\lfloor n^2/4\rfloor\le n^3.
\]

This geometric identity does not prove the physical interface, delivery multiplicities, or nonproductive receipts by itself.

## 6. Optimize the number and sizes of subdivisions

For this section ignore integer and geometry restrictions only to solve the continuous optimization. Define the positive scalar account

\[
F=\sum_{j=0}^{r-1}b_j^2+t+\frac{n}{t\prod_jb_j}.
\]

Put `z=n/(t product b_j)`. Apply the arithmetic--geometric mean inequality to these `r+4` positive numbers:

\[
b_0^2,\ldots,b_{r-1}^2,
\frac t2,\frac t2,\frac z2,\frac z2.
\]

Their sum is `F`; their product is `n^2/16`. Thus

\[
\boxed{F\ge(r+4)(n/4)^{2/(r+4)}.}                          \tag{19}
\]

Equality holds when

\[
b_j=(n/4)^{1/(r+4)}\quad\hbox{for all }j,
\qquad t=z=2(n/4)^{2/(r+4)}.                              \tag{20}
\]

Since `r=L-1`, the fixed-depth exponent is

\[
\boxed{2+\frac{2}{L+3}.}                                   \tag{21}
\]

| Routing layers `L` | Predicted exponent from this account |
|---:|---:|
| 1 | `5/2` |
| 2 | `12/5` |
| 3 | `7/3` |
| 4 | `16/7` |
| 5 | `9/4` |
| 7 | `11/5` |
| General `L` | `2+2/(L+3)` |

The rows beyond the established supplied construction are conditional targets, not newly certified puzzle bounds. The first row is a comparison to the original single-level account; the all-depth root formulation here starts at `L=2`.

### Substitute an arbitrary permitted function `L=f(n)`

With depth-uniform physical receipts and uniform rounding as below, the bound has the form

\[
n^3+O\left[n^2(f(n)+3)
\exp\left(\frac{2\ln n}{f(n)+3}\right)\right].              \tag{22}
\]

The constant in this conditional statement is independent of `f(n)`. That independence cannot be inferred merely from separate theorems with a different unspecified constant for every fixed depth.

Some possible choices are:

| Choice of depth | Conditional excess scale |
|---|---|
| Fixed integer `L` | `O(n^(2+2/(L+3)))` |
| `ceil(ln ln n)` | `n^(2+o(1))`, with overhead roughly `ln ln n * exp(2 ln n/ln ln n)` above `n^2` |
| `ceil(sqrt(ln n))` | `n^2 exp(O(sqrt(ln n)))` |
| `L ~ ln n/ln ln n` | `O(n^2 (ln n)^3/ln ln n)` |
| A sufficiently small positive constant times `ln n` | `O(n^2 ln n)` |

The fixed minimum branching limits nontrivial depths to `O(log n)`. In this construction, a region shrinks by at least a fixed factor greater than one at every real subdivision. Inserting levels with no shrinking does not remove the work of the meaningful levels.

### Is logarithmic depth actually optimal for this account?

For `n>4`, write `x=r+4`. The right side of (19) is

\[
x\exp(2\ln(n/4)/x).
\]

As a function of positive real `x`, its minimum is `2e ln(n/4)`, at `x=2 ln(n/4)`. This unconstrained optimizer uses branching `sqrt(e)`, which is not an admissible integer layout here. Fixed admissible branching still gives the same logarithmic order, with a larger constant.

Thus the optimized order of this **positive upper-bound account** is `n^2 log n`. This is not a lower bound for the actual puzzle, nor proof that different accounting or a different construction cannot do better.

## 7. Rounding without a hidden exponential-in-depth loss

For fixed depth it is harmless to write each branching factor as the floor of a real scale. With growing depth, replacing the same real scale by its floor at every stage can multiply a fixed relative loss many times. That may leave the leaf regions polynomially larger than intended.

Here is a depth-uniform scalar construction. Fix

\[
C_0=2^{20},\quad p=L+3=r+4,\quad q=(n/C_0)^{1/p},
\quad q\ge16.
\]

Set `b=floor q`. Choose `j` so that

\[
P=b^{r-j}(b+1)^j\le q^r
\quad\hbox{and}\quad
P\ge\frac{q^r}{1+1/b}.                                    \tag{23}
\]

Such a `j` exists by taking the largest product in this finite progression not exceeding `q^r`. Use `j` branching factors equal to `b+1` and `r-j` equal to `b`. They may be distributed as evenly as possible over the levels. The total product, not every individual factor, has a controlled rounding loss.

Use exactly these integer region sizes:

\[
h_0=32b_0^2+64,\qquad s_1=\left\lfloor\frac{n-h_0}{2b_0}\right\rfloor,
\]

and for `1<=i<r`,

\[
w_i=8b_{i-1}+8,\quad h_i=16b_i^2+64,\quad
s_{i+1}=\left\lfloor\frac{s_i-w_i-2-h_i}{b_i}\right\rfloor. \tag{24}
\]

The actual global hub side is `n-2b_0 s_1`, absorbing the outer remainder. Middle remainders belong to the corresponding region's reserve.

At the leaf put

\[
m=s_r,\quad V=m-(8b_{r-1}+8)-2,\quad
\ell=\lfloor\sqrt V/8\rfloor,\quad t=\lfloor V/\ell\rfloor.
\]

These are scalar dimensions, not a proof of all grid-frame disjointness.

### Uniform bounds on the final scale

For `q>=16`, every `b_i` lies between `q-1` and `q+1`, with `b_i<=17q/16`. In (24), the subtracted hub-plus-strip width is at most `20q^2`. An additional `b_i` safely accounts for each flooring loss when unrolling the divisions. Suffix products are at least `(q-1)^j`, so their reciprocals form a geometric sum. The total additive loss at the leaf is less than `50q`, including the root's hub and floor loss. In particular,

\[
\frac{n}{2P}-50q\le m\le\frac{n}{2P}.
\]

Together with (23) and the large fixed `C_0`, this gives

\[
\boxed{\frac{C_0}{4}q^4\le m\le C_0q^4.}                 \tag{25}
\]

All higher regions are at least as large. The widths are `O(q^2)` and the leaf-region sides are `Omega(q^4)`, leaving a uniform margin independent of depth. The leaf floor estimates give, for example,

\[
4\sqrt m\le t\le16\sqrt m,
\quad t\ge16\ell+32,
\quad t+(8b_{r-1}+8)+10\le m.                              \tag{26}
\]

Using (23)--(26), the scalar account satisfies

\[
\sum b_i^2+t+\frac{n}{Pt}
\le\left(2r+20\sqrt{C_0}\right)q^2.                       \tag{27}
\]

Since `C_0` is fixed, this establishes the order claimed in (22) uniformly in the allowed depth. A sufficient admissibility range for this particular deliberately generous construction is

\[
n\ge2^{20}\,16^{L+3}.
\]

The numerical checker verifies the scalar inequalities exactly on its listed cases; the inequalities above supply the depth-uniform arithmetic explanation. Neither establishes the unresolved spatial representation theorem.

## 8. An easier near-quadratic candidate: fixed branching and adaptive stopping

For pursuing the best asymptotic order, it is not necessary to implement mixed factors. Fix `b=16` at every star stage and stop subdividing once a region has a fixed, sufficiently large side.

The middle size recurrence is

\[
s_{i+1}=\left\lfloor\frac{s_i-K}{16}\right\rfloor,
\quad K=16\cdot16^2+8\cdot16+74=4298.
\]

Choose a fixed leaf minimum `M=2^20` and stop when

\[
s_i\le16M+K.
\]

The last child then has side between `M` and `16M+K`. Leaf hubs, leaf blocks, and leaf harmonic factors consequently have fixed bounded sizes. The number of layers is `Theta(log n)`, with rounding affecting only fixed additive constants.

Every star level has at most `n^2` total region area. Its hub/reserve account is `O(n^2)`. The weighted lead recurrence has contraction at most `1/2`, so its lead-dependent account is also `O(n^2)` per level. The terminal account is `O(n^2)` because its sizes are fixed.

Under the uniform physical premise, the total is therefore

\[
\boxed{n^3+O(n^2\log n).}
\]

This fixed-branching construction is the simpler candidate to formalize first. It avoids taking a limit of fixed-depth theorems and avoids inferring a uniform constant from nonuniform ones.

## 9. Checks actually performed

`verify_variable_depth.py` uses exact integers and `Fraction`, not floating-point comparisons, for its assertions. Decimal harmonic ratios are display-only.

The saved results contain:

- 1,440 variable-branch recurrence tests, including depths up to 128 star stages and arbitrary nonnegative terminal weights.
- 177 exact mixed-factor scalar-geometry and cost-account cases, with prescribed routing depths up to 120.
- Nine constant-branch adaptive-stopping checks, including an integer dimension `2^4096` and 1,019 routing layers. These manipulate dimensions only; no enormous board is allocated.
- Fresh execution of the supplied peak-credit counter checker: 40 cases, 75,538 states, and 374,921 transitions, all passing.

The adaptive-stop and mixed-factor tests are not physical-board replays. The checks do not test all boards, expand three-cycle macros, or run Lean. The complete written derivation and the explicit physical premise remain the distinction between a conditional account and a universal move theorem.

## 10. What has changed in the research direction

The main all-depth numerical obstacle is narrower than before: repeated harmonic factors do not inherently force an extra logarithm at each layer. Region-size weighting and geometric contraction control them with depth-independent constants, even for varying branching factors.

The remaining universal work is structural: prove one recursively stable region interface with exclusive, depth-uniform physical receipts, initialize it on arbitrary reachable boards, and compose finishing on the same single-blank path. That proof is still required even though the scalar account now supports a near-quadratic correction.

# A harmonic bound for historical maximum credits

## Status and purpose

This note proves a finite scheduling lemma. It is not, by itself, a sliding-puzzle upper bound. The lemma strengthens the retirement-credit estimate used in the supplied two-level package: it bounds the **sum of the historical maxima**, not just the sum of the credits at retirement.

Historical maxima matter because the next routing level needs a lead bound valid throughout each child's entire execution.

## Definitions

There are `J` branches, indexed by `i`. Branch `i` has a fixed positive integer population `m_i`.

At each complete service boundary, let:

- `S_i` be its number of returned original sources;
- `D_i` be its number of admitted destination labels;
- `C_i = S_i - D_i` be its credit.

The populations need not be equal. Assume `0 <= S_i,D_i <= m_i`. A branch is **active** when `S_i < m_i` and **retired** otherwise. A retired branch has nonnegative credit because `C_i=m_i-D_i>=0`.

Assume a fixed real number `B >= 0` bounds the sum of all current credits at every boundary:

\[
\sum_i C_i\le B.
\]

Initially all credits are zero. The possible updates have the following properties:

1. A destination-input service cannot increase any credit.
2. A helper-input service selects a minimum-current-credit active branch. Only that selected credit can increase, and its increase is at most one.
3. The active set only shrinks. A branch's credit cannot increase after it retires. This includes final draining, when there are no original returns left.
4. Each service retires at most one branch. Simultaneous retirements could instead be ordered, but that extension is not needed here.

For a fixed finite execution prefix, define

\[
P_i=\max\bigl(0,\ C_i\text{ at every boundary in that prefix}\bigr),
\qquad H_J=\sum_{a=1}^J\frac1a.
\]

`P_i` is a number attached to branch `i`, not a physical buffer or a count of tiles currently in a location.

## Theorem

Every such prefix satisfies

\[
\boxed{\sum_iP_i\le J+B H_J.}
\]

This controls the sum of maxima taken at **different times**. It is stronger than a simultaneous bound on the current credits.

## Proof

First suppose `a>0` branches are active. Removing retired, nonnegative credits from the total gives

\[
\sum_{i\text{ active}}C_i\le B.
\]

The least current active credit is consequently at most `B/a`. A helper service can increase its selected credit only to `1+B/a`. Destination services do not increase credits. When the active population decreases, `1+B/a` becomes larger, because `B>=0`.

Induction therefore gives, for every currently active branch,

\[
C_i\le1+B/a.
\]

It also bounds that branch's **past** credits: at any earlier time it was active among at least `a` branches, so its earlier cap was no larger. Thus

\[
P_i\le1+B/a
\]

for every currently active branch.

If branch `i` retired when `a_i` branches were active immediately before its final return, the final increment was bounded by `1+B/a_i`. Every earlier cap was no larger, and later credits do not increase. Hence

\[
P_i\le1+B/a_i.
\]

For a completed execution, the retirement counts are exactly `J,J-1,...,1`, once each. Adding these inequalities proves

\[
\sum_i P_i\le\sum_{a=1}^J(1+B/a)=J+B H_J.
\]

For an unfinished prefix with `a>0` active branches, retired branches contribute at most

\[
(J-a)+B(H_J-H_a),
\]

and the active historical maxima contribute at most

\[
a(1+B/a)=a+B.
\]

Their sum is

\[
J+B(H_J-H_a+1)\le J+B H_J,
\]

because `H_a>=1`. The case `a=0` is the completed calculation. The case `J=0` is an empty sum. This proves the theorem without assuming eventual completion. QED.

## Application to the next layer's export lead

Consider a large region of side `s`, served externally by a source-first request interface. Suppose its completed external histories have export lead at most `B_parent`. Its middle router has `J` child branches and uses the minimum-credit rule.

The existing source/destination coupling gives the middle total-credit cap

\[
B=B_{\rm parent}+1.
\]

For a child `i`, let `E_i` count originals that have physically left the child, and let `A_i` count destination labels that have physically entered the child. At a completed middle service boundary, the occurrence inventory gives

\[
E_i-A_i=C_i+I_i+O_i,
\]

where `I_i` is the number of that child's originals still on its inward lane and `O_i` is the number of admitted child goals still on its outward lane.

Write `a_i` for the inward lane's number of occupied data positions and `b_i+1` for the outward lane's number of data positions. In the proposed geometry `a_i,b_i<=2s`. Consequently

\[
I_i+O_i\le4s+1.
\]

A middle service contains at most two completed requests to its child. Each can raise `E_i-A_i` by at most one. The **preceding** middle boundary therefore gives a uniform allowance during all completed child-request prefixes:

\[
\lambda_i:=P_i+4s+3,
\qquad E_i-A_i\le\lambda_i.
\]

This argument does not assume that the next request has finished: it bounds the increment of every already-completed request prefix. Ancestor helper substitutions do not change `E_i` or `A_i`.

Summing the bounds needed by the children's local cost theorem gives

\[
\begin{aligned}
\sum_i(\lambda_i+1)
&\le J(4s+4)+\sum_iP_i\\
&\le\boxed{J(4s+5)+(B_{\rm parent}+1)H_J.}
\end{aligned}
\]

The term inherited from the large region's external lead occurs **harmonically**, not once with its full worst-case size for every child.

## What must still be connected to physical routing

The scheduling theorem above is proved under explicit finite-counter hypotheses. Its use for a universal three-level puzzle theorem requires the physical construction to maintain those hypotheses for every admissible input board and every allowed recursive helper replacement. The prototype checks that maintenance on the saved executions, but finite replay does not establish the universal statement.

Relevant existing source entry points are `RetirementCredit.lean`, `HarmonicPrefix.lean`, `ParentCreditTrace.lean`, and `RootParentLead.lean`. This work does not modify or extend those Lean files.

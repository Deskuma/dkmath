# ASTRA-001 — norm-minus-three fiber and represented-pair review

## Research log

This report records the review as it proceeds. Production coordinates and the
previous scratch source were inspected directly on the v1 branch.

1. The proposed ideal/unit argument has no apparent sign or integrality
   obstruction. Its fifteen individual steps are being checked below.
2. A simpler candidate proof emerged: compare two positive solutions using
   the integer determinant `y2*d1-y1*d2`. Its product with
   `y2*d1+y1*d2` is `3*(d2^2-d1^2)`. Integrality may exclude even two points
   in one fixed-`(T,r)` shell. This is a proof candidate, not an inference from
   the previous numerical maximum of one.
3. The literature review is checking uniform large-square-divisor estimates
   separately from full-squarefull-value counts and squarefree asymptotics.
   Their quantifiers and error terms cannot be interchanged.

4. **SCRATCH-PROVED:** the integer separation theorem and the full production
   fiber consumer now compile. `shellFiber_card_le_one` has no nonstandard
   axioms; the bound two follows immediately. The improvement to one comes
   from a different elementary proof, not from numerical extrapolation.
5. **NUMERIC:** a fresh prime-square-root sieve through `a=3000000` checked
   195455 repeated points, 216678 lifted roots and 875 independent
   factorizations. No size-two or size-three refined shell fiber appeared.
6. **MATHEMATICAL DERIVATION:** splitting at `r=R` gives
   `N_X(D) << R*X^2/D + sqrt(D/R)`. Balancing at `R=D/X^(4/3)` yields
   `N_X(D) << X^(2/3)` and a shell moment `O(X^(17/12))`. This improves the
   previous rectangular summation without invoking an average theorem.
7. A uniform Mordell-curve bound has been located in the primary literature.
   Its specialization and constants are under review; no external estimate
   is a Lean dependency.
8. **EXTERNAL-DERIVED:** the sharper specialization uses Helfgott--Venkatesh,
   Corollary 3.11 and Lemma 4.1 directly. For
   `K=-48*S^2*u^4=-3*(4*S*u^2)^2`, the field `Q(sqrt(K))` is fixed.
   The rank is `O(1+omega(S*u))`; the integral-point count is consequently
   `O_epsilon((S*u)^epsilon)`, uniformly in positive `S,u`. This deduction
   retains every coefficient dependence and is not a Lean theorem.
9. Splitting at `u=D^(1/5)` now gives
   `N_X(D) <<_epsilon X^(2+epsilon)D^(-4/5)`. Combined with the elementary
   `min(sqrt(D),X^(2/3))` envelope, it gives moment exponent
   `31/24+epsilon`, with worst shell `D` of size `X^(5/3)`. This is a new
   quantitative deduction for the campaign, still superlinear.

## 1. Fiber theorem verdict

**VALID.** The stated bound two is correct. All fifteen steps of the proposed
ideal argument survive review. In addition, an elementary integer separation
argument proves the stronger bound **one**, without quadratic fields,
squarefreeness, or primitive-solution assumptions. The reason for retaining
this stronger result is its much smaller formal proof, not an improvement
of an asymptotic exponent by changing a constant.

The statements in this report have the following distinct statuses:

| Result | Status |
|---|---|
| Production square-cube/Pell/support packets | Existing Lean declarations, inspected |
| `D² T³ < 54 (X+1)⁶` | Previous scratch theorem, independently rechecked |
| Denominator separation; refined fiber cardinality at most one | **SCRATCH-PROVED** in [scratch-001.lean](scratch-001.lean) |
| Injectivity of the canonical `(r,S)` map within one shell | **SCRATCH-PROVED** in the same file |
| Mordell transport; Eisenstein coordinate identities | **SCRATCH-PROVED**, identities only |
| Elementary shell moment `O((X+1)^(17/12))` | Mathematical counting deduction below; not formalized |
| Moment `O_ε((X+1)^(31/24+ε))` | **EXTERNAL-DERIVED**, using two unconditional literature results |
| Further uniform saving in the critical parameter boxes | **OPEN** |

Here and below set

\[
F(a)=a^2+3a+3,\quad H=X+1,\quad
M=r d^2=r^3u^2,\quad d=ru,\quad F(a)=MS,\quad T=rS.
\]

Coordinates always mean the canonical production coordinates. In particular,
`S` is the quotient by the **full repeated prime-power part**, not the parity
squarefree kernel. Write `W_X(D)` for the number of witnesses, `N_X(D)` for
the number of distinct realized moduli, and `C_X(D)` for the number of
represented canonical pairs `(r,S)`, all in the same large-modulus shell.
The new injectivity theorem gives `C_X(D)=W_X(D)` and `N_X(D)≤C_X(D)`.
It does **not** give injectivity of `a ↦ M(a)`.

For the elementary proof, let `T≥2`, `0<d₁<d₂`, and `y₁,y₂≥0` be integers
satisfying `yᵢ²+3=4T dᵢ²`. The equation implies `yᵢ≥2dᵢ`.
Eliminating `T` gives

\[
(y_2d_1)^2-(y_1d_2)^2=3(d_2^2-d_1^2)>0.
\]

Set `A=y₂d₁`, `B=y₁d₂`. Both are nonnegative integers, so `A≥B+1` and

\[
3(d_2^2-d_1^2)=A^2-B^2\ge 2B+1\ge4d_1d_2+1.
\]

If `d₂²<2d₁²`, the left side is `<3d₁²`, whereas the right side is
`>4d₁²`: a contradiction. Thus **`2d₁²≤d₂²`**. Two members of a fixed
`(T,r)` shell would instead satisfy
`r d₂²<2D≤2r d₁²`. This is impossible. Equal denominators give equal
nonnegative numerators, hence equal `a`.

Production has `T≥2`: `T=0` contradicts the equation; `T=1` would make
`F(a)` a square, excluded by `cubicQuadratic_ne_square`. This reduction and
the application to the actual production finite set both compile.

## 2. Detailed gap audit

The following checks concern the original ideal proof, with squarefree `T>1`.
They are a mathematical reconstruction; the scratch proof above avoids
formalizing this algebraic-number-theory chain.

1. **Integrality, including `T≡1 mod 4`.** The element `√T` satisfies the
   monic polynomial `z²-T`, so it is integral. Therefore
   `α=y+2d√T` lies in `O_K`. When `O_K=ℤ[(1+√T)/2]`, the inclusion
   `ℤ[√T]⊂O_K` still holds; using the full ring introduces no denominator.
2. **Principal ideal norm.** The field norm is exactly
   `y²-4Td²=-3`, hence `α≠0`. Multiplication by `α` on the rank-two
   integer lattice `O_K` has determinant `Norm_K/Q(α)`. The index of its
   image is the absolute determinant, so `#(O_K/(α))=3`.
3. **At most two ideals.** An ideal of index three has quotient ring of
   order three, hence quotient `𝔽₃`. It is a prime above three with residue
   degree one. In a quadratic field the identity `Σ e_i f_i=2` permits at
   most two such primes. There are no additional composite ideals of this
   index.
4. **Splitting cases.** If three splits there are two norm-three primes;
   if ramified there is one; if inert the prime above three has norm nine
   and there is no ideal of norm three. The inert case therefore has no
   `α` of norm minus three. Ramification does not create extra ideals.
5. **Unit norm sign.** Equality `(α₁)=(α₂)` gives
   `α₂=εα₁` with `ε,ε⁻¹∈O_K`. Its norm is the ratio `(-3)/(-3)=+1`,
   not minus one.
6. **Total positivity.** In the chosen real embedding `αᵢ>0`, and
   `αᵢ'=-3/αᵢ<0` in the other embedding. The quotient is positive in
   both embeddings. No separate choice of a positive generator is needed.
7. **Integral trace.** A unit is an algebraic integer. Its trace is a
   rational algebraic integer and is therefore an integer. Norm one gives
   `ε'=ε⁻¹`, identifying the trace with `ε+ε⁻¹`.
8. **Trace gap.** Order the two distinct solutions so that `ε>1`.
   Then `ε+ε⁻¹>2`, so its integral value is at least three. Equality to
   two would imply `(ε-1)²=0`, hence the identical solution.
9. **The quantity `x`.** Since `y>0`,
   `α=y+√(y²+3)>√3`. Consequently `x=α₁²/3>1`. The positive witness
   restriction supplies the strict inequality.
10. **Exact ratio identity.** Subtracting conjugates gives
    `4d√T=α+3/α`. Substitute `α₂=εα₁` and divide the two identities:
    `d₂/d₁=(εx+ε⁻¹)/(x+1)`. All denominators are positive.
11. **Ratio inequality.** Subtract the proposed lower bound. The difference
    is `(x-1)(ε-ε⁻¹)/(2(x+1))`, which is positive with the above ordering.
    Thus `d₂/d₁≥(ε+ε⁻¹)/2≥3/2` is valid.
12. **Shell ratio.** Nonempty shells force `D>0` and `r>0`. For fixed `r`,
    `D≤rd₁²` and `rd₂²<2D` give `d₂²<2d₁²`, hence
    `d₂/d₁<√2`. The strict upper endpoint matters.
13. **Ordering and signs.** At fixed positive `T`, increasing positive `d`
    strictly increases `y=√(4Td²-3)` and then `α`. Thus the larger
    denominator gives `ε>1`. Replacing a generator by its negative or
    conjugate does not yield another positive production numerator and
    denominator escaping this ordering.
14. **Witness multiplicity.** The map `a↦2a+3` is injective. Fixed `T`
    and positive `y` determine the positive `d`, hence `α`; conversely
    `α` determines its coefficients. The chosen generator map introduces
    no duplicate copy of a witness.
15. **`T=1`.** Production would give `F(a)=d²`, impossible for natural
    `a`. In the abstract positive integer equation
    `(2d-y)(2d+y)=3`, the only solution is `d=y=1`; it corresponds to
    `a=-1`, outside the witness range. There is no exceptional production
    fiber to add to the bound.

Each ideal contributes at most one witness because `√2<3/2`; at most two
ideals therefore prove the requested bound. The independent determinant
proof explains why even two different norm-three ideals cannot both contribute
to the same refined shell in these integral coordinates.

## 3. Counterexample search

**No size-two fiber and no fiber of size at least three was found.** This
statement is diagnostic evidence; Section 1 supplies the proof.

[numeric-001.py](numeric-001.py) uses a fresh sparse sieve. It enumerates
the two simple roots of `F` modulo each prime `p≡1 mod 3`, lifts them to
`p²`, visits their arithmetic progressions, and recovers the full exact
valuation at each visited point. This differs from the previous scan's
factorization strategy. Completeness holds because a repeated prime is
at most `√F(limit)<limit+2`; primes two and three never occur to depth two,
and every other prime divisor of `F` is one modulo three.

The retained [raw output](numeric-001-output.txt) records:

| Check | Result |
|---|---|
| Polynomial range | `0≤a≤3000000` |
| Points having a repeated prime | `195455` |
| Prime-square roots checked | `216678` |
| Independent `factorint` coordinate checks | `875`, seed `1001` |
| Maximum refined shell fiber | `1` |
| Size two / size at least three | `0 / 0` |
| Adjacent pairs with equal `(T,r)` | `17`, all satisfy the squared gap |
| Independent direct conics | `2≤T≤2000`, `1≤d≤3000` |
| Direct conic solutions / adjacent gaps | `122 / 17`, all checks pass |

The main fiber scan uses **all** repeated points, without imposing
`X+1<M`; adjacent-gap checks also cover arbitrary shell locations, not only
powers of two. The direct conic scan does not use the polynomial sieve.
Mordell transport is checked by exact arithmetic on every repeated point.

For the production height restriction, the windows are:

| `X` | Distinct large `M` | Witnesses | Nonempty dyadic shells |
|---:|---:|---:|---:|
| `100000` | `86` | `99` | `13` |
| `300000` | `138` | `172` | `15` |
| `1000000` | `250` | `304` | `15` |
| `3000000` | `436` | `535` | `17` |

### Mandatory regression audit

| Regression | Compatibility with the endorsed theorem |
|---|---|
| `M=169`, `a=21,145` | `r=1` but complements are `3,127`; the fixed `(T,r)` fibers differ. |
| `M=8281`, `a=2173,3018,5260,6105` | The common `r=1` has four distinct complements, since `F` is strictly increasing. All four collisions remain in the new exact scan. |
| Infinite complement-three Pell family | Here `r=1,T=3` stay fixed, but denominators grow and lie in different dyadic shells. A ten-term recurrence check is retained; infinitude is the existing production theorem, not a consequence of this finite check. |
| Independent paired exact depths | The argument concerns one orientation's global conic coordinates. It imposes no relation between opposite-orientation depths. The `a=7428` check still gives `v₇(F)=2` and `v₁₃(3a²+3a+1)=2`. |
| Arbitrarily large coprime paired repeated parts | Neither the fiber theorem nor any bound here asserts an absolute bound for an individual repeated part. The estimates count points relative to their height and admit infinitely many exceptional points. |
| Arbitrary finite Hensel lifting | Lifting preserves local roots. It need not preserve `T`, `r`, or a common shell. No argument substitutes local uniqueness for a global incidence bound. The sieve checks finite lifts; the arbitrary-depth assertion remains the existing theorem. |
| All three mod-49 states | Among `1,8,15,22,29,36,43`, the forward-deep state is `29`, swap-deep is `22`, and the other five are shallow. They are all retained; no state is discarded to prove a density claim. |

The infinite/quantified regressions above are checked for logical
compatibility against the existing v0 results. This pass does not claim to
have rerun every v0 regression module.

## 4. Weakest correct theorem

The minimal useful abstract statement endorsed by this review is:

> For natural `T,r,D,y₁,y₂,d₁,d₂`, if `T≥2`, `dᵢ>0`,
> `yᵢ²+3=4Tdᵢ²`, and `D≤rdᵢ²<2D` for both indices, then
> `y₁=y₂` and `d₁=d₂`.

It needs neither squarefree `T`, primitive coordinates, `r|d`, nor an upper
bound on `a`. The shell hypotheses themselves exclude `r=0` and `D=0`.
For the actual production finite set, the exact endorsed consumer is

```lean
theorem shellFiber_card_le_one (X D T r : ℕ) :
    (shellFiber X D T r).card ≤ 1
```

where `shellFiber` filters
`GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T` by
`oddPart (GNExcessCubicFullRepeatedModulus a)=r`.
`shellFiber_card_le_two` supplies the originally requested conclusion.
`shell_pair_injective` additionally proves the canonical `(r,S)` injection
on `GNExcessCubicRealizedLargeModulusShellWitnessSpace X D`.

These are successful scratch declarations, not new production declarations.
The smaller constant does not improve any exponent below.

## 5. Height inequality audit

**SCRATCH-PROVED / mathematically valid.** For a nonempty shell `D>0`.
Cubing `DS≤3H²` and multiplying `r³<2D` by `D³S³` gives

\[
D^3T^3=D^3r^3S^3 < 2D\,(DS)^3\le54D H^6.
\]

Cancellation of positive `D` proves `D²T³<54H⁶`. This is also the
independently rechecked conclusion of [scratch-000.lean](scratch-000.lean).
Empty fibers cause no cancellation obligation.

There is a constant sharpening already implicit in the exact identities:

\[
M^2T^3\le F(a)^3,
\qquad F(a)^3=u^2M^2T^3,
\qquad D^2T^3\le F(X)^3\le27H^6.
\]

It uses `r³≤M` and `MS=F(a)`. It changes neither the exponent nor the
counting region up to absolute constants, so no additional constant-only
formalization is proposed. The useful quantitative refinements below come
from splitting the coordinate region, not from replacing 54 by 27.

## 6. Quantitative consequence

All asymptotic statements here are mathematical deductions, not Lean
theorems. Constants are absolute unless an `ε` subscript is displayed.
Take `X≥1,D≥1`. Empty shells contribute zero. In any nonempty shell,
`H/2<D≤F(X)≤3H²`. Put `L=F(X)/D≤3H²/D`; integer complements satisfy
`1≤S≤L` (and also `S≤X`). Floors or ceilings change only absolute constants.
Define the dyadic moment

\[
\mathcal M(X)=\sum_{j\ge0}N_X(2^j)(2^j)^{3/8}.
\]

The sum is finite by the preceding height bound.

### 6.1 Recovered SOL-000 bounds

There are `O(D^(1/3))` possible `r` because `r³<2D`, and `O(H²/D)`
possible complements. The checked fiber theorem therefore gives

\[
C_X(D)=W_X(D)\ll H^2D^{-2/3},\qquad
N_X(D)\ll H^2D^{-2/3}.
\]

Squarefull integers have the unique canonical form `M=r³u²`, with `r`
squarefree. Dropping squarefreeness gives the convergent majorant

\[
\#\{M<2D:M\text{ squarefull}\}
\le\sum_{r\ge1}\left\lfloor\sqrt{2D/r^3}\right\rfloor
\ll\sqrt D.
\]

No `+1` per possible `r` is needed in this sum: the upper count starts at
`u=1`. It follows that `N_X(D)≪min(√D,H²D^(-2/3))`.
The two terms meet at `D=H^(12/7)`. After multiplication by `D^(3/8)`,
the increasing branch is `D^(7/8)` and the decreasing branch is
`H²D^(-7/24)`. Both have size `H^(3/2)` at the intersection. Geometric
summation proves **`𝓜(X)≪H^(3/2)`**, recovering the required old consequence.
Using only `√D` through `D≈H²` gives the older `H^(7/4)` bound.

### 6.2 An elementary split improves the envelope

Choose a real cutoff `R≥1`. For witnesses with `r≤R`, the injection into
`(r,S)` gives at most `O(RL)` points. For the distinct moduli represented
by witnesses with `r>R`, the square-cube form gives

\[
\sum_{r>R}\left\lfloor\sqrt{2D/r^3}\right\rfloor
\ll \sqrt D\sum_{r>R}r^{-3/2}
\ll\sqrt{D/R}.
\]

Consequently

\[
N_X(D)\ll RL+\sqrt{D/R}.
\]

If `D≥H^(4/3)`, take `R=D/H^(4/3)`; both terms are `O(H^(2/3))`.
If `D<H^(4/3)`, use the generic `√D` bound instead. Thus

\[
\boxed{N_X(D)\ll\min\{\sqrt D,H^{2/3},H^2D^{-2/3}\}.}
\]

The moment is now **`O(H^(17/12))`**. Below `H^(4/3)`, use `D^(7/8)`;
above it, sum the increasing branch `H^(2/3)D^(3/8)` up to `O(H²)`.
This improves the rectangular summation by using unequal costs for small
and large `r`. It does not require an average theorem for principal ideals.

The large-`r` argument counts **moduli**, not witnesses. To state an
analogous represented-pair bound correctly, a modulus fiber has at most
`2^ω(M)` witnesses: all its prime factors differ from two and three, each
has two simple roots of `F`, and `1≤a≤X<M` has no residue-class repetitions.
Finite Hensel uniqueness and CRT give that root count. Since `M≤3H²`,
`2^ω(M)≪_ε H^ε`. Therefore

\[
C_X(D)=W_X(D)\ll_\varepsilon
H^\varepsilon\min\{\sqrt D,H^{2/3}\},
\qquad C_X(D)\ll H^2D^{-2/3}.
\]

This distinction prevents the known modulus collisions from being lost.

### 6.3 Second use of `r|d`: a fixed-field Mordell bound

Starting with `y²+3=4Sr³u²`, put `A=4Su²`, `Z=Ar`, and `Y=Ay`.
The checked polynomial identity is

\[
Y^2=Z^3-3A^2=Z^3-48S^2u^4.
\]

For fixed positive `S,u`, this map is injective in `(a,r)` because `A>0`
is fixed and `y=2a+3`. The uniform, unconditional literature deduction
in Section 8 gives

\[
\#\{(Z,Y)\in\mathbb Z^2:Y^2=Z^3-48S^2u^4\}
\ll_\varepsilon(Su)^\varepsilon.
\tag{MF}
\]

This is a bound for all integral points, so ignoring the extra congruence
and positivity restrictions only enlarges the set being counted.

Split the actual witnesses at `u=U≥1`. For `u≤U`, sum (MF) over
`S≤L` and these `u`: the result is `O_ε(H^ε L U)`. The replacement of
`(Su)^ε` by a power of `H` is legitimate uniformly, since in a nonempty
shell `S≤X` and `u≤√(2D)≪H`; choose the exponent in (MF) smaller first.
For `u>U`, the shell implies `r³<2D/U²`; injection into `(r,S)` gives
`O(L D^(1/3)U^(-2/3))` witnesses. Hence

\[
C_X(D)\ll_\varepsilon
H^\varepsilon L\bigl(U+D^{1/3}U^{-2/3}\bigr).
\]

With `U=D^(1/5)`, this proves the new represented-pair saving

\[
\boxed{C_X(D)\ll_\varepsilon H^{2+\varepsilon}D^{-4/5}.}
\tag{RP}
\]

It applies to `N_X(D)` as well. Combining all branches yields

\[
N_X(D),\ C_X(D)\ll_\varepsilon
H^\varepsilon\min\{\sqrt D,H^{2/3},H^2D^{-4/5}\}.
\tag{E}
\]

For `N`, the first two individual bounds have absolute constants and
require no external result. For `C`, their `H^ε` factor records possible
modulus collisions. The last branch is external-derived for both counts.

| Shell range, ignoring absolute constants | Moment bound per shell |
|---|---|
| `D≤H^(4/3)` | `H^ε D^(7/8)` |
| `H^(4/3)≤D≤H^(5/3)` | `H^(2/3+ε) D^(3/8)` |
| `D≥H^(5/3)` | `H^(2+ε) D^(-17/40)` |

The second and third branches meet at `D=H^(5/3)` with exponent

\[
\frac23+\frac53\frac38
=2-\frac53\frac{17}{40}
=\boxed{\frac{31}{24}}.
\]

Geometric summation proves **`𝓜(X)≪_ε H^(31/24+ε)`**; the same upper
bound holds if `N` is replaced by `C`. At the very top `D≈H²`, the bound
is `H^(23/20+ε)`, so the worst shell has moved below the top shell.
The exact rational arithmetic is retained in the numerical script/output.

These are improvements within the campaign, not claims of priority in
the literature. In particular, `31/24>1`: this does not close the required
near-linear arithmetic estimate, and it does not prove ABC.

Relative to the old box, (RP) saves `D^(2/15)` up to `H^ε`.
The instruction's stronger benchmark `H D^(-1/2)` would still require
a factor `H D^(-3/10)` beyond (RP), equal to `H^(1/2)` at the new critical
shell. For the narrower goal of making just this moment linear, (E) still
needs a saving `H^(7/24)` at that shell. The two thresholds are different.

## 7. Represented-pair sparsity review

### B1a — Principal norm-three ideals: necessary, not yet a counting tool

A represented `T` has a principal ideal of norm three. That condition
forgets the sign of a generator's field norm, its height, and the condition
`r|d`. Conversely, a principal norm-three ideal alone need not provide
the required negative-norm generator in the required shell. Even an exact
principal-ideal count cannot be treated as an exact witness count.

No average theorem with a suitable uniform saving over this weighted
`T=rS` region was established in this review. Counting residue splitting
at three is insufficient; assuming independent class-group randomness is
not a proof. **Prune this as the immediate quantitative route.**

### B1b — Large square divisors: retain the boundary term

Here `F(a)=Td²` and `d≥D^(1/3)` since `M=r d²≤d³`. For each possible
`d`, a root-class majorant has shape

\[
\#\{a\le X:d^2\mid F(a)\}
\ll_\varepsilon H^\varepsilon(X/d^2+1).
\]

As `d≤√(2D)`, summing this unrestricted majorant gives

\[
W_X(D)\ll_\varepsilon
H^\varepsilon\bigl(H D^{-1/3}+\sqrt D\bigr).
\]

The `+1` creates the dominant square-root term. Unique Hensel digits do
not remove it. A squarefree-value asymptotic, which involves signed
Möbius sums, does not by itself bound this positive tail of square divisors.

Known full-squarefull-value estimates concern `S=1`. Allowing all small
squarefree `S` requires uniformity in a changing polynomial or a joint
incidence theorem. Section 8 records the actual scope of two relevant
primary sources. **Do not transfer a fixed-polynomial constant through a
sum over varying `S`.** The elementary split and (RP) supply explicit
unconditional estimates for the present set instead.

### B1c — Fixed Eisenstein coordinates: an exact incidence condition

Let `ω²+ω+1=0`. In the fixed ring `ℤ[ω]`,

\[
z=(a+2)+\omega,\qquad N(z)=F(a),\qquad
z-\bar z=1+2\omega,\quad N(z-\bar z)=3.
\]

Thus common prime-ideal factors of `z` and its conjugate lie only above
three. Since production excludes three from `d`, the square factors
associated with `d` are assigned to just one conjugate. Unique
factorization in this ring gives a mathematical factorization
`z=βγ²`, with `N(γ)=d`, `N(β)=T`, after absorbing a unit into `β`.
This existence statement was **not formalized** in this pass.

Write `γ=m+nω`, `β=b+cω`. The coefficient of `ω` gives

\[
b(2mn-n^2)+c(m^2-2mn)=1,\qquad
m^2-mn+n^2=d,\quad b^2-bc+c^2=T.
\tag{EI}
\]

The norm multiplication formula and the consequence that
`2mn-n²` and `m²-2mn` are coprime are scratch-proved. They are conditional
coordinate identities; the Lean file does not assert the above
factorization exists for every production witness.

(EI) exposes a primitive lattice incidence in a **fixed** ring. It is
more informative than splitting at three in the varying real field.
But counting every admissible `(m,n)` and applying a linear congruence
still incurs a boundary term. No saving over (E) follows from Bezout
coprimality alone. The worthwhile next step is an averaged incidence
estimate with the norms and `r|d` retained, not another local root lemma.

### B1d — Averaged Pell incidence: reformulate before counting

The height inequality gives `T≪H²D^(-2/3)`. Counting every such `T`, then
all squarefree divisors `r|T`, with an `O(1)` fiber only recovers the box
bound up to divisor factors. A fixed-`T` gap does not make the represented
values of `T` sparse by itself.

No sufficiently uniform average theorem for the moving real quadratic
fields was obtained. Instead, (MF) applies after moving to a family whose
rank-controlling quadratic field is fixed. It changes the actual average
to one over `(S,u)`, where we can state every coefficient dependence.
**Retain that reformulation; defer an unsupported average-Pell claim.**

### B1e — Cubic occurrence of `r`: a genuine second use

The first use of `r|d` is `r³<2D`. The second use is the exact
Mordell transport in Section 6.3. Its coefficient is
`-48S²u⁴=-3(4Su²)²`; hence the quadratic field in the rank estimate is
always `ℚ(√-3)`. No varying class-group bound is needed there.

For fixed `(S,u)` there are only subpower many possible `(a,r)` by (MF).
Combining that with the fixed `(r,S)` shell theorem saves `D^(2/15)`
over the rectangular pair count. This is a genuine reduction in the
number of represented pairs. It still treats every small `(S,u)` as
potentially represented, leaving the critical balanced boxes unresolved.

## 8. External theorem ledger

Only primary sources below are used. None is introduced as a Lean axiom or
an imported analytic theorem. Source statements and the specialization
derived in this report are separated explicitly.

### 8.1 Helfgott–Venkatesh: the two inputs actually used

Source: H. A. Helfgott and A. Venkatesh, *Integral points on elliptic curves
and 3-torsion in class groups*, [author preprint, arXiv:math/0405180](https://arxiv.org/pdf/math/0405180),
Corollary 3.11 (printed p. 16) and Lemma 4.1 (printed p. 18).

**Unconditional source statements.** For an integral Weierstrass model
`E/ℚ`, let `Σ` include infinity and every prime dividing its nonzero
discriminant `Δ`; write `s=#Σ`, `p=max(Σ\{∞})`, `ρ=rank E(ℚ)`. For
sufficiently small `η>0`, Corollary 3.11 gives

\[
\#E(\mathbb Q,\Sigma)\ll_\eta
C^s\eta^{-2(s+1)}(\log|\Delta|+\log p)^2
\exp((\beta(0)+\eta)\rho),\qquad \beta(0)\simeq0.2782,
\]

with absolute `C`. Lemma 4.1 bounds the rank of `Y²=Z³+K`, for nonzero
negative integer `K`, by

\[
\rho\le A_0+B_0\omega(|K|)
+2\log_3 h_3(\mathbb Q(\sqrt K)),
\]

with absolute `A₀,B₀`. Here `h₃` is the size of class-group three-torsion.

**This report's specialization, not a quoted theorem.** Set
`K=-48S²u⁴`, for arbitrary positive integers `S,u`. The integral model
has discriminant `Δ=-432K²≠0`. Take
`Σ={∞}∪{p:p|6Su}`, which contains all required bad primes, including
those of this possibly nonminimal model. Then

\[
s\le3+\omega(Su),\qquad
\log|\Delta|+\log p\ll\log(2Su),\qquad
\mathbb Q(\sqrt K)=\mathbb Q(\sqrt{-3}).
\]

The last equality makes `h₃` a fixed constant. In particular we do not
need a numerical class-number estimate. The rank is
`O(1+ω(Su))`, uniformly in both parameters. Fix one admissible `η` once
and for all; the corollary is now at most

\[
C_0^{\omega(Su)}(\log(2Su))^2
\ll_\varepsilon(Su)^\varepsilon.
\]

For completeness, the final elementary estimate is uniform: for fixed
`C₀` and any positive exponent, split the prime factors at a fixed
threshold above which `C₀≤p^δ`. The finitely many smaller primes
contribute a constant; the remaining product is at most `n^δ`.
Absorb the logarithm with another smaller exponent. This proves (MF).

There is no restriction on sixth-power factors of `K` in the quoted
integral-model statement. Alternatively, passing to a minimal model and
including primes dividing `6Su` only enlarges the permitted denominators.
No ineffective dependence on a varying field is being suppressed here.
The resulting exponent is `ε` for each fixed `(S,u)` curve, not for the
whole parameter family. Summing and balancing gives exactly (RP), not a
uniformly bounded total number of represented pairs.

### 8.2 Wongcharoenbhorn–Meemark: useful comparison, limited direct scope

Source: W. Wongcharoenbhorn and Y. Meemark, *Square-full values of quadratic
polynomials*, [author preprint, arXiv:2405.06968v2](https://arxiv.org/html/2405.06968v2),
Theorem B and Proposition 3.2.

For a fixed integer quadratic `f` of nonzero discriminant, their
unconditional Theorem B bounds the number of positive squarefull values
`f(n)`, `n≤N`, by `O_{ε,f}(N^(ϖ+ε))`, where

\[
\varpi=\frac{2(1+4\kappa)}{5+12\kappa}\simeq0.4769,
\qquad \kappa\simeq0.1688.
\]

Their Proposition 3.2 supplies the uniform generic Mordell bound
`O_ε(|K|^(κ+ε))` for nonzero integer coefficient `K`. The fixed-field
specialization above retains information that this generic estimate drops.
For the current problem Theorem B directly treats only `S=1`; its
`f`-dependent constant cannot be summed over varying complements.
Even that sector's bound, weighted at `D≈H²`, gives exponent
`ϖ+3/4≈1.2269`, still above one.

The paper also discusses conditional improvements. No conjectural Mordell
estimate or ABC-dependent consequence is used in this report.

### 8.3 Heath-Brown: a model for a positive incidence estimate

Source: D. R. Heath-Brown, *Square-free values of n²+1*,
[author preprint, arXiv:1010.6217](https://arxiv.org/pdf/1010.6217),
main theorem. Unconditionally, for real `x≥1` and every `ε>0`,

\[
\sum_{1\le n\le x}\mu^2(n^2+1)
=c_0x+O_\varepsilon(x^{7/12+\varepsilon}),\quad
c_0=\prod_{p\equiv1\ (4)}(1-2p^{-2}).
\]

Normalization audit: the preprint's opening display has an extra factor
`1/2`. Its Section 2 Euler-product derivation, with no roots modulo four,
gives the normalization written here. Only the exponent is used for this
comparison; that displayed factor is not propagated as a mathematical fact.

The polynomial is fixed as `n²+1`; this is not a theorem uniform in a
varying discriminant or complement. The proof's positive incidence problem
`e²f=n²+1` and fixed Gaussian ring suggest a method to reconstruct over
Eisenstein integers, but that transfer was not proved here. Nor can the
signed asymptotic error simply replace an unsigned large-square-divisor
tail. Even a hypothetical applicable `H^(7/12+ε)` bound, used alone at
the top shell, would give moment exponent `4/3+ε`, above one.

**Ledger decision:** only Section 8.1 is an external input to the new
quantitative estimate. Sections 8.2–8.3 are checked comparisons with
explicit domain mismatches, not additional assumptions or claimed
applications.

## 9. Best next theorem

The next missing saving is an **average over represented coefficients**,
after the per-curve bound (MF). The following local problem isolates the
current worst region without postulating an ABC-equivalent provider.

For `B≥2`, let `Q(B)` count positive canonical witnesses with

\[
B\le r<2B,\qquad B\le u<2B,\qquad B\le S<2B.
\]

These satisfy `M=r³u²≈B⁵`, `F(a)=Sr³u²≈B⁶`, and `a≈B³`.
There are only an absolute number of dyadic `M` shells in this box.
The checked fixed-`(r,S)` theorem gives `Q(B)≪B²`; the alternative
fixed-`(S,u)` estimate gives `Q(B)≪_ε B^(2+ε)`.

**OPEN next theorem candidate:** establish an explicit absolute `δ>0`
such that, uniformly for all `B≥2`,

\[
\boxed{Q(B)\ll_\varepsilon B^{2-\delta+\varepsilon}.}
\tag{NEXT}
\]

This is a strict reduction in represented pairs in the balanced boxes.
The concrete mechanism to investigate is (EI) with its norm constraints
and the cubic divisibility retained, or an equivalent averaged count of
the (MF) curves with the scaling congruences `A|Z,Y`. Neither a count of
all principal ideals nor another worst-case per-curve bound supplies
(NEXT). No value of `δ` has been proved here.

The quantitative limit is explicit. Weighting a critical box contributes
at most `B^(31/8-δ+ε)`. Since its natural height is `H≈B³`, its moment
exponent becomes `31/24-δ/3+ε`. A small positive `δ` is a useful partial
advance; **`δ≥7/8` would be needed just to reach a linear bound in that
box**. A global conclusion would additionally need uniform estimates
for the adjacent and unbalanced boxes. Thus even proving a small saving
in (NEXT) must not be announced as near-linear closure.

## 10. Production recommendation

**A. implement only the validated fixed-(T,r) fiber theorem now.**

This is a recommendation for the later implementation gate; this review
does not perform production edits. The theorem is independent of the
unresolved average question, uses a short integral argument, and has
already been checked against the actual production witness definitions.
It can expose a stable one-point fiber consumer and the `(r,S)` injection.

Keep the analytical shell estimates, the external Mordell specialization,
and (NEXT) in the research report until their own formalization scopes are
defined. The Eisenstein identities are retained as successful scratch;
they do not justify exporting an unproved factorization or counting API.

Verification artifacts for this checkpoint are
[scratch-001.lean](scratch-001.lean),
[numeric-001.py](numeric-001.py),
[numeric-001-output.txt](numeric-001-output.txt), and
[validation-001.txt](validation-001.txt).

## 11. Verdict

**Outcome B — fiber valid but global sparsity still unresolved.**

The local fiber mechanism is now kernel-checked, with the stronger bound
one obtained by an elementary proof. The review also derives a partial
represented-pair saving, and the unconditional literature specialization
improves the moment to `H^(31/24+ε)`. The outstanding problem is a further
uniform family-level saving, concentrated at `D≈H^(5/3)` with balanced
`r,u,S`. No near-linear shell theorem or ABC conclusion follows.

This completes the ASTRA-001 research checkpoint. No automatic production
instruction is opened.

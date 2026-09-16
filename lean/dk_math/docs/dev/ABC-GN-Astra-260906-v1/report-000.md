# SOL-000 — cubic realized shell-count attack

## Research checkpoint log

1. **Baseline reconstructed.**  The two immediate bounds are the witness bound
   `N_X(D) <= X` and the generic squarefull-shell bound
   `N_X(D) << D^(1/2)`.  Either gives a worst dyadic moment exponent `7/4`.
2. **A new exact height identity was isolated.**  The production packets imply
   `D*S <= 3*(X+1)^2` and `r^3 < 2D`.  The Lean scratch file proves the
   root-free consequence `D^2*T^3 < 54*(X+1)^6`.
3. **False multiplicity statements were tested.**  Fixed `M`, fixed `S`, and
   fixed `T` are not globally injective coordinates.  The known `M=169`,
   `M=8281`, and complement-3 Pell examples were reproduced.
4. **A shell-local fiber was found.**  Fixing `(T,r)`, rather than only `T`,
   puts the Pell denominator `d` in an interval of ratio `sqrt(2)`.  A
   norm-minus-three ideal/unit argument predicts an absolute fiber bound `2`.
5. **The exponent was propagated before acceptance.**  That fiber theorem
   would give `N_X(D) << X^2 D^(-2/3)`.  Combined with the squarefull bound it
   reduces the full shell moment from `X^(7/4)` to `X^(3/2)`.  It remains
   superlinear, so this pass ends at a meaningful partial mechanism.

The trust labels used below are literal.  `PRODUCTION-PROVED` refers to current
`DkMath/ABC` theorems; `SCRATCH-PROVED` refers only to the checked file
`scratch-000.lean`; `NUMERIC` is finite diagnostic evidence; and `OPEN` means
that no Lean theorem or imported research assumption supplies the statement.

## 1. Exact mathematical restatement

Put

```text
F(a) = a^2 + 3a + 3
M(a) = product of p^v over p^v || F(a) with v >= 2
S(a) = F(a) / M(a).
```

The equality with the non-exceptional repeated part is
`PRODUCTION-PROVED`: the prime `3` never occurs to depth at least two in
`F(a)`, so no repeated prime power is lost by exceptional-prime removal.

The finite quantity under attack is exactly

```text
N_X(D)
  = #{ M(a) : 1 <= a <= X,
                X+1 < M(a),
                D <= M(a) < 2D }.
```

The braces denote a set of **distinct** moduli.  If

```text
W_X(D)
  = #{ a : 1 <= a <= X,
            X+1 < M(a),
            D <= M(a) < 2D },
```

then production proves the image description and hence

```text
N_X(D) <= W_X(D).
```

For every counted witness, production supplies the unique arithmetic packet

```text
M*S = F(a),                 1 <= S <= X,
Squarefree S,               gcd(M,S)=1,
M = r*d^2 = u^2*r^3,        d=u*r,
r=oddPart(M),               Squarefree r,
T=r*S,                      Squarefree T,
y=2a+3,
y^2+3 = 4*T*d^2,            gcd(y,d)=1,
gcd(y,T) | 3.
```

All prime divisors of `M`, hence of `r` and `d`, are `1 mod 3`.  Shell
membership also gives

```text
X+1 < M,
D <= M < 2D,
M <= 3*(X+1)^2.
```

The upper endpoint follows directly from `M <= F(a) <= 3*(X+1)^2`.

## 2. Baseline bounds

### 2.1 Witness counting

The image map immediately gives

```text
N_X(D) <= W_X(D) <= X.                         (B1)
```

This bound uses no arithmetic sparsity.  After insertion of the capstone
weight, one shell costs

```text
N_X(D) D^(3/8) <= X D^(3/8).
```

At `D` of size `X^2`, this is `X^(7/4)`.

### 2.2 Generic squarefull geometry

The canonical decomposition of a positive squarefull integer is

```text
M = u^2*r^3,  r squarefree.
```

For fixed `r`, shell membership is

```text
sqrt(D/r^3) <= u < sqrt(2D/r^3).
```

The interval therefore contains at most

```text
(sqrt(2)-1)*sqrt(D)/r^(3/2) + 1
```

integers.  Positivity of `u` also gives `r^3 < 2D`.  Summing over squarefree
`r <= (2D)^(1/3)` gives

```text
# {squarefull M in [D,2D)}
  << sqrt(D) * sum_r r^(-3/2) + D^(1/3)
  << sqrt(D).
```

Consequently

```text
N_X(D) << D^(1/2).                              (B2)
```

The prime-support restriction `p == 1 mod 3` makes the actual candidate set
smaller, but a congruence-semigroup count alone does not change the power
`D^(1/2)`.  Any logarithmic saving here remains far below the required power
saving.

The shell contribution from (B2) is

```text
N_X(D) D^(3/8) << D^(7/8).
```

Since represented shells have `D << X^2`, the largest shell again has size
`X^(7/4)`.  Summing over powers of two is a geometric sum and remains of this
order; a logarithm is not the essential loss.

### 2.3 Exact location of the loss

Combining the two immediate estimates gives

```text
N_X(D) << min(X, D^(1/2)).                       (B0)
```

Write `D=X^delta`, with the relevant large range heuristically
`1 <= delta <= 2`.  The squarefull estimate contributes exponent

```text
7*delta/8,
```

which reaches `7/4` at `delta=2`.  The witness estimate contributes

```text
1 + 3*delta/8,
```

and also reaches `7/4`.  Thus the failure is concentrated toward the largest
modulus shells: generic squarefull geometry permits about `X` candidates when
`D` is of size `X^2`, while the desired rough estimate permits only
`X^epsilon` candidates there.

For comparison, the ASTRA-007 target

```text
N_X(D) <<_epsilon X^(1+epsilon) D^(-1/2)
```

would give shell cost

```text
X^(1+epsilon) D^(-1/8).
```

It decreases with `D`; its worst large shell near `D=X` is
`X^(7/8+epsilon)`, sublinear for `epsilon<1/8`.

## 3. Route ledger

### Route A — square-cube shell geometry

**PRODUCTION-PROVED.**  `M=u^2*r^3`, `r` is squarefree, `r^3<2D`, and every
prime divisor of `u*r` is `1 mod 3`.

**WEAK.**  Fixed `r` gives the short `u` interval above, but summing its length
over all `r` gives only `D^(1/2)`.  The condition `r | d` is already absorbed
by `d=u*r`; it does not improve the generic exponent by itself.

**NUMERIC.**  At `X=10^6`, in the lowest represented shell `D=2^20`, there
are 53 squarefull candidates whose prime support is `1 mod 3`, and 52 distinct
ones are realized.  Thus realization is nearly saturated in this particular
low shell.  At `D=2^37`, the corresponding numbers are 14310 candidates and
1 realization.  The realization gain is strongly shell-dependent and cannot
be replaced by a uniform constant-density assertion.

**Verdict: WEAK alone.**  Retain `D^(1/2)` as one half of a hybrid bound.

### Route B — product incidence

From `D<=M`, `M*S=F(a)`, and `a<=X`, one gets

```text
D*S <= M*S = F(a) <= 3*(X+1)^2.                 (P1)
```

This sharper complement range is

```text
S <= floor(3*(X+1)^2/D).
```

**SCRATCH-PROVED.**  Inequality (P1) is a step in
`realized_shell_pellParameter_height_cube` and was checked against the current
production incidence packet.

**DEAD:** `a -> M` injectivity.  `M=169` has witnesses `21,145`, and
`M=8281` has witnesses `2173,3018,5260,6105`.

**DEAD:** a uniform all-height fixed-`S` bound.  `S=3` occurs along an infinite
Pell family.

**WEAK:** fixed-`M` spacing and CRT root counts control witness fibers over a
known modulus.  They do not upper-bound the number of distinct moduli, because
`N_X(D)<=W_X(D)` points in the opposite direction from a lower bound on fiber
size.

**SURVIVES as input.**  The complement box in (P1) is essential when combined
with a shell-local Pell fiber theorem.

### Route C — Pell/conic incidence

The production equation is

```text
y^2 - 4*T*d^2 = -3,
T=r*S,
M=r*d^2.
```

The shell and product constraints give

```text
r^3 < 2D,
D*S <= 3*(X+1)^2.
```

Cubing `D*T = r*(D*S)` and cancelling one positive factor `D` yields

```text
D^2*T^3 < 54*(X+1)^6.                           (C1)
```

**SCRATCH-PROVED.**  Both the abstract arithmetic lemma and its consumer for
the production Pell-parameter space compile in `scratch-000.lean`.  The
checked axiom set is `[propext, Classical.choice, Quot.sound]`.

Equivalently, in real-size notation,

```text
T < 3*cuberoot(2)*(X+1)^2*D^(-2/3).
```

This is a correct finite search region, but counting every `T` in the region
is still much too generous.

The stronger shell mechanism is obtained by fixing `(T,r)`.  Then `S=T/r`
is fixed and

```text
sqrt(D/r) <= d < sqrt(2D/r),                     (C2)
```

an interval of multiplicative width `sqrt(2)`.

For squarefree `T>1`, put `K=Q(sqrt(T))` and

```text
alpha = y + 2*d*sqrt(T).
```

It is an algebraic integer of norm `-3`.  Its principal ideal has ideal norm
`3`, and a quadratic field has at most two integral ideals of norm `3`.  Two
positive solutions generating the same ideal differ by a totally positive
norm-one unit `epsilon>1`.  Since

```text
epsilon + epsilon^(-1)
```

is an integer at least `3`, and

```text
4*d*sqrt(T) = alpha + 3/alpha,
```

the next solution in that ideal orbit has denominator ratio at least `3/2`.
This exceeds `sqrt(2)`, so (C2) contains at most one solution from each norm-3
ideal orbit.  The rational case `T=1` is elementary and finite.

More explicitly, if `alpha_2=epsilon*alpha_1` and
`x=alpha_1^2/3>1`, then

```text
d_2/d_1
  = (epsilon*x + epsilon^(-1))/(x+1)
  >= (epsilon + epsilon^(-1))/2
  >= 3/2.
```

The first inequality uses `(x-1)(epsilon-epsilon^(-1))>=0`; the second uses
the integral trace of a nontrivial totally positive quadratic unit.

**OPEN / PROMISING.**  This gives a concise route to the fixed-`(T,r)` fiber
bound `<=2`.  The full ideal/unit proof has not been formalized or externally
reviewed in this pass.  In particular, the ring-of-integers normalization and
the `T=1` edge must be checked independently before this is called a theorem.

**NUMERIC.**  Exhaustive factor-sieve scans through `a<=10^6` found maximum
fixed-`(T,r)` shell-fiber cardinality `1` in every represented shell.  This is
diagnostic evidence only.

**Verdict: PROMISING partial route.**

### Route D — squarefree kernel and the `(r,S)` box

Every witness has a unique pair `(r,S)`, with

```text
1 <= r <= floor(cuberoot(2D-1)),
1 <= S <= floor(3*(X+1)^2/D),
Squarefree(r*S),
r | d.
```

Ignoring squarefreeness and support already gives at most

```text
cuberoot(2D) * 3*(X+1)^2/D
  = 3*cuberoot(2)*(X+1)^2*D^(-2/3)               (D1)
```

possible pairs.  The map `(r,S)->T=r*S` is not injective in general, but no
injectivity is needed: index the witnesses by the actual pair `(r,S)`, or
equivalently by `(T,r)`.

**OPEN / SURVIVES.**  Combining (D1) with the Route C fiber bound `<=2` gives

```text
N_X(D) <= W_X(D)
  <= 2*floor(cuberoot(2D-1))*floor(3*(X+1)^2/D)
  << (X+1)^2 D^(-2/3).                           (D2)
```

**WEAK beyond (D2).**  Squarefreeness, coprimality, and prime support
`1 mod 3` can remove logarithmic density, but no proved power saving is
available from those conditions alone.  Requiring an actual primitive conic
point must provide the next gain.

### Route E — paired orientation

**PRODUCTION-PROVED.**  The forward and swap repeated parts are coprime;
ordinary overlap is only at `7`; their product divides
`3*(a+1)^4+a^2`; and the seven-sector residues are exactly forward-deep `29`,
swap-deep `22`, and five shallow states modulo `49`.

**DEAD as an independent shell-count route.**  Exact CRT constructions give
independent depths at `7` and `13`, and production proves that both coprime
repeated parts can be arbitrarily large in absolute size.  The quartic
divisibility has no current height-relative incidence estimate.  The mod-49
split changes only a constant-density local classification and supplies no
decay in `D`.

**Verdict: DEAD for SOL-000.**  Reopen only if a new averaged, height-relative
paired estimate is supplied.

## 4. Branch pruning

The following branches are removed from the candidate set.

1. **Generic squarefull enumeration.**  It ends at `D^(1/2)` and therefore at
   moment exponent `7/4`.
2. **Injective witness/modulus counting.**  The explicit modulus collisions
   refute it.
3. **Uniform fixed-complement counting.**  The complement-3 Pell family
   refutes an all-height `O(1)` statement.
4. **Local Hensel rarity.**  Every admissible simple root lifts uniquely, and
   arbitrary finite depths can be arranged.  Local uniqueness is a
   parametrization, not a density estimate.
5. **Paired depth competition.**  Independent forward/swap exact depths and
   arbitrarily large coprime repeated parts refute an absolute obstruction.
6. **Mod-49 density.**  The three states exhaust the seven-sector; classifying
   them does not shrink the global shell count by a power.

The surviving mechanism uses three facts together: the product bound limits
`S`, square-cube geometry limits `r`, and the dyadic shell makes a fixed
norm-minus-three unit orbit too widely spaced to contribute twice.

## 5. Best candidate theorem

For a witness `a`, write `r(a)=oddPart(M(a))` and `T(a)=r(a)S(a)`.  Define

```text
P_X,D(T,r)
  = { a : 1 <= a <= X,
          X+1 < M(a),
          D <= M(a) < 2D,
          T(a)=T,
          r(a)=r }.
```

The weakest serious new theorem is:

> **Dyadic norm-minus-three fiber theorem (OPEN).**  For every `X,D,T,r`,
> with `T` squarefree, `#P_X,D(T,r) <= 2`.

The constant `2` is tied to the number of ideals of norm `3` in a quadratic
field.  A version with any absolute constant would have the same exponent and
would be enough for the consequence below.

Together with the already proved packet, this theorem implies the explicit
shell estimate

```text
N_X(D)
  <= 2*floor(cuberoot(2D-1))*floor(3*(X+1)^2/D)
  << (X+1)^2 D^(-2/3).                           (CAND)
```

This is nontrivial compared with `D^(1/2)` once

```text
D >> X^(12/7),
```

and compared with the witness bound `X` once `D >> X^(3/2)`.

The theorem survives all known regressions because it fixes both the Pell
field parameter `T` and the cube-core `r`, and it uses one dyadic shell.  It
does not assert a global fixed-`T`, fixed-`S`, or fixed-`M` bound.

## 6. Quantitative exponent propagation

Assuming the candidate fiber theorem, combine (CAND) with (B2):

```text
N_X(D) << min(D^(1/2), X^2 D^(-2/3)).            (H)
```

The two terms meet when

```text
D^(1/2) = X^2 D^(-2/3)
D^(7/6) = X^2
D = X^(12/7).
```

After multiplication by `D^(3/8)`:

```text
D <= X^(12/7):   shell cost << D^(7/8),
D >= X^(12/7):   shell cost << X^2 D^(-7/24).
```

At the crossover both expressions equal

```text
X^((12/7)*(7/8)) = X^(3/2).
```

The first expression increases geometrically over dyadic `D`; the second
decreases geometrically.  Therefore their dyadic sum is

```text
O(X^(3/2)),
```

up to constants and harmless endpoint changes.  This is a power improvement
of `X^(1/4)` over the baseline `X^(7/4)` shell moment.

At the top shell `D` of size `X^2`, (CAND) gives

```text
N_X(D) << X^(2/3),
N_X(D)D^(3/8) << X^(2/3+3/4) = X^(17/12).
```

This is still **superlinear**.  The hybrid worst case `X^(3/2)` is also
superlinear.  Thus the candidate is quantitatively useful but does not close
the capstone or prove ABC.

To reach the ASTRA-007 scale from the `(r,S)` box, the conic-solubility count
must save an additional factor of approximate size

```text
X / D^(1/6)
```

over (CAND).  A uniform fiber theorem alone cannot supply that saving; it must
come from sparsity of represented pairs `(r,S)` or an averaged incidence
estimate across `T`.

## 7. Counterexample and multiplicity audit

### 7.1 Maps used by the counting arguments

| Map | Status | Multiplicity fact | Shell/height mechanism |
|---|---|---|---|
| `a -> M` | not injective | `169` has 2 known witnesses; `8281` has 4 | none controls distinct `M` directly |
| `a -> (M,S)` | injective | the product is `F(a)`, strictly increasing for `a>=0` | exact incidence-pair coordinate |
| `a -> T` | unbounded over all heights | `T=3` along the complement-3 Pell family | fixing one shell is essential |
| `(M,S) -> T` | not known injective | `T=oddPart(M)*S` forgets the factorization into `r,S` | candidate fixes `r` as well |
| `a -> (T,r)` | finite in a shell | **OPEN** candidate bound `<=2` | `M=r*d^2` restricts `d` to width `sqrt(2)` |
| `a ->` paired coordinates | no useful absolute size dichotomy | both repeated parts can be arbitrarily large and coprime | would need a new averaged height theorem |

The shell-cardinality argument deliberately passes through

```text
N_X(D) <= W_X(D) = sum_(T,r) #P_X,D(T,r).
```

No lower bound on modulus-fiber size and no hidden image injectivity is used.

### 7.2 Mandatory regressions

1. **Modulus collisions — PASSED.**  The exact integer scan reproduces
   `M=169` at `a=21,145` and `M=8281` at
   `a=2173,3018,5260,6105`.  The candidate counts witnesses first, so
   collisions only make `N<=W` strict.
2. **Complement-3 Pell family — PASSED.**  The scan reproduces
   `(a,d)=(0,1),(21,13),(312,181),(4365,2521),(60816,35113),...` with
   `M=d^2`, `S=T=3`.  For `X=10^6`, the large-witness fixed-`T` fiber contains
   three points, at `a=4365,60816,847077`, but in three different dyadic
   shells.  The candidate is shell-local and remains compatible.
3. **Independent exact paired depths — PASSED.**  At `a=7428`, the scan checks
   `v_7(F(a))=2` and `v_13(G(a))=2`.  The candidate does not use paired depth
   competition.
4. **Arbitrarily large coprime paired parts — PASSED.**  This production
   theorem removes Route E but has no bearing on the one-orientation norm
   fiber.
5. **Finite Hensel lifting — PASSED.**  The script lists the two roots modulo
   `p^2` for `p=7,13,19,31,37` and checks reduction to the two roots modulo
   `p`.  The candidate uses global unit-orbit spacing after `T,r` are fixed,
   not rarity of local lifts.
6. **All mod-49 states — PASSED.**  Residues
   `1,8,15,22,29,36,43` are classified respectively as five shallow states,
   swap-deep at `22`, and forward-deep at `29`.  No state is discarded by the
   candidate.

### 7.3 Numerical scale diagnostics

The script factors every `F(a)` exactly and independently cross-checks 228
sampled values with `sympy.factorint`.  Selected results are:

| `X` | distinct large `M` over all shells | large witnesses | max modulus fiber | max fixed-`(T,r)` shell fiber | shell moment diagnostic divided by `X` |
|---:|---:|---:|---:|---:|---:|
| 1,000 | 7 | 8 | 2 | 1 | 0.2650 |
| 10,000 | 25 | 28 | 2 | 1 | 0.2593 |
| 100,000 | 86 | 99 | 3 | 1 | 0.2736 |
| 300,000 | 138 | 172 | 4 | 1 | 0.2156 |
| 1,000,000 | 250 | 304 | 4 | 1 | 0.1899 |

The last column uses floating-point powers only as a diagnostic.  Exact
factorization, coordinate identities, shell membership, Pell identities, and
regression assertions use integers.

The fact that the observed fixed-`(T,r)` fiber is `1`, rather than merely `2`,
is not promoted to a conjecture.  The ideal count naturally permits two
orbits, and finite computation cannot remove the second one.

## 8. Mathematical proof plan

This is a mathematics plan, not a production Lean plan.

1. **Define the correct fiber.**  Partition the shell witness set by the exact
   pair `(T,r)`.  Since `S=T/r` on a nonempty fiber, this is equivalent to
   fixing `(r,S)` while retaining the field parameter `T`.
2. **Pass to a norm equation.**  For `T>1`, work in the full ring of integers
   of `K=Q(sqrt(T))` with
   `alpha=y+2d*sqrt(T)`.  Check integrality in both congruence classes of `T`
   and verify `Norm(alpha)=-3`.
3. **Bound ideal orbits.**  Show that `(alpha)` is an integral ideal of norm
   `3`.  Factorization of `(3)` in a quadratic field gives at most two such
   ideals.  This avoids any dependence on the class number.
4. **Control generators of one ideal.**  If two admissible `alpha` generate
   the same ideal, their quotient is a totally positive norm-one unit.
   Order these units by the identity embedding.
5. **Prove the uniform gap.**  A nontrivial totally positive quadratic unit
   satisfies `epsilon+epsilon^(-1)>=3`.  Using
   `4d sqrt(T)=alpha+3/alpha`, prove that the next denominator is at least
   `3d/2`.
6. **Use the dyadic shell.**  With `r` fixed,
   `D<=r d^2<2D` forces any two denominators to have ratio below `sqrt(2)`.
   Since `sqrt(2)<3/2`, each ideal orbit contributes at most one witness.
7. **Handle `T=1`.**  Factor `y^2-4d^2=-3` over the integers and check the
   positive-witness edge directly.
8. **Count parameter pairs.**  Apply `r^3<2D` and
   `D*S<=3(X+1)^2` to count the rectangular `(r,S)` envelope, then sum the
   fiber bound.  Squarefreeness and support restrictions may be retained but
   are not needed for (CAND).
9. **Search for the missing average saving.**  After the fiber theorem is
   settled, study the number of pairs `(r,S)` in this box for which the
   primitive norm equation is soluble.  The required additional saving is
   `X/D^(1/6)`; logarithmic support density cannot suffice.

## 9. ASTRA REVIEW TARGET

1. **Dyadic norm-minus-three fiber theorem.**  Check the claimed bound
   `#P_X,D(T,r)<=2`, especially integrality in the full quadratic ring,
   the number of norm-3 ideals, total positivity of generator quotients, the
   denominator growth inequality `d_next/d>=3/2`, and the `T=1` edge.
2. **Represented `(r,S)` sparsity.**  Decide whether primitive solvability of
   `y^2+3=4rS d^2` with `r|d` can save a power over the box count
   `X^2D^(-2/3)`.  The minimum useful extra factor is `X/D^(1/6)` if the
   original near-linear capstone target is retained.

## 10. Verdict

**Outcome B — meaningful partial mechanism.**

The fixed-`(T,r)` dyadic fiber theorem is precise, survives every known
regression, has a short ideal/unit proof route, and would improve the shell
moment exponent from `7/4` to `3/2`.  It does not make the capstone linear or
sublinear.  No provider, conjecture constant, axiom, production module, public
import, or ABC endpoint has been added.

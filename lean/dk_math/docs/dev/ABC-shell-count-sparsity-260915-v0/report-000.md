# ABC shell-count sparsity — report-000

## Scope and checkout

- Repository: `Deskuma/dkmath`
- Branch: `research/ABC-shell-count-sparsity-260915-v0`
- HEAD at inventory time: `98c53193fc9d97777504ff92e75f9b546c212791`
- Working tree at inventory time: clean
- Lean build directory: `lean/dk_math`
- Governing research contract: this directory's `instruction-000.md`

The user request is to continue the workspace investigation after the branch
change.  The attached document supplies the bounded mathematical scope and
required deliverables.  In particular, the previous Eisenstein factor-counting
Outcome B is an input to this audit, not a request to resume factor-record
normalization.

## Initial production inventory

The exact object to bound is
`GNExcessCubicRealizedLargeModulusShellCount X D`, the cardinality of the
distinct realized repeated moduli in `[D,2D)`.  Production currently supplies:

1. `GNExcessCubicRealizedDyadic`: the exact dyadic shell and its weighted
   moment bounds, including the conditional consumer
   `GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds`.
2. `GNExcessCubicRealizedIncidence`: an actual witness space, its image onto
   the modulus shell, the domination
   `GNExcessCubicRealizedLargeModulusShellCount_le_witnessCount`, exact
   fixed-`M` fiber sums, and the fixed-`M` spacing inequality
   `M ≤ (b-a)*(a+b+3)`.
3. `GNExcessCubicComplementIncidence`: the injective canonical `(M,S)` map,
   exact complement-fiber sum, and incidence-pair cardinality exactly equal to
   the witness count.
4. `GNExcessCubicSquarefulPell` and
   `GNExcessCubicPellParameterIncidence`: exact coordinates
   `M=r*d^2=e^2*r^3`, positivity/squarefreeness, `r^3<2D`, the represented
   parameter `T=r*S`, the fixed-`T` equation
   `(2*a+3)^2+3=4*T*d^2`, and an exact sum of fixed-`T` fiber cards.
5. `GNExcessCubicPrimitivePell` and `GNExcessCubicThreeSector`: coprimality,
   prime-support, square-divisibility, exceptional-prime-3, and primitive
   fixed-`T` packets.  Their module contracts explicitly contain no Pell
   solution count or density estimate.
6. `GNExcessCubicIncidenceObstruction`: a necessary weighted incidence
   inequality, not an upper bound.
7. `GNExcessCubicResearchFrontier`: the deterministic reduction to shell-card
   bounds and the unproved research target of rough size
   `X^(1+epsilon)/sqrt(D)`.
8. `GNExcessCubicEisensteinSquareFactorProvider`: actual factor existence,
   already audited on the preceding branch.  Its raw/canonical factor spaces
   do not improve shell cardinality.

The earlier reports confirm three negative boundaries relevant here:
fixed complement admits unbounded Pell families over unbounded height;
simple-root/Hensel data alone is not global rarity; and all current
`M`/`S`/`T` ledgers are finite identities without sparsity estimates.

## Library search status

The repository contains exact Pell, conic, Mordell-transform, finite-fiber,
and squarefull-coordinate APIs, but the audited surface does not expose a
height-bounded Pell solution count, a divisor-type count for Eisenstein norm
representations, or a uniform integral-point count for the required Mordell
family.  Mathlib contains general algebraic-number/elliptic infrastructure and
finite-cardinality tools, but no directly applicable theorem was found under
the searched representation/cardinality names.  Exact names and any usable
imports will be recorded below if a narrower search finds one.

The next required step is an exact diagnostic of the actual shell object over
a grid of `X`, including distinct moduli, witness multiplicities, `M/S/T`
fibers, and the normalized quantity `N_X(D)*sqrt(D)/X`.

## Actual-shell numerical diagnostic

`scratch/ShellDiagnostics.py` computes the production arithmetic object from
the exact identity `a^2+3*a+3`.  For each `1 ≤ a ≤ X`, it factors the value,
forms the complete repeated prime-power part `M`, retains only witnesses with
`M>X+1`, and groups them by the actual dyadic shell
`D=2^floor(log2 M)`.  Distinct `M` values, rather than witnesses, define
`N_X(D)`.  The stored run uses `sympy.factorint 1.12` and the grid

```text
X = 100, 300, 1000, 3000, 10000, 30000, 100000.
```

The hardest represented shell for each `X`, measured by
`N_X(D)*sqrt(D)/X`, was:

| `X` | `D` | `N_X(D)` | normalized | ambient squarefull `(r,e)` | raw `(r,S)` box |
|---:|---:|---:|---:|---:|---:|
| 100 | 256 | 2 | 0.32000 | 12 | 833 |
| 300 | 256 | 2 | 0.10667 | 12 | 7427 |
| 1000 | 16384 | 2 | 0.25600 | 105 | 5673 |
| 3000 | 65536 | 2 | 0.17067 | 213 | 20600 |
| 10000 | 1048576 | 2 | 0.20480 | 882 | 36322 |
| 30000 | 2097152 | 3 | 0.14482 | 1256 | 207207 |
| 100000 | 4294967296 | 1 | 0.65536 | 58369 | 12282 |

At `X=100000`, the numerically hardest shell lies at
`D/X = 42949.67296`, or `D ≈ 0.4295 X^2`.  Its sole point is

```text
a=88915, M=7906143973, S=1, r=13, d=24661, e=1897, T=13.
```

Thus the hard normalized regime is the high-modulus end `D` comparable with
`X^2`, where the target is essentially constant.  The observed counts remain
very small, but all elementary ambient spaces overcount them by many orders
of magnitude.

Across every represented shell in the stored grid, the largest observed
fixed-`T`, fixed-`S`, fixed-`M`, and fixed Mordell-parameter `(S,e)` witness
fibers were respectively `1`, `2`, `3`, and `1`.  These are diagnostics only.
The production complement-3 Pell family rules out converting the fixed-`S`
observation into a global constant theorem.

The JSON snapshot also records every represented shell, its witness/modulus/
Pell/Mordell parameter counts, coordinate distributions, local quadratic-root
budgets, and the raw bounds forced by current production inequalities.

## Route A — squarefull coordinates and root congruences

Production already proves the canonical identity `M=e^2*r^3`, positivity,
squarefreeness of `r`, and `r^3<2D`.  The scratch theorem
`squarefull_shell_parameter_bounds` additionally checks the neutral
consequence `e^2<2D` from positivity and `M<2D`.

The number of ambient canonical squarefull pairs in `[D,2D)` has the familiar
elementary scale

```text
sum_{r squarefree} sqrt(D/r^3) = O(sqrt D).
```

This reaches the baseline target `X/sqrt(D)` only near the bottom range
`D≲X`.  At `D≈X^2`, it is order `X`, while the target is order `1` (or
`X^epsilon`).  The `X=100000`, `D=2^32` scan makes the failure concrete:
`58369` ambient squarefull pairs versus one realized modulus.

There is more local root-counting infrastructure than the initial inventory
suggested.  `GNLegacyTailCountingBridge` proves:

- `GNDeepLiftResidues_card_base_le`;
- `GNDeepLiftCongruenceUnique_of_simpleRoot`;
- `GNDeepLiftResidues_card_le_of_simpleRoot`;
- `card_gn_deep_lift_range_le_of_residueCover`.

For the cubic nonexceptional channel these give at most two roots per prime
power and an interval count from a residue cover.  What is absent is a CRT
composition followed by a weighted sum over squarefull composite `M`.
Assembling only the product root budget `2^omega(M)` over all ambient
squarefull `M` retains at least the `sqrt(D)` exponent and therefore does not
repair the high-`D` failure.

## Route B — fixed-`T` Pell fibers

Production is already sharper than a generic logarithmic Pell count after
also fixing `r`: the theorem
`GNExcessCubicRealizedLargeModulusShellPellCubeCoreFiber_card_le_one` gives
cardinality at most one for fixed `(T,r)` in a dyadic shell.  Equivalently,
the canonical `(r,S)` map is injective inside the shell.

The remaining problem is therefore the number of represented parameter
pairs, not recurrence length.  From the production bounds

```text
r^3 < 2D,
D*S ≤ 3*(X+1)^2,
```

the direct ambient scale is

```text
#(r,S) ≲ D^(1/3) * X^2/D = X^2*D^(-2/3).
```

Even adding a hypothetical logarithmic fixed-`T` theorem would give at best
this scale times `log X`.  At `D≈X^2` this is `X^(2/3) log X`, far above the
desired `X^epsilon`.  Therefore a height-bounded Pell fiber theorem by itself
is not the missing bridge.

## Route C — Mordell coordinates

The proposed transform is already present in production as
`cubicPell_to_Mordell_identity`, its natural version, the shell witness
wrapper, and the fixed-`(S,e)` Mordell incidence/cardinality ledger.
`scratch/CoordinateBridges.lean` verifies the instruction's normalized form

```text
A*r^3 = y^2+3, U=A*r, V=A*y
=> V^2 = U^3 - 3*A^2.
```

It also kernel-checks full recovery: squarefree-square uniqueness makes
`A=4*S*e^2` determine positive `(S,e)`, after which `U,V` determine `r,y`.
There is no hidden scaling multiplicity under these hypotheses.

No DkMath or Mathlib theorem was found that bounds integral points on this
Mordell family.  More decisively, current bounds allow approximately

```text
#(S,e) ≲ (X^2/D) * sqrt(D) = X^2/sqrt(D)
```

parameter curves.  A uniform constant number of points per curve would still
miss the target by a factor of order `X`.  A useful theorem would have to be
an average estimate coupled across `(S,e)`, not merely a per-curve integral
point bound.

## Hybrid exponent audit

Combining the two strongest elementary ambient bounds gives

```text
N_X(D) ≲ min(sqrt(D), X^2*D^(-2/3)).
```

The two terms balance at `D=X^(12/7)`, where the bound is `X^(6/7)`.
The target there is `X^(1/7+epsilon)`, leaving a loss
`X^(5/7-epsilon)`.  Squarefreeness and coprimality change densities but do
not change this exponent calculation.  The numerical scan likewise shows
that splitting by `r`, `e`, `S`, or `T` leaves ambient boxes much larger than
the realized shell in the high-`D` regime.

## Verdict

**Outcome B — current coordinates still insufficient.**

The actual shell data are very sparse numerically, but the present
squarefull, fixed-`T`, root-congruence, and Mordell ledgers do not explain that
sparsity quantitatively.  Their best direct hybrid loses
`X^(5/7-epsilon)` at its balance point, while the observed hard regime extends
to `D` comparable with `X^2`.  No single missing Pell or per-curve Mordell
theorem would close this exponent gap; a new weighted/average incidence input
across the parameter families is required.  Consequently no production
module is added in this checkpoint.

## Validation

```text
lake env lean docs/dev/ABC-shell-count-sparsity-260915-v0/scratch/CoordinateBridges.lean   exit 0
python3 docs/dev/ABC-shell-count-sparsity-260915-v0/scratch/ShellDiagnostics.py           exit 0
cmp regenerated JSON scratch/ShellDiagnostics-results.json                                exit 0
lake build DkMath.ABC                                                                     exit 0
git diff --check                                                                          exit 0
```

The three scratch theorems report only the standard inherited foundations:
`propext`, and where the reused natural factorization uniqueness theorem is
involved, `Classical.choice` and `Quot.sound`.  There is no `sorry`, `admit`,
new `axiom`, `abc_main_axiom`, `native_decide`, or `unsafe` declaration, and
no production Lean file was changed.

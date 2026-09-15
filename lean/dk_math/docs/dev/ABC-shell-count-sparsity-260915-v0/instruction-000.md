# Instruction-000 — Direct shell-count sparsity audit after factor-counting Outcome B

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-shell-count-sparsity-260915-v0
base: db63fbf2a3add68311c9e85493553684f5f85d35
```

This branch is forked after the provider-backed Eisenstein factor-counting audit.
That audit ended with:

```text
Outcome B — STRUCTURAL NORMALIZATION ONLY
```

The factor provider remains a production success, but raw/canonical factor records did not yield a strict shell-cardinality gain. Do not continue polishing factor-record encodings unless they feed a quantitatively smaller shell-count bound.

The deterministic ABC reduction already stops at the finite arithmetic quantity

```lean
GNExcessCubicRealizedLargeModulusShellCount X D
```

and the existing research target recorded by `GNExcessCubicResearchFrontier` is of rough shape

```text
N_X(D) <= C_epsilon * X^(1+epsilon) / sqrt(D)
```

through the realized large range. This is a research target, not an assumption and not a Lean theorem.

The sole goal of this branch is to decide which existing coordinate system can plausibly produce a genuine upper bound for `N_X(D)`, and to prove any deterministic bridge that materially narrows that gap.

---

## 0. Repository-first audit

Before coding, read and inventory the current production surface around:

```text
DkMath.ABC.GNExcessCubicResearchFrontier
DkMath.ABC.GNExcessCubicRealizedDyadic
DkMath.ABC.GNExcessCubicRealizedIncidence
DkMath.ABC.GNExcessCubicComplementIncidence
DkMath.ABC.GNExcessCubicSquarefulPell
DkMath.ABC.GNExcessCubicPellParameterIncidence
DkMath.ABC.GNExcessCubicPrimitivePell
DkMath.ABC.GNExcessCubicThreeSector
DkMath.ABC.GNExcessCubicIncidenceObstruction
DkMath.ABC.GNExcessCubicEisensteinSquareFactorProvider
```

Also inspect the reports:

```text
docs/dev/ABC-GN-Astra-260906-v0/report-014.md
docs/dev/ABC-GN-Astra-260906-v0/report-015.md
docs/dev/ABC-GN-Astra-260906-v0/report-022.md
docs/dev/ABC-Eisenstein-factor-counting-260915-v0/report-000.md
```

Search current DkMath and Mathlib for reusable results on:

```text
Pell equations / Pell recurrences
binary quadratic forms
squarefull / powerful numbers
quadratic congruence roots
number of divisors / prime support
integral points on elliptic or Mordell curves
finite-set cardinality summation
```

Do not assume a theorem exists because it is mathematically standard. Record exact theorem names and imports when found.

Create:

```text
docs/dev/ABC-shell-count-sparsity-260915-v0/report-000.md
```

and update it throughout the investigation.

---

## 1. Exact coordinates to treat as fixed facts

For a represented shell witness `a`, use the existing canonical notation conceptually as follows:

```text
M := GNExcessCubicFullRepeatedModulus a
S := GNExcessCubicComplement a
r := oddPart M
d := evenPart M
e := GNExcessCubicSquarefulQuotient M
T := r * S
y := 2*a + 3
```

Production already provides the exact identities/conditions of the form

```text
M * S = a^2 + 3*a + 3
M = r * d^2
r | d
d = r * e
M = e^2 * r^3
Squarefree r
Squarefree S
Squarefree T
1 <= S <= X
D <= M < 2*D
y^2 + 3 = 4*T*d^2
Nat.Coprime y d
gcd(y,T) | 3
```

and prime support restrictions for represented moduli.

Do not re-prove these merely under new names.

---

## 2. Numerical scaling diagnostic — mandatory before theorem guessing

Build an exact deterministic diagnostic for the actual shell-count object, not a surrogate.

For a useful grid of `X` values and every represented dyadic shell `D=2^k`, compute at least:

```text
N_X(D)
N_X(D) * sqrt(D) / X
witness count
modulus count
Pell-parameter count
maximum fixed-T fiber size
maximum fixed-S fiber size
maximum fixed-M fiber size
```

When feasible also record distributions of:

```text
r = oddPart M
d = evenPart M
e = squarefulQuotient M
S
T = r*S
```

The purpose is to identify the hardest regime as a function of `D` relative to `X`.

Do not infer an asymptotic theorem from the scan. Use it to falsify bad routes and choose thresholds.

Save reproducible source/results under:

```text
docs/dev/ABC-shell-count-sparsity-260915-v0/scratch/
```

---

## 3. Route A — squarefull-coordinate count

Use the exact production identity

```text
M = e^2 * r^3
```

with squarefree positive `r`.

### 3A. Deterministic parameter bounds

Derive and kernel-check all genuinely useful inequalities forced by

```text
D <= e^2*r^3 < 2*D.
```

Examples to test, not assume:

```text
r^3 < 2*D
1 <= e
D / r^3 <= e^2
```

and any finite interval for `e` for fixed `r`.

### 3B. Count the ambient squarefull parameter space

Determine whether the number of pairs `(r,e)` satisfying the shell inequalities admits an elementary Lean-checkable bound strong enough to matter.

Do not count an ambient `O(sqrt D)`-type statement as progress unless, after combining all other available restrictions, it pushes the actual shell-count frontier.

### 3C. Root congruence route

For fixed `M`, inspect the exact congruence

```text
a^2 + 3*a + 3 = 0 mod M
```

and the existing local facts that all non-three represented primes satisfy `q % 3 = 1` and are simple-root/Hensel controlled.

Audit whether DkMath already has enough to prove a bound for the number of residue classes modulo `M` solving the quadratic. If a bound such as a product over prime supports is available, quantify its contribution after summing over squarefull `M` in `[D,2D)`.

Because the realized range has `M > X+1`, do not silently replace a residue-class count by `X/M`; endpoint effects matter.

---

## 4. Route B — fixed-T Pell fibers

Production already gives, on the fixed Pell-parameter fiber,

```text
y^2 + 3 = 4*T*d^2
```

with primitive/copime conditions.

### 4A. Reject false constant-fiber claims

The existing complement/Pell developments contain infinite increasing Pell-type families. Reconfirm which fixed parameter can have arbitrarily many witnesses over unbounded height. Do not conjecture a uniform constant bound if an existing family refutes it.

### 4B. Height-bounded Pell count

Audit Mathlib and DkMath for a theorem that bounds the number of solutions to a Pell equation below a height by a logarithmic or recurrence-index bound.

If available, specialize it to the exact `T`-fiber equation and state a Lean-shaped shell-fiber bound.

If unavailable, identify the smallest missing theorem. A useful Outcome-P bridge would be something like:

```lean
card (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T)
  <= C * (Nat.log B + 1)
```

for an explicit height `B`, derived from a recurrence or fundamental-unit description, with all exceptional `T` cases identified.

Do not add an axiom or conjecture wrapper.

### 4C. Aggregate test

Even if a fixed-`T` logarithmic bound is obtained, estimate the size of the represented `T` parameter space. Determine whether the aggregate can plausibly approach

```text
X^(1+epsilon) / sqrt(D).
```

If the parameter-space count kills the gain, record that and stop this route.

---

## 5. Route C — Mordell transform from square-cube coordinates

This route is algebraically distinct from the fixed-`T` Pell slicing.

From

```text
y^2 + 3 = 4*S*e^2*r^3
```

set

```text
A := 4*S*e^2
U := A*r
V := A*y
```

and verify in scratch Lean the exact transform

```text
V^2 = U^3 - 3*A^2.
```

Do not treat this algebraic rewrite as a counting theorem.

### 5A. Exact injectivity / recovery audit

Determine exactly which of `(a,r,S,e)` can be recovered from `(A,U,V)` under the production positivity and shell constraints. Record any unit/scaling multiplicity.

### 5B. Integral-point theorem audit

Search DkMath/Mathlib for actual usable integral-point bounds for curves of the form

```text
V^2 = U^3 + K
```

or relevant elliptic/Mordell APIs.

If only external mathematics would supply the bound, state the precise theorem required, including its parameter dependence. Do not write an unsupported wrapper.

### 5C. Aggregate dependence

A bound per Mordell curve is useless if the number of `(S,e)` curves is too large. Compute the resulting aggregate exponent before recommending this route.

The requested verdict must distinguish:

```text
algebraic transform exists
```

from

```text
transform plus a quantitatively sufficient integral-point theorem exists.
```

---

## 6. Two-regime / hybrid optimization

The core task is not to crown one coordinate system prematurely.

Try to combine two valid but individually weak bounds by splitting the shell according to an explicit threshold, for example in one of:

```text
r small / large
e small / large
S small / large
T small / large
```

For each proposed split:

1. state both bounds exactly;
2. optimize the threshold algebraically;
3. compare the resulting exponent with the target `X^(1+epsilon)/sqrt(D)`;
4. test the proposed split numerically on actual realized shells.

A hybrid bound counts as progress only if it is genuinely stronger than all pre-existing ledgers for a nontrivial range and can be stated without a research axiom.

---

## 7. Role of the new Eisenstein provider

The provider is available, but the previous branch established that raw factor records do not compress shell witnesses.

Use it only if it supplies a new restriction on one of the shell coordinates above, for example:

```text
an additional coprimality condition,
a canonical quotient eliminating a multiplicity,
a new norm-support restriction,
or a map into a strictly smaller finite arithmetic space.
```

Do not spend this branch formalizing the six Eisenstein unit associates or a canonical associate merely to recover one record per witness. That is structural normalization, not shell sparsity.

---

## 8. Required outcome classification

Return exactly one principal verdict.

### Outcome A — STRICT SHELL-COUNT GAIN

At least one new kernel-checked theorem gives a nontrivial upper bound for

```lean
GNExcessCubicRealizedLargeModulusShellCount X D
```

or for an exact witness space dominating it, and the bound is strictly stronger than the pre-existing cardinal ledgers in a mathematically useful range.

State the exact range and exponent. Production Lean is allowed only for the load-bearing theorem and reusable neutral lemmas.

### Outcome P — PRECISE QUANTITATIVE BRIDGE MISSING

No sufficient shell bound is yet proved, but the obstruction is reduced to one explicit theorem materially narrower than the original shell-count problem.

Examples:

```text
height-bounded primitive Pell fiber count;
weighted count of roots over squarefull moduli;
uniform/average integral-point bound for the exact Mordell family;
a specific hybrid incidence inequality.
```

State the theorem in Lean-shaped form and show algebraically that it would imply a strict improvement.

### Outcome B — CURRENT COORDINATES STILL INSUFFICIENT

All tested routes reduce to existing incidence data or give bounds too weak in the hard `D/X` regime.

Provide the numerical hard regime and the explicit exponent failure. Add no decorative production module.

---

## 9. Validation / reporting

Required deliverables:

```text
docs/dev/ABC-shell-count-sparsity-260915-v0/report-000.md
scratch Lean files for every claimed algebraic bridge
reproducible numerical diagnostics and stored results
```

For every production theorem, run focused builds, public `DkMath.ABC` build, axiom audit, forbidden-token scan, and `git diff --check`.

Keep the existing trust firewall:

```text
no abc_main_axiom
no new axiom
no sorry/admit
no unsupported external counting theorem
no claim that ABC is proved
```

The desired output is a real shell-count inequality or a sharply identified next theorem — not another reindexing of the same finite set.

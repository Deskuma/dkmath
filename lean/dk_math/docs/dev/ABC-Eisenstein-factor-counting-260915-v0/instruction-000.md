# Instruction-000 — Provider-backed Eisenstein factor counting / balanced-line audit

## Working branch

Work only on:

```text
repository: Deskuma/dkmath
branch: research/ABC-Eisenstein-factor-counting-260915-v0
base provider commit: 11c8416bf5950840bc8d5571291b6b07e94046b2
```

This branch is intentionally forked from the completed Outcome-A provider branch. Do not modify or weaken the provider theorem merely to make counting easier.

The immediately preceding checkpoint is production-proved:

```lean
GNExcessCubicRealizedLargeModulusShellWitness_exists_eisenstein_square_factor
```

For each realized shell witness `a` it supplies `beta gamma : TraceOneInt (-1)` with

```text
alpha := eisensteinCoord ((a : ℤ) + 2) 1
M := GNExcessCubicFullRepeatedModulus a
S := GNExcessCubicComplement a
T := oddPart M * S
d := evenPart M

alpha = beta * gamma^2
natAbs (norm beta) = T
natAbs (norm gamma) = d
```

The old factor-existence gap is CLOSED. The task now is quantitative counting.

---

## 0. Repository-first audit

Before adding production Lean, inspect and record the current theorem surface around:

```text
DkMath.ABC.GNExcessCubicEisensteinSquareFactorProvider
DkMath.ABC.GNExcessCubicEisensteinFactorConsequences
DkMath.ABC.GNExcessCubicRealizedDyadic
DkMath.ABC.GNExcessCubicRealizedIncidence
DkMath.ABC.GNExcessCubicComplementIncidence
DkMath.ABC.GNExcessCubicSquarefulPell
DkMath.ABC.GNExcessCubicPrimitivePell
DkMath.ABC.GNExcessCubicIncidenceObstruction
DkMath.Lib.NumberTheory.EisensteinCoordinates
```

Also inspect any existing Mordell / Pell / lattice-point / divisor-count / finite-box helpers already in the repository or Mathlib before inventing new infrastructure.

Write the initial inventory to:

```text
docs/dev/ABC-Eisenstein-factor-counting-260915-v0/report-000.md
```

The report must distinguish exact finite identities already proved from genuinely missing quantitative estimates.

---

## 1. Central question

The provider gives an actual factor pair for every realized shell witness. Does this allow a STRICTLY SMALLER or quantitatively useful counting space for

```lean
GNExcessCubicRealizedLargeModulusShellWitnessCount X D
```

than the already existing witness / `(M,S)` incidence descriptions?

Do not count the mere existence of another injective encoding as progress. A successful result must create a new cardinality restriction or a path to one.

The desired pipeline is:

```text
realized shell witness a
  -> actual Eisenstein factor pair (beta,gamma)
  -> coefficient-one Bezout line
  -> finite balanced coordinate space
  -> strict fiber/cardinality bound
  -> dyadic shell count bound
```

The task is NOT yet to prove ABC, Helfgott–Venkatesh, or a global Mordell estimate.

---

## 2. Exact coordinate equations — use the production convention

Use standard omega coordinates consistently.

Write

```text
beta  = eisensteinCoord b c
gamma = eisensteinCoord m n
```

and reuse the existing production theorem `eisensteinCoord_mul_sq` / ABC factor consequences instead of re-deriving the multiplication convention by hand.

The coefficient-one equation is already available in production in the form

```text
b * (2*m*n - n^2) + c * (m^2 - 2*m*n) = 1.
```

Define, only if it materially simplifies later statements,

```text
Q(m,n) := 2*m*n - n^2
R(m,n) := m^2 - 2*m*n
```

so every provider factor pair satisfies

```text
b*Q + c*R = 1
IsCoprime Q R
```

and the norm equations

```text
b^2 - b*c + c^2 = T
m^2 - m*n + n^2 = d
```

up to the exact existing `natAbs (norm ...)` convention.

Do not silently replace integer norm statements by natural equalities without proving nonnegativity / sign normalization under the actual coordinate API.

---

## 3. First required new bridge: provider-backed finite factor relation

Build a clean relation or structure for a factor datum belonging to a shell witness. Prefer an application-owned API such as

```lean
structure GNExcessCubicEisensteinFactorData (a : ℕ) where
  beta  : TraceOneInt (-1)
  gamma : TraceOneInt (-1)
  factor_eq : eisensteinCoord ((a : ℤ) + 2) 1 = beta * gamma^2
  beta_norm : ...
  gamma_norm : ...
```

or an equivalent relation if that composes better with finite sets.

Requirements:

1. every realized shell witness has such data, by the production provider;
2. the factor pair determines the cubic coordinate, hence determines `a`;
3. if a classical choice map from shell witnesses to factor data is introduced, prove its injectivity from the factor equality — do not assume uniqueness of factorization;
4. keep the six Eisenstein unit associates visible as multiplicity, not as false uniqueness.

A theorem of the conceptual form

```lean
shellWitnessCount <= admissibleFactorPairSpace.card
```

is useful only if `admissibleFactorPairSpace` is genuinely finite and subsequently admits a nontrivial bound.

---

## 4. Balanced-line theorem — highest priority

This is the main deterministic target.

For a fixed `gamma = (m,n)`, all admissible `beta = (b,c)` lie on the integer Bezout line

```text
b*Q + c*R = 1.
```

Prove a reusable comparison theorem for TWO solutions.

Suggested theorem shape, with signs adjusted to the repository convention:

```lean
theorem eisenstein_coeff_one_solution_difference
    {Q R b c b' c' : ℤ}
    (hcop : IsCoprime Q R)
    (h1 : b*Q + c*R = 1)
    (h2 : b'*Q + c'*R = 1) :
    ∃ k : ℤ,
      b' - b = k * R ∧
      c' - c = -k * Q
```

or an equivalent parametrization.

Do not add this theorem if Mathlib already has an exact linear-Diophantine solution parametrization that is convenient enough.

Then specialize it to the coefficient pair generated by `gamma`.

This theorem is valuable because it reduces beta-counting at fixed gamma from a 2D box to a 1D integer parameter `k`.

---

## 5. Norm geometry / finite coordinate bounds

Establish the smallest reusable coordinate bounds needed to make factor spaces finite.

For Eisenstein norm

```text
N(x,y) = x^2 - x*y + y^2
```

use the positive-definite identity already present or prove a neutral lemma such as

```text
x^2 + y^2 <= 2 * N(x,y)
```

over `ℤ`/`ℕ` in a form suitable for bounding `natAbs x`, `natAbs y`.

Avoid intentionally weak linear-in-norm boxes if a square-root bound is straightforward with existing `Int.natAbs`, `Nat.sqrt`, or real inequalities.

From the provider derive finite bounds for:

```text
|b|, |c| in terms of T
|m|, |n| in terms of d
```

and remember the shell relations

```text
M = oddPart(M) * d^2
D <= M < 2D
T = oddPart(M) * S
1 <= S <= X
```

already exist.

The point of these bounds is not merely executable enumeration. They must feed a cardinality estimate.

---

## 6. Test the strongest deterministic fiber bound available

After the balanced-line theorem, investigate in this order.

### 6.1 Fixed `(gamma,T)` beta multiplicity

The line

```text
b*Q + c*R = 1
```

intersected with the positive-definite norm shell

```text
b^2 - b*c + c^2 = T
```

is the intersection of a line with an ellipse. Determine whether the repository can prove a uniform integer bound such as

```text
# { beta : N(beta)=T and coeffOne(beta,gamma) } <= 2
```

for nondegenerate `gamma`.

Do not assert `<= 2` merely from geometric intuition. Kernel-check the algebraic reduction, including degenerate cases `Q=0` or `R=0` if they can occur under `N(gamma)>0` and the coefficient-one equation.

If an exact bound `1`, `2`, `6`, or another small constant is correct, record the sharp statement.

### 6.2 Fixed gamma with variable T

If fixed-T multiplicity is bounded but summing over all T destroys the gain, parameterize the Bezout line by `k` and derive the exact quadratic norm polynomial

```text
N(beta(k))
```

and the shell restrictions it must satisfy.

Look for a genuinely short interval for `k`, not just a restatement of `a <= X`.

### 6.3 Gamma norm representation count

For `N(gamma)=d`, inspect existing Mathlib / DkMath representation-count results before proving a new divisor bound. If only a crude finite count is available, state it honestly.

Do not import analytic number theory merely to make the report look stronger.

---

## 7. Compare against the existing incidence frontier

The branch is successful only if the factor coordinates improve the actual shell-count problem.

Explicitly compare any new bound with the current production facts:

```text
GNExcessCubicRealizedLargeModulusShellCount_le_witnessCount
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_fiberCards
GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_complementFiberCards
GNExcessCubicRealizedLargeModulusShellIncidencePairSpace_card
GNExcessCubicRealizedLargeModulusMoment_le_of_dyadicShellCardBounds
```

The old `(M,S)` pair is already injective. Replacing it with `(beta,gamma)` is not a gain unless the coefficient-one equation / norm geometry produces a smaller fiber or box.

A claim of progress must identify the strict new restriction explicitly.

---

## 8. Numerical diagnostics — strongly encouraged, never a proof

Extend or create a deterministic Python diagnostic for moderate `X` that records, for realized/relevant cubic points where practical:

- number of provider-compatible `(beta,gamma)` pairs modulo / including units;
- distribution of beta multiplicity for fixed `(gamma,T)`;
- distribution of gamma norm representation counts;
- observed range of the balanced-line parameter `k`;
- comparison between witness count, incidence-pair count, and admissible factor-data count;
- candidate sharp constants and counterexamples to overly optimistic bounds.

If the existing `Diagnostics.py` can be extended cleanly, preserve reproducibility and commit the exact JSON snapshot.

Do not infer an asymptotic theorem from the scan.

---

## 9. Outcome classification

Return exactly one principal outcome in `report-000.md` or a subsequent `report-001.md` if implementation follows the initial audit.

### Outcome A — STRICT FACTOR-COUNTING GAIN

Use only if you kernel-check a new quantitative theorem that makes the shell counting problem strictly stronger than the existing incidence encoding.

Examples include:

```text
uniform small beta fiber at fixed gamma/T
```

plus a finite factor-space injection that yields a genuinely smaller RHS, or an explicit shell-cardinality inequality unavailable before the provider.

State the exact new cardinality bound.

### Outcome P — PRECISE COUNTING BRIDGE MISSING

Use when the provider creates a real new route and all but one narrow quantitative lemma are in place.

Examples:

```text
need representation count for N(gamma)=d
```

or

```text
need a sharp bound for the integer k interval on the Bezout line
```

The missing theorem must be substantially narrower than `factor counting / balanced-box sparsity` as a whole.

### Outcome B — STRUCTURAL NORMALIZATION ONLY

Use if `(beta,gamma)` is merely another encoding of `(M,S,a)` and no strict cardinality improvement survives after all multiplicities are counted.

In Outcome B, do not add decorative production counting modules.

---

## 10. Production rule

Production Lean is authorized for:

- neutral Eisenstein norm-coordinate bounds that are independently reusable;
- the exact coefficient-one solution-difference / balanced-line theorem;
- provider-backed factor-data bridge and injectivity;
- a genuinely nontrivial finite fiber/cardinality theorem.

Do NOT add production modules solely for experimental definitions with no proved counting consequence.

Scratch Lean belongs under:

```text
docs/dev/ABC-Eisenstein-factor-counting-260915-v0/scratch/
```

until its mathematical role is clear.

---

## 11. Validation

At minimum, run focused builds for every changed production module and then:

```text
lake build DkMath.ABC
lake build DkMath.Lib
```

as applicable.

Also run:

```text
git diff --check
```

and scan changed production Lean for:

```text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
```

For load-bearing theorems print axioms and report any dependency beyond the standard inherited kernel/Mathlib foundations.

---

## 12. Scope firewall

Do not claim any of the following without a separate proof:

```text
ABC conjecture
near-linear shell count
Helfgott–Venkatesh
Mordell integral-point bound
uniform divisor-function asymptotics
```

The sole goal of this branch is:

> Convert the newly production-proved Eisenstein square-factor provider into a genuinely quantitative factor-counting restriction, or identify precisely why it does not yet improve the existing shell-incidence frontier.

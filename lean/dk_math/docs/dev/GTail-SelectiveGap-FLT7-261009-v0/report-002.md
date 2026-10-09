# Report 002 — selected factors and coefficient-content boundary

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Outcome **B — algebraic instrument only**. Step 002 is complete; stop before Step 003.

## Changed files

Paths are relative to `lean/dk_math`:

- `DkMath/Lib/Cosmic/GTailFactor.lean`: three definitions and sixteen public theorems.
- `DkMathTest/CosmicFormula/GTailFactor.lean`: focused regressions and all sixteen axiom checks.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-002.md`: pre-edit source/API audit.
- This report and the adjacent `ROADMAP.md`.

The initial working tree was clean. Step 001 sources and all existing theorem
owners remain unchanged. New Lean files follow the repository License header,
import/file-print ordering, documentation, spacing and indentation conventions.
Direct import is `DkMath.Lib.Cosmic.GTailFactor`; façade promotion stays deferred.

## Definitions and mathematical scope

Namespace: `DkMath.CosmicFormula`.

```lean
def activeSelectedIndices (d : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun k => k ∈ S)

def selectedResidual {R : Type*} [CommSemiring R]
    (d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R) : R :=
  ∑ k ∈ activeSelectedIndices d S,
    (Nat.choose d k : R) * x ^ (k - i) * u ^ (j - k)

def coeffGCD (d : ℕ) (S : Finset ℕ) : ℕ :=
  (activeSelectedIndices d S).gcd (Nat.choose d)
```

All definitions are total. Residual exponents use natural subtraction; its
factor theorem explicitly requires upper and lower bounds on active indices.
Raw S can contain arbitrary out-of-range elements, which never contribute.
The factor theorem does not require a nonempty set. For a nonempty active set,
`Finset.min'` and `max'` provide a proved corollary.

The `_hij : i ≤ j` premise follows the requested bound schema. It is redundant
for the termwise proof once all active-index bounds hold, but retained in the
public contract, including its empty-set case. No stronger hypothesis is hidden.

`coeffGCD` is the gcd of raw active Pascal coefficients, not of values after
coordinate evaluation. Its empty-active-set convention is 0, including a
nonempty raw selection with no in-range member. An active endpoint forces 1,
including the single endpoint at degree zero. No polynomial content carrier,
maximal coordinate exponent, evaluated-value gcd equality, cancellation,
nonzero-coordinate requirement, or ring subtraction is introduced.

## Exact theorem signatures

These are the source declaration types; the first two algebraic factor
theorems are explicitly polymorphic over a commutative semiring. Other
factor/content divisibility results are over naturals.

```lean
@[simp] theorem mem_activeSelectedIndices (d : ℕ) (S : Finset ℕ) (k : ℕ) :
    k ∈ activeSelectedIndices d S ↔ k ≤ d ∧ k ∈ S

theorem selectedBody_eq_monomial_mul_residual
    {R : Type*} [CommSemiring R]
    (d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R)
    (_hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    selectedBody d S x u = x ^ i * u ^ (d - j) * selectedResidual d S i j x u

theorem selectedBody_eq_min_max_mul_residual
    {R : Type*} [CommSemiring R]
    (d : ℕ) (S : Finset ℕ) (x u : R)
    (hne : (activeSelectedIndices d S).Nonempty) :
    selectedBody d S x u =
      x ^ (activeSelectedIndices d S).min' hne *
        u ^ (d - (activeSelectedIndices d S).max' hne) *
        selectedResidual d S ((activeSelectedIndices d S).min' hne)
          ((activeSelectedIndices d S).max' hne) x u

theorem monomial_dvd_selectedBody
    (d : ℕ) (S : Finset ℕ) (i j x u : ℕ)
    (hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    x ^ i * u ^ (d - j) ∣ selectedBody d S x u

@[simp] theorem coeffGCD_empty (d : ℕ) : coeffGCD d ∅ = 0

theorem coeffGCD_dvd_choose (d : ℕ) (S : Finset ℕ) (k : ℕ)
    (hk : k ∈ activeSelectedIndices d S) :
    coeffGCD d S ∣ Nat.choose d k

theorem dvd_coeffGCD_iff (d : ℕ) (S : Finset ℕ) (c : ℕ) :
    c ∣ coeffGCD d S ↔ ∀ k ∈ activeSelectedIndices d S, c ∣ Nat.choose d k

theorem dvd_selectedResidual_of_dvd_coeff
    (d : ℕ) (S : Finset ℕ) (i j x u c : ℕ)
    (hc : ∀ k ∈ activeSelectedIndices d S, c ∣ Nat.choose d k) :
    c ∣ selectedResidual d S i j x u

theorem coeffGCD_dvd_selectedBody (d : ℕ) (S : Finset ℕ) (x u : ℕ) :
    coeffGCD d S ∣ selectedBody d S x u

theorem coeffGCD_eq_one_of_zero_mem (d : ℕ) (S : Finset ℕ) (hzero : 0 ∈ S) :
    coeffGCD d S = 1

theorem coeffGCD_eq_one_of_self_mem (d : ℕ) (S : Finset ℕ) (htop : d ∈ S) :
    coeffGCD d S = 1

theorem coeffGCD_mul_monomial_dvd_selectedBody
    (d : ℕ) (S : Finset ℕ) (i j x u : ℕ)
    (hij : i ≤ j) (hjd : j ≤ d)
    (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
    coeffGCD d S * x ^ i * u ^ (d - j) ∣ selectedBody d S x u

@[simp] theorem activeSelectedIndices_interior (d : ℕ) :
    activeSelectedIndices d (Finset.Ico 1 d) = Finset.Ico 1 d

theorem coeffGCD_eq_prime_of_interior
    (p : ℕ) (S : Finset ℕ) (hp : Nat.Prime p)
    (hinterior : ∀ k ∈ activeSelectedIndices p S, 0 < k ∧ k < p)
    (hone : 1 ∈ activeSelectedIndices p S) :
    coeffGCD p S = p

theorem coeffGCD_prime_interior (p : ℕ) (hp : Nat.Prime p) :
    coeffGCD p (Finset.Ico 1 p) = p

theorem prime_mul_coords_dvd_selectedBody_interior
    (p x u : ℕ) (hp : Nat.Prime p) :
    p * x * u ∣ selectedBody p (Finset.Ico 1 p) x u
```

## Proof dependencies and reuse

- `activeSelectedIndices` names exactly the bounded filter already used by
  `selectedBody`, without redefining that Body. Its membership theorem reduces
  to `k ≤ d ∧ k ∈ S`.
- The general factor uses `Finset.sum_congr`, `Finset.mul_sum`, `pow_add`,
  multiplication associativity/commutativity, and `omega` for
  `i+(k-i)=k` and `(d-j)+(j-k)=d-k`. No division or cancellation occurs.
- The extrema adapter uses `Finset.min'_le_max'`, `max'_mem`, `min'_le`,
  and `le_max'` to discharge the general theorem's bounds.
- Natural monomial divisibility uses the residual as the explicit witness.
- Coefficient gcd endpoints adapt `Finset.gcd_dvd` and `dvd_gcd_iff`;
  natural divisibility uses `Finset.dvd_sum` and multiplication divisibility.
  Endpoint gcd 1 follows from `Nat.choose_zero_right` / `choose_self`.
- The combined coefficient/monomial divisor uses divisibility of the residual,
  then multiplies through the exact monomial identity. Coprimality is unnecessary.
- The prime sparse-selection adapter uses `Nat.Prime.dvd_choose_self` for
  all active interior indices and `Nat.choose_one_right` for the retained
  index 1. Two divisibility directions give exact gcd p. Specializing to
  `Ico 1 p` includes p=2 because the only required prime bound is `hp.two_le`.
- The prime Body divisor specializes the combined factor with i=1, j=p-1;
  hence `p-(p-1)=1`, yielding `p*x*u`. It does not infer this product divisor
  merely from separate divisors (which would be invalid without coprimality).

The existing `pascalInnerCommonDivisor` and full-row prime classification were
identified in the inventory. The new general sparse-selection adapter reuses
Mathlib's coefficient divisibility instead of importing that broader owner or
reproving its whole-row classification. GTail recursion and balance are not
replaced or duplicated. The polynomial-content library was inspected, but its
univariate ring carrier is unnecessary for the specified natural coefficient gcd.

## Regression coverage

The focused test module checks:

1. Sparse degree five `{1,3}` gives `x*u^2*(5*u^2+10*x^2)` via the general
   factor theorem and a separately computed residual, rather than an expanded
   Body identity proved only by `ring`. The extrema corollary also type-checks.
2. Generic endpoint singleton Bodies are `u^d` and `x^d`; selections `{0}`,
   `{d}` and `{0,d}` have coefficient gcd 1 for every degree.
3. Empty residual/Body factor, degree-zero endpoint Body 1, degree-zero empty
   gcd 0, and degree-zero out-of-range gcd 0. At degree three `{1,100}` has
   active set `{1}`, exact factor `x*u^2*3`, and coefficient gcd 3.
4. Prime interiors p=2,3,7 have exact coefficient gcd p and Body divisible
   by `p*x*u`. Independent `decide` computations check the degree-3/7 gcds.
   Degree-2 Body is `2*x*u`; degree-3 Body is `3*x*u*(x+u)`. No degree-seven
   norm-square factorization is added.
5. General CommSemiring factor examples, including x=0 and u=0. Each zero
   conclusion is obtained through the factor theorem, with no nonvanishing premise.
6. Sparse prime selection `{1,4,100}` at degree seven has coefficient gcd 7.
   A concrete evaluation has coefficient gcd 3 but Body value 6 at x=u=1,
   documenting that coefficient content is not the evaluated Body itself.

## Exact validation commands and outputs

Working directory: `lean/dk_math`. Final successful runs:

```text
lake build DkMath.Lib.Cosmic.GTailFactor
ℹ [1062/1062] Built DkMath.Lib.Cosmic.GTailFactor (2.1s)
info: DkMath/Lib/Cosmic/GTailFactor.lean:12:0: file: DkMath.Lib.Cosmic.GTailFactor
Build completed successfully (1062 jobs).
exit 0

lake build DkMathTest.CosmicFormula.GTailFactor
ℹ [1063/1063] Built DkMathTest.CosmicFormula.GTailFactor (2.9s)
info: DkMathTest/CosmicFormula/GTailFactor.lean:11:0: file: DkMathTest.CosmicFormula.GTailFactor
Build completed successfully (1063 jobs).
exit 0
```

Both final builds have no warnings/errors. Initial proof iteration encountered
a recursive rewrite and an explicit Finset parameter mismatch; these were
repaired with typed exponent equalities and the correct explicit parameter.
An unused simp argument in the test was removed before the final build.
No theorem statement was strengthened to repair these elaboration issues.

The test executes `#print axioms DkMath.CosmicFormula.<name>` for every
public theorem below. Each output is `[propext, Classical.choice, Quot.sound]`:

- `mem_activeSelectedIndices`
- `selectedBody_eq_monomial_mul_residual`
- `selectedBody_eq_min_max_mul_residual`
- `monomial_dvd_selectedBody`
- `coeffGCD_empty`
- `coeffGCD_dvd_choose`
- `dvd_coeffGCD_iff`
- `dvd_selectedResidual_of_dvd_coeff`
- `coeffGCD_dvd_selectedBody`
- `coeffGCD_eq_one_of_zero_mem`
- `coeffGCD_eq_one_of_self_mem`
- `coeffGCD_mul_monomial_dvd_selectedBody`
- `activeSelectedIndices_interior`
- `coeffGCD_eq_prime_of_interior`
- `coeffGCD_prime_interior`
- `prime_mul_coords_dvd_selectedBody_interior`

The last output wraps the same three names over multiple lines. There are no
nonstandard axioms or `sorryAx` dependencies. Axiom checks are compiled inside
the focused test target, not inferred from a text scan.

Step 001 replay (its sources are untouched):

```text
lake build DkMath.Lib.Cosmic.GTailSelection DkMathTest.CosmicFormula.GTailSelection
Build completed successfully (1047 jobs).
exit 0
```

From repository root:

```text
rg -n '\b(sorry|admit|axiom|unsafe)\b|^import DkMath\.FLT\.' \
  lean/dk_math/DkMath/Lib/Cosmic/GTailFactor.lean \
  lean/dk_math/DkMathTest/CosmicFormula/GTailFactor.lean
(no matches; exit 1)

git diff --check
(no output; exit 0)
```

The production import list is selection plus Mathlib finite gcd, finite maxima,
and prime choose divisibility. The only DkMath dependency is the neutral
selection/GTail kernel. Focused incremental builds were used; no clean or
full-project build is claimed. New files were read back for source review.

## Conclusions and remaining scope

The requested factor and content interfaces are well typed and kernel checked.
The gcd milestone is complete, without fallback or deferred subgoal. No false
specification or added hypothesis required a repair. Outcome B records a finite
algebraic/divisibility instrument, not a new FLT7 obstruction.

Steps 003–007 remain unimplemented: selection transport, degree-seven norm
factorization, FLT7 bridge and constraint audit, and façade promotion. There
is no claim about maximal monomial factors, evaluated gcd exactness, valuation
preservation, descent, or FLT7 closure. Work stops after instruction 002.

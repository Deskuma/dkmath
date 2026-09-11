# FLT prime-generalization Phase 20 — real TraceOne signature bridge and Dirichlet sectors

## Goal

Unblock the real prime-discriminant branch from Phase 19 without relying on a field-discriminant equality that is not currently exposed.

For an odd prime `p` with

```text
p % 4 = 1
```

set

```text
s := signedPrimeParameter p
K := TraceOneRat s
R := TraceOneInt s
```

so the quadratic discriminant is `D_p = p > 0`.

The Phase-20 target is:

1. prove `NumberField.IsTotallyReal K` directly from the explicit quadratic equation;
2. deduce the real-quadratic signature / unit rank `1`;
3. build a genuine `UnitPowerSectorSystem R p` with `Sector := Fin p` from Dirichlet's unit theorem;
4. transport it through the Phase-17 ring-of-integers equivalence;
5. compose with Phase 18 so class-group principalization yields
   `a = rep i * delta ^ p` for some `i : Fin p`.

Do **not** attempt sector elimination, FLT contradiction, class-group torsion-freeness, regular-prime theory, or a general field-discriminant formula in this phase.

Success classifications:

```text
PGEN-TRACEONE-REAL-SIGNATURE-GREEN
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-GREEN
```

Fallback classification if the direct signature route is blocked:

```text
PGEN-TRACEONE-REAL-SIGNATURE-API-BLOCKED
```

---

## A. Test-first API audit

Create or extend a focused audit file, e.g.

```text
DkMathTest/FLT/Prime/TraceOneRealSignatureApiAudit.lean
```

Pin the exact signatures available in the current Mathlib checkout for at least:

```text
NumberField.IsTotallyReal
NumberField.isTotallyReal_iff
NumberField.maximalRealSubfield
NumberField.mem_maximalRealSubfield_iff
NumberField.maximalRealSubfield_eq_top_iff_isTotallyReal
NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
NumberField.IsTotallyReal.finrank
NumberField.InfinitePlace.card_add_two_mul_card_eq_rank
NumberField.Units.rank
NumberField.Units.fundSystem
NumberField.Units.exist_unique_eq_mul_prod
NumberField.Units.torsion
NumberField.RingOfIntegers.equiv
RingEquiv.toMonoidHom
Units.map
Units.val_zpow_eq_zpow_val
```

Also pin whatever complex-number API is actually used for:

```text
Complex.re
Complex.im
Complex.ext
map_add/map_mul/map_pow
star / conj
```

and the exact rational-scalar coercion lemmas needed for ring homomorphisms into `ℂ`.

Do not code against remembered theorem names.

---

## B. Direct real-signature bridge

### B1. Avoid `NumberField.discr` as the primary route

Do **not** make the theorem

```text
NumberField.discr K = signedPrimeDiscriminant p
```

a prerequisite unless the pinned API makes it trivial.

Instead prove total reality directly from the explicit quadratic relation.

For

```text
K := TraceOneRat (signedPrimeParameter p)
```

let `omega` denote the `QuadraticAlgebra` generator.  Under

```text
hp   : Nat.Prime p
hmod : p % 4 = 1
```

we have

```text
discr (signedPrimeParameter p) = p
```

and hence the generator relation is equivalent to a quadratic with positive discriminant.

### B2. Core complex-root lemma

Prove a neutral lemma of the following mathematical shape:

```text
if z : ℂ satisfies z^2 - z - s = 0
and 1 + 4*s > 0,
then z.im = 0.
```

For the prime specialization, use `1 + 4*s = p`.

Suggested proof:

Write `z = x + y i`.  Taking imaginary parts gives

```text
y * (2*x - 1) = 0.
```

If `y ≠ 0`, then `2*x = 1`.  Substituting in the real-part equation yields

```text
y^2 = -(1 + 4*s)/4.
```

which contradicts positivity of the discriminant.

This avoids choosing `Real.sqrt p`, avoids explicit root enumeration, and avoids a field-discriminant calculation.

A theorem specialized to `signedPrimeParameter p` is acceptable if that materially simplifies Lean.

### B3. Every complex embedding is real on `omega`

For any

```lean
φ : K →+* ℂ
```

use preservation of the defining quadratic relation to show

```text
(φ omega).im = 0.
```

Then prove every element of `K` maps to a real complex number by the two-coordinate decomposition

```text
x = a + b * omega
```

with `a b : ℚ`.

Prefer reusing existing `QuadraticAlgebra` coordinate decomposition / extensionality APIs from Phase 17 rather than introducing a new field model.

### B4. Package total reality

Preferred route if the pinned APIs fit cleanly:

1. prove every `x : K` belongs to `NumberField.maximalRealSubfield K` using
   `NumberField.mem_maximalRealSubfield_iff`;
2. conclude
   `NumberField.maximalRealSubfield K = ⊤`;
3. use
   `NumberField.maximalRealSubfield_eq_top_iff_isTotallyReal`.

Alternative: construct `NumberField.IsTotallyReal K` directly from infinite-place `IsReal` evidence if that is shorter in the pinned API.

Expose a production theorem such as

```lean
traceOneRat_isTotallyReal_of_prime_mod_four_eq_one
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    NumberField.IsTotallyReal
      (TraceOneRat (signedPrimeParameter p))
```

under the explicit `Field` / `NumberField` instances already used in Phase 17.

Classification on success:

```text
PGEN-TRACEONE-REAL-SIGNATURE-GREEN
```

---

## C. Rank-one Dirichlet consequence

For the same `K`, prove the exact real-quadratic signature facts needed for units.

Target facts:

```text
Module.finrank ℚ K = 2
nrComplexPlaces K = 0
nrRealPlaces K = 2
NumberField.Units.rank K = 1
```

Use the smallest available chain from the pinned API.  Expected ingredients are:

- Phase-17 quadratic/number-field realization;
- the explicit two-dimensional `QuadraticAlgebra` basis;
- the new `IsTotallyReal K`;
- `NumberField.IsTotallyReal.finrank` or
  `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`;
- the definition/theorem for `NumberField.Units.rank`.

Do not hardcode `r₁=2` without a kernel-checked derivation.

Expose a theorem or simp-normal form making

```text
NumberField.Units.rank K = 1
```

usable downstream.

---

## D. Rank-one unit decomposition modulo `p`-th powers

### D1. Use `exist_unique_eq_mul_prod`

For

```text
u : (NumberField.RingOfIntegers K)ˣ
```

Dirichlet gives

```text
u = torsion_part * ∏ i, fundSystem K i ^ exponent_i.
```

After rewriting `rank K = 1`, reduce the product to one fundamental unit `ε` and one exponent `n : ℤ`.

Do not manually reprove Dirichlet's theorem or construct a Pell fundamental unit.

### D2. Torsion absorption for odd `p`

The final sector system should have only `Fin p`, not an unnecessary sign/roots-of-unity factor.

For a real quadratic field, the torsion unit is expected to be `±1`.  Prove only the exact statement needed to absorb the torsion factor into a `p`-th power for odd prime `p`.

Possible routes:

- show the relevant torsion unit has order dividing `2`, then odd `p` makes the `p`-power map an automorphism on that 2-torsion;
- or prove directly that real roots of unity are `±1` using the totally-real embedding / roots-of-unity API.

Do not assume `torsion_part = ±1` without proof.

If the pinned Dirichlet decomposition already packages torsion in a form with a ready-made odd-power absorption theorem, use it.

### D3. Reduce the integer exponent modulo `p`

For the fundamental unit exponent `n : ℤ`, write

```text
n = r + p*q
```

with

```text
0 ≤ r < p.
```

Use the pinned integer quotient/remainder API audited in Phase 19.

Convert `r` to

```lean
i : Fin p
```

and use `zpow_add` / `zpow_mul` (exact pinned names) to obtain

```text
ε^n = ε^r * (ε^q)^p.
```

Combine with torsion absorption to get

```text
u = ε^i * e^p.
```

---

## E. Build the real `Fin p` sector system on the ring of integers

Define a `UnitPowerSectorSystem` first on

```text
NumberField.RingOfIntegers K
```

with

```lean
Sector := Fin p
rep i := ε ^ (i : ℕ)
```

(or the exact transported unit form required by the pinned APIs).

The completeness theorem must be genuine:

```text
∀ u, ∃ i : Fin p, ∃ e, u = rep i * e^p.
```

No uniqueness of the sector is required by Phase 18.

---

## F. Transport sectors to `TraceOneInt`

Use the Phase-17 equivalence

```text
traceOneRat_ringOfIntegers_equiv
```

to transport the unit-sector system from the ring of integers to

```text
R := TraceOneInt (signedPrimeParameter p).
```

Use the pinned

```text
RingEquiv.toMonoidHom
Units.map
```

route.  Do not introduce an unsupported `RingEquiv.unitsEquiv` name.

Expose a production definition such as

```lean
traceOnePrimeRealFinSectorSystem
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    UnitPowerSectorSystem
      (TraceOneInt (signedPrimeParameter p)) p
```

with sector type definitionally or provably equivalent to `Fin p`.

Classification on success:

```text
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-GREEN
```

---

## G. Compose with Phase 15/16/18

Add a conditional endpoint for the real branch:

```text
span {a} = I^p
I ≠ 0
classGroupPTorsionFreeAt R p
--------------------------------
∃ i : Fin p, ∃ delta,
  a = rep i * delta^p
```

Use the Phase-18 theorem

```text
exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
```

rather than duplicating class-group / principal-ideal reasoning.

Do **not** eliminate `i ≠ 0` in this phase.

---

## H. Finite regressions

Add a focused probe, e.g.

```text
DkMathTest/FLT/Prime/TraceOneRealUnitSectorProbe.lean
```

Required checks:

### p = 5

```text
signedPrimeParameter 5 = 1
IsTotallyReal (TraceOneRat 1)
Units.rank (TraceOneRat 1) = 1
TraceOneInt 1 has a Fin 5 sector system
```

This is on the new TraceOne carrier.  Do not claim that this is definitionally the old `GoldenInt` implementation.

### p = 13

```text
signedPrimeParameter 13 = 3
IsTotallyReal (TraceOneRat 3)
Units.rank (TraceOneRat 3) = 1
TraceOneInt 3 has a Fin 13 sector system
```

### p = 7 / 11

Keep the Phase-19 imaginary singleton regression intact and ensure no real-branch import breaks it.

### p = 3

Keep the existing Eisenstein exception explicit; do not collapse it into the `p >= 7` imaginary singleton theorem.

---

## I. Axiom / forbidden-construct audit

Create an axiom audit for all new public production declarations.

Required checks:

```text
#print axioms <total-reality theorem>
#print axioms <unit-rank theorem>
#print axioms <real Fin-p sector system / completeness theorem>
#print axioms <conditional real sector endpoint>
```

No new:

```text
sorry
sorryAx
admit
axiom
unsafe
```

in fresh production/test files.

Inherited standard axioms such as `propext`, `Classical.choice`, and `Quot.sound` are acceptable if they arise from Mathlib/choice-based number-field APIs.

---

## J. Focused builds

At minimum:

```text
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.NumberTheory.TraceOnePrimeUnitSectors
lake build DkMath.Lib.NumberTheory.UnitPowerSector
lake build DkMathTest.FLT.Prime.TraceOneRealSignatureApiAudit
lake build DkMathTest.FLT.Prime.TraceOneRealUnitSectorProbe
lake build <new axiom audit>
lake build DkMath.FLT.Seven
git diff --check
```

Run a fresh warning/error scan and distinguish the pre-existing
`ZsigmondyCyclotomicResearch.lean:147` `sorry` warning from Phase-20 output.

---

## K. Report

Create

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-020.md
```

The report must separate:

1. direct `TraceOneRat` total-reality proof;
2. signature/unit-rank derivation;
3. Dirichlet rank-one decomposition;
4. torsion absorption for odd `p`;
5. exponent reduction mod `p`;
6. ring-of-integers `Fin p` sector system;
7. transport to `TraceOneInt`;
8. Phase-18 conditional sector endpoint;
9. p=5 / p=13 regressions;
10. remaining non-goals: class-group torsion-freeness, sector elimination, FLT.

If the direct total-reality proof is blocked, stop honestly and record the exact missing theorem/signature under

```text
PGEN-TRACEONE-REAL-SIGNATURE-API-BLOCKED
```

Do not replace the missing bridge by an assumption merely to obtain the GREEN label.

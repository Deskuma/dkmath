# FLT prime-generalization Phase 19 — TraceOne prime-discriminant unit sectors

## Scope and outcome

This report records the bounded implementation requested by
`instruction-019.md`.  The phase constructs the generic imaginary
prime-discriminant unit sector and keeps the real Dirichlet construction
explicitly blocked at the missing quadratic-signature transport.  It does
not prove FLT, class-group p-torsion-freeness, regular-prime results, or
sector elimination.

The two branch statuses are separate:

~~~text
PGEN-TRACEONE-IMAGINARY-UNIT-SINGLETON-GREEN
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-API-BLOCKED
~~~

## A. Pinned API audit

The test-first audit is
`DkMathTest/FLT/Prime/TraceOnePrimeUnitSectorApiAudit.lean`.
The following declarations compile in the pinned checkout.

### Dirichlet unit API

~~~lean
NumberField.Units.rank (K : Type) [Field K] [NumberField K] : ℕ

NumberField.Units.fundSystem (K : Type) [Field K] [NumberField K] :
  Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ

NumberField.Units.exist_unique_eq_mul_prod (K : Type) [Field K]
    [NumberField K] (x : (NumberField.RingOfIntegers K)ˣ) :
  ∃! ζe, x = ↑ζe.1 * ∏ i, NumberField.Units.fundSystem K i ^ ζe.2 i

NumberField.Units.basisModTorsion (K : Type) [Field K] [NumberField K] :
  Module.Basis (Fin (NumberField.Units.rank K)) ℤ
    (Additive ((NumberField.RingOfIntegers K)ˣ /
      NumberField.Units.torsion K))

NumberField.Units.finrank_modTorsion K :
  Module.finrank ℤ (Additive ((NumberField.RingOfIntegers K)ˣ /
    NumberField.Units.torsion K)) = NumberField.Units.rank K

NumberField.Units.rank_modTorsion K :
  Module.finrank ℤ (Additive ((NumberField.RingOfIntegers K)ˣ /
    NumberField.Units.torsion K)) = NumberField.Units.rank K
~~~

`finrank_modTorsion` is the current pinned declaration; the audit also
confirms that `rank_modTorsion` is available as the compatibility alias.

### Signature and transport API

~~~lean
NumberField.InfinitePlace.nrRealPlaces K : ℕ
NumberField.InfinitePlace.nrComplexPlaces K : ℕ

NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K :
  nrRealPlaces K + 2 * nrComplexPlaces K = Module.finrank ℚ K

NumberField.sign_discr K :
  (NumberField.discr K).sign = (-1) ^ nrComplexPlaces K

NumberField.IsTotallyReal.nrComplexPlaces_eq_zero K :
  [IsTotallyReal K] → nrComplexPlaces K = 0

NumberField.IsTotallyReal.finrank K :
  [IsTotallyReal K] → Module.finrank ℚ K = nrRealPlaces K

NumberField.RingOfIntegers.equiv (R) :
  NumberField.RingOfIntegers K ≃+* R

RingEquiv.toMonoidHom (e : R ≃+* S) : R →* S
Units.map (f : R →* S) : Rˣ →* Sˣ
Units.val_zpow_eq_zpow_val (u : Rˣ) (n : ℤ) :
  ↑(u ^ n) = (↑u : R) ^ n
~~~

The actual totally-real helper used by the audit is also available as
`NumberField.IsTotallyReal.nrComplexPlaces_eq_zero`; the corresponding iff is
`NumberField.InfinitePlace.nrComplexPlaces_eq_zero_iff`.
Unit transport therefore uses the pinned `e.toMonoidHom`/`Units.map` route.
There is no `RingEquiv.unitsEquiv` declaration in this checkout.

### Integer exponent API

~~~lean
zpow_add₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n
zpow_mul (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ m) ^ n

Int.ediv_emod_unique {a b r q : ℤ} (h : 0 < b) :
  a / b = q ∧ a % b = r ↔
    r + b * q = a ∧ 0 ≤ r ∧ r < b
Int.ediv_mul_add_emod (a b : ℤ) : a / b * b + a % b = a
Int.emod_nonneg (a : ℤ) {b : ℤ} : b ≠ 0 → 0 ≤ a % b
Int.emod_lt (a : ℤ) {b : ℤ} (h : b ≠ 0) : a % b < ↑b.natAbs
~~~

The audit found no pinned `Int.ediv_emod` constant; the quotient/remainder
names above are the ones available for the planned real-branch normalization.

## B. Imaginary branch: `p % 4 = 3`, `p >= 7`

The production module is
`DkMath/NumberTheory/TraceOnePrimeUnitSectors.lean`.  It imports the
Phase-17 TraceOne field/maximal-order module and the neutral Phase-18
`UnitPowerSector` API; it has no `DkMath.FLT.*` import.

For
`R = TraceOneInt (signedPrimeParameter p)`, the implementation first rewrites
the prime discriminant as `-p` and proves the positive norm identity

~~~text
4 * norm <a,b> = (2*a+b)^2 + p*b^2.
~~~

The same identity proves that every nonzero element has positive norm.  A
unit and its inverse have multiplicative norms with product one, so a unit
has norm one.  When `p >= 7`, the norm-one equation forces `b = 0` and then
`a = 1` or `a = -1`.  The public result is:

~~~lean
traceOnePrimeImaginary_unit_eq_one_or_neg_one
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (u : (TraceOneInt (signedPrimeParameter p))ˣ) :
    (u : TraceOneInt (signedPrimeParameter p)) = 1 ∨
      (u : TraceOneInt (signedPrimeParameter p)) = -1
~~~

Since `p` is odd, both signs are p-th powers.  The production definition
`traceOnePrimeImaginarySingletonSectorSystem` consequently provides a genuine
`UnitPowerSectorSystem R p` with `Sector := PUnit`.

The theorem
`traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow` composes this singleton
system with the Phase-16/18 principal-ideal endpoint.  Under the explicit
nonzero ideal, class-group p-torsion-free, and span hypotheses it returns
`a = delta ^ p`.  This is a conditional local endpoint; it is not a proof of
the class-group hypothesis or FLT.

### p=3 exception

The probe keeps p=3 on the existing Eisenstein carrier and checks
`exists_sector_mul_cube_of_unit`.  It does not force p=3 through the
singleton theorem: the extra unit classes are represented by
`1`, `tau`, and `tau^2` modulo cubes.

## C. Real branch: `p % 4 = 1`

Status:

~~~text
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-API-BLOCKED
~~~

The pinned Dirichlet decomposition and unit transport APIs are present, but
the current Phase-17 TraceOne module does not provide the smallest necessary
quadratic signature bridge for
`K := TraceOneRat (signedPrimeParameter p)`.

What is already available is:

~~~lean
traceOneRatField
traceOneRat_numberField
traceOneRat_isIntegralClosure
traceOneRat_ringOfIntegers_equiv
~~~

The missing source-level theorem is an explicit bridge of the following
form, or an equivalent pair of results:

~~~lean
IsTotallyReal (TraceOneRat (signedPrimeParameter p))
-- from hp : Nat.Prime p and hmod : p % 4 = 1

NumberField.discr (TraceOneRat (signedPrimeParameter p)).sign = 1
-- or an equality/sign theorem connecting NumberField.discr K to
-- signedPrimeDiscriminant p
~~~

`NumberField.sign_discr` only translates an already-known field-discriminant
sign into `nrComplexPlaces`; it does not connect the `TraceOne` norm
discriminant to `NumberField.discr K`.  Likewise,
`traceOneRat_ringOfIntegers_equiv` transports the integral closure but does
not prove that the quadratic field is totally real.  Consequently the
required chain

~~~text
finrank_Q K = 2 -> nrComplexPlaces K = 0 -> nrRealPlaces K = 2
             -> NumberField.Units.rank K = 1
~~~

cannot be kernel-checked from the currently exposed APIs without adding that
bridge.  The rank-one Dirichlet decomposition, torsion sign proof, `Fin p`
sector definition, and transported real-sector endpoint are therefore not
asserted in this phase.  No stronger assumption was inserted to disguise the
gap.

The units-equivalence transport itself is not the blocker: once a suitable
ring equivalence is available, `RingEquiv.toMonoidHom` and `Units.map` provide
the required map and inverse map.  The quotient/remainder and zpow APIs were
also confirmed in Part A.

## D. p=5 and carrier boundary

The probe verifies the generic TraceOne parameters

~~~text
signedPrimeParameter 5 = 1
signedPrimeParameter 13 = 3.
~~~

The old p=5 theorem remains checked as
`goldenUnitClassesModFifth : GoldenUnitClassesModFifth`; its carrier is the
predicate `GoldenUnit` on `GoldenInt`, not `GoldenIntˣ`.  No fake coercion or
unsupported `GoldenIntˣ ≃+* TraceOneInt 1` bridge was added.  Because Part C
is blocked, a generic five-sector or thirteen-sector TraceOne production
system is not claimed.

## E. Finite regressions

The Phase-19 probe is
`DkMathTest/FLT/Prime/TraceOnePrimeUnitSectorProbe.lean`.

~~~text
p=3   existing Eisenstein 3-sector compatibility: checked
p=5   signed parameter / old GoldenUnit carrier audit: checked; generic real sector blocked
p=7   imaginary singleton sector: checked
p=11  imaginary singleton sector: checked
p=13  signed parameter / real carrier audit: checked; generic real sector blocked
~~~

These are API and sector regressions only.  They do not assert FLT5, FLT7,
FLT11, or FLT13.

## F. Post-Phase-19 frontier

For the imaginary branch with `p % 4 = 3` and `p >= 7`, the unit obstruction
has disappeared.  After the existing principal-ideal factorization, the
remaining arithmetic condition before exact p-th-power extraction is exactly

~~~text
classGroupPTorsionFreeAt R p.
~~~

For the real branch with `p % 4 = 1`, the intended future result is a finite
`Fin p` unit-sector system.  Even after class-group principalization, the
output would be only

~~~text
a = rep i * delta^p,  for some i : Fin p.
~~~

The future FLT work is to eliminate nonzero sectors from the specific
TraceOne/GTail coordinate equation.  This is a different frontier from the
imaginary singleton case and from the existing p=5 GoldenUnit proof.

## G. Axiom and forbidden-construct audit

The audit file is
`DkMathTest/FLT/Prime/TraceOnePrimeUnitSectorAxiomAudit.lean`.
The three new public imaginary declarations report only the standard
inherited Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
The fresh scan of the Phase-19 production and test sources found no
`sorry`, `sorryAx`, `admit`, explicit `axiom`, or `unsafe` occurrence.

## Verification

The focused Phase-19 build passed:

~~~text
lake build DkMath.NumberTheory.TraceOneQuadraticField \
  DkMath.NumberTheory.TraceOnePrimeUnitSectors \
  DkMath.Lib.NumberTheory.UnitPowerSector \
  DkMath.Lib.NumberTheory.PrincipalIdealPower \
  DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorApiAudit \
  DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorProbe \
  DkMathTest.FLT.Prime.TraceOnePrimeUnitSectorAxiomAudit \
  DkMath.FLT.Seven
~~~

`git diff --check` passed.  The focused build retained the pre-existing
warning at
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147` (declaration uses
`sorry`); after excluding that known warning, the fresh warning scan was
empty.  That unrelated warning is not attributed to Phase 19.

# FLT prime-generalization Phase 19 — TraceOne prime-discriminant unit sectors

## Goal

Phase 18 introduced the neutral `UnitPowerSectorSystem R p` interface and connected
class-group principalization to a sector-normalized element equation.

Phase 19 should now construct concrete sector systems for the arbitrary odd-prime
TraceOne carrier

```lean
TraceOneInt (signedPrimeParameter p)
```

using the Phase-17 maximal-order / number-field transport.

Do **not** prove FLT, class-group p-torsion-freeness, regular-prime theorems, or
sector elimination in this phase.

The central mathematical split is by the sign of

```text
D_p = signedPrimeDiscriminant p = (-1)^((p-1)/2) * p.
```

For odd primes:

```text
p % 4 = 3  -> D_p = -p < 0   (imaginary quadratic)
p % 4 = 1  -> D_p = +p > 0   (real quadratic)
```

The two unit-sector mechanisms are genuinely different and should remain explicit.

---

## Part A — pinned API audit first

Before production code, audit the pinned Mathlib checkout for the exact declarations
needed below. Record exact names/signatures in `report-019.md`.

At minimum inspect:

1. Dirichlet unit theorem:
   - `NumberField.Units.rank`
   - `NumberField.Units.fundSystem`
   - `NumberField.Units.exist_unique_eq_mul_prod`
   - `NumberField.Units.basisModTorsion`
   - `NumberField.Units.rank_modTorsion`

2. number-field signatures:
   - `NumberField.InfinitePlace.nrRealPlaces`
   - `NumberField.InfinitePlace.nrComplexPlaces`
   - `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank`
   - `NumberField.sign_discr`
   - totally-real / totally-complex helpers if useful

3. units transport through ring equivalences:
   - the pinned `RingEquiv` / `Units` map/equivalence API
   - how to transport `(𝓞 K)ˣ` to
     `(TraceOneInt (signedPrimeParameter p))ˣ` using
     `traceOneRat_ringOfIntegers_equiv`

4. integer exponent decomposition:
   - `zpow`
   - Euclidean quotient/remainder APIs for `ℤ`
   - conversion of `epsilon ^ (p*q+r)` into
     `epsilon^r * (epsilon^q)^p`

Do not rely on remembered upstream names where the pinned checkout differs.

---

## Part B — imaginary branch: `p % 4 = 3`

### B1. classify units directly for `p >= 7`

For

```lean
R := TraceOneInt (signedPrimeParameter p)
```

with

```text
hp    : Nat.Prime p
hp7   : 7 <= p
hmod  : p % 4 = 3
```

prove that every unit is `±1`.

Use the TraceOne norm identity rather than Dirichlet theory.

When `D_p = -p`, for `x = <a,b>`:

```text
4 * norm(x) = (2*a+b)^2 + p*b^2.
```

A unit has norm `1` in this imaginary quadratic order. Hence

```text
(2*a+b)^2 + p*b^2 = 4.
```

Since `p >= 7`, necessarily `b = 0`, hence `a = ±1`.

Target theorem shape, naming may be adjusted:

```lean
theorem traceOnePrimeImaginary_unit_eq_one_or_neg_one
    {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) (hmod : p % 4 = 3)
    (u : (TraceOneInt (signedPrimeParameter p))ˣ) :
    (u : TraceOneInt (signedPrimeParameter p)) = 1 ∨
    (u : TraceOneInt (signedPrimeParameter p)) = -1
```

Keep the proof generic in `p`; do not enumerate p=7,11,19,...

### B2. singleton sector for odd p

For odd p, both `1` and `-1` are p-th powers in the unit group:

```text
1  = 1^p
-1 = (-1)^p.
```

Therefore construct

```lean
traceOnePrimeImaginarySingletonSectorSystem
```

with sector type `PUnit` for `p >= 7`, `p % 4 = 3`.

This should be a genuine `UnitPowerSectorSystem R p`.

Then compose with Phase 18 / Phase 16 to expose the conditional exact-power endpoint:

```text
span {a} = I^p
classGroupPTorsionFreeAt R p
--------------------------------
a = delta^p
```

for the imaginary branch, because the unit obstruction has disappeared.

Classification if green:

```text
PGEN-TRACEONE-IMAGINARY-UNIT-SINGLETON-GREEN
```

### B3. p=3 is exceptional

Do not force p=3 into the singleton theorem.

Reuse/audit the existing Eisenstein 3-sector result and record that the extra roots of
unity make p=3 exceptional:

```text
1, tau, tau^2 modulo cubes.
```

A compatibility adapter to `UnitPowerSectorSystem` may remain test-side if it already
exists from Phase 18.

---

## Part C — real branch: `p % 4 = 1`

The intended result is a generic p-sector system on

```lean
TraceOneInt (signedPrimeParameter p)
```

without choosing an explicit Pell fundamental unit by hand.

Use the Phase-17 equivalence with the ring of integers of

```lean
K := TraceOneRat (signedPrimeParameter p)
```

and Mathlib's Dirichlet unit theorem.

### C1. prove the quadratic signature / unit rank

For

```text
hp   : Nat.Prime p
hmod : p % 4 = 1
```

prove or obtain from the pinned API:

```text
finrank_Q K = 2
nrComplexPlaces K = 0
nrRealPlaces K = 2
NumberField.Units.rank K = 1.
```

Prefer deriving the signature from the positive signed discriminant and the known
quadratic dimension. If the pinned API makes this awkward, isolate the exact missing
bridge rather than inserting a stronger assumption silently.

### C2. torsion is only ±1

Show that the torsion unit in the Dirichlet decomposition is `1` or `-1`.

A real embedding is enough: a real root of unity is ±1.

Do not assume the p-th power map is surjective on the whole unit group.
Only the torsion sign should be absorbed, using oddness of p.

If there is a pinned theorem giving torsion = {±1} for a totally-real quadratic field,
use it; otherwise prove the small bridge from a real embedding.

### C3. rank-one Dirichlet decomposition

Let `epsilon` be the single fundamental unit supplied by `fundSystem` after proving
`rank K = 1`.

From `NumberField.Units.exist_unique_eq_mul_prod`, normalize every unit to

```text
u = sign * epsilon^n
```

with `n : ℤ`.

Write

```text
n = p*q + r,   0 <= r < p.
```

Absorb `sign` and `epsilon^(p*q)` into a p-th power. Obtain

```text
u = epsilon^r * e^p.
```

Transport this decomposition through
`traceOneRat_ringOfIntegers_equiv` to the TraceOne carrier.

Construct a production sector system with

```lean
Sector := Fin p
rep i  := epsilon^i
```

(up to the transported-unit representation actually convenient in Lean).

Suggested endpoint:

```lean
noncomputable def traceOnePrimeRealUnitPowerSectorSystem
    {p : ℕ} (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    UnitPowerSectorSystem
      (TraceOneInt (signedPrimeParameter p)) p
```

No uniqueness of the sector is required by Phase 18. Completeness is sufficient.

Classification if green:

```text
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-GREEN
```

If the pinned Dirichlet/signature API blocks the full construction, classify exactly:

```text
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-API-BLOCKED
```

and identify the smallest missing theorem/signature transport.

---

## Part D — p=5 compatibility and carrier cleanup

Phase 18 recorded that the old FLT5 theorem is stated on the custom `GoldenInt` /
`GoldenUnit` carrier rather than `GoldenIntˣ`.

Do **not** make a fake coercion bridge merely to reuse that theorem.

Instead, if Part C succeeds, instantiate the generic real-TraceOne sector system at
`p = 5` on

```text
TraceOneInt 1.
```

Then compare it mathematically with the existing GoldenInt result:

```text
five sectors modulo fifth powers.
```

A full `GoldenInt ≃+* TraceOneInt 1` production equivalence is optional only if it is
small and already essentially present. It is not required for Phase 19 success.

The important point is that p=5 now has a sector system on the same generic TraceOne
carrier used by Phase 13-17.

---

## Part E — finite regressions

At minimum test:

```text
p=3   -> exceptional Eisenstein 3-sector compatibility
p=5   -> real branch, 5 sectors on TraceOneInt 1
p=7   -> imaginary singleton
p=11  -> imaginary singleton
p=13  -> real branch, 13 sectors
```

For p=13 no explicit fundamental unit formula is required; the Dirichlet system may be
noncomputable.

Do not claim FLT13 or sector elimination.

---

## Part F — relation to class-group obstruction

Record in the report the new post-Phase-19 frontier:

### imaginary branch `p % 4 = 3`, p >= 7

If Part B is green, the unit obstruction vanishes entirely. The only remaining
arithmetic condition before exact p-th-power extraction is

```text
classGroupPTorsionFreeAt R p.
```

### real branch `p % 4 = 1`

The unit obstruction becomes a finite `Fin p` sector problem. Even after class-group
principalization, one obtains only

```text
a = rep(i) * delta^p
```

for some `i : Fin p`.

The future FLT work is to eliminate nonzero sectors from the specific TraceOne / GTail
coordinate equation, just as FLT5 eliminates nonzero fifth-power unit classes.

This distinction should be explicit in `report-019.md`.

---

## Production placement

Preferred new production module:

```text
DkMath/NumberTheory/TraceOnePrimeUnitSectors.lean
```

It may import:

```text
DkMath.NumberTheory.TraceOneQuadraticField
DkMath.Lib.NumberTheory.UnitPowerSector
```

plus the required pinned Mathlib unit-theorem/signature modules.

Do not import `DkMath.FLT.*` from this production module.

Specialized p=3/5/7 comparisons belong in `DkMathTest/FLT/Prime/*`.

---

## Verification

Add test-first probes and an axiom audit. Focused build should include at least:

```text
DkMath.NumberTheory.TraceOneQuadraticField
DkMath.NumberTheory.TraceOnePrimeUnitSectors
DkMath.Lib.NumberTheory.UnitPowerSector
DkMath.Lib.NumberTheory.PrincipalIdealPower
new Phase-19 probes
new Phase-19 axiom audit
DkMath.FLT.Seven
```

Also run:

```text
git diff --check
```

and scan the fresh Phase-19 sources for

```text
sorry
sorryAx
admit
axiom
unsafe
```

Do not attribute pre-existing warnings elsewhere in the repository to Phase 19.

---

## Report

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-019.md
```

Report separately:

```text
PGEN-TRACEONE-IMAGINARY-UNIT-SINGLETON-GREEN
PGEN-TRACEONE-REAL-DIRICHLET-SECTOR-GREEN
```

or the exact blocked classification for Part C.

Do not collapse the real and imaginary unit mechanisms into one opaque theorem.

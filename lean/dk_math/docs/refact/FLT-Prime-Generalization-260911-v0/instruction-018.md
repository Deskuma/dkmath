# FLT prime-generalization Phase 18 — generic unit-power sectors

## Goal

Phase 17 made `TraceOneInt (signedPrimeParameter p)` a Dedekind-domain carrier for arbitrary odd prime `p`, and Phases 15–16 connected ideal factorization / class-group principalization to the element-level statement

```text
a = u * gamma^p
```

with a residual unit `u`.

Do **not** try to prove that every unit is a `p`-th power.  That is only a sufficient special case and is false in general (notably on real-quadratic carriers).  The correct generic boundary is the quotient of the unit group by `p`-th powers.

The target of this phase is therefore a neutral API for **unit-power sector systems** and its composition with the Phase-16 principal-ideal bridge.

Success classification:

```text
PGEN-UNIT-SECTOR-GREEN
PGEN-IDEAL-TO-SECTOR-POWER-GREEN
```

This phase does not eliminate sectors, prove a general FLT theorem, prove class-group p-torsion-freeness, or classify arbitrary quadratic-field units.

---

## A. Audit the existing specialized models

Use the pinned branch as authority.

Compare at least:

```text
DkMath.FLT.Three.EisensteinUnitSectors
DkMath.FLT.Five.GoldenUnitClassification
DkMath.FLT.Seven.QuadraticUnits
```

Record the exact common shape:

- FLT3: representatives `1`, `tau`, `tau^2` modulo cubes;
- FLT5: representatives `phi^i`, `i : Fin 5`, modulo fifth powers;
- FLT7: the stronger special case in which every unit is already a seventh power, so the sector space can be taken to be a singleton.

Do not rewrite those existing proofs in this phase.

---

## B. Neutral sector structure

Add a neutral production module, suggested path:

```text
DkMath/Lib/NumberTheory/UnitPowerSector.lean
```

with no `DkMath.FLT.*` imports.

Preferred shape:

```lean
structure UnitPowerSectorSystem
    (R : Type*) [CommMonoidWithZero R] (p : ℕ) where
  Sector : Type
  rep : Sector → Rˣ
  complete : ∀ u : Rˣ,
    ∃ s : Sector, ∃ e : Rˣ,
      u = rep s * e ^ p
```

If pinned elaboration makes the above dependent field awkward, an equivalent data structure is acceptable, but keep representatives in `Rˣ` rather than as bare elements whenever practical.

Do **not** require `Fintype Sector` in the base structure.  Finiteness is useful for concrete FLT sector elimination, but not necessary for the algebraic normalization theorem.

Optionally add a finite refinement / predicate if useful:

```lean
FiniteUnitPowerSectorSystem
```

or simply support `[Fintype S.Sector]` externally.

---

## C. Generic unit normalization

Prove a neutral theorem converting an arbitrary unit-times-power equation

```text
a = (u : R) * gamma ^ p
```

into a sector-normalized equation

```text
a = (S.rep s : R) * delta ^ p
```

for some sector `s` and element `delta`.

Suggested endpoint:

```lean
theorem exists_sector_mul_pow_of_unit_mul_pow
    (S : UnitPowerSectorSystem R p)
    {a gamma : R} (u : Rˣ)
    (h : a = (u : R) * gamma ^ p) :
    ∃ s : S.Sector, ∃ delta : R,
      a = (S.rep s : R) * delta ^ p
```

The proof should use `S.complete u`, multiply the unit-root into `gamma`, and use `mul_pow`.

Also expose an `Associated`-input wrapper if it is naturally useful:

```lean
Associated a (gamma^p)
  -> ∃ s delta, a = rep(s) * delta^p
```

This should connect cleanly to Phase 14.

---

## D. Compose with Phase 16

Use

```text
exists_unit_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
```

from `PrincipalIdealPower.lean` to obtain the main ideal-to-sector endpoint.

Target shape:

```lean
theorem exists_sector_mul_pow_of_span_eq_pow_of_classGroupPTorsionFreeAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} {a : R} {p : ℕ}
    (S : UnitPowerSectorSystem R p)
    (hI0 : I ∈ (Ideal R)⁰)
    (hfree : classGroupPTorsionFreeAt R p)
    (hspan : Ideal.span ({a} : Set R) = I ^ p) :
    ∃ s : S.Sector, ∃ delta : R,
      a = (S.rep s : R) * delta ^ p
```

This is the preferred Phase-18 endpoint.

It must keep the sector explicit; do not silently collapse it to the identity representative.

---

## E. Recover the Phase-16 surjective-unit special case

Show that the old unit-surjectivity hypothesis gives a trivial/singleton sector system.

For example, from

```lean
hunit : ∀ u : Rˣ, ∃ e : Rˣ, u = e ^ p
```

construct a sector system with one representative `1`.

Then either prove or regression-check that the Phase-18 sector endpoint reduces to the existing exact-power endpoint when the sector system is trivial.

This confirms that Phase 16 is a special case, not a competing route.

---

## F. Specialized compatibility probes

Add test-first compatibility modules under:

```text
DkMathTest/FLT/Prime/
```

At minimum audit / instantiate:

### p = 3

Using the existing Eisenstein unit classification, build a sector system equivalent in content to:

```text
{1, tau, tau^2} modulo cubes
```

Prefer a thin adapter around `exists_sector_mul_cube_of_unit`; do not duplicate the six-unit classification.

### p = 5

Audit whether `GoldenInt` exposes enough actual `Units` API to build a thin adapter from

```text
goldenUnitClassesModFifth
```

If the existing theorem is phrased only in the custom `GoldenUnit` predicate and an honest `GoldenIntˣ` adapter is nontrivial, do not fake it.  Classify the exact missing bridge explicitly.

### p = 7

Build the singleton sector system from the existing theorem that every unit of `TraceOneInt (-2)` is a seventh power, if the unit-group coercion bridge is straightforward.

The finite probe should make the carrier distinctions explicit:

```text
TraceOneInt (-1)
GoldenInt
TraceOneInt (-2)
```

Do not claim that GoldenInt is definitionally `TraceOneInt 1`.

---

## G. Optional quotient-group audit

Audit pinned Mathlib for a canonical quotient-group presentation of

```text
Rˣ / (Rˣ)^p
```

or the subgroup `Set.range (powMonoidHom p)` / equivalent.

If there is a clean ready-made API, record it in the report.  Do not replace the concrete sector-system implementation with a difficult quotient construction unless it clearly simplifies the proof.

The sector-system abstraction is sufficient for this phase.

---

## H. Stop boundary

Do not implement:

- arbitrary-prime unit classification for `TraceOneInt (signedPrimeParameter p)`;
- Dirichlet's unit theorem;
- fundamental-unit computation;
- sector exclusion for arbitrary p;
- class-number / class-group p-torsion-freeness;
- general FLT contradiction.

After Phase 18, the honest remaining arithmetic obligations should read:

```text
1. classGroupPTorsionFreeAt R p
2. a concrete UnitPowerSectorSystem R p
3. elimination of all non-admissible sectors for the FLT coordinate equation
```

This is the desired architectural boundary.

---

## I. Verification

Add focused probe and axiom audit, suggested names:

```text
DkMathTest/FLT/Prime/UnitPowerSectorAuditProbe.lean
DkMathTest/FLT/Prime/UnitPowerSectorAuditAxiomAudit.lean
```

Build at least:

```text
DkMath.Lib.NumberTheory.PowerFactor
DkMath.Lib.NumberTheory.IdealPowerFactor
DkMath.Lib.NumberTheory.PrincipalIdealPower
DkMath.Lib.NumberTheory.UnitPowerSector
DkMathTest.FLT.Prime.UnitPowerSectorAuditProbe
DkMathTest.FLT.Prime.UnitPowerSectorAuditAxiomAudit
DkMath.FLT.Seven
```

Run:

- `git diff --check`;
- fresh warning scan;
- `sorry`, `sorryAx`, `admit`, explicit `axiom`, `unsafe` scan on new production/test files;
- `#print axioms` for every new public production theorem.

Expected classification on success:

```text
PGEN-UNIT-SECTOR-GREEN
PGEN-IDEAL-TO-SECTOR-POWER-GREEN
```

Report to:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-018.md
```

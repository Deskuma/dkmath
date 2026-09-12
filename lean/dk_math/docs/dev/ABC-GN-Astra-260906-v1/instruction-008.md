# instruction-008 — LUNA Lib promotion and p=3 Eisenstein API reconciliation

## Mission

The repository has changed underneath the ABC-GN v1 campaign.

The current branch has already been fast-forwarded to the latest `develop`, which now contains the promoted `DkMath.Lib` number-theory layer and the conditional odd-prime FLT architecture.

LUNA-008 is a **reconciliation/refactor task**, not a new mathematics task.

It must:

```text
1. promote the reusable Eisenstein coordinate core into DkMath.Lib;
2. preserve old imports through a compatibility facade;
3. switch ABC-GN to the Lib owner;
4. expose the definitional p=3 TraceOne/Eisenstein carrier compatibility;
5. package the existing FLT3 cube-unit sectors through the new generic
   UnitPowerSectorSystem API.
```

Do not prove a new FLT theorem.
Do not prove ABC factorization existence.
Do not add asymptotic counting.

Read first:

```text
reconciliation-008.md
report-007.md

../../refact/FLT-Prime-Generalization-260911-v0/summary-026.md
```

Inspect current production source before editing.

---

## Part I — promote the neutral Eisenstein core into DkMath.Lib

Create:

```text
DkMath/Lib/NumberTheory/EisensteinCoordinates.lean
```

Canonical namespace:

```text
DkMath.Lib.NumberTheory
```

Import only the neutral lower dependency:

```text
DkMath.NumberTheory.TraceOneQuadratic
```

Move the implementation currently owned by:

```text
DkMath.NumberTheory.EisensteinCoordinates
```

into the Lib module.

The promoted public API should include the same mathematical content:

```text
eisensteinCoord
norm_eisensteinCoord
eisensteinCoord_mul
eisensteinCoord_sq
eisensteinCoord_mul_sq
norm_eisensteinCoord_mul_sq
norm_eisensteinCoord_mul_sq_polynomial
eisenstein_square_coefficient_coprime

eisenstein_mul_sq_eq_cubicCoord_fst
eisenstein_mul_sq_eq_cubicCoord_snd
eisenstein_mul_sq_eq_cubicCoord_coefficients_isCoprime
eisenstein_mul_sq_eq_cubicCoord_norm
eisenstein_mul_sq_eq_cubicCoord_polynomial_norm
```

The underlying carrier remains:

```text
TraceOneInt (-1).
```

Do not define a second ring or norm.

---

## Part II — historical compatibility facade

Replace the implementation in:

```text
DkMath/NumberTheory/EisensteinCoordinates.lean
```

with a thin compatibility facade importing:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates
```

Preserve historical names in namespace:

```text
DkMath.NumberTheory.EisensteinCoordinates
```

Each historical declaration should forward to the new Lib owner.

Follow the same architectural pattern as:

```text
DkMath.ABC.PadicValNat
  -> DkMath.Lib.NumberTheory.PadicValNat.
```

Do not duplicate proofs in the compatibility file.

Do not remove historical names yet.

---

## Part III — update ABC-GN to use the Lib owner directly

Update:

```text
DkMath/ABC/GNExcessCubicEisensteinCoordinates.lean
DkMath/ABC/GNExcessCubicEisensteinFactorConsequences.lean
```

so new production code imports:

```text
DkMath.Lib.NumberTheory.EisensteinCoordinates
```

rather than the historical NumberTheory facade.

Use/open:

```text
DkMath.Lib.NumberTheory
```

for the promoted Eisenstein declarations.

Preserve all theorem statements in the ABC namespace unless a namespace qualification must change internally.

No mathematical behavior should change.

---

## Part IV — add the promoted module to the Lib entry point

Update:

```text
DkMath/Lib.lean
```

with:

```text
import DkMath.Lib.NumberTheory.EisensteinCoordinates
```

Place it with the other NumberTheory imports.

The target public dependency direction is:

```text
TraceOneQuadratic
  -> Lib.NumberTheory.EisensteinCoordinates
  -> ABC / FLT bridges.
```

---

## Part V — p=3 signed-prime parameter fact

The generic odd-prime TraceOne architecture uses:

```text
TraceOneInt (signedPrimeParameter p).
```

For p=3 prove the exact specialization:

```text
signedPrimeParameter 3 = -1.
```

Preferred location:

```text
DkMath.NumberTheory.PrimeQuadraticDiscriminant
```

Recommended theorem name:

```text
signedPrimeParameter_three
```

Proof should be a direct computation from the existing definitions.

Do not introduce any new field theory.

---

## Part VI — FLT3 / Lib carrier-coordinate bridge

Create a thin bridge module:

```text
DkMath/FLT/Three/EisensteinLibBridge.lean
```

Import:

```text
DkMath.FLT.Three.EisensteinUnitSectors
DkMath.Lib.NumberTheory.EisensteinCoordinates
DkMath.Lib.NumberTheory.UnitPowerSector
DkMath.NumberTheory.PrimeQuadraticDiscriminant
```

The existing FLT3 substrate already defines:

```text
abbrev EisensteinInt := TraceOneInt (-1).
```

Therefore do NOT define a type equivalence.

Instead expose the API compatibility explicitly.

### VI-a — generic p=3 carrier specialization

Prove or record by rewriting `signedPrimeParameter_three` that:

```text
TraceOneInt (signedPrimeParameter 3)
```

is the same carrier used by:

```text
EisensteinInt = TraceOneInt (-1).
```

A theorem involving equality of values after rewriting is preferable to an unnecessary `Equiv`.

If no theorem is needed because the type reduces definitionally after `rw [signedPrimeParameter_three]`, document that and provide one small compile-time example theorem instead.

### VI-b — omega/tau coordinate convention

The promoted Lib coordinate is the standard omega convention:

```text
Lib.eisensteinCoord m n = <m,-n>.
```

FLT3 uses the tau convention:

```text
FLT.Three.eisensteinCoord r s = <r,s>.
```

Prove:

```text
DkMath.Lib.NumberTheory.eisensteinCoord m n
=
DkMath.FLT.Three.eisensteinCoord m (-n).
```

Recommended theorem:

```text
lib_eisensteinCoord_eq_FLT3_coord
```

This should be `rfl` or a trivial extensional proof.

Also provide the corresponding norm compatibility theorem if it is essentially free.

No new algebra is required.

---

## Part VII — package FLT3 cube sectors through UnitPowerSectorSystem

The generic Lib API now contains:

```text
UnitPowerSectorSystem R p.
```

FLT3 already proves:

```text
exists_sector_mul_cube_of_unit
```

with the three sectors:

```text
1
tau
tau^2.
```

Package the existing theorem as:

```text
noncomputable def eisensteinCubeUnitPowerSectorSystem :
  DkMath.Lib.NumberTheory.UnitPowerSectorSystem
    (TraceOneInt (-1)) 3
```

Preferred sector type:

```text
EisensteinUnitSector.
```

Preferred representative:

```text
(EisensteinUnitSector.rep_isUnit sector).unit
```

For completeness, consume only the already-proved:

```text
exists_sector_mul_cube_of_unit.
```

Convert the returned `IsUnit delta` into a unit with its existing `.unit` / `.unit_spec` API.

No new unit classification proof.

No `Classical.choose` should be needed for the mathematical content beyond what is already present in the source theorem; if Lean engineering requires noncomputability for the unit wrapper, keep it local and explicit.

---

## Part VIII — generic sector API compatibility theorem

Add a thin theorem showing that the new system really recovers the existing FLT3 statement at the generic Lib interface.

For example, for every:

```text
u : (TraceOneInt (-1))ˣ
```

prove via the `UnitPowerSectorSystem.complete` field:

```text
∃ s : EisensteinUnitSector,
  ∃ e : (TraceOneInt (-1))ˣ,
    u = eisensteinCubeUnitPowerSectorSystem.rep s * e^3.
```

Recommended theorem:

```text
eisensteinCubeUnitPowerSectorSystem_complete
```

This is an API bridge only.

Do not specialize the whole generic FLT prime-descent theorem to p=3 in this checkpoint.

---

## Part IX — do NOT overclaim the summary-026 boundary

After this task, the p=3 situation should be described carefully:

```text
carrier mismatch:
  CLOSED / there was no mathematical type mismatch;
  both are TraceOneInt (-1).

coordinate convention mismatch:
  CLOSED by explicit omega/tau sign bridge.

unit-sector packaging mismatch:
  CLOSED by UnitPowerSectorSystem wrapper.

full generic odd-prime p=3 facade integration:
  NOT CLAIMED.
```

The generic `PrimeTraceOneConditionalDescent` also contains cyclotomic coordinate packets, stripped ideals, Dedekind/class-group hypotheses, and branch-specific interfaces.

Do not claim the full p=3 facade is integrated merely because the carrier and sector layers now line up.

---

## Part X — relation to ABC-GN research

Do NOT add any theorem asserting:

```text
(a+2)+omega = beta * gamma^2
```

for shell witnesses.

Do NOT derive ABC factorization existence from:

```text
PrincipalIdealPower
PowerFactor
UnitPowerSector.
```

Those new Lib modules provide downstream machinery **if** future research supplies the required ideal-power/factorization hypotheses.

The ABC-GN research frontier remains:

```text
actual Eisenstein factorization existence/counting
and/or
balanced-box represented-pair sparsity.
```

---

## Part XI — aggregators

Update the appropriate stable entry points:

```text
DkMath.Lib
```

must expose the promoted Eisenstein coordinate module.

If `DkMath.FLT.Three` is an existing stable aggregator, import:

```text
DkMath.FLT.Three.EisensteinLibBridge
```

there in dependency order.

Do not create a new top-level dependency from Lib into FLT.

---

## Part XII — report

Create:

```text
lean/dk_math/docs/dev/ABC-GN-Astra-260906-v1/report-008.md
```

Title:

```text
# LUNA-008 — Lib promotion and p=3 Eisenstein API reconciliation
```

Report:

1. branch sync baseline;
2. files changed;
3. Lib promotion;
4. historical compatibility facade;
5. ABC import migration;
6. `DkMath.Lib` entry-point update;
7. `signedPrimeParameter_three`;
8. carrier identity status;
9. omega/tau coordinate bridge;
10. FLT3 cube-sector `UnitPowerSectorSystem`;
11. generic completeness theorem;
12. exact meaning of the former p=3 API boundary;
13. relation to new PrincipalIdealPower / UnitPowerSector APIs;
14. explicit no-ABC-factorization boundary;
15. focused builds;
16. aggregator builds;
17. forbidden scan;
18. axiom audit;
19. remaining research frontier.

Do not include commit hashes.

---

## Part XIII — validation

At minimum run:

```text
lake build DkMath.Lib.NumberTheory.EisensteinCoordinates
lake build DkMath.NumberTheory.EisensteinCoordinates
lake build DkMath.ABC.GNExcessCubicEisensteinFactorConsequences
lake build DkMath.FLT.Three.EisensteinLibBridge
lake build DkMath.Lib
lake build DkMath.ABC
```

If the FLT3 aggregator is updated, build it too.

Scan changed production Lean for:

```text
sorry
admit
axiom
abc_main_axiom
native_decide
unsafe
```

No new occurrences.

Audit principal declarations:

```text
promoted Eisenstein coordinate API
signedPrimeParameter_three
omega/tau coordinate bridge
eisensteinCubeUnitPowerSectorSystem_complete
```

Expected trust boundary:

```text
propext
Classical.choice
Quot.sound
```

or a subset.

---

## Stop condition

Stop when:

```text
A. DkMath.Lib owns the neutral Eisenstein coordinate API;
B. the historical NumberTheory path is only a compatibility facade;
C. ABC uses the Lib owner directly;
D. p=3 generic TraceOne carrier and FLT3 Eisenstein carrier are explicitly aligned;
E. FLT3 cube sectors are packaged as UnitPowerSectorSystem (TraceOneInt (-1)) 3.
```

Do not specialize the entire generic FLT prime descent to p=3.
Do not prove ABC factorization existence.
Do not start new counting research.
Do not open LUNA-009 automatically.

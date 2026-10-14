# FPTC-008 instruction — real `Fin p` sector receiver and obstruction frontier

Branch: `research/FLT-Prime-TraceOne-Closure-260916-v0`

## Context

FPTC-000 through FPTC-006 are green. FPTC-007 ended with:

```text
Outcome C — CLASS-NUMBER FRONTIER ISOLATED
```

The imaginary branch now has an exact external arithmetic frontier:

```text
p.Prime -> p % 4 = 3 ->
Nat.Coprime p
  (NumberField.classNumber
    (TraceOneRat (signedPrimeParameter p))).
```

Do not reopen that frontier in this checkpoint.

The present checkpoint is the real branch `p % 4 = 1`. The existing generic endpoint is:

```text
exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
```

and returns, conditionally on class-group p-torsion-freeness,

```text
Q.residual =
  (traceOnePrimeRealFinSectorSystem hp hmod).rep i * delta ^ p
```

for some `i : Fin p`.

FPTC-002/FPTC-003 already provide the arbitrary-power integer coordinate kernel and Core-image landing theorem.

FPTC-006 separately provides an explicit p=5 Golden `Fin 5` sector system and an unconditional p=5 structural sector endpoint. The specialized FLT5 theorem

```text
signedGolden_nonzero_unitSector_false
```

eliminates nonzero Golden sectors, but it assumes a `SignedGoldenRamifierStrippedPacket`; it must not be applied to a generic `PrimeTraceOneStrippedIdealPacket` without a checked bridge.

## Main objective

Expose a machine-checkable real-sector arithmetic receiver for the generic TraceOne packet, then determine exactly whether the current generic packet invariants suffice to eliminate a nonzero sector.

The checkpoint must distinguish:

```text
sector factorization exists
```

from

```text
nonzero sector is impossible.
```

Do not assume the latter.

## Required repository audit before editing

Read the current production APIs at least in:

```text
DkMath/FLT/Prime/PrimeTraceOneConditionalDescent.lean
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
DkMath/NumberTheory/TraceOnePrimeUnitSectors.lean
DkMath/NumberTheory/TraceOneDiscriminantAxis.lean
DkMath/FLT/Prime/PrimeTraceOneFiveSectorClosure.lean
DkMath/FLT/Five/TraceOneBridge.lean
DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean
DkMath/FLT/Five/SignedGoldenRamifierStripped.lean
```

Also read `report-004.md`, `report-006.md`, and `report-007.md`.

Pin exact Lean 4.34 declarations with a scratch/API audit before relying on guessed names.

## Part A — generic real sector coordinate receiver

Add a thin FLT-side production receiver, preferably in a new module such as:

```text
DkMath/FLT/Prime/PrimeTraceOneRealSectorReceiver.lean
```

Use the existing theorem

```text
exists_sector_mul_pow_of_primeTraceOneRealStrippedIdealPacket
```

and FPTC-003

```text
traceOne_pow_core_landing_iff
```

with conceptually:

```text
alpha = Q.residual
beta  = (traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i
r     = p.
```

Target a theorem of the following conceptual form; adapt names and local `let` bindings to the actual API:

```lean
theorem exists_realSector_powCoords_of_primeTraceOneStrippedIdealPacket
    (...)
    (hmod : p % 4 = 1) :
    ...
    classGroupPTorsionFreeAt
      (TraceOneInt (signedPrimeParameter p)) p ->
    ∃ i : Fin p, ∃ m n : ℤ,
      let beta : TraceOneInt (signedPrimeParameter p) :=
        (traceOnePrimeRealFinSectorSystem P0.prime hmod).rep i
      (Q.residual * conj beta).fst =
          norm beta * (traceOnePowCoords
            (signedPrimeParameter p) m n p).1 ∧
      (Q.residual * conj beta).snd =
          norm beta * (traceOnePowCoords
            (signedPrimeParameter p) m n p).2
```

Do not re-prove the recurrence. Do not unfold Dirichlet unit classification in this FLT consumer.

The only extra obligation should be `norm beta ≠ 0`. Discharge it from the fact that the sector representative is a unit. If a small reusable neutral lemma such as

```text
IsUnit x -> Int.natAbs (norm x) = 1
```

or

```text
IsUnit x -> norm x = 1 ∨ norm x = -1
```

is genuinely missing and falls out directly from `traceOne_norm_mul`, it may be added in the nearest neutral TraceOne module. Do not create a large unit theory layer.

## Part B — terminal-axis consequence for the p-th-power base

Audit and, if clean, expose the generic arithmetic consequence of

```text
Q.residual_axis_terminal
```

using the existing prime-discriminant equivalence

```text
discrAxis_dvd_iff_prime_dvd_natAbs_norm.
```

The desired intermediate fact is conceptually:

```text
¬ p ∣ Int.natAbs (norm Q.residual).
```

Then combine a sector factorization

```text
Q.residual = beta * delta ^ p
```

with unit norm and norm multiplicativity to derive the p-th-power-base condition

```text
¬ p ∣ Int.natAbs (norm delta).
```

Prefer a theorem attached to `PrimeTraceOneStrippedIdealPacket` or the new receiver module if it is reusable. This is the generic analogue of the specialized FLT5 fact that the fifth-power base norm is prime to five.

Do not claim that this fact alone excludes a nonzero sector.

## Part C — p=5 explicit Golden calibration

Use the FPTC-006 endpoint

```text
exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five
```

and the explicit representative compatibility theorem

```text
goldenTraceOneFifthUnitPowerSectorSystem_rep_apply
```

to expose the p=5 sector-coordinate receiver without any class-group hypothesis.

A useful target is conceptually:

```lean
∃ i : Fin 5, ∃ m n : ℤ,
  ... exact coordinate equations for Q.residual and goldenPhi^i ...
```

The theorem may use the generic FPTC-003 landing theorem or a direct specialization of Part A to the explicit Golden sector system. Prefer reuse over duplicated fifth-power coordinate algebra.

Audit the relation between:

```text
traceOnePrimeRealFinSectorSystem at p=5
```

and

```text
goldenTraceOneFifthUnitPowerSectorSystem.
```

Do not assert definitional equality. The generic system is built from a Dirichlet fundamental unit, while the explicit Golden system is built from `goldenPhi`. If only existence of a reindexing/permutation can be justified, record the exact theorem needed; do not invent uniqueness of representatives.

## Part D — test the specialized p=5 nonzero-sector obstruction

The specialized theorem

```text
signedGolden_nonzero_unitSector_false
```

uses packet-specific facts including:

```text
5 ∣ beta.snd
5 ∤ powerSplit.b
goldenNorm gamma = ± powerSplit.b
```

or equivalent consequences.

Determine whether the generic packet already supplies enough checked information to reproduce these facts for `Q.residual` at `p=5`.

In particular audit:

```text
Q.adicSplit
Q.parent
Q.residual
Q.axis_eq
Q.residual_axis_terminal
Q.residual_coordinate_coprime
Q.residual_norm_pow
```

and the p=5 identity

```text
discrAxis 1 = <-1,2>
```

against the Golden ramifier facts. Note that the specialized Golden ramifier `goldenTau = <2,1>` is only associated to the discriminant axis through a Golden unit; this association must be proved if it is used.

Search for an existing checked bridge between

```text
PrimeTraceOneStrippedIdealPacket at p=5
```

and

```text
SignedGoldenRamifierStrippedPacket.
```

If such a bridge already exists or a very small structural bridge is justified by existing packet data, compose it and prove the strongest p=5 nonzero-sector elimination theorem that genuinely follows.

If no bridge exists, do not reconstruct the full specialized FLT5 front end in this checkpoint. Record the exact missing theorem-shaped correspondence, for example an equality/association between the generic residual and specialized Golden stripped factor together with the packet invariants needed by `signedGolden_nonzero_unitSector_false`.

## Part E — p=13 regression

Check the real generic route at `p = 13`:

```text
13 % 4 = 1
signedPrimeParameter 13 = 3
```

Do not prove a class-number theorem for `TraceOneInt 3`.

The p=13 receiver should remain conditional on

```text
classGroupPTorsionFreeAt (TraceOneInt 3) 13
```

unless an already-existing structural discharge is found.

Expose the exact sector-coordinate equations and the terminal-axis/base-norm-prime-to-13 consequence. Do not claim that any `i ≠ 0` sector is impossible unless a checked arithmetic theorem proves it.

## Outcome classification

Use the strongest accurate outcome:

```text
Outcome A — REAL SECTOR RECEIVER AND P5 NONZERO-SECTOR ELIMINATION GREEN
```

Use only if the generic p=5 packet itself is connected by checked theorems to enough arithmetic to eliminate every `i ≠ 0` sector.

```text
Outcome B — REAL SECTOR RECEIVER GREEN; P5 BRIDGE FRONTIER ISOLATED
```

Use if the generic receiver and base-norm obstruction are green, but specialized FLT5 nonzero-sector elimination cannot yet be applied because the generic/specialized stripped-packet correspondence is missing.

```text
Outcome C — REAL SECTOR COORDINATE SURFACE GREEN; ARITHMETIC OBSTRUCTION FRONTIER ISOLATED
```

Use if the coordinate receiver is green but the stronger terminal/base-norm theorem or p=5 calibration exposes a separate missing arithmetic theorem.

```text
Outcome D — REAL SECTOR LANDING/API BLOCKED
```

Use only if the current APIs do not permit a clean sector-preserving FPTC-003 composition. Record the exact Lean/API blocker.

Outcome B or C is a valid research success. Do not force Outcome A.

## Required regressions

The focused tests should check at least:

```text
p=5:
  signedPrimeParameter 5 = 1
  explicit Golden Fin 5 sector endpoint
  p=5 sector coordinate receiver
  base norm prime to 5

p=13:
  signedPrimeParameter 13 = 3
  generic real Fin 13 sector receiver under explicit class-group hypothesis
  base norm prime to 13
```

If representative norm is normalized only to `±1`, keep the sign explicit unless a stronger theorem is already available.

## Validation

Add focused API and axiom audits. At minimum build the new module plus its direct dependencies and tests, including:

```text
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.NumberTheory.TraceOnePrimeUnitSectors
DkMath.FLT.Prime.PrimeTraceOneConditionalDescent
DkMath.FLT.Prime.PrimeTraceOneFiveSectorClosure
<new real-sector receiver module>
<API audit>
<axiom audit>
```

Also run:

```text
git diff --check
```

and the repository-standard forbidden-source scan on edited/new Lean files.

No new `sorry`, `sorryAx`, `admit`, explicit project axiom, or `unsafe` declaration.

## Required report

Write:

```text
docs/dev/FLT-Prime-TraceOne-Closure-260916-v0/report-008.md
```

The report must state:

1. exact outcome A/B/C/D;
2. exact generic real receiver theorem signature;
3. how `norm beta ≠ 0` is discharged;
4. whether terminal-axis gives `p ∤ natAbs(norm delta)` and by which theorem chain;
5. p=5 explicit Golden receiver status;
6. whether generic and Dirichlet p=5 sector systems are related, and how;
7. whether `signedGolden_nonzero_unitSector_false` can be used on the generic packet;
8. if not, the exact missing generic/specialized packet bridge;
9. p=13 conditional status;
10. axiom audit and focused build results.

## Stop rules

Stop and report rather than forcing a theorem if:

- p=5 nonzero-sector elimination requires a missing generic-to-specialized packet correspondence;
- equality of the generic Dirichlet sector system and Golden sector system is not derivable from current APIs;
- p=13 requires a new class-number theorem;
- a sector index is discarded before the coordinate obstruction is extracted;
- a specialized FLT5 final contradiction theorem is used as a black box;
- the checkpoint begins rebuilding the full FLT5 front end or proving general FLT.

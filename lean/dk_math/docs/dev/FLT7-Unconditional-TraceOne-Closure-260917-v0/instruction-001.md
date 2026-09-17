# FLT7TC-001 — Seventh-power coordinate bridge and 7-unit residual root

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint follows the read-only `FLT7TC-000` reconnaissance recorded in
`report-000.md`.

Treat the following result as fixed input:

```text
FLT7TC-000: Outcome B

- the p=7 generic ramified endpoint already gives an unconditional
  `Q.residual = delta ^ 7`;
- p=7 class-group torsion is already discharged structurally;
- `Q.residual_axis_terminal` gives the residual a 7-unit norm;
- the same exact root therefore has 7-unit norm;
- the generic recurrence coordinates and the existing explicit p=7 seventh
  power polynomials describe the same `TraceOneInt (-2)` seventh power;
- however, the generic parent provenance and its relation to
  `cyclotomicSevenToTraceOne` remain unproved and belong to FLT7TC-002.
```

The purpose of FLT7TC-001 is to turn the first five items into a small,
kernel-checked production API.  Do **not** work on the parent provenance in
this checkpoint.

## 1. Read first

Before editing, inspect at minimum:

```text
DkMath/FLT/Prime/PrimeTraceOneCoordinateReceiver.lean
DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean
DkMath/FLT/Seven/SeventhPowerCoordinates.lean
DkMath/NumberTheory/TraceOneDiscriminantAxis.lean
DkMath/NumberTheory/TraceOnePrimeDiscriminant.lean
DkMath/NumberTheory/PrimeQuadraticDiscriminant.lean
```

Also read:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-000.md
```

Do not infer exact names or theorem signatures from this instruction when the
source already supplies them.  Use the current Lean API.

## 2. Dependency direction

Prefer a new **p=7 specialized leaf module** rather than adding specialized
seventh-power polynomials to the generic `DkMath.FLT.Prime` layer.

Suggested production path:

```text
DkMath/FLT/Seven/PrimeTraceOneClosureBridge.lean
```

Conceptually its dependencies may point in this direction:

```text
DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.FLT.Seven.SeventhPowerCoordinates
DkMath.NumberTheory.TraceOnePrimeDiscriminant
```

Audit the actual imports and avoid a cycle.  It is acceptable for this new
specialized leaf to consume the generic Prime API.  Do not make the generic
Prime facade depend on this new FLT7 leaf in this checkpoint.

Do not import a specialized theorem whose conclusion is already an FLT7
contradiction.

## 3. Coordinate identity bridge

Add the smallest checked bridge between the neutral recurrence coordinates and
the existing explicit p=7 polynomials.

Target theorem shapes conceptually equivalent to:

```lean
(traceOnePowCoords (-2) u v 7).1 = seventhPowerFst u v
(traceOnePowCoords (-2) u v 7).2 = seventhPowerSnd u v
```

Naming may follow repository conventions, for example:

```text
traceOnePowCoords_negTwo_seven_fst
traceOnePowCoords_negTwo_seven_snd
```

or an equivalent pair.

### Required proof method

Do **not** re-expand the seventh power polynomial with a second `ring` proof.
Use the two already checked descriptions of the same element:

```text
traceOne_pow_coordinates (-2) u v 7
traceOne_pow_seven_eq u v
```

and compare `.fst` / `.snd`, e.g. by `congrArg` plus simplification.

The point of this lemma is API identification, not duplicate algebra.

## 4. Explicit p=7 residual coordinate receiver

Consume the existing generic p=7 receiver and the bridge above to expose the
specialized coordinate surface for a generic stripped packet.

Target a theorem equivalent in content to:

```lean
∃ u v : ℤ,
  Q.residual.fst = seventhPowerFst u v ∧
  Q.residual.snd = seventhPowerSnd u v
```

for

```text
P0 : PrimeAdicFactorPacket 7 g u0 x
P  : PrimeTraceOneCoordinatePacket L 7 ζ hζ
Q  : PrimeTraceOneStrippedIdealPacket L P0 P.
```

Use
`exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven` and the
new recurrence-to-explicit bridge.  Do not reconstruct the class-group proof.

This theorem is a **residual** theorem only.  It must not state or imply any
identification of `Q.parent` with `cyclotomicSevenToTraceOne`.

## 5. Residual 7-unit norm from axis terminality

Promote the deduction found in `report-000.md` to a production theorem.

Using the p=7 `signedPrimeDiscriminantPacket` and
`PrimeDiscriminantPacket.discrAxis_dvd_iff_prime_dvd_natAbs_norm`, prove the
strongest clean form supported by the existing API, preferably both a Nat
presentation and/or an Int presentation when one follows cheaply:

```text
¬ 7 ∣ Int.natAbs (norm Q.residual)
```

and conceptually

```text
¬ (7 : ℤ) ∣ norm Q.residual.
```

The proof must use `Q.residual_axis_terminal`; do not smuggle in a specialized
FLT7 terminal theorem.

Do not assume `discrAxis (-2) = sevenAxis` by definitional equality.  If a
named adapter is needed, either prove the tiny normalization locally or add a
small reusable theorem at the nearest appropriate p=7 boundary.  Do not infer
anything from norm equality alone.

## 6. Same-root 7-unit theorem

The crucial theorem of this checkpoint must connect the **same seventh-power
root** to the 7-unit norm fact.

Start from the existing element-level endpoint:

```text
exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
```

and prove a theorem with content equivalent to:

```text
∃ delta : TraceOneInt (-2),
  Q.residual = delta ^ 7 ∧
  ¬ (7 : ℤ) ∣ norm delta
```

The exact carrier presentation may initially be
`TraceOneInt (signedPrimeParameter 7)` if that is cleaner; normalize to
`TraceOneInt (-2)` only by a checked simplification of
`signedPrimeParameter 7`.

Derive the root norm statement by:

```text
Q.residual_axis_terminal
  -> 7 ∤ norm Q.residual
Q.residual = delta^7
traceOne_norm_pow
  -> norm Q.residual = norm delta ^ 7
7 prime
  -> 7 ∤ norm delta.
```

Do not use an injectivity assertion for seventh powers unless Lean genuinely
needs it.  Divisibility of `norm delta` into its seventh power is enough.

## 7. Prefer one theorem that preserves root coordinates

For the next checkpoint, it is particularly useful if the API exposes the
same root as explicit integer coordinates.

If cleanly expressible without type-cast gymnastics, add a theorem equivalent
to:

```lean
∃ u v : ℤ,
  Q.residual.fst = seventhPowerFst u v ∧
  Q.residual.snd = seventhPowerSnd u v ∧
  ¬ (7 : ℤ) ∣ norm (⟨u, v⟩ : TraceOneInt (-2))
```

This is stronger for consumers than obtaining an unrelated existential
coordinate pair and an unrelated existential `delta`.

Preferred proof:

1. obtain the actual `delta` from the element-level exact-power endpoint;
2. destruct `delta` as its two integer coordinates `⟨u,v⟩`;
3. use `traceOne_pow_seven_eq` / the coordinate bridge;
4. prove the 7-unit norm for this same root.

If the exact statement becomes awkward solely because of the
`signedPrimeParameter 7` normalization, keep a small internal normalization
lemma rather than introducing an unsafe cast or a new carrier.

## 8. Immediate polynomial consequences

From the same-root theorem, expose only consequences that follow directly from
already checked `SeventhPowerCoordinates` lemmas and are likely to be consumed
by FLT7TC-003.

High-value targets are:

```text
(7 : ℤ) ∣ Q.residual.snd

¬ (7 : ℤ) ∣ seventhPowerSndCore u v

(49 : ℤ) ∣ Q.residual.snd ↔ (7 : ℤ) ∣ v
```

for the same witness `u,v` when possible.

The existing consumers are:

```text
seventhPowerSnd_eq_seven_mul
seven_not_dvd_seventhPowerSndCore_of_norm
fortyNine_dvd_seventhPowerSnd_iff
```

A `ZMod 7` first-coordinate consequence from
`seventhPowerFst_mod_seven` may be added if it is clean, but do not spend this
checkpoint building an `Int.emod` presentation layer just for aesthetics.

The fact

```text
¬ (7 : ℤ) ∣ Q.residual.fst
```

may also be added if it follows cleanly from
`Q.residual_coordinate_coprime` and `7 ∣ Q.residual.snd`.  Do not let a library
API detour on `IsCoprime` block the main checkpoint.

## 9. Root-coordinate primitivity

`report-000.md` found the existing specialized theorem

```text
coordinates_isCoprime_of_pow_seven_coordinates_isCoprime
```

in a deeper ramified module.

Do **not** import the historical ramified tower merely to add root-coordinate
primitivity to this bridge module.

For FLT7TC-001:

- if an equivalent neutral/basic lemma already exists at a shallow import
  boundary, reuse it;
- if the statement has a short self-contained proof that belongs naturally in
  a lower neutral module, document that possibility but do not broaden this
  checkpoint unless needed by the main theorems;
- otherwise defer root-coordinate primitivity to FLT7TC-003 or a later focused
  bridge.

The coordinate bridge and same-root 7-unit theorem take priority.

## 10. Tests

Add focused tests under a path such as:

```text
DkMathTest/FLT/Seven/PrimeTraceOneClosureBridgeApiAudit.lean
DkMathTest/FLT/Seven/PrimeTraceOneClosureBridgeAxiomAudit.lean
```

Adjust names to the existing test layout if necessary.

The API audit should pin at least:

```text
recurrence -> seventhPowerFst
recurrence -> seventhPowerSnd
explicit residual coordinate receiver
residual 7-unit norm theorem
same-root 7-unit endpoint
```

and any immediate factorization corollaries actually promoted to production.

The axiom audit should `#print axioms` for representative new public theorems.
Expected foundational dependencies are the ordinary existing Lean/Mathlib
surface such as:

```text
propext
Classical.choice
Quot.sound
```

as applicable.  A new project axiom, `sorryAx`, or unexpected assumption is a
failure.

## 11. Validation

At minimum run the focused targets needed by the final implementation.  The
expected set includes conceptually:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneClosureBridge
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMath.FLT.Seven.SeventhPowerCoordinates
lake build DkMathTest.FLT.Seven.PrimeTraceOneClosureBridgeApiAudit
lake build DkMathTest.FLT.Seven.PrimeTraceOneClosureBridgeAxiomAudit
git diff --check
```

Use the actual test module names if the repository layout requires a slight
variation.

Scan all newly edited production/test Lean sources for fresh uses of:

```text
sorry
sorryAx
admit
axiom
unsafe
```

Distinguish comments / `#print axioms` from actual forbidden declarations.

## 12. Report

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-001.md
```

The report must state:

1. exact files changed;
2. exact theorem signatures added;
3. whether the recurrence-to-explicit coordinate bridge is kernel-checked;
4. whether residual axis terminality was promoted to an explicit 7-unit norm
   theorem;
5. whether the **same** seventh-power root is proved to have norm prime to 7;
6. which specialized seventh-power consequences are now directly available;
7. exact build / axiom / forbidden-source results;
8. the unchanged FLT7TC-002 parent-provenance frontier.

Update `ROADMAP.md` after successful validation:

```text
FLT7TC-000: completed — Outcome B
FLT7TC-001: completed — <actual outcome>
FLT7TC-002: current
```

Do not mark FLT7TC-002 current until the report and audits for this checkpoint
are complete.

## 13. Outcome classification

Use exactly one of:

```text
Outcome A — P=7 EXPLICIT SEVENTH-POWER / SAME-ROOT 7-UNIT BRIDGE GREEN
Outcome B — COORDINATE BRIDGE GREEN; SAME-ROOT 7-UNIT API NEEDS NORMALIZATION
Outcome C — RECURRENCE IDENTIFICATION GREEN; SPECIALIZED RESIDUAL CONSUMER BLOCKED
```

Outcome A requires all of:

- the recurrence-coordinate identities are checked without duplicate
  seventh-power expansion;
- an existing generic p=7 stripped packet reaches explicit
  `seventhPowerFst / seventhPowerSnd` coordinates;
- axis terminality yields a checked residual 7-unit norm statement;
- the same exact seventh-power root has a checked 7-unit norm statement;
- focused builds and axiom audits are green;
- no parent provenance is assumed.

The optional `49`/core/first-coordinate corollaries are desirable but not
required for Outcome A if the main same-root API is green.

## Hard boundaries

Do **not** in FLT7TC-001:

- identify `Q.parent` with `P.coord (g+u) u` unless a retained theorem actually
  proves it for the arbitrary packet `Q`;
- identify `P.coord (g+u) u` with `cyclotomicSevenToTraceOne (g+u) u`;
- infer equality of TraceOne elements merely from equality of norms;
- modify the generic `PrimeTraceOneCoordinatePacket` to force p=7
  canonicity;
- open the FLT7TC-002 parent orientation/provenance problem;
- claim the ramified branch is contradictory;
- import a specialized FLT7 final contradiction theorem;
- import the deep historical ramified tower solely to obtain a cosmetic
  corollary;
- treat `residual = delta^7` as itself contradictory;
- assume root-coordinate primitivity without a checked theorem;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

The desired result of this checkpoint is a **small reusable p=7 bridge**, not a
premature FLT7 proof.
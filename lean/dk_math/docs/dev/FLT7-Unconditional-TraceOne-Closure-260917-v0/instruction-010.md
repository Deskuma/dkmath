# FLT7TC-005R5 — Counterexample-origin ramified provenance and terminalization criterion

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the checked FLT7TC-005R4 result:

```text
CounterexamplePack x y z
  -> PrimitiveCounterexampleRamifiedResolution source
  -> PrimitiveRamifiedSummitPacket
```

with exactly one original endpoint divisible by `7` and the exact depth law

```text
v7(|root.snd|) + 2 = 7 * v7(distinguishedEndpoint).
```

The purpose of this checkpoint is **not** to manufacture a descent or assume the
historical terminal hypothesis.  The purpose is to retain the branch-specific
counterexample provenance that the bare common summit forgets, compare it
precisely with `TerminalPrimitiveRamifiedSummitPacket`, and attempt a direct
counterexample-origin ramified obstruction before opening any broader tower.

## 0. Required reading

Read the current checked files before editing:

- `DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedResolution.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionRamifiedResolution.lean`
- `DkMath/FLT/Seven/PrimeTraceOneRamifiedSummitBridge.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedSummit.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedDepth.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedCompensationRouting.lean`
- `docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-009.md`
- `DkMath/FLT/Seven/docs/STATUS.md` only as historical context.

Do not assume that a historical `TerminalPrimitiveRamifiedSummitPacket` exists
for the new global resolution.  Construct it only when its fields are proved.

## 1. Preserve the provenance currently forgotten by the bare summit

The current `PrimitiveCounterexampleRamifiedResolution source` retains only:

- which original endpoint is the unique `7`-divisible endpoint;
- the common summit;
- equality of that endpoint with `summit.distinguished`.

However each of the three checked constructors knows more.

### x-divisible case

The summit constructed from the ordinary ramified packet has the orientation

```text
endpointLeft  = z
endpointRight = y
distinguished = x
```

and its split supplies

```text
Nat.Coprime summit.gapRoot summit.residualRoot.
```

### y-divisible case

After exchanging the two positive summands, the summit has

```text
endpointLeft  = z
endpointRight = x
distinguished = y
```

and the underlying `SevenAdicPowerSplit` again supplies coprimality of the two
natural roots.

### z-divisible case

The signed alternating construction has

```text
endpointLeft  = x
endpointRight = -(y : ℤ)
distinguished = z
```

and `PrescribedCarrierAlternatingPowerSplit.coprime_a_b` supplies the same
natural-root coprimality.

Add the smallest production structure or inductive wrapper that preserves this
information.  A conceptual shape is:

```lean
inductive PrimitiveCounterexampleRamifiedProvenance
    {x y z : ℕ} (source : CounterexamplePack x y z) : Type
  | xCase
      (seven_dvd : 7 ∣ x)
      (summit : PrimitiveRamifiedSummitPacket)
      (endpointLeft_eq : summit.endpointLeft = (z : ℤ))
      (endpointRight_eq : summit.endpointRight = (y : ℤ))
      (distinguished_eq : summit.distinguished = (x : ℤ))
      (gap_residual_coprime : Nat.Coprime summit.gapRoot summit.residualRoot)
  | yCase ...
  | zCase ...
```

Names may differ if a cleaner API is available.

Requirements:

1. Provide a constructor theorem from every `CounterexamplePack`.
2. Provide a projection/adapter back to the already public
   `PrimitiveCounterexampleRamifiedResolution source` rather than duplicating
   existing downstream APIs.
3. Do not choose a second independent summit.  The provenance object and the
   old resolution must refer to the same checked summit data, propositionally
   or definitionally as appropriate.
4. Retain the original unique-endpoint divisibility/nondivisibility facts when
   useful, but do not bloat the structure with facts derivable cheaply from
   the source and orientation equalities.

## 2. Pull out the new uniform counterexample-origin facts

From the provenance packet, expose at least:

```text
Nat.Coprime summit.gapRoot summit.residualRoot
```

and the exact original endpoint orientation.

Also audit whether the following are uniformly provable and publish them if
clean:

```text
¬ (7 : ℤ) ∣ summit.endpointLeft
¬ (7 : ℤ) ∣ summit.endpointRight
¬ (7 : ℤ) ∣ summit.endpointLeft + summit.endpointRight
```

The first two should follow from the one-hot primitive classification and the
orientation.  The endpoint-sum fact is branch-sensitive:

- x-case: use the already checked exclusion of `7 ∣ y + z`;
- y-case: use the mod-7 relation with `7 ∣ y`;
- z-case: use the signed orientation and the mod-7 relation with `7 ∣ z`.

Do not assert a uniform unit fact unless all three branches check.

These endpoint-unit facts are **not** by themselves a contradiction; the
historical ramified factorization is compatible with them.

## 3. Define the exact terminalization predicate

The old packet is:

```lean
structure TerminalPrimitiveRamifiedSummitPacket : Type where
  summit : PrimitiveRamifiedSummitPacket
  carrierUnit : ℕ
  carrierUnit_pos : 0 < carrierUnit
  carrierUnit_not_seven_dvd : ¬ 7 ∣ carrierUnit
  carrier_eq : carrierUnit = summit.gapRoot * summit.residualRoot
  gap_residual_coprime : Nat.Coprime summit.gapRoot summit.residualRoot
```

Define a light proposition or structure saying that a provenance packet can be
terminalized **with the same summit**.  For example:

```lean
def CounterexampleOriginTerminalizable
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) : Prop :=
  ∃ t : TerminalPrimitiveRamifiedSummitPacket,
    t.summit = r.summit
```

If a stronger equality-preserving wrapper is cleaner, use it.

Do not identify two independently chosen summits merely because their fields
or norms agree.

## 4. Prove the exact terminalization criterion

The current common-summit theorem already gives

```text
v7(|distinguished|) = 1 + v7(gapRoot).
```

Using the new `gap_residual_coprime` provenance, prove the strongest honest
criterion of the conceptual form

```text
CounterexampleOriginTerminalizable r
  ↔ padicValNat 7 r.distinguishedEndpoint = 1
```

or, if the API is cleaner,

```text
CounterexampleOriginTerminalizable r
  ↔ ¬ 7 ∣ r.summit.gapRoot.
```

and separately prove the equivalence between the right-hand conditions.

### Forward direction

A terminal packet with the same summit gives

```text
¬ 7 ∣ summit.gapRoot
```

via the existing `TerminalPrimitiveRamifiedSummitPacket.gapRoot_not_seven_dvd`.
Transport this through the same-summit equality and the checked distinguished
valuation law.  Do not silently replace one summit by another.

### Reverse direction

If the distinguished endpoint has exact depth one, deduce

```text
padicValNat 7 summit.gapRoot = 0
¬ 7 ∣ summit.gapRoot.
```

Construct the terminal packet with

```text
carrierUnit := summit.gapRoot * summit.residualRoot.
```

Use:

- `summit.gapRoot_pos`;
- `summit.residualRoot_pos`;
- `summit.residualRoot_not_seven_dvd`;
- the newly retained `gap_residual_coprime`.

The carrier-unit seven-unit proof must be explicit and kernel checked.

## 5. Split the counterexample-origin summit by endpoint depth

Every distinguished endpoint is divisible by seven, so its depth is positive.
Prove a clean dichotomy:

```text
endpoint depth = 1
or
2 ≤ endpoint depth.
```

Then expose the consequences:

### depth = 1

- the provenance packet terminalizes;
- the historical terminal ramified API is honestly reachable for the same
  summit.

Do **not** claim that the historical tower proves a contradiction.  Audit only
the first reusable public endpoint(s) reachable from the newly constructed
terminal packet.

### depth >= 2

Prove at least:

```text
7 ∣ summit.gapRoot
¬ CounterexampleOriginTerminalizable r
```

This is the genuine higher-depth branch absent from the historical terminal
entry surface.

## 6. Direct counterexample-origin obstruction attempt

Before stopping at the classification, make one bounded attempt to derive
`False` from the stronger provenance packet, using only already checked
arithmetic plus the new provenance fields.

Relevant facts include:

```text
summit.fermat_eq
summit.gap_eq
summit.residual_eq
summit.distinguished_eq
summit.coordinate_eq
summit.root_norm_eq
summit.residualRoot_not_seven_dvd
summit.rootSnd_padicValNat
summit.distinguished_padicValNat
summit.rootSnd_padicValNat_add_two_eq
Nat.Coprime summit.gapRoot summit.residualRoot
```

plus the orientation and one-hot endpoint facts from the actual source.

Check, but do not assume, whether the new endpoint-unit/orientation facts make
any existing ramified factor theorem contradictory.

If no contradiction follows, stop.  Do not re-enter the full heavy fusion
chain merely to reproduce the historical U1.6 frontier.

## 7. Historical reachability audit

In the report, state exactly:

1. whether depth-one counterexample-origin summits can now construct an actual
   `TerminalPrimitiveRamifiedSummitPacket`;
2. the deepest **immediately reusable** old public theorem reached without an
   additional unproved receiver;
3. the first old input that remains unavailable after terminalization, if any;
4. why the depth >= 2 branch cannot use the old terminal entry packet;
5. whether any direct contradiction was found from the new provenance.

Do not state that U1.6 reconstruction has been solved unless the exact named
obligation is inhabited.

## 8. Suggested production files

Prefer a shallow module such as

```text
DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedProvenance.lean
```

and, only if needed for the old terminal type boundary, a second small adapter
module such as

```text
DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedTerminalization.lean
```

Avoid importing the entire heavy historical tower into the first provenance
module.

Update `DkMath/FLT/Seven.lean` only after focused builds succeed.

## 9. API and axiom audits

Add focused tests, e.g.

```text
DkMathTest/FLT/SevenPrimeTraceOnePrimitiveRamifiedProvenanceApiAudit.lean
DkMathTest/FLT/SevenPrimeTraceOnePrimitiveRamifiedProvenanceAxiomAudit.lean
```

Pin at least:

- construction from `CounterexamplePack`;
- same-summit adapter to the existing resolution;
- orientation equations in all three cases;
- `gap_residual_coprime`;
- terminalization criterion;
- depth-one terminalization;
- depth>=2 `7 ∣ gapRoot` and non-terminalizability;
- any direct contradiction theorem if one genuinely exists.

Run `#print axioms` on all new public theorem surfaces.

## 10. ROADMAP / report

Create

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-010.md
```

and update `ROADMAP.md`.

The report must explicitly distinguish:

```text
arbitrary PrimitiveRamifiedSummitPacket
```

from

```text
counterexample-origin provenance packet
```

and from

```text
TerminalPrimitiveRamifiedSummitPacket.
```

Record whether the exact remaining frontier is:

- a direct contradiction already obtained;
- depth-one historical receiver/reconstruction;
- a genuinely new higher-depth (`v7(distinguished) >= 2`) ramified branch;
- or some smaller exact missing invariant discovered during implementation.

## 11. Outcome labels

Use exactly one of:

```text
Outcome A — COUNTEREXAMPLE-ORIGIN RAMIFIED SUMMIT EXCLUDED;
            PRIMITIVE FLT7 CLOSURE NOW AVAILABLE
```

Only use this if a checked theorem from the actual provenance packet gives
`False` with no new hypothesis.

```text
Outcome B — COUNTEREXAMPLE PROVENANCE GREEN; TERMINALIZATION IFF DEPTH ONE;
            HIGHER-DEPTH RAMIFIED BRANCH IS THE PRECISE OPEN FRONTIER
```

Use this if the provenance/terminalization theory checks but no contradiction
is obtained.

```text
Outcome C — ORIENTATION/COPRIMALITY PROVENANCE NEARLY SUFFICIENT;
            ONE EXPLICIT BRIDGE FIELD REMAINS MISSING
```

Use this only if one exact branch field needed for the honest same-summit
terminalization cannot be recovered.

## 12. Hard boundaries

- Do not assume `padicValNat 7 distinguishedEndpoint = 1`.
- Do not assume `¬ 7 ∣ gapRoot`.
- Do not fabricate a terminal carrier or terminal row provenance.
- Do not identify independently chosen summits by norm equality.
- Do not infer a new `CounterexamplePack` from `gapRoot`, `residualRoot`, or
  `root.snd`.
- Do not claim the historical U1.6 reconstruction obligation is inhabited.
- Do not use `sorry`, `sorryAx`, `admit`, `unsafe`, or a new project axiom.
- Do not claim unconditional FLT7 unless the actual counterexample-origin
  provenance packet is kernel-checked impossible.

## 13. Validation

At minimum run focused builds for all new production and audit modules, then:

```text
lake build DkMath.FLT.Seven
```

Run:

- API audit;
- axiom audit;
- forbidden-source scan;
- `git diff --check`.

Preserve existing public APIs unless a change is strictly necessary.

# FLT7TC-005R7 — Higher-depth canonical split and unified receiver frontier

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the completed FLT7TC-005R6 primary routing.  Its
purpose is to determine whether the historical terminal canonical split and
quadratic inner-root extraction are genuinely terminal-depth phenomena, or
whether they extend after the checked 7-primary normalization

```text
gapRoot = 7^k * gapUnit,
right columns = 7^(5 + 7*k), gapUnit^7, |Q|.
```

Do not claim an unconditional receiver, counterexample transition, descent, or
FLT7 contradiction unless Lean actually constructs it.

## 0. Read first

Read at least:

- `DkMath/FLT/Seven/PrimeTraceOneHigherDepthRamifiedRouting.lean`
- `DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedProvenance.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedCanonicalSplit.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedQuadraticInnerRoot.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedGapUnitBridge.lean`
- `DkMath/FLT/Seven/SevenBaseTerminalRamifiedRouting.lean`
- `docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-011.md`
- the current campaign `ROADMAP.md`.

Reuse existing arithmetic lemmas instead of reproving the old terminal tower.

## 1. Generalize the canonical second-coordinate split

Starting from

```lean
r : RamifiedPrimarySecondCoordinateRoutingPacket p
```

construct the higher-depth analogue of
`RamifiedSecondCoordinateCanonicalSplit`.

A suggested public shape is:

```lean
structure RamifiedPrimarySecondCoordinateCanonicalSplit
    (p : PrimitiveRamifiedSummitPacket) : Type where
  primaryRouting : RamifiedPrimarySecondCoordinateRoutingPacket p
  verticalUnitRoot : ℕ
  horizontalUnitRoot : ℕ
  compensationCore : ℕ
  quotientRemainder : ℕ
  unitRoot_eq :
    primaryRouting.primary.unitRoot =
      verticalUnitRoot * horizontalUnitRoot
  rootSnd_eq :
    Int.natAbs p.root.snd =
      7 ^ (5 + 7 * primaryRouting.primary.depth) *
        verticalUnitRoot ^ 7 * compensationCore
  sndCore_eq :
    Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd) =
      horizontalUnitRoot ^ 7 * quotientRemainder
  gapQuotient_eq :
    Int.natAbs
      (ramifiedGapQuotient
        (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
        p.endpointRight).snd =
      compensationCore * quotientRemainder
```

Names may be adjusted to fit the repository, but preserve this mathematical
content.

The expected cell calibration is

```text
c31 = c32 = c33 = 1
c21 = 1
c11 = 7^(5 + 7*k)
c13 = gcd(|root.snd|, |Q|)
```

where `k = primary.depth`.

Use the already checked pairwise-coprime normalized columns from R6.  The
`unitRoot^7` column should split into seventh powers by
`seventh_power_factor_split` exactly as the old `gapRoot^7` column did.

Do not identify independently chosen historical and generalized witnesses.
For depth zero, prove only equation/proposition-level calibration unless
witness identity is definitional.

## 2. Promote the compensation core to a terminal-independent notion

The historical compensation core is only a gcd:

```text
gcd(|root.snd|, |Q|).
```

Expose the smallest terminal-independent definition on a primitive ramified
summit, or on the generalized canonical split, and prove that the generalized
canonical cell `c13` equals it.

At depth zero, if a same-summit terminal packet is supplied, prove that this
new compensation core agrees with the historical
`TerminalPrimitiveRamifiedSummitPacket.ramifiedCompensationCore` by unfolding,
not by choosing a new summit.

## 3. Generalized cubic-gap formula

For the generalized canonical split prove the exact natural formula suggested
by

```text
R - L = 7 * root.snd * norm(root)
```

and the canonical row-one factorization:

```text
|R-L|
  = 7^(6 + 7*k)
      * verticalUnitRoot^7
      * (compensationCore * residualRoot).
```

Here `residualRoot = p.residualRoot` and `k = primary.depth`.

For counterexample-origin provenance, use the retained

```text
Coprime p.gapRoot p.residualRoot
```

to prove the analogue of the historical
`vertical_coprime_compensation_residual` theorem.  It is acceptable for this
coprimality theorem to require a
`PrimitiveCounterexampleRamifiedProvenance source` or an explicit
`Nat.Coprime p.gapRoot p.residualRoot` hypothesis; do not strengthen an
arbitrary summit silently.

## 4. Define the unified receiver

Define the higher-depth receiver by the same integer content as the historical
one:

```text
∃ w : ℕ, compensationCore * residualRoot = w^7.
```

Suggested name:

```lean
RamifiedPrimaryCubicGapSeventhShapeReceiver
```

or another repository-consistent name.

Also define the generalized cubic-gap seventh-power shape:

```text
∃ W,
  |R-L| = 7^(6 + 7*k) * W^7.
```

For counterexample provenance (or with the explicit required coprimality),
prove the exact equivalence

```text
receiver <-> generalized cubic-gap seventh-power shape.
```

As in the historical theorem, the forward root should be
`verticalUnitRoot * w`; the reverse direction must use checked coprimality and
`seventh_power_factor_split`.

Also prove the analogue of

```text
receiver
  <-> (∃ c, compensationCore = c^7)
      ∧ (∃ b, residualRoot = b^7)
```

when the required compensation/residual coprimality is available.

### Depth-zero calibration

If the same summit is terminalizable / supplied as a
`TerminalPrimitiveRamifiedSummitPacket`, show that the generalized receiver
reduces propositionally to the historical
`RamifiedCubicGapSeventhShapeReceiver`.

Do not claim equality of separately chosen canonical split records.

## 5. Attempt to derive the receiver — bounded audit

Now make one honest bounded attempt to derive the receiver from the currently
checked counterexample-origin data.

Permitted inputs include:

- `PrimitiveCounterexampleRamifiedProvenance`;
- the generalized canonical split;
- `ramifiedGapUnitBridge` and its exact integral identity;
- endpoint orientation and endpoint/unit facts;
- `gap_residual_coprime`;
- exact distinguished/root/gap valuations;
- existing mod `7`, `49`, or higher `7^n` facts already in the repository.

A successful result must actually inhabit the receiver or an equivalent
seventh-power shape.  A local unit congruence or a `ZMod` seventh root alone is
not an integer/global receiver.

If the bridge only shows that the cubic and endpoint gaps differ by a 7-adic
unit, record that this is insufficient to prove a global seventh-power unit
without an additional checked invariant.

Do not assume the receiver from the historical terminal tower; that would be
circular.

## 6. Conditional higher-depth inner-root extraction

If the generalized receiver is available as an explicit hypothesis, generalize
the useful part of RAMIFIED-008.

Construct a packet analogous to `RamifiedQuadraticInnerRootPacket` retaining:

```text
root = innerRoot^7
norm(innerRoot) = residualNormRoot
primitive innerRoot coordinates
inner norm is a 7-unit
```

and prove the exact depth transform

```text
v7(|innerRoot.snd|) = 4 + 7*k.
```

Equivalently, for counterexample provenance with distinguished endpoint depth
`d = k + 1`, prove

```text
v7(|innerRoot.snd|) + 3 = 7*d.
```

This is a conditional theorem under the receiver.  Do not call it a descent of
FLT counterexamples.

## 7. Recover the `7^4 * seventh-power` inner shape

The higher-depth primary load should be absorbable into the seventh-power root:

```text
7^(4 + 7*k) * M^7 = 7^4 * (7^k * M)^7.
```

Under the receiver, prove the generalized inner second-coordinate product in
that normalized form, ideally:

```text
|innerRoot.snd| * |innerSndCore|
  = 7^4 * innerLoad^7
```

for an explicit `innerLoad` containing the old vertical/compensation factors
and `7^k`.

Then reuse `seventh_power_split_after_seven_pow_four` if its hypotheses are
honestly available to obtain

```text
|innerRoot.snd| = 7^4 * innerVerticalRoot^7
|innerSndCore|   = innerHorizontalRoot^7.
```

Important: in higher depth, `innerVerticalRoot` need not be a 7-unit.  Therefore
this algebraic `7^4 * seventh-power` normal form does **not** imply exact
`padicValNat = 4`.

If cheap, prove

```text
padicValNat 7 innerVerticalRoot = k
```

or the equivalent depth identity from the two checked formulas.  Do not assume
it.

## 8. Audit downstream reuse

Search all uses of

```lean
RamifiedQuadraticInnerRootPacket.innerRootSnd_depth_eq_four
```

and distinguish:

1. downstream results that only need the algebraic shape
   `7^4 * innerVerticalRoot^7` or seventh-power cubic factors;
2. downstream results that genuinely require exact depth `4` / a 7-unit inner
   vertical root.

Do not port the large fusion tower in this checkpoint.  Record the nearest
reusable next API and the first theorem that genuinely breaks when `k > 0`.

This audit is important because higher depth may preserve the algebraic
seventh-power shape while changing exact valuation from `4` to `4 + 7*k`.

## 9. Files and audits

Prefer a focused new production module, for example:

```text
DkMath/FLT/Seven/PrimeTraceOneHigherDepthRamifiedCanonicalReceiver.lean
```

and, if conditional inner-root code is large, optionally a second focused
module rather than modifying the historical terminal implementation heavily.

Add facade exports and focused tests such as:

```text
DkMathTest/FLT/SevenPrimeTraceOneHigherDepthRamifiedCanonicalReceiverApiAudit.lean
DkMathTest/FLT/SevenPrimeTraceOneHigherDepthRamifiedCanonicalReceiverAxiomAudit.lean
```

Run focused production builds, facade build, API/axiom audit, forbidden-source
scan, and `git diff --check`.

Axiom budget remains inherited kernel axioms only.  No `sorry`, `admit`,
`unsafe`, project `axiom`, or circular final FLT7 import.

## 10. Report and ROADMAP

Create `report-012.md` and update the campaign ROADMAP only after validation.

The report must explicitly distinguish:

- generalized canonical split: proved or not;
- generalized receiver equivalences: proved or not;
- receiver existence from actual counterexample provenance: proved or still
  missing;
- conditional inner-root extraction/depth transform: proved or not;
- downstream exact-depth-4 dependency boundary.

## Outcomes

Use one of the following.

```text
Outcome A — UNIFIED RECEIVER DERIVED FROM COUNTEREXAMPLE PROVENANCE;
            CONDITIONAL BOUNDARY DISCHARGED
```

This requires an actual kernel-checked inhabitant of the generalized receiver
for every counterexample-origin provenance packet.  Do not use Outcome A for
canonical normalization alone.

```text
Outcome B — GENERALIZED CANONICAL SPLIT / RECEIVER EQUIVALENCES GREEN;
            CONDITIONAL INNER-ROOT GENERALIZATION GREEN;
            RECEIVER EXISTENCE REMAINS THE PRECISE GLOBAL FRONTIER
```

Use this if the whole normalized/conditional tower is implemented but the
receiver itself cannot be derived.

```text
Outcome C — GENERALIZED CANONICAL SPLIT GREEN;
            ONE EXPLICIT RECEIVER OR INNER-ROOT BRIDGE REMAINS UNIMPLEMENTED
```

Use this only if the failure is narrower than receiver existence itself.

## Hard boundaries

- Do not treat a `ZMod (7^n)` seventh root as an integer seventh root.
- Do not infer that a 7-adic unit is a global seventh power.
- Do not silently use `gapRoot_not_seven_dvd` in higher depth.
- Do not identify independently chosen canonical routing witnesses.
- Do not call `4 + 7*k` equal to `4` when `k > 0`.
- Do not call the inner-root depth transform a well-founded FLT descent without
  constructing an actual smaller counterexample and measure.
- Do not import a theorem whose conclusion already contains the desired FLT7
  contradiction.

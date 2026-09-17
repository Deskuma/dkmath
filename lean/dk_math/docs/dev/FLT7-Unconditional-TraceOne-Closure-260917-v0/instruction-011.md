# FLT7TC-005R6 — Higher-depth ramified 7-primary normalization and routing

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This checkpoint starts from the exact boundary fixed by FLT7TC-005R5:

```text
CounterexamplePack
  -> PrimitiveCounterexampleRamifiedProvenance
  -> PrimitiveRamifiedSummitPacket
  -> distinguished depth = 1 + v7(gapRoot)
```

Depth one is already terminalizable.  The new open frontier is

```text
v7(distinguishedEndpoint) >= 2
  -> 7 | gapRoot
  -> old TerminalPrimitiveRamifiedSummitPacket unavailable.
```

The historical `RamifiedSecondCoordinateRoutingPacket` fails to apply here for
one structural reason: its right-hand routing columns are

```text
7^5, gapRoot^7, |Q|
```

and the first two are not coprime when `7 | gapRoot`.

The purpose of this checkpoint is to normalize all 7-primary mass out of
`gapRoot`, rebuild the second-coordinate routing board at arbitrary ramified
depth, and determine the exact inner-root depth transform if the historical
shape receiver is generalized honestly.

Do **not** construct a new FLT counterexample, do **not** assume a receiver,
and do **not** claim descent merely because one internal coordinate loses one
factor of seven.

---

## 0. Read first

Read these current files before changing anything:

```text
DkMath/FLT/Seven/PrimeTraceOnePrimitiveRamifiedProvenance.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedDepth.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedRouting.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedCompensationRouting.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedCanonicalSplit.lean
DkMath/FLT/Seven/SevenBaseTerminalRamifiedQuadraticInnerRoot.lean
DkMath/FLT/Seven/CoprimeTripleRouting.lean
```

Also read:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-010.md
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/ROADMAP.md
```

Treat existing terminal theorems as checked reference implementations.  Do not
silently transport a theorem whose proof needs `7 ∤ gapRoot` to the higher-depth
case.

---

## 1. First isolate the terminal-independent arithmetic

Several theorems currently live under `TerminalPrimitiveRamifiedSummitPacket`
even though their proofs use only the underlying `PrimitiveRamifiedSummitPacket`.
Audit them one by one.

The important generic facts are conceptually:

```text
root.snd * SndCore(root) = 7^5 * gapRoot^7 * Q
Coprime(|root.snd|, |SndCore(root)|)
Coprime(residualRoot, |root.snd|)
Coprime(residualRoot, |SndCore(root)|)
Coprime(gapRoot, |endpointRight|)
Coprime(gapRoot, |Q|)
```

where

```text
Q := (ramifiedGapQuotient
        (7^5 * gapRoot^7)
        endpointRight).snd.
```

Prefer exposing generic `PrimitiveRamifiedSummitPacket` versions rather than
duplicating long proofs.  If an old theorem can be refactored so the terminal
version becomes a corollary, preserve the old public API.

Do **not** generalize any fact that actually uses
`TerminalPrimitiveRamifiedSummitPacket.gapRoot_not_seven_dvd`.

In particular, these terminal facts must remain terminal-only:

```text
rootSnd_depth_eq_five
endpointGap_depth_eq_six
cubicGap_depth_eq_six
```

The already generic depth law remains:

```text
v7(|root.snd|) = 5 + 7*v7(gapRoot).
```

---

## 2. Exact 7-primary decomposition of `gapRoot`

For every positive summit gap root define or construct a checked decomposition

```text
k := padicValNat 7 gapRoot

gapRoot = 7^k * gapUnit
0 < gapUnit
7 ∤ gapUnit.
```

Use an existing Mathlib/DkMath valuation decomposition if one is already
available.  Otherwise add the smallest local/general helper needed.  Avoid
inventing a second valuation definition.

Suggested packet shape (name may vary):

```lean
structure RamifiedGapRootPrimaryDecomposition
    (p : PrimitiveRamifiedSummitPacket) : Type where
  depth : ℕ
  unitRoot : ℕ
  depth_eq : depth = padicValNat 7 p.gapRoot
  unitRoot_pos : 0 < unitRoot
  gapRoot_eq : p.gapRoot = 7 ^ depth * unitRoot
  unitRoot_not_seven_dvd : ¬ 7 ∣ unitRoot
```

A definition with `depth` definitionally equal to `padicValNat ...` is also
fine.  The mathematical content is the exact factorization and unit statement.

Pin the special case:

```text
depth = 0  <->  7 ∤ gapRoot.
```

For a `PrimitiveCounterexampleRamifiedProvenance r`, also expose

```text
primary.depth + 1 = v7(r.distinguishedEndpoint)
```

or the equivalent orientation.

---

## 3. Normalize the second-coordinate product

Starting from the generic identity

```text
root.snd * SndCore(root) = 7^5 * gapRoot^7 * Q,
```

prove its natural-absolute-value form after primary decomposition:

```text
|root.snd| * |SndCore(root)|
  = 7^(5 + 7*k) * gapUnit^7 * |Q|.
```

Here `k = v7(gapRoot)`.

This equality is a required checkpoint theorem.  Do not leave the expression
as `(7^5) * (7^k * gapUnit)^7` in the public theorem unless Lean normalization
makes the combined exponent materially awkward; the report must still record
the exact exponent `5 + 7*k`.

Also prove the three right-column factors are pairwise coprime:

```text
Coprime (7^(5 + 7*k)) (gapUnit^7)
Coprime (7^(5 + 7*k)) |Q|
Coprime (gapUnit^7) |Q|.
```

The first two should come from the 7-unit facts.  The third should descend from
the generic `Coprime(gapRoot, |Q|)` using `gapUnit ∣ gapRoot`.

This is the exact repair for the higher-depth failure of the old board.

---

## 4. Generalized second-coordinate routing board

If Section 3 is green, construct the arbitrary-depth analogue of
`RamifiedSecondCoordinateRoutingPacket`.

Suggested shape:

```lean
structure RamifiedPrimaryNormalizedSecondCoordinateRoutingPacket
    (p : PrimitiveRamifiedSummitPacket) : Type where
  primary : RamifiedGapRootPrimaryDecomposition p
  routing :
    CoprimeTripleRouting
      (Int.natAbs p.root.snd)
      (Int.natAbs (seventhPowerSndCore p.root.fst p.root.snd))
      1
      (7 ^ (5 + 7 * primary.depth))
      (primary.unitRoot ^ 7)
      (Int.natAbs
        (ramifiedGapQuotient
          (7 ^ 5 * (p.gapRoot : ℤ) ^ 7)
          p.endpointRight).snd)
```

Use `nonempty_coprimeTripleRouting`; do not hand-construct nine cells.

Required public theorem:

```text
PrimitiveRamifiedSummitPacket
  -> Nonempty (RamifiedPrimaryNormalizedSecondCoordinateRoutingPacket p)
```

or an equivalent theorem with a canonical decomposition argument.

This theorem should work both at depth zero and higher depth.

### Depth-zero calibration

Show that when `k = 0`, the normalized right columns reduce to the historical
terminal columns

```text
7^5, gapRoot^7, |Q|
```

up to the proved equality `gapUnit = gapRoot`.

Do not claim equality of independently chosen routing packets.  Proposition- or
parameter-level calibration is enough.

---

## 5. Generalized canonical split

If Section 4 is green without importing a contradiction, adapt the historical
canonical-split argument to the normalized board.

Expected data:

```text
unitRoot = verticalUnitRoot * horizontalUnitRoot

|root.snd|
  = 7^(5 + 7*k) * verticalUnitRoot^7 * compensationCore

|SndCore(root)|
  = horizontalUnitRoot^7 * quotientRemainder

|Q| = compensationCore * quotientRemainder.
```

Suggested packet name:

```text
RamifiedPrimaryNormalizedCanonicalSplit
```

The old proof that the entire visible 7-primary column goes to the root-second
coordinate should now use

```text
7 ∤ SndCore(root)
7 ∤ gapUnit
7 ∤ Q.
```

Do not use `gapRoot_not_seven_dvd` here.

If this section exposes a hidden use of terminality that cannot be replaced by
unit-normalization, stop and report the exact theorem/field.

---

## 6. Optional but high-value: generalized receiver and inner-root depth

Proceed here only if Sections 1–5 are green and the implementation remains
local/auditable.

Generalize the historical cubic-gap shape receiver to the normalized primary
load.  The expected cubic-gap valuation is

```text
v7(|ramifiedRightCubic - ramifiedLeftCubic|)
  = 6 + 7*k.
```

The normalized shape should therefore be conceptually

```text
∃ W,
  |ramifiedRightCubic - ramifiedLeftCubic|
    = 7^(6 + 7*k) * W^7.
```

Prove the analogue of the historical receiver equivalence if its proof uses
only the normalized canonical split and coprimality:

```text
receiver
  <-> compensationCore is a seventh power
      and residualRoot is a seventh power.
```

Do **not** prove or assume that the receiver is inhabited.

If a receiver is supplied as an explicit hypothesis, construct the corresponding
inner quadratic root exactly as the old
`RamifiedQuadraticInnerRootPacket` does:

```text
summit.root = innerRoot^7.
```

Then prove the exact depth transform

```text
v7(|innerRoot.snd|) = 4 + 7*k.
```

This should follow from

```text
v7(|summit.root.snd|) = 5 + 7*k
summit.root.snd = seventhPowerSnd(innerRoot)
7 ∤ inner SndCore.
```

For counterexample provenance, rewrite it using

```text
d := v7(distinguishedEndpoint) = 1 + k
```

and expose

```text
v7(|innerRoot.snd|) = 7*d - 3.
```

Use a subtraction-free equivalent if preferable in `Nat`, e.g.

```text
v7(|innerRoot.snd|) + 3 = 7*d.
```

Finally record the direction of this transform:

```text
1 ≤ d -> d < v7(|innerRoot.snd|).
```

Thus the historical internal `root.snd -> innerRoot.snd` step drops depth by
exactly one **inside the quadratic root tower**, but if `|innerRoot.snd|` is
viewed as a candidate next distinguished FLT carrier, its depth is strictly
larger than the original distinguished endpoint depth.  This is **not** a
well-founded FLT descent measure.

Do not manufacture a new `CounterexamplePack` from this candidate.

---

## 7. Counterexample-origin higher-depth audit

For

```text
r : PrimitiveCounterexampleRamifiedProvenance source
hdepth : 2 ≤ padicValNat 7 r.distinguishedEndpoint
```

pin these facts together in one small public audit theorem/packet:

```text
k = v7(r.summit.gapRoot) >= 1
7 | r.summit.gapRoot
normalized routing exists
historical same-summit terminalization does not exist.
```

If Section 6 is implemented, additionally state the conditional receiver
consequence with inner depth `7*d - 3`.

This theorem is meant to make the exact higher-depth frontier visible to later
checkpoints.

---

## 8. Direct contradiction audit

After all checked normalized data are available, make one bounded attempt at a
direct contradiction using only:

- counterexample provenance and orientation;
- endpoint and endpoint-sum 7-unit facts;
- `Coprime gapRoot residualRoot`;
- exact primary decomposition;
- normalized second-coordinate routing;
- generic ramified cubic routing already available for
  `PrimitiveRamifiedSummitPacket`;
- exact depth identities.

Do not import a historical theorem whose assumptions include the missing
receiver and then treat it as unconditional.

If no contradiction follows, say so explicitly.  The likely frontier is then
the generalized shape receiver / global seventh-power condition, not the
7-primary routing itself.

---

## 9. Suggested files

Prefer one light production module:

```text
DkMath/FLT/Seven/PrimeTraceOneHigherDepthRamifiedRouting.lean
```

If Section 6 becomes large, split the conditional receiver/inner-root layer:

```text
DkMath/FLT/Seven/PrimeTraceOneHigherDepthRamifiedInnerRoot.lean
```

Add facade exports only for stable public theorems.

Audits:

```text
DkMathTest/FLT/SevenPrimeTraceOneHigherDepthRamifiedRoutingApiAudit.lean
DkMathTest/FLT/SevenPrimeTraceOneHigherDepthRamifiedRoutingAxiomAudit.lean
```

If the optional inner-root module is public, include its primary endpoint in
the same audit or add a narrowly named second audit.

Report:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-011.md
```

Update `ROADMAP.md` after validation.

---

## 10. Required API audit points

At minimum pin:

```text
exact gapRoot = 7^k * gapUnit decomposition
7 ∤ gapUnit
normalized product exponent = 5 + 7*k
pairwise coprimality of normalized right columns
Nonempty generalized second-coordinate routing
```

If canonical split is implemented, pin its three factor equations.

If the conditional inner-root layer is implemented, pin:

```text
root = innerRoot^7
inner root second-coordinate depth = 4 + 7*k
counterexample form: inner depth + 3 = 7*distinguished depth
```

For provenance, pin the higher-depth nonterminalization theorem.

The axiom audit should remain on the inherited surface only, expected:

```text
[propext, Classical.choice, Quot.sound]
```

subject to the exact transitive dependencies used.

---

## 11. Outcome labels

Use exactly one of these unless an actual FLT contradiction is kernel-checked.

### Outcome A

```text
Outcome A — HIGHER-DEPTH 7-PRIMARY NORMALIZATION AND GENERALIZED ROUTING GREEN;
            CONDITIONAL INNER-ROOT DEPTH TRANSFORM RECOVERED
```

Use this if the normalized routing/canonical split is complete and the optional
receiver implication reaches the exact inner-depth transform.

### Outcome B

```text
Outcome B — HIGHER-DEPTH 7-PRIMARY NORMALIZATION AND GENERALIZED ROUTING GREEN;
            SHAPE RECEIVER / INNER-ROOT EXTRACTION REMAINS THE PRECISE FRONTIER
```

Use this if the routing layer is fully generalized but Section 6 stops at the
receiver boundary.

### Outcome C

```text
Outcome C — PRIMARY NORMALIZATION GREEN; ONE EXPLICIT COPRIMALITY OR ROUTING
            BRIDGE REMAINS MISSING
```

Use this only if the exact 7-primary decomposition/product rewrite succeeds but
`nonempty_coprimeTripleRouting` cannot yet be supplied.  Name the exact missing
pairwise-coprime theorem or product identity.

If a genuine contradiction

```text
PrimitiveCounterexampleRamifiedProvenance source -> False
```

is obtained without extra hypotheses, stop immediately, audit it separately,
and report that FLT7TC-006 may now be opened.  Do not bury such a result inside
Outcome A/B/C.

---

## 12. Hard boundaries

Do not:

- assume `7 ∤ gapRoot` in the higher-depth branch;
- replace `gapRoot` by a chosen unit factor without proving the exact product;
- assume the historical `RamifiedCubicGapSeventhShapeReceiver`;
- infer a new FLT counterexample from an inner quadratic coordinate;
- call `d -> 7*d-3` a descent;
- identify independently chosen routing/canonical-split witnesses by
  definitional equality;
- treat a local seventh-power shape as a global natural Fermat reconstruction;
- add `sorry`, `sorryAx`, `admit`, `unsafe`, or a project `axiom`.

The purpose is to decide whether higher ramified depth is a genuinely new
arithmetic obstruction or merely the old second-coordinate routing with its
7-primary load normalized correctly.

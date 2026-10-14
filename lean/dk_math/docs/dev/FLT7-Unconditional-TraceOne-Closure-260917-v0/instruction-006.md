# FLT7TC-005R — Common counterexample-carrier reconstruction kernel

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

This is a bounded intermediate checkpoint between completed `FLT7TC-005` and the still-blocked primitive branch closure `FLT7TC-006`.

Do **not** mark primitive FLT7 closure complete in this checkpoint.

The purpose is to determine whether the two currently named reconstruction failures

```text
AwayDescentClosureProvider
InternalDepthFourCounterexampleReconstructionObligation
```

are genuinely different mathematical obligations, or merely two specializations of the same missing receiver:

```text
"construct an actual away FLT7 counterexample whose exceptional carrier is a prescribed natural number C".
```

The expected result is a small reconstruction-kernel API plus exact equivalence theorems.  No existence theorem for the kernel may be assumed.

---

## 0. Read first

Read the current production sources and reports before editing:

```text
DkMath/FLT/Seven/AwayValuationTransfer.lean
DkMath/FLT/Seven/DescentClosureAudit.lean
DkMath/FLT/Seven/SevenPivotDepthPacket.lean
DkMath/FLT/Seven/SevenRamifiedFusionStrictDescentFailureBoundary.lean
DkMath/FLT/Seven/PrimeTraceOneAwayClosureAudit.lean
DkMath/FLT/Seven/PrimeTraceOneRamifiedSummitBridge.lean

docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-004.md
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-005.md
DkMath/FLT/Seven/docs/STATUS.md
```

The current checked boundaries are:

### Away route

For

```lean
p : AwayValuationTransferPacket x y z
```

we have

```text
padicValNat 7 p.carrier
  = 1 + padicValNat 7 (Int.natAbs p.normal.root.snd)
```

and hence a strict depth drop to the candidate carrier

```text
Int.natAbs p.normal.root.snd.
```

But `AwayDescentClosureProvider` requires an actual new away FLT7 counterexample whose selected carrier equals that candidate.

### Ramified U1.6 route

For

```lean
p : RamifiedSignedRootRoutingPacket
```

we have

```text
padicValNat 7 (internalDepthFourCarrier p) = 4
padicValNat 7 (outerDepthFiveCarrier p) = 5
```

and the missing proposition

```lean
InternalDepthFourCounterexampleReconstructionObligation p
```

is literally the existence of an actual `AwayValuationTransferPacket` whose carrier is `internalDepthFourCarrier p`.

Do not assume either obligation is inhabited.

---

## 1. Core reconstruction predicate

Add the smallest honest production abstraction, preferably in a new module such as

```text
DkMath/FLT/Seven/PrimeTraceOneReconstructionKernel.lean
```

or a better repository-conventional name if source inspection suggests one.

Define a proposition conceptually equivalent to:

```lean
def AwayCarrierReconstruction (carrier : ℕ) : Prop :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = carrier
```

Use a name that clearly means:

```text
"there exists an actual primitive positive away FLT7 counterexample
 whose selected exceptional carrier is exactly carrier".
```

Do **not** weaken this to arbitrary integers, arbitrary coordinate solutions, or an isolated valuation packet.

The witness must remain an actual `AwayValuationTransferPacket`.

Do **not** add this proposition as a structure field elsewhere to fake existence.

---

## 2. Normalize `AwayDescentClosureProvider`

Prove that the historical away closure provider is equivalent to the new carrier reconstruction predicate at the old root second coordinate.

Target shape, adapting names as appropriate:

```lean
theorem awayCarrierReconstruction_iff_nonempty_descentClosureProvider
    {x y z : ℕ} (p : AwayValuationTransferPacket x y z) :
    AwayCarrierReconstruction (Int.natAbs p.normal.root.snd) ↔
      Nonempty (AwayDescentClosureProvider x y z p)
```

Important observation to kernel-check rather than merely state in the report:

`AwayDescentClosureProvider.nextPack` is not extra mathematical data beyond `nextRoute`, because

```lean
nextRoute.normal.counterexample : CounterexamplePack nextX nextY nextZ
```

is already available from the route.

Thus, in the forward construction, use the route's own counterexample packet rather than introducing any new axiom or arbitrary source.

Conversely, extract the provider's `nextRoute` and `carrier_match`.

This theorem is an exact logical normalization of the old closure boundary; it is **not** a proof that the boundary is inhabited.

---

## 3. Normalize U1.6 reconstruction

Bridge the heavy ramified U1.6 boundary to the same predicate.

Target shape:

```lean
theorem internalDepthFourReconstruction_iff_awayCarrierReconstruction
    (p : RamifiedSignedRootRoutingPacket) :
    InternalDepthFourCounterexampleReconstructionObligation p ↔
      AwayCarrierReconstruction
        (RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier p)
```

Use the exact namespace path required by the existing source.

This should be close to definitional/propositional normalization.  Do not rebuild any degree-six arithmetic.

If importing the U1.6 source into the light kernel module creates an undesirable dependency direction, split the implementation into:

```text
light common reconstruction-kernel module
heavy U1.6 bridge module
```

The common predicate must not depend on the degree-six tower merely to state away reconstruction.

---

## 4. Necessary local conditions for a reconstructible carrier

From an actual reconstruction witness, expose the local facts that every prescribed carrier must satisfy.

At minimum prove, with exact theorem names chosen to fit conventions:

```text
AwayCarrierReconstruction carrier -> 0 < carrier
AwayCarrierReconstruction carrier -> 1 ≤ padicValNat 7 carrier
AwayCarrierReconstruction carrier -> 7 ∣ carrier
```

The source must be the existing `AwayValuationTransferPacket` fields/theorems, especially

```lean
AwayValuationTransferPacket.carrier_pos
AwayValuationTransferPacket.one_le_carrier_depth
```

plus standard checked `padicValNat` divisibility APIs.

Do not claim these necessary conditions are sufficient.

---

## 5. Exact predecessor depth for the away target

For

```lean
p : AwayValuationTransferPacket x y z
```

make the existing valuation equation available in the target-carrier language.

Prove a theorem conceptually equivalent to:

```lean
padicValNat 7 (Int.natAbs p.normal.root.snd)
  = padicValNat 7 p.carrier - 1
```

using only

```lean
p.valuation_eq
```

and natural arithmetic.

Then classify the two depth regimes.

### 5a. Terminal depth one

If

```text
padicValNat 7 p.carrier = 1
```

then the candidate carrier has depth zero.

Since every actual `AwayValuationTransferPacket` carrier has positive seven-adic depth, prove:

```lean
¬ AwayCarrierReconstruction (Int.natAbs p.normal.root.snd)
```

and consequently, via the equivalence from section 2:

```lean
¬ Nonempty (AwayDescentClosureProvider x y z p)
```

or the strongest clean theorem surface that follows without awkward negative `Nonempty` syntax.

This is important: the historical `AwayDescentClosureProvider` is **not** intended to exist at terminal depth one.  At depth one the recursive away target has fallen outside the away-carrier class and the separate terminal machinery must take over.

Do not interpret failure of an away provider at depth one as an FLT contradiction.

### 5b. Depth at least two

If

```text
2 ≤ padicValNat 7 p.carrier
```

prove that the target candidate satisfies

```text
7 ∣ Int.natAbs p.normal.root.snd
```

or the equivalent integer divisibility statement already supported by the repository.

This shows that the target passes the **necessary local seven-divisibility gate** for being another away exceptional carrier.

Do not promote this to an existence theorem.

A useful existing theorem may be

```lean
AwayValuationTransferPacket.fortyNine_dvd_carrier_iff
```

or direct `padicValNat` arithmetic.  Use the shortest checked route.

---

## 6. U1.6 admissibility check

Use

```text
padicValNat 7 (internalDepthFourCarrier p) = 4
```

to show that the U1.6 target satisfies the necessary local reconstruction conditions from section 4:

```text
0 < internalDepthFourCarrier p
7 ∣ internalDepthFourCarrier p
1 ≤ padicValNat 7 (internalDepthFourCarrier p)
```

where positivity follows honestly from the exact positive valuation/nonzero API available in the repository.

If positivity is not available without additional work, report that exact gap rather than silently inferring it from informal valuation language.

The intended conclusion is only:

```text
U1.6 is not blocked by the trivial depth-zero obstruction.
```

It remains blocked by actual counterexample reconstruction.

---

## 7. Audit the terminal/recursive split

Read the existing pivot/terminal APIs around

```text
AwaySevenPivotDepthPacket
SevenBaseTerminal*
```

and record the exact relation between:

```text
away carrier depth = 1
root candidate depth = 0
historical terminal route
```

Do not manufacture an equality between independently chosen routing packets.

If there is already a direct checked theorem that starts from the same `AwayValuationTransferPacket` and identifies the terminal exponent with its carrier depth, use it.

If existing terminal code obtains a newly chosen `AwayValuationTransferPacket` through `AwayCubicProductPacket` / `AwayCubicRoutingPacket`, and therefore does not definitionally preserve the original packet's selected carrier, state this precisely in the report.

The checkpoint does **not** require rebuilding the terminal route.

---

## 8. Architectural theorem / report conclusion

The report must answer these questions explicitly.

### Q1

Are

```text
AwayDescentClosureProvider
InternalDepthFourCounterexampleReconstructionObligation
```

instances of one common prescribed-carrier reconstruction problem?

Expected answer is `YES` only if the requested equivalence theorems kernel-check.

### Q2

Is `AwayDescentClosureProvider` actually too strong at depth one?

Expected checked statement:

```text
carrier depth = 1
-> target root.snd depth = 0
-> no target can be the carrier of an AwayValuationTransferPacket
```

### Q3

At carrier depth >= 2, what is proved?

Distinguish carefully:

```text
necessary local divisibility/admissibility
```

from

```text
actual FLT counterexample reconstruction.
```

### Q4

Does U1.6 fail for the same reason as nonterminal away descent?

If the common predicate theorem succeeds, the precise answer should be:

```text
both require constructing an actual away FLT7 counterexample
with a prescribed exceptional carrier;
the prescribed carriers differ, but the receiver type is the same.
```

### Q5

Does this checkpoint construct either of those counterexamples?

Unless a genuinely new proof is found, the answer must be `NO`.

---

## 9. Suggested production theorem surface

Names may be adjusted to repository conventions, but aim for a compact reusable surface resembling:

```text
AwayCarrierReconstruction
awayCarrierReconstruction_iff_nonempty_descentClosureProvider
internalDepthFourReconstruction_iff_awayCarrierReconstruction
AwayCarrierReconstruction.carrier_pos
AwayCarrierReconstruction.one_le_carrier_depth
AwayCarrierReconstruction.seven_dvd_carrier
AwayValuationTransferPacket.root_snd_depth_eq_carrier_depth_sub_one
AwayValuationTransferPacket.no_reconstruction_at_depth_one
AwayValuationTransferPacket.seven_dvd_root_snd_of_two_le_carrier_depth
```

Do not add duplicate theorems if equivalent APIs already exist; reuse and expose them instead.

---

## 10. Stop rules

Stop and report rather than force a theorem if any of the following occurs:

- a new FLT7 counterexample is inferred merely from a smaller natural number;
- an `AwayValuationTransferPacket` is created without an actual `CounterexamplePack`;
- a carrier equality is inferred only from equal `padicValNat` values;
- independently chosen routing/valuation packets are identified by proof irrelevance when their **data fields** are not propositions;
- the U1.6 internal coordinate is called an endpoint/carrier of a Fermat counterexample without the reconstruction witness;
- terminal depth one is treated as recursive away descent;
- a well-founded recursive relation is claimed without an indexed state transition;
- any theorem requires `sorry`, `sorryAx`, `admit`, `axiom`, or `unsafe`.

---

## 11. Outcome labels

Use exactly one of the following.

### Outcome A — COMMON RECONSTRUCTION KERNEL GREEN; NEW PROVIDER FOUND

Use only if the common kernel is established **and** this checkpoint genuinely constructs a previously missing reconstruction witness (`AwayDescentClosureProvider`, U1.6 obligation, or equivalent actual away counterexample at the prescribed carrier).

This would be a major mathematical advance; explain exactly which reconstruction was obtained.

### Outcome B — COMMON RECONSTRUCTION KERNEL GREEN; TERMINAL DEPTH SPLIT EXPOSED; PROVIDER STILL MISSING

Expected outcome if:

- both historical obligations normalize to the same carrier-reconstruction predicate;
- depth-one away reconstruction is proved impossible/terminal;
- depth >= 2 passes only the necessary local seven-divisibility gate;
- U1.6 target is locally admissible;
- no new counterexample is constructed.

### Outcome C — AWAY AND U1.6 RECONSTRUCTION OBLIGATIONS ARE NOT THE SAME RECEIVER

Use if exact source typing/provenance prevents the requested common-predicate equivalences.  Identify the first non-equivalent field precisely.

### Outcome D — PROPOSED NORMALIZATION IS FALSE OR CIRCULAR

Use if the proposed equivalence would require assuming the reconstruction itself, identifying unrelated chosen packets, or importing a theorem whose conclusion already contains the desired provider.

---

## 12. Verification

Add focused API and axiom audits for the new public theorem surface.

At minimum run focused builds for all directly modified/added modules plus:

```text
lake build DkMath.FLT.Seven.AwayValuationTransfer
lake build DkMath.FLT.Seven.DescentClosureAudit
lake build DkMath.FLT.Seven.SevenRamifiedFusionStrictDescentFailureBoundary
lake build DkMath.FLT.Seven
```

Run the corresponding new API audit and axiom audit.

Check public declarations with `#print axioms`.

Expected allowed foundational surface remains the repository's ordinary inherited set, typically:

```text
propext
Classical.choice
Quot.sound
```

Do not add project axioms.

Also run:

```text
forbidden-source scan
git diff --check
```

Create:

```text
docs/dev/FLT7-Unconditional-TraceOne-Closure-260917-v0/report-006.md
```

Update `ROADMAP.md` honestly.  Since the existing `FLT7TC-006` primitive branch closure remains blocked until reconstruction is solved, prefer recording this checkpoint as an intermediate reconstruction-kernel frontier (for example `FLT7TC-005R`) rather than falsely marking primitive closure current/completed.

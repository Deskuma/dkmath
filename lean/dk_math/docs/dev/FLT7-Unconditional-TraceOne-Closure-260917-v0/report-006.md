# FLT7TC-005R — Common counterexample-carrier reconstruction kernel

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

The attached `instruction-006.md` was treated as the bounded implementation
contract, separately from the user's request to read, reason, and implement.
This checkpoint normalizes the two named reconstruction failures.  It does
not mark primitive FLT7 closure complete and does not assume existence of any
new counterexample.

## 1. Files changed

Production:

- `DkMath/FLT/Seven/PrimeTraceOneReconstructionKernel.lean`
- `DkMath/FLT/Seven/PrimeTraceOneReconstructionKernelU16.lean`
- `DkMath/FLT/Seven.lean` (facade exports)

Audits:

- `DkMathTest/FLT/SevenPrimeTraceOneReconstructionKernelApiAudit.lean`
- `DkMathTest/FLT/SevenPrimeTraceOneReconstructionKernelAxiomAudit.lean`

Documentation:

- this report;
- `ROADMAP.md` status update.

The attached `instruction-006.md` was preserved unchanged.

## 2. Common reconstruction receiver

The light production module defines:

```lean
def AwayCarrierReconstruction (carrier : ℕ) : Prop :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = carrier
```

The witness remains an actual `AwayValuationTransferPacket`, and therefore
retains its `CounterexamplePack` through `route.normal.counterexample`.  No
isolated valuation packet or arbitrary coordinate solution is admitted.

The theorem
`awayCarrierReconstruction_iff_nonempty_descentClosureProvider` proves:

```text
AwayCarrierReconstruction (Int.natAbs p.normal.root.snd)
  ↔ Nonempty (AwayDescentClosureProvider x y z p).
```

The forward direction constructs `nextPack` from
`nextRoute.normal.counterexample`; the reverse direction extracts
`nextRoute` and its `carrier_match`.  Thus the historical provider's explicit
`nextPack` field is not additional mathematical data beyond the chosen route.
This is an exact proposition-level normalization, not an inhabitance result.

## 3. Necessary conditions on a reconstructible carrier

The public namespace `AwayCarrierReconstruction` exposes:

```text
AwayCarrierReconstruction carrier -> 0 < carrier
AwayCarrierReconstruction carrier -> 1 ≤ padicValNat 7 carrier
AwayCarrierReconstruction carrier -> 7 ∣ carrier.
```

These are necessary local conditions inherited from the actual route's
`carrier_pos` and `one_le_carrier_depth` fields plus the checked
`padicValNat` divisibility API.  They are not claimed sufficient for
`AwayCarrierReconstruction`.

## 4. Away predecessor depth and the terminal split

The theorem
`AwayValuationTransferPacket.root_snd_depth_eq_carrier_depth_sub_one` rewrites
the existing valuation equation into the target-carrier form:

```text
padicValNat 7 (Int.natAbs p.normal.root.snd)
  = padicValNat 7 p.carrier - 1.
```

At carrier depth one, the target depth is zero.  Since every actual away
packet carrier has positive seven-adic depth, the kernel proves both:

```text
¬ AwayCarrierReconstruction (Int.natAbs p.normal.root.snd)
¬ Nonempty (AwayDescentClosureProvider x y z p).
```

This is a terminal classification, not an FLT contradiction and not a
recursive away step.  The existing terminal/seed audit remains consistent
with this split: `AwayDescentReconstructionSeed.two_le_pivotExponent` and
`AwayDescentClosureProvider.two_le_pivotExponent` place those recursive
providers beyond exponent one.  The terminal machinery uses its own checked
routing construction; this checkpoint does not identify independently chosen
routing packets or rebuild that route.

At carrier depth at least two, the theorem
`AwayValuationTransferPacket.seven_dvd_root_snd_of_two_le_carrier_depth`
proves only:

```text
7 ∣ Int.natAbs p.normal.root.snd.
```

This is the necessary local seven-divisibility gate for a possible next
carrier.  It does not construct a new `CounterexamplePack`, a new
`AwayValuationTransferPacket`, or a provider.

## 5. U1.6 normalization and admissibility

The heavy bridge module proves:

```lean
internalDepthFourReconstruction_iff_awayCarrierReconstruction
```

for the exact existing `InternalDepthFourCounterexampleReconstructionObligation`
and the exact carrier
`RamifiedSignedRootRoutingPacket.QuotientPrimeSupport.internalDepthFourCarrier`.
The equivalence is a direct normalization of the existential packet witness;
it does not rebuild degree-six arithmetic.

The theorem `internalDepthFourCarrier_admissible` uses the checked exact
valuation

```text
padicValNat 7 (internalDepthFourCarrier p) = 4
```

to prove positivity, depth at least one, and divisibility by seven.  Hence
the U1.6 target is not blocked by the trivial depth-zero obstruction.  It
still requires the same missing actual away counterexample reconstruction,
with a different prescribed carrier.

## 6. Answers to the checkpoint questions

Q1. **YES.** Both `AwayDescentClosureProvider` and
`InternalDepthFourCounterexampleReconstructionObligation` normalize to the
same prescribed-carrier receiver, and both equivalences kernel-check.

Q2. **YES, at depth one.** The away provider is too strong there because its
candidate root second coordinate has depth zero, outside the carrier class.
The result is a terminal split, not a contradiction.

Q3. At depth at least two, only the necessary local divisibility gate for the
candidate is proved.  No actual away counterexample reconstruction follows.

Q4. **They fail for the same receiver reason.** The prescribed carriers are
different, but both obligations require an actual away FLT7 counterexample
whose selected exceptional carrier equals the prescribed natural number.

Q5. **NO.** This checkpoint constructs neither an away closure provider nor
the U1.6 reconstruction witness.

## Outcome

**Outcome B — COMMON RECONSTRUCTION KERNEL GREEN; TERMINAL DEPTH SPLIT
EXPOSED; PROVIDER STILL MISSING**.

The common API is now reusable, but FLT7TC-006 remains blocked.  No primitive
closure theorem, general FLT7 theorem, or unconditional counterexample
reconstruction is claimed.

## Validation

The following focused builds completed successfully:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionKernel
lake build DkMath.FLT.Seven.PrimeTraceOneReconstructionKernelU16
lake build DkMath.FLT.Seven.AwayValuationTransfer
lake build DkMath.FLT.Seven.DescentClosureAudit
lake build DkMath.FLT.Seven.SevenRamifiedFusionStrictDescentFailureBoundary
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneReconstructionKernelApiAudit
lake build DkMathTest.FLT.SevenPrimeTraceOneReconstructionKernelAxiomAudit
```

The new public declarations' axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.  No project axiom was added.  The
production and API-audit Lean sources contain no `sorry`, `sorryAx`, `admit`,
`axiom`, or `unsafe` declaration; the separate axiom-audit file contains only
intentional `#print axioms` commands.  The forbidden-source scan and
`git diff --check` completed without diagnostics, including the new report's
whitespace check.

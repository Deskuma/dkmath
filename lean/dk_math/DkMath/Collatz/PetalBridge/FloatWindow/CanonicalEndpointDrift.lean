/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift"

namespace DkMath.Collatz

/-!
# Canonical endpoint drift

This module isolates the arithmetic boundary left by the finite source-age
certificate audit.  The endpoint term is exactly a binary-width difference.
Two boundedness questions must therefore remain distinct:

* `RootwiseEndpointDriftBound n` fixes one odd root and ranges over its blocks;
* `GlobalEndpointDriftBound` asks for one ceiling shared by every odd root.

A family of different roots may refute the second statement without saying
anything about the first.  The distinction is part of the public API and must
not be erased by later finite-signature work.
-/

/-! ## Exact canonical width ledger -/

/-- The endpoint accounting term is exactly the signed width change from the
canonical block start to the next canonical block start. -/
theorem endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub
    (n : OddNat) (m : ℕ) :
    endpointAccountingTerm n m =
      (bitWidth (canonicalBlockNextStartState n m) : ℤ) -
        bitWidth (canonicalBlockStartState n m) := by
  rw [endpointAccountingTerm_eq_universalPaymentBlockSignedDriftAt,
    universalPaymentBlockSignedDriftAt_eq_bitWidth_sub n
      (paymentEndpointSeq n m)
      (orbitPaymentSourceFiberAt_nonempty_paymentEndpointSeq n m)]
  rw [← canonicalBlockStartTime_eq_universalPaymentBlockStart]
  rfl

/-- Canonical prefix telescope: the sum through block `m` is the width change
from the initial root to the next start after block `m`. -/
theorem sum_endpointAccountingTerm_eq_canonicalBlockNextStart_bitWidth_sub
    (n : OddNat) (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), endpointAccountingTerm n k) =
      (bitWidth (canonicalBlockNextStartState n m) : ℤ) - bitWidth n.1 := by
  simpa [canonicalBlockNextStartState] using
    sum_endpointAccountingTerm_paymentEndpointSeq n m

/-! ## Rootwise versus global boundedness -/

/-- One fixed odd root has a uniform upper bound on all of its endpoint
drifts. -/
def RootwiseEndpointDriftBound (n : OddNat) : Prop :=
  ∃ B : ℤ, ∀ m, endpointAccountingTerm n m ≤ B

/-- One integer bounds endpoint drift simultaneously for every odd root and
every canonical block.  This is strictly a cross-root statement. -/
def GlobalEndpointDriftBound : Prop :=
  ∃ B : ℤ, ∀ (n : OddNat) (m : ℕ), endpointAccountingTerm n m ≤ B

/-- The cp-339 endpoint condition is exactly the rootwise condition. -/
theorem rootwiseEndpointDriftBound_iff_canonicalEndpointUniformUpperBound
    (n : OddNat) :
    RootwiseEndpointDriftBound n ↔
      CanonicalEndpointAccountingTermUniformUpperBound n :=
  Iff.rfl

/-- The fixed-horizon cp-339 frontier theorem concerns one fixed root only. -/
theorem canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_rootwiseEndpoint
    (n : OddNat) (H : ℕ) :
    CanonicalSourceAgeFrontierIncrementUniformUpperBound n H ↔
      RootwiseEndpointDriftBound n := by
  rw [rootwiseEndpointDriftBound_iff_canonicalEndpointUniformUpperBound]
  exact canonicalSourceAgeFrontierIncrementUniformUpperBound_iff_endpoint n H

/-- A global drift ceiling implies every rootwise ceiling.  The converse is
not asserted: choosing a bound separately for each root need not produce one
bound uniform across roots. -/
theorem GlobalEndpointDriftBound.rootwise
    (h : GlobalEndpointDriftBound) (n : OddNat) :
    RootwiseEndpointDriftBound n := by
  rcases h with ⟨B, hB⟩
  exact ⟨B, hB n⟩

/-! ## Exact positive-drift normal forms -/

/-- Exact claim/capacity form with terminal capacity expressed by its 2-adic
valuation.  Positivity is not needed for the identity. -/
theorem endpointAccountingTerm_eq_claimCount_sub_terminalValuation
    (n : OddNat) (m : ℕ) :
    endpointAccountingTerm n m =
      (canonicalBlockClaimCount n m : ℤ) -
        canonicalBlockTerminalValuation n m := by
  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount,
    canonicalBlockCapacityCount_eq_terminalValuation]

/-- Endpoint drift is bounded by block length minus terminal valuation. -/
theorem endpointAccountingTerm_le_length_sub_terminalValuation
    (n : OddNat) (m : ℕ) :
    endpointAccountingTerm n m ≤
      (canonicalBlockLength n m : ℤ) -
        canonicalBlockTerminalValuation n m := by
  simpa [canonicalBlockCapacityCount_eq_terminalValuation] using
    endpointAccountingTerm_le_length_sub_capacity n m

/-- Exact carry-word refinement: the gap between the coarse
`length - valuation` ceiling and actual drift is precisely the number of
missing claim depths. -/
theorem endpointAccountingTerm_add_claimHoles_eq_length_sub_terminalValuation
    (n : OddNat) (m : ℕ) :
    endpointAccountingTerm n m + (canonicalBlockClaimHoles n m).card =
      (canonicalBlockLength n m : ℤ) -
        canonicalBlockTerminalValuation n m := by
  rw [endpointAccountingTerm_eq_length_sub_terminalValuation_sub_claimHoles]
  ring

/-! ## Sufficient rootwise hypotheses

These implications do not claim that any of their hypotheses holds.  They
make explicit which arithmetic estimate would close the rootwise endpoint
boundary.
-/

/-- A uniform canonical block-length ceiling is sufficient for rootwise drift
boundedness. -/
theorem rootwiseEndpointDriftBound_of_blockLength_bound
    {n : OddNat} {B : ℕ}
    (hB : ∀ m, canonicalBlockLength n m ≤ B) :
    RootwiseEndpointDriftBound n := by
  refine ⟨B, ?_⟩
  intro m
  calc
    endpointAccountingTerm n m ≤
        (canonicalBlockLength n m : ℤ) -
          canonicalBlockTerminalValuation n m :=
      endpointAccountingTerm_le_length_sub_terminalValuation n m
    _ ≤ canonicalBlockLength n m := sub_le_self _ (Int.natCast_nonneg _)
    _ ≤ B := Int.ofNat_le.mpr (hB m)

/-- A direct uniform ceiling on `length - terminal valuation` is sufficient
for rootwise endpoint-drift boundedness. -/
theorem rootwiseEndpointDriftBound_of_length_sub_terminalValuation_bound
    {n : OddNat} {B : ℤ}
    (hB : ∀ m,
      (canonicalBlockLength n m : ℤ) -
        canonicalBlockTerminalValuation n m ≤ B) :
    RootwiseEndpointDriftBound n := by
  exact ⟨B, fun m =>
    (endpointAccountingTerm_le_length_sub_terminalValuation n m).trans (hB m)⟩

/-- A uniform additive bound on next-start width above start width is
sufficient for rootwise endpoint-drift boundedness. -/
theorem rootwiseEndpointDriftBound_of_nextStart_bitWidth_le_start_add
    {n : OddNat} {B : ℕ}
    (hB : ∀ m,
      bitWidth (canonicalBlockNextStartState n m) ≤
        bitWidth (canonicalBlockStartState n m) + B) :
    RootwiseEndpointDriftBound n := by
  refine ⟨B, ?_⟩
  intro m
  rw [endpointAccountingTerm_eq_canonicalBlock_bitWidth_sub]
  have hwidth := hB m
  omega

end DkMath.Collatz

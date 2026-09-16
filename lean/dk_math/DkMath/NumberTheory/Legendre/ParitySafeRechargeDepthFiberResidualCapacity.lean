/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberExcess
import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberResidualCapacity"

/-!
## ParitySafeRechargeDepthFiberResidualCapacity

PRIM-L058 charges exact-depth multiplicity to the existing residual-pair
capacity at the same seat.  A reverse recharge key recovers the two residual
primes, and fixed-seat injectivity sends a depth fiber into the unordered
pairs of the erased canonical co-support.

This is a finite local-capacity result.  It does not make depth fibers
singletons, introduce a fifth direction, or provide a descent, analytic
estimate, Legendre-conjecture proof, or RH conclusion.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableDepthFiberResidualCapacity (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L058.1: canonical reverse key -/

/-- A canonical choice of surviving recharge key for an exact dual-base pair.

The default value is irrelevant off the exact universe; all public packets
below require exact-pair membership.
-/
noncomputable def paritySafeRechargeExactKeyOfPair
    (n : ℕ) (bt : ℕ × ℕ) : ℕ × (ℕ × ℕ) :=
  if h : bt ∈ paritySafeRechargeExactDualBasePairs n then
    Classical.choose (paritySafeRechargeExactDualBasePairs_exists_recharge_key h)
  else
    (0, (0, 0))

/-- The chosen key is a surviving recharge key and recovers the pair. -/
theorem paritySafeRechargeExactKeyOfPair_packet
    {n : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDualBasePairs n) :
    paritySafeRechargeExactKeyOfPair n bt ∈
        paritySafeRechargeSurvivingFarProductKeys n ∧
      paritySafeRechargeDualBaseKey n
          (paritySafeRechargeExactKeyOfPair n bt) = bt := by
  classical
  simp only [paritySafeRechargeExactKeyOfPair, dite_eq_left hbt]
  exact Classical.choose_spec
    (paritySafeRechargeExactDualBasePairs_exists_recharge_key hbt)

/-! ### PRIM-L058.2: local residual-pair universe -/

/-- Unordered pairs in the canonical co-support after the anchor prime is
erased at seat `r`.
-/
noncomputable def paritySafeCanonicalResidualPairsAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  upperPairs
    ((squareQuotientAnchorNondivisorSupport n
      (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r))

/-- The local residual-pair card is the expected binomial capacity. -/
theorem paritySafeCanonicalResidualPairsAtSeat_card_eq_choose
    {n r : ℕ}
    (hr : r ∈ paritySafeCoveredCandidates n) :
    (paritySafeCanonicalResidualPairsAtSeat n r).card =
      Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
  unfold paritySafeCanonicalResidualPairsAtSeat
  rw [card_upperPairs_eq_choose]
  rw [paritySafeSupportExcess_seat_eq_quotientCoSupport_card hr]

/-! ### PRIM-L058.3: depth fiber to local residual pair -/

/-- The reverse key retains canonical ownership and its local residual pair. -/
theorem paritySafeRechargeExactKeyOfPair_farResidual_packet
    {n r : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDepthPairsAtSeat n r) :
    let key := paritySafeRechargeExactKeyOfPair n bt;
      key ∈ paritySafeRechargeSurvivingFarProductKeys n ∧
      paritySafeRechargeDualBaseKey n key = bt ∧
      key.1 = paritySafeCanonicalSupportPrime n r ∧
      key.2 ∈ paritySafeCanonicalResidualPairsAtSeat n r ∧
      r ∈ paritySafeCoveredCandidates n := by
  classical
  have hfiber := mem_paritySafeRechargeExactDepthPairsAtSeat.mp hbt
  have hdepth := (mem_paritySafeRechargeExactDepthDualBasePairs.mp hfiber.1).1
  have hkey := paritySafeRechargeExactKeyOfPair_packet hdepth
  have hseat := paritySafeRechargeExactSeat_eq_waveNextSeat_of_recharge_key
    hkey.1 hkey.2
  rcases key : paritySafeRechargeExactKeyOfPair n bt with ⟨p, q, s⟩
  have hkey' : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n := by
    simpa [key] using hkey.1
  have hcoord' : paritySafeRechargeDualBaseKey n (p, (q, s)) = bt := by
    simpa [key] using hkey.2
  have hseat' : paritySafeFarProductWaveNextSeat n (p, (q, s)) = r := by
    calc
      paritySafeFarProductWaveNextSeat n (p, (q, s)) =
          paritySafeRechargeExactSeat n bt.1 bt.2 := by
            symm
            simpa [key] using hseat
      _ = r := hfiber.2
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp
    (mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey').1
  have hrough : paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeFarProductWaveRoughOffsets n (p, (q, s)) := by
    exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
      hsurv.1).mpr ⟨hsurv.2, rfl⟩
  have hcanonical : paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeCanonicalFarProductWaveOffsets n (p, (q, s)) := by
    rw [← paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector hsurv.1]
    exact hrough
  have hinc := paritySafeCanonicalFarProductWaveOffset_mem_farResidual
    hsurv.1 hcanonical
  have hinc0 := (mem_paritySafeCanonicalFarResidualTripleIncidences.mp hinc).1
  rw [hseat'] at hinc0
  have hcovered : r ∈ paritySafeCoveredCandidates n := by
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hinc0).1).1
  have hcond := (Finset.mem_filter.mp hinc0).2
  have hres : (q, s) ∈
      upperPairs ((squareQuotientAnchorNondivisorSupport n
        (paritySafeCanonicalSupportPrime n r) r).erase
          (paritySafeCanonicalSupportPrime n r)) := by
    simp only [upperPairs, Finset.mem_filter, Finset.mem_offDiag]
    refine ⟨?_, hcond.1⟩
    refine ⟨hcond.2.1, hcond.2.2, ?_⟩
    intro hqs
    subst s
    have hlt : q < q := by simpa using hcond.1
    exact (Nat.lt_irrefl q) hlt
  have hp : p = paritySafeCanonicalSupportPrime n r := by
    have hcanon := (mem_paritySafeCanonicalFarProductWaveOffsets.mp hcanonical).2.2
    rw [hseat'] at hcanon
    exact hcanon
  dsimp [key]
  exact ⟨hkey', hcoord', hp,
    by simpa [paritySafeCanonicalResidualPairsAtSeat] using hres, hcovered⟩

/-- Every exact-depth pair at a covered seat yields a local residual pair. -/
theorem paritySafeRechargeExactDepthPair_residualPair_mem
    {n r : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDepthPairsAtSeat n r) :
    (paritySafeRechargeExactKeyOfPair n bt).2 ∈
      paritySafeCanonicalResidualPairsAtSeat n r := by
  exact (paritySafeRechargeExactKeyOfPair_farResidual_packet hbt).2.2.2.1

/-- An occupied exact-depth seat is a covered parity-safe candidate. -/
theorem paritySafeRechargeExactDepthPair_mem_covered
    {n r : ℕ} {bt : ℕ × ℕ}
    (hbt : bt ∈ paritySafeRechargeExactDepthPairsAtSeat n r) :
    r ∈ paritySafeCoveredCandidates n := by
  exact (paritySafeRechargeExactKeyOfPair_farResidual_packet hbt).2.2.2.2

/-! ### PRIM-L058.4: fixed-seat injection and capacity -/

/-- The reverse residual-pair map is injective on every exact-depth fiber. -/
theorem paritySafeRechargeExactDepthPair_residualPair_injectiveOn
    {n r : ℕ} :
    Set.InjOn
      (fun bt => (paritySafeRechargeExactKeyOfPair n bt).2)
      (paritySafeRechargeExactDepthPairsAtSeat n r : Set (ℕ × ℕ)) := by
  intro bt₁ h₁ bt₂ h₂ hpair
  have hpacket₁ := paritySafeRechargeExactKeyOfPair_farResidual_packet h₁
  have hpacket₂ := paritySafeRechargeExactKeyOfPair_farResidual_packet h₂
  have hkey : paritySafeRechargeExactKeyOfPair n bt₁ =
      paritySafeRechargeExactKeyOfPair n bt₂ := by
    apply Prod.ext
    · exact hpacket₁.2.2.1.trans hpacket₂.2.2.1.symm
    · exact hpair
  calc
    bt₁ = paritySafeRechargeDualBaseKey n
        (paritySafeRechargeExactKeyOfPair n bt₁) := hpacket₁.2.1.symm
    _ = paritySafeRechargeDualBaseKey n
        (paritySafeRechargeExactKeyOfPair n bt₂) := by rw [hkey]
    _ = bt₂ := hpacket₂.2.1

/-- The exact-depth fiber fits the local erased-support pair capacity. -/
theorem paritySafeRechargeExactDepthPairsAtSeat_card_le_choose_support
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthSeats n) :
    (paritySafeRechargeExactDepthPairsAtSeat n r).card ≤
      Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 := by
  classical
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats hr with
    ⟨bt, hbt⟩
  have hcovered := paritySafeRechargeExactDepthPair_mem_covered hbt
  rw [← paritySafeCanonicalResidualPairsAtSeat_card_eq_choose hcovered]
  apply Finset.card_le_card_of_injOn
    (fun bt => (paritySafeRechargeExactKeyOfPair n bt).2)
  · intro bt hbt
    exact paritySafeRechargeExactDepthPair_residualPair_mem hbt
  · intro bt₁ h₁ bt₂ h₂ hpair
    exact paritySafeRechargeExactDepthPair_residualPair_injectiveOn h₁ h₂ hpair

/-! ### PRIM-L058.5: collision support richness -/

/-- A collision seat has at least four active support primes. -/
theorem paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    4 ≤ (paritySafeActiveSupport n r).card := by
  have hseat := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
  have hcollision := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).2
  have hcapacity := paritySafeRechargeExactDepthPairsAtSeat_card_le_choose_support hseat
  have hchoose : 2 ≤ Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 :=
    hcollision.trans hcapacity
  rw [Nat.choose_two_right] at hchoose
  by_contra hsmall
  have hcard : (paritySafeActiveSupport n r).card ≤ 3 := by omega
  interval_cases hs : (paritySafeActiveSupport n r).card <;>
    norm_num [hs] at hchoose

/-! ### PRIM-L058.6: residual capacity consumer -/

/-- Residual-pair capacity left after paying one copy at each collision seat. -/
noncomputable def paritySafeRechargeExactDepthResidualPairCapacityExcess
    (n : ℕ) : ℕ :=
  ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
    (Nat.choose ((paritySafeActiveSupport n r).card - 1) 2 - 1)

/-- Exact-depth fiber excess is bounded by the local residual-pair capacity. -/
theorem paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess
    (n : ℕ) :
    paritySafeRechargeExactDepthFiberExcess n ≤
      paritySafeRechargeExactDepthResidualPairCapacityExcess n := by
  rw [paritySafeRechargeExactDepthFiberExcess_eq_collision_sum,
    paritySafeRechargeExactDepthResidualPairCapacityExcess]
  apply Finset.sum_le_sum
  intro r hr
  have hseat := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
  exact Nat.sub_le_sub_right
    (paritySafeRechargeExactDepthPairsAtSeat_card_le_choose_support hseat) 1

/-- Residual mass with exact depth charged to local residual-pair capacity. -/
theorem paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthResidualCapacity_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n ≤
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  have hupper :=
    paritySafeResidualPairMass_le_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth n
  have hexcess :=
    paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess n
  omega

/-- The same residual-capacity replacement in the prime-pair overlap ledger. -/
theorem paritySafePrimePairOverlapCount_le_supportExcess_add_near_add_terminal_add_L018Depth_add_depthResidualCapacity_add_fourth
    (n : ℕ) :
    paritySafePrimePairOverlapCount n ≤
      paritySafeSupportExcess n +
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      squareAnchorCoprimePrimeSquareDepthBudget n +
      paritySafeRechargeExactDepthResidualPairCapacityExcess n +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  have hupper :=
    paritySafePrimePairOverlapCount_le_supportExcess_add_near_add_terminal_add_L018Depth_add_depthFiberExcess_add_fourth n
  have hexcess :=
    paritySafeRechargeExactDepthFiberExcess_le_residualPairCapacityExcess n
  omega

/-! ### PRIM-L058.7: concrete regression -/

/-- The accepted `n = 58`, `r = 101` collision forces support richness. -/
theorem paritySafeRechargeExactDepthFiber_collision_support_58 :
    4 ≤ (paritySafeActiveSupport 58 101).card := by
  apply paritySafeRechargeExactDepthFiberCollision_support_card_ge_four
  have hw := paritySafeRechargeExactDepthFiber_collision_witness_58
  rcases hw with ⟨h15, _h21, hseat15, _hseat21, hcard⟩
  exact mem_paritySafeRechargeExactDepthFiberCollisionSeats.mpr
    ⟨Finset.mem_image.mpr ⟨(15, 21), h15, hseat15⟩, hcard⟩

end
end DkMath.NumberTheory.Legendre

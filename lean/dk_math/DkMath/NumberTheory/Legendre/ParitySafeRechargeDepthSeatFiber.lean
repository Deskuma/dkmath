/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFourthSplit
import DkMath.NumberTheory.Legendre.LocalizedObstruction

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthSeatFiber"

/-!
## ParitySafeRechargeDepthSeatFiber

PRIM-L056 returns each exact selected-depth recharge coordinate to the
existing L018 coprime prime-square seat ledger.  The construction keeps the
pair fiber explicit: different exact pairs may occupy the same seat, and the
cardinality statement is therefore a fiber sum rather than an injectivity
claim.

This is a finite coordinate and ledger result.  It does not bound the exact
depth cardinality by the L018 budget, prove fiber uniqueness, or provide a
descent, analytic estimate, or Legendre/RH conclusion.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableDepthSeat (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L056.1: exact seats and the return packet -/

/-- The shell point offset from the anchor square for an exact pair. -/
def paritySafeRechargeExactSeat (n b t : ℕ) : ℕ :=
  paritySafeRechargeExactShellPoint n b t - n ^ 2

private theorem paritySafeRechargeExactSeat_eq_waveNextSeat
    {n b t : ℕ}
    {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hcoord : paritySafeRechargeDualBaseKey n key = (b, t)) :
    paritySafeRechargeExactSeat n b t =
      paritySafeFarProductWaveNextSeat n key := by
  rcases key with ⟨p, q, s⟩
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n := hsurv.1
  have hfit : ParitySafeFarProductKeyFitsShell n (p, (q, s)) := hsurv.2.1
  have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hgate).mpr
    ⟨hfit, rfl⟩
  have hcoord1 : p * q = b := by
    simpa [paritySafeRechargeDualBaseKey] using congrArg Prod.fst hcoord
  have hcoord2 :
      paritySafeFarProductWaveNextQuotient n (p, (q, s)) = t := by
    simpa [paritySafeRechargeDualBaseKey] using congrArg Prod.snd hcoord
  have hfactor := paritySafeFarProductWaveCofactor_packet hgate hwave
  have hfactor' := hfactor.2.1
  rw [paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient hgate hfit]
    at hfactor'
  rw [hcoord2] at hfactor'
  have hs := paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient
    hkey
  have hscoord :
      paritySafeRechargeOddShellQuotient n (p * q)
          (paritySafeFarProductWaveNextQuotient n (p, (q, s))) =
        paritySafeRechargeOddShellQuotient n b t := by
    rw [hcoord1, hcoord2]
  have hs' : s = paritySafeRechargeOddShellQuotient n b t :=
    hs.trans hscoord
  have hpointcoord :
      p * q * s * t = paritySafeRechargeExactShellPoint n b t := by
    unfold paritySafeRechargeExactShellPoint
    rw [hcoord1, hs']
    ring
  have hpoint : n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) =
      paritySafeRechargeExactShellPoint n b t := by
    calc
      n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) =
          p * q * s * t := hfactor'.symm
      _ = paritySafeRechargeExactShellPoint n b t := hpointcoord
  unfold paritySafeRechargeExactSeat
  apply Nat.sub_eq_iff_eq_add (by omega) |>.mpr
  simpa [Nat.add_comm] using hpoint.symm

/-- The exact seat of a surviving recharge coordinate is its wave next seat.

This public wrapper exposes the return identity needed by the subsequent
fixed-seat residual-pair capacity module while keeping the reconstruction
proof local to the depth-seat layer.
-/
theorem paritySafeRechargeExactSeat_eq_waveNextSeat_of_recharge_key
    {n b t : ℕ}
    {key : ℕ × (ℕ × ℕ)}
    (hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n)
    (hcoord : paritySafeRechargeDualBaseKey n key = (b, t)) :
    paritySafeRechargeExactSeat n b t =
      paritySafeFarProductWaveNextSeat n key :=
  paritySafeRechargeExactSeat_eq_waveNextSeat hkey hcoord

/-- An exact pair returns to an odd coprime L018 seat and its shell point. -/
theorem paritySafeRechargeExactPair_seat_packet
    {n b t : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactDualBasePairs n) :
    let r := paritySafeRechargeExactSeat n b t
    r ∈ squareAnchorOddPointCoprimeOffsets n ∧
      n ^ 2 + r = paritySafeRechargeExactShellPoint n b t := by
  obtain ⟨key, hkey, hcoord⟩ :=
    paritySafeRechargeExactDualBasePairs_exists_recharge_key hbt
  rcases key with ⟨p, q, s⟩
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate : (p, (q, s)) ∈ paritySafeTripleGateFarTriples n := hsurv.1
  have hfit : ParitySafeFarProductKeyFitsShell n (p, (q, s)) := hsurv.2.1
  have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hgate).mpr
    ⟨hfit, rfl⟩
  have hcoord1 : p * q = b := by
    simpa [paritySafeRechargeDualBaseKey] using congrArg Prod.fst hcoord
  have hcoord2 :
      paritySafeFarProductWaveNextQuotient n (p, (q, s)) = t := by
    simpa [paritySafeRechargeDualBaseKey] using congrArg Prod.snd hcoord
  have hcop : Nat.Coprime (2 * n)
      (paritySafeFarProductWaveCofactor n (p, (q, s))
        (paritySafeFarProductWaveNextSeat n (p, (q, s)))) := by
    rw [paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient hgate hfit,
      hcoord2]
    simpa [hcoord2] using hsurv.2.2.1
  have hcand :=
    (paritySafeFarProductWave_mem_candidate_iff_cofactor_coprime hgate hwave).mpr
      hcop
  have hseat := paritySafeRechargeExactSeat_eq_waveNextSeat hkey hcoord
  have hfactor := paritySafeFarProductWaveCofactor_packet hgate hwave
  have hfactor' := hfactor.2.1
  rw [paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient hgate hfit,
    hcoord2] at hfactor'
  have hs := paritySafeRechargeSurvivingFarProductKey_thirdPrime_eq_oddShellQuotient
    hkey
  have hscoord :
      paritySafeRechargeOddShellQuotient n (p * q)
          (paritySafeFarProductWaveNextQuotient n (p, (q, s))) =
        paritySafeRechargeOddShellQuotient n b t := by
    rw [hcoord1, hcoord2]
  have hs' : s = paritySafeRechargeOddShellQuotient n b t := hs.trans hscoord
  have hpointcoord :
      p * q * s * t = paritySafeRechargeExactShellPoint n b t := by
    unfold paritySafeRechargeExactShellPoint
    rw [hcoord1, hs']
    ring
  have hpoint : n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) =
      paritySafeRechargeExactShellPoint n b t := by
    calc
      n ^ 2 + paritySafeFarProductWaveNextSeat n (p, (q, s)) =
          p * q * s * t := hfactor'.symm
      _ = paritySafeRechargeExactShellPoint n b t := hpointcoord
  constructor
  · rw [hseat]
    exact hcand
  · rw [hseat]
    exact hpoint

/-! ### PRIM-L056.2: depth seat image and L018 budget -/

/-- Seats occupied by exact depth coordinates, with pair multiplicity erased. -/
noncomputable def paritySafeRechargeExactDepthSeats (n : ℕ) : Finset ℕ :=
  (paritySafeRechargeExactDepthDualBasePairs n).image
    (fun bt => paritySafeRechargeExactSeat n bt.1 bt.2)

/-- Every exact depth seat is an L018 odd coprime seat. -/
theorem paritySafeRechargeExactDepthSeats_subset_oddPointCoprimeOffsets
    (n : ℕ) :
    paritySafeRechargeExactDepthSeats n ⊆ squareAnchorOddPointCoprimeOffsets n := by
  intro r hr
  rcases Finset.mem_image.mp hr with ⟨bt, hbt, rfl⟩
  exact (paritySafeRechargeExactPair_seat_packet
    (mem_paritySafeRechargeExactDepthDualBasePairs.mp hbt).1).1

/-- A depth pair occupies one of the L018 coprime prime-square fibers. -/
theorem paritySafeRechargeExactDepthPair_primeSquare_seat
    {n b t : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactDepthDualBasePairs n) :
    ∃ d ∈ squareAnchorNondivisorPrimes n,
      paritySafeRechargeExactSeat n b t ∈
        squareAnchorCoprimePrimeSquareOffsets n d := by
  have hpacket := paritySafeRechargeExactPair_seat_packet
    (mem_paritySafeRechargeExactDepthDualBasePairs.mp hbt).1
  have hsquare := paritySafeRechargeExactDepth_selected_square_dvd_shellPoint hbt
  rcases hsquare with ⟨p, q, hwitness, hdiv⟩
  have hcop := (mem_squareAnchorOddPointCoprimeOffsets.mp hpacket.1).1
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hwitness.1).1
  have hpdata := mem_squareAnchorOddActivePrimes.mp hpactive
  have hpworld := mem_squareAnchorNondivisorPrimes.mpr
    ⟨hpdata.1, hpdata.2.1, hpdata.2.2.1⟩
  have hqdata := mem_squareAnchorOddActivePrimes.mp hwitness.2.1
  have hqworld := mem_squareAnchorNondivisorPrimes.mpr
    ⟨hqdata.1, hqdata.2.1, hqdata.2.2.1⟩
  have hexact := mem_paritySafeRechargeExactDualBasePairs.mp
    (mem_paritySafeRechargeExactDepthDualBasePairs.mp hbt).1
  have hadmiss := mem_paritySafeRechargePrimeAdmissibleDualBasePairs.mp hexact.1
  have hsdata := mem_squareAnchorOddActivePrimes.mp hadmiss.2.1
  have hsworld := mem_squareAnchorNondivisorPrimes.mpr
    ⟨hsdata.1, hsdata.2.1, hsdata.2.2.1⟩
  have hpoint : n ^ 2 + paritySafeRechargeExactSeat n b t =
      paritySafeRechargeExactShellPoint n b t := hpacket.2
  rcases hdiv with hpdiv | hqdiv | hsdiv
  · refine ⟨p, hpworld, ?_⟩
    apply mem_squareAnchorCoprimePrimeSquareOffsets.mpr
    exact ⟨hcop, by rw [hpoint]; exact hpdiv⟩
  · refine ⟨q, hqworld, ?_⟩
    apply mem_squareAnchorCoprimePrimeSquareOffsets.mpr
    exact ⟨hcop, by rw [hpoint]; exact hqdiv⟩
  · refine ⟨paritySafeRechargeOddShellQuotient n b t, hsworld, ?_⟩
    apply mem_squareAnchorCoprimePrimeSquareOffsets.mpr
    exact ⟨hcop, by rw [hpoint]; exact hsdiv⟩

/-- Distinct exact depth seats are paid for by the L018 prime-square budget. -/
theorem paritySafeRechargeExactDepthSeats_card_le_primeSquareDepthBudget
    (n : ℕ) :
    (paritySafeRechargeExactDepthSeats n).card ≤
      squareAnchorCoprimePrimeSquareDepthBudget n := by
  let U : Finset ℕ := (squareAnchorNondivisorPrimes n).biUnion
    (fun p => squareAnchorCoprimePrimeSquareOffsets n p)
  have hsub : paritySafeRechargeExactDepthSeats n ⊆ U := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨bt, hbt, rfl⟩
    obtain ⟨d, hd, hseat⟩ := paritySafeRechargeExactDepthPair_primeSquare_seat hbt
    exact Finset.mem_biUnion.mpr ⟨d, hd, hseat⟩
  calc
    (paritySafeRechargeExactDepthSeats n).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ squareAnchorNondivisorPrimes n,
        (squareAnchorCoprimePrimeSquareOffsets n p).card := by
      exact Finset.card_biUnion_le
    _ = squareAnchorCoprimePrimeSquareDepthBudget n := rfl

/-! ### PRIM-L056.3: exact depth fibers -/

/-- Exact depth pairs whose returned seat is `r`. -/
noncomputable def paritySafeRechargeExactDepthPairsAtSeat
    (n r : ℕ) : Finset (ℕ × ℕ) :=
  (paritySafeRechargeExactDepthDualBasePairs n).filter
    (fun bt => paritySafeRechargeExactSeat n bt.1 bt.2 = r)

@[simp] theorem mem_paritySafeRechargeExactDepthPairsAtSeat
    {n r b t : ℕ} :
    (b, t) ∈ paritySafeRechargeExactDepthPairsAtSeat n r ↔
      (b, t) ∈ paritySafeRechargeExactDepthDualBasePairs n ∧
        paritySafeRechargeExactSeat n b t = r := by
  simp [paritySafeRechargeExactDepthPairsAtSeat]

/-- The exact depth pair card is the sum of the occupied-seat fiber cards. -/
theorem paritySafeRechargeExactDepthPairs_card_eq_sum_seat_fibers
    (n : ℕ) :
    (paritySafeRechargeExactDepthDualBasePairs n).card =
      ∑ r ∈ paritySafeRechargeExactDepthSeats n,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
  classical
  let s := paritySafeRechargeExactDepthDualBasePairs n
  let g := fun (bt : ℕ × ℕ) => paritySafeRechargeExactSeat n bt.1 bt.2
  let seats := s.image g
  change s.card = ∑ r ∈ seats,
    (paritySafeRechargeExactDepthPairsAtSeat n r).card
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter s seats g
  calc
    s.card = (s.filter (fun bt => g bt ∈ seats)).card := by
      congr 1
      symm
      apply Finset.filter_eq_self.mpr
      intro bt hbt
      change g bt ∈ s.image g
      exact Finset.mem_image.mpr ⟨bt, hbt, rfl⟩
    _ = ∑ r ∈ seats, (s.filter (fun bt => g bt = r)).card := by
      symm
      exact hfiber
    _ = ∑ r ∈ seats,
        (paritySafeRechargeExactDepthPairsAtSeat n r).card := by
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg Finset.card
      ext bt
      simp [s, g, paritySafeRechargeExactDepthPairsAtSeat]

/-! ### PRIM-L056.4: residual pair ledgers -/

/-- The near/terminal/depth/fourth decomposition of residual pair mass. -/
theorem paritySafeResidualPairMass_eq_near_add_terminal_add_depth_add_fourth
    (n : ℕ) :
    paritySafeResidualPairMass n =
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      (paritySafeRechargeExactDepthDualBasePairs n).card +
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  rw [paritySafeResidualPairMass_eq_near_add_far_card,
    paritySafeCanonicalFarResidual_card_eq_terminal_add_depth_add_fourth]
  simp [Nat.add_assoc]

/-! ### PRIM-L056.5: arithmetic false beam -/

/-- The n=58 depth arithmetic has two distinct triple labels and one seat. -/
theorem paritySafeRechargeDepthSeat_false_beam_arithmetic :
    58 ^ 2 + 101 = 3 ^ 2 * 5 * 7 * 11 ∧
      3 * 5 * 11 * 21 = 3465 ∧
      3 * 7 * 11 * 15 = 3465 ∧
      3 * 5 * 11 * 21 = 58 ^ 2 + 101 ∧
      3 * 7 * 11 * 15 = 58 ^ 2 + 101 ∧
      (3, 5, 11) ∈ ({(3, 5, 11), (3, 7, 11)} : Finset (ℕ × ℕ × ℕ)) := by
  norm_num

end
end DkMath.NumberTheory.Legendre

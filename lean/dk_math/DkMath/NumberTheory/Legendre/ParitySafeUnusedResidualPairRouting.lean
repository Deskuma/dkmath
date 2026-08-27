/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeCollisionResidualPairSlackIncidence

#print "file: DkMath.NumberTheory.Legendre.ParitySafeUnusedResidualPairRouting"

/-!
## ParitySafeUnusedResidualPairRouting

PRIM-L072 routes the residual pairs left unused by a colliding exact-depth
fiber back into the existing near/far residual ledger.  The construction is
finite: it introduces no new prime direction and makes no claim about
injectivity, descent, asymptotics, Legendre symbols, or RH.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

private theorem erased_quotientCoSupport_subset_activeSupport_l072
    {n r : ℕ} (hr : r ∈ paritySafeCoveredCandidates n) :
    (squareQuotientAnchorNondivisorSupport n
      (paritySafeCanonicalSupportPrime n r) r).erase
        (paritySafeCanonicalSupportPrime n r) ⊆
      paritySafeActiveSupport n r := by
  intro q hq
  have hp := (paritySafeCanonicalSupportPrime_packet hr).2.2.1
  have hqoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport hp
    (Finset.erase_subset _ _ hq)
  rw [squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
    (mem_paritySafeCoveredCandidates.mp hr).1] at hqoff
  exact hqoff

/-! ### PRIM-L072.1: unused pairs are canonical residual incidences -/

/- The local unused pair is tagged by its collision seat in the global ledger. -/
theorem paritySafeDepthCollisionUnusedResidualPair_mem_canonicalResidualTriple
    {n r q s : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n)
    (hqs : (q, s) ∈ paritySafeDepthCollisionUnusedResidualPairsAtSeat n r) :
    (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n := by
  classical
  have hcovered := paritySafeDepthFiberCollisionSeat_mem_covered hr
  have hres : (q, s) ∈ paritySafeCanonicalResidualPairsAtSeat n r :=
    (Finset.mem_sdiff.mp hqs).1
  have hres' := hres
  simp only [paritySafeCanonicalResidualPairsAtSeat, upperPairs,
    Finset.mem_filter, Finset.mem_offDiag] at hres'
  have hqactive : q ∈ squareAnchorOddActivePrimes n := by
    exact (Finset.mem_filter.mp
      (erased_quotientCoSupport_subset_activeSupport_l072 hcovered hres'.1.1)).1
  have hsactive : s ∈ squareAnchorOddActivePrimes n := by
    exact (Finset.mem_filter.mp
      (erased_quotientCoSupport_subset_activeSupport_l072 hcovered hres'.1.2.1)).1
  have hpair : (q, s) ∈
      ((squareAnchorOddActivePrimes n).product
        (squareAnchorOddActivePrimes n)).filter
        (fun pair =>
          pair.1 < pair.2 ∧
          pair.1 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r) ∧
          pair.2 ∈
            (squareQuotientAnchorNondivisorSupport n
              (paritySafeCanonicalSupportPrime n r) r).erase
                (paritySafeCanonicalSupportPrime n r)) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hqactive, hsactive⟩,
      ⟨hres'.2, hres'.1.1, hres'.1.2.1⟩⟩
  have hrprod : r ∈ paritySafeCoveredCandidates n := hcovered
  exact Finset.mem_filter.mpr ⟨
    Finset.mem_product.mpr ⟨hrprod, Finset.mem_product.mpr
      ⟨hqactive, hsactive⟩⟩,
    (Finset.mem_filter.mp hpair).2⟩

/-! ### PRIM-L072.2: global unused incidence and its exact mass -/

/-- Unused local residual pairs, tagged by their collision seat. -/
noncomputable def paritySafeDepthCollisionUnusedResidualTripleIncidences
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeRechargeExactDepthFiberCollisionSeats n).biUnion (fun r =>
    (paritySafeDepthCollisionUnusedResidualPairsAtSeat n r).image
      (fun qs => (r, qs)))

@[simp] theorem mem_paritySafeDepthCollisionUnusedResidualTripleIncidences
    {n r q s : ℕ} :
    (r, (q, s)) ∈ paritySafeDepthCollisionUnusedResidualTripleIncidences n ↔
      r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n ∧
        (q, s) ∈ paritySafeDepthCollisionUnusedResidualPairsAtSeat n r := by
  classical
  simp [paritySafeDepthCollisionUnusedResidualTripleIncidences]

theorem paritySafeDepthCollisionUnusedResidualTripleIncidences_card_eq_mass
    (n : ℕ) :
    (paritySafeDepthCollisionUnusedResidualTripleIncidences n).card =
      paritySafeDepthCollisionUnusedResidualPairMass n := by
  classical
  let C := paritySafeRechargeExactDepthFiberCollisionSeats n
  let U := fun r => paritySafeDepthCollisionUnusedResidualPairsAtSeat n r
  have hdis : (C : Set ℕ).PairwiseDisjoint (fun r => (U r).image (fun qs => (r, qs))) := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨qs, hqs, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨qt, hqt, hEq⟩
    have : s = r := by simpa using congrArg Prod.fst hEq
    exact hrs this.symm
  change (C.biUnion (fun r => (U r).image (fun qs => (r, qs)))).card = _
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro r hr
  have himg : ((U r).image (fun qs => (r, qs))).card = (U r).card := by
    apply Finset.card_image_of_injOn
    intro qs hqs qt hqt hEq
    exact congrArg Prod.snd hEq
  rw [himg]

/-! ### PRIM-L072.3: near/far routing split -/

/-- Unused incidences routed through the existing near residual ledger. -/
noncomputable def paritySafeDepthCollisionUnusedNearResidualTriples
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeDepthCollisionUnusedResidualTripleIncidences n).filter
    (fun triple => triple ∈ paritySafeCanonicalNearResidualTripleIncidences n)

/-- Unused incidences routed through the existing far residual ledger. -/
noncomputable def paritySafeDepthCollisionUnusedFarResidualTriples
    (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeDepthCollisionUnusedResidualTripleIncidences n).filter
    (fun triple => triple ∈ paritySafeCanonicalFarResidualTripleIncidences n)

@[simp] theorem mem_paritySafeDepthCollisionUnusedNearResidualTriples
    {n : ℕ} {triple : ℕ × (ℕ × ℕ)} :
    triple ∈ paritySafeDepthCollisionUnusedNearResidualTriples n ↔
      triple ∈ paritySafeDepthCollisionUnusedResidualTripleIncidences n ∧
        triple ∈ paritySafeCanonicalNearResidualTripleIncidences n := by
  simp [paritySafeDepthCollisionUnusedNearResidualTriples]

@[simp] theorem mem_paritySafeDepthCollisionUnusedFarResidualTriples
    {n : ℕ} {triple : ℕ × (ℕ × ℕ)} :
    triple ∈ paritySafeDepthCollisionUnusedFarResidualTriples n ↔
      triple ∈ paritySafeDepthCollisionUnusedResidualTripleIncidences n ∧
        triple ∈ paritySafeCanonicalFarResidualTripleIncidences n := by
  simp [paritySafeDepthCollisionUnusedFarResidualTriples]

theorem paritySafeDepthCollisionUnusedNearFarResidual_disjoint (n : ℕ) :
    Disjoint (paritySafeDepthCollisionUnusedNearResidualTriples n)
      (paritySafeDepthCollisionUnusedFarResidualTriples n) := by
  rw [Finset.disjoint_left]
  intro triple hnear hfar
  exact Finset.disjoint_left.mp (paritySafeCanonicalNearFarResidual_disjoint n)
    (mem_paritySafeDepthCollisionUnusedNearResidualTriples.mp hnear).2
    (mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp hfar).2

theorem paritySafeDepthCollisionUnusedNearFarResidual_union (n : ℕ) :
    paritySafeDepthCollisionUnusedNearResidualTriples n ∪
        paritySafeDepthCollisionUnusedFarResidualTriples n =
      paritySafeDepthCollisionUnusedResidualTripleIncidences n := by
  ext triple
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hnear | hfar
    · exact (mem_paritySafeDepthCollisionUnusedNearResidualTriples.mp hnear).1
    · exact (mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp hfar).1
  · intro hu
    have hcanon := paritySafeDepthCollisionUnusedResidualPair_mem_canonicalResidualTriple
      (n := n) (r := triple.1) (q := triple.2.1) (s := triple.2.2)
      (mem_paritySafeDepthCollisionUnusedResidualTripleIncidences.mp hu).1
      (mem_paritySafeDepthCollisionUnusedResidualTripleIncidences.mp hu).2
    have hnf := (paritySafeCanonicalNearFarResidual_union n) ▸ hcanon
    rcases Finset.mem_union.mp hnf with hnear | hfar
    · exact Finset.mem_union.mpr (Or.inl
        (mem_paritySafeDepthCollisionUnusedNearResidualTriples.mpr ⟨hu, hnear⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_paritySafeDepthCollisionUnusedFarResidualTriples.mpr ⟨hu, hfar⟩))

theorem paritySafeDepthCollisionUnusedResidualTriples_card_eq_near_add_far
    (n : ℕ) :
    (paritySafeDepthCollisionUnusedResidualTripleIncidences n).card =
      (paritySafeDepthCollisionUnusedNearResidualTriples n).card +
      (paritySafeDepthCollisionUnusedFarResidualTriples n).card := by
  rw [← paritySafeDepthCollisionUnusedNearFarResidual_union n]
  exact Finset.card_union_of_disjoint
    (paritySafeDepthCollisionUnusedNearFarResidual_disjoint n)

theorem paritySafeDepthCollisionUnusedNearResidualTriples_subset_canonicalNear
    (n : ℕ) :
    paritySafeDepthCollisionUnusedNearResidualTriples n ⊆
      paritySafeCanonicalNearResidualTripleIncidences n := by
  intro triple h
  exact (mem_paritySafeDepthCollisionUnusedNearResidualTriples.mp h).2

theorem paritySafeDepthCollisionUnusedNearResidualTriples_card_le_near
    (n : ℕ) :
    (paritySafeDepthCollisionUnusedNearResidualTriples n).card ≤
      (paritySafeCanonicalNearResidualTripleIncidences n).card :=
  Finset.card_le_card (paritySafeDepthCollisionUnusedNearResidualTriples_subset_canonicalNear n)

/-! ### PRIM-L072.4: far unused incidences are recharge keys -/

private theorem paritySafeDepthCollisionUnusedFarResidual_nextSeat_eq_seat
    {n r q s : ℕ}
    (htriple : (r, (q, s)) ∈
      paritySafeDepthCollisionUnusedFarResidualTriples n) :
    paritySafeFarProductWaveNextSeat n
        (paritySafeCanonicalSupportPrime n r, (q, s)) = r := by
  have hu := mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp htriple
  have hfar := mem_paritySafeCanonicalFarResidualTripleIncidences.mp hu.2
  have hrough : r ∈ paritySafeFarProductWaveRoughOffsets n
      (paritySafeCanonicalSupportPrime n r, (q, s)) := by
    rw [paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector hfar.2]
    exact paritySafeCanonicalFarResidual_mem_productWaveSelector hu.2
  exact ((mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
    hfar.2).mp hrough).2.symm

/-- A far unused incidence has the surviving key selected by the far wave. -/
theorem paritySafeDepthCollisionUnusedFarResidual_key_mem_recharge
    {n r q s : ℕ}
    (htriple : (r, (q, s)) ∈
      paritySafeDepthCollisionUnusedFarResidualTriples n) :
    (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeRechargeSurvivingFarProductKeys n := by
  classical
  have hu := mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp htriple
  have hlocal := mem_paritySafeDepthCollisionUnusedResidualTripleIncidences.mp hu.1
  have hcollision := hlocal.1
  have hfar := mem_paritySafeCanonicalFarResidualTripleIncidences.mp hu.2
  let key := (paritySafeCanonicalSupportPrime n r, (q, s))
  have hrough : r ∈ paritySafeFarProductWaveRoughOffsets n key := by
    rw [paritySafeFarProductWaveRoughOffsets_eq_canonicalSelector
      hfar.2]
    exact paritySafeCanonicalFarResidual_mem_productWaveSelector hu.2
  have hsurv :=
    (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
      hfar.2).mp hrough
  have hsurvKey : key ∈ paritySafeSurvivingFarProductKeys n :=
    mem_paritySafeSurvivingFarProductKeys.mpr ⟨hfar.2, hsurv.1⟩
  have hquot_ne : paritySafeFarProductWaveNextQuotient n key ≠ 1 := by
    intro hquot
    have hterminal : key ∈ paritySafeTerminalSurvivingFarProductKeys n := by
      apply mem_paritySafeTerminalSurvivingFarProductKeys.mpr
      exact ⟨hsurvKey, hquot⟩
    have hterminalSeat : r ∈ paritySafeTerminalFarProductSeats n := by
      apply mem_paritySafeTerminalFarProductSeats.mpr
      exact ⟨key, hterminal, hsurv.2.symm⟩
    exact Finset.disjoint_left.mp
      (paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats n)
      hterminalSeat hcollision
  have hquot_pos : 0 < paritySafeFarProductWaveNextQuotient n key := by
    simp [paritySafeFarProductWaveNextQuotient]
  have hquot_gt : 1 < paritySafeFarProductWaveNextQuotient n key := by
    omega
  exact mem_paritySafeRechargeSurvivingFarProductKeys.mpr ⟨hsurvKey, hquot_gt⟩

/-! ### PRIM-L072.5: the far route lands in the exact-fourth branch -/

/-- The dual-base coordinate of a far unused incidence is exact-fourth. -/
theorem paritySafeDepthCollisionUnusedFarResidual_dualBase_mem_exactFourth
    {n r q s : ℕ}
    (htriple : (r, (q, s)) ∈
      paritySafeDepthCollisionUnusedFarResidualTriples n) :
    paritySafeRechargeDualBaseKey n
        (paritySafeCanonicalSupportPrime n r, (q, s)) ∈
      paritySafeRechargeExactFourthDirectionPairs n := by
  classical
  let key := (paritySafeCanonicalSupportPrime n r, (q, s))
  have hkey : key ∈ paritySafeRechargeSurvivingFarProductKeys n :=
    paritySafeDepthCollisionUnusedFarResidual_key_mem_recharge htriple
  have hbase : paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargeExactDualBasePairs n :=
    paritySafeRechargeDualBaseKey_mem_exact hkey
  have hnotdepth : ¬ paritySafeRechargeDualBaseKey n key ∈
      paritySafeRechargeExactDepthDualBasePairs n := by
    intro hdepth
    have hseat := paritySafeRechargeExactSeat_eq_waveNextSeat_of_recharge_key
      hkey rfl
    have hnext := paritySafeDepthCollisionUnusedFarResidual_nextSeat_eq_seat htriple
    have hseat' : paritySafeRechargeExactSeat n
        (paritySafeRechargeDualBaseKey n key).1
        (paritySafeRechargeDualBaseKey n key).2 = r := by
      exact hseat.trans hnext
    have hfiber : paritySafeRechargeDualBaseKey n key ∈
        paritySafeRechargeExactDepthPairsAtSeat n r := by
      apply mem_paritySafeRechargeExactDepthPairsAtSeat.mpr
      exact ⟨hdepth, hseat'⟩
    have hres := paritySafeRechargeExactDepthPair_residualPair_mem hfiber
    have hunused := (mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp htriple).1
    have hlocal := mem_paritySafeDepthCollisionUnusedResidualTripleIncidences.mp hunused
    have hnotimage := (Finset.mem_sdiff.mp hlocal.2).2
    have hpacket := paritySafeRechargeExactKeyOfPair_packet
      (mem_paritySafeRechargeExactDepthDualBasePairs.mp hdepth).1
    have hchosen : paritySafeRechargeExactKeyOfPair n
        (paritySafeRechargeDualBaseKey n key) = key := by
      apply paritySafeRechargeDualBaseKey_injectiveOn n hpacket.1 hkey
      exact hpacket.2
    have himage : (q, s) ∈
        paritySafeRechargeExactDepthResidualPairImageAtSeat n r := by
      apply Finset.mem_image.mpr
      refine ⟨paritySafeRechargeDualBaseKey n key, hfiber, ?_⟩
      rw [hchosen]
    exact hnotimage himage
  change paritySafeRechargeDualBaseKey n key ∈
    paritySafeRechargeExactFourthDirectionPairs n
  exact mem_paritySafeRechargeExactFourthDirectionPairs.mpr ⟨hbase, by
    intro hdepth
    exact hnotdepth (mem_paritySafeRechargeExactDepthDualBasePairs.mpr
      ⟨hbase, hdepth⟩)⟩

/-! ### PRIM-L072.6: far-to-fourth map and cardinality -/

/-- The unused far incidence is sent to its exact fourth dual-base pair. -/
noncomputable def paritySafeDepthCollisionUnusedFarToFourth
    (n : ℕ) (triple : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  paritySafeRechargeDualBaseKey n
    (paritySafeCanonicalSupportPrime n triple.1, triple.2)

theorem paritySafeDepthCollisionUnusedFarToFourth_injectiveOn
    (n : ℕ) :
    Set.InjOn (paritySafeDepthCollisionUnusedFarToFourth n)
      (paritySafeDepthCollisionUnusedFarResidualTriples n :
      Set (ℕ × (ℕ × ℕ))) := by
  intro a ha b hb heq
  rcases a with ⟨ar, aq, ass⟩
  rcases b with ⟨br, bq, bss⟩
  have ha' := mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp ha
  have hb' := mem_paritySafeDepthCollisionUnusedFarResidualTriples.mp hb
  have hka := paritySafeDepthCollisionUnusedFarResidual_key_mem_recharge ha
  have hkb := paritySafeDepthCollisionUnusedFarResidual_key_mem_recharge hb
  have hkey :
      (paritySafeCanonicalSupportPrime n ar, (aq, ass)) =
        (paritySafeCanonicalSupportPrime n br, (bq, bss)) := by
    apply paritySafeRechargeDualBaseKey_injectiveOn n hka hkb
    exact heq
  have hseat : ar = br := by
    calc
      ar = paritySafeFarProductWaveNextSeat n
          (paritySafeCanonicalSupportPrime n ar, (aq, ass)) :=
        (paritySafeDepthCollisionUnusedFarResidual_nextSeat_eq_seat
          (show (ar, (aq, ass)) ∈ paritySafeDepthCollisionUnusedFarResidualTriples n
            from ha)).symm
      _ = paritySafeFarProductWaveNextSeat n
          (paritySafeCanonicalSupportPrime n br, (bq, bss)) := by rw [hkey]
      _ = br := paritySafeDepthCollisionUnusedFarResidual_nextSeat_eq_seat
        (show (br, (bq, bss)) ∈ paritySafeDepthCollisionUnusedFarResidualTriples n
          from hb)
  have hpair : (aq, ass) = (bq, bss) := by
    exact congrArg Prod.snd hkey
  exact Prod.ext hseat hpair

theorem paritySafeDepthCollisionUnusedFarResidualTriples_card_le_exactFourth
    (n : ℕ) :
    (paritySafeDepthCollisionUnusedFarResidualTriples n).card ≤
      (paritySafeRechargeExactFourthDirectionPairs n).card := by
  apply Finset.card_le_card_of_injOn
    (paritySafeDepthCollisionUnusedFarToFourth n)
  · intro triple htriple
    exact paritySafeDepthCollisionUnusedFarResidual_dualBase_mem_exactFourth htriple
  · exact paritySafeDepthCollisionUnusedFarToFourth_injectiveOn n

/-! ### PRIM-L072.7--8: low-cost reabsorption -/

theorem paritySafeDepthCollisionUnusedResidualPairMass_le_near_add_fourth
    (n : ℕ) :
    paritySafeDepthCollisionUnusedResidualPairMass n ≤
      (paritySafeCanonicalNearResidualTripleIncidences n).card +
        (paritySafeRechargeExactFourthDirectionPairs n).card := by
  have hmass := paritySafeDepthCollisionUnusedResidualTripleIncidences_card_eq_mass n
  have hsplit := paritySafeDepthCollisionUnusedResidualTriples_card_eq_near_add_far n
  have hnear := paritySafeDepthCollisionUnusedNearResidualTriples_card_le_near n
  have hfar := paritySafeDepthCollisionUnusedFarResidualTriples_card_le_exactFourth n
  omega

theorem paritySafeDepthCollisionUnusedResidualPairMass_le_lowCostResidualMass
    (n : ℕ) :
    paritySafeDepthCollisionUnusedResidualPairMass n ≤
      paritySafeLowCostResidualMass n := by
  have hmass := paritySafeDepthCollisionUnusedResidualPairMass_le_near_add_fourth n
  unfold paritySafeLowCostResidualMass
  omega

/-- The LowCost remainder after removing the routed unused-pair mass. -/
noncomputable def paritySafeLowCostResidualMassAfterUnused
    (n : ℕ) : ℕ :=
  paritySafeLowCostResidualMass n -
    paritySafeDepthCollisionUnusedResidualPairMass n

theorem paritySafeLowCostResidualMass_eq_unused_add_afterUnused
    (n : ℕ) :
    paritySafeLowCostResidualMass n =
      paritySafeDepthCollisionUnusedResidualPairMass n +
        paritySafeLowCostResidualMassAfterUnused n := by
  have hle := paritySafeDepthCollisionUnusedResidualPairMass_le_lowCostResidualMass n
  unfold paritySafeLowCostResidualMassAfterUnused
  omega

/-! ### PRIM-L072.9: second cancellation frontier -/

/-- Full-cover frontier after absorbing unused residual-pair mass into LowCost. -/
theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_threeTotient_le_fullCoverLowCostAfterUnused
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualMassAfterUnused n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_twoUnusedResidualPairMass_add_threeTotient_le_fullCoverActualMass
      hn hfull
  have hsplit := paritySafeLowCostResidualMass_eq_unused_add_afterUnused n
  omega

theorem two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_threeTotient_le_reducedQuotient_fullCoverLowCostAfterUnused
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePairOverlapOutsideDepthCollision n +
      9 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      3 * (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualMassAfterUnused n := by
  have hfront :=
    two_mul_outsideCollisionPairOverlap_add_nineCollision_add_threeFiveDirection_add_threeTotient_le_fullCoverLowCostAfterUnused
      hn hfull
  have hinc := paritySafeIncidenceCount_eq_reducedQuotientInterval_sum n
  omega

end DkMath.NumberTheory.Legendre

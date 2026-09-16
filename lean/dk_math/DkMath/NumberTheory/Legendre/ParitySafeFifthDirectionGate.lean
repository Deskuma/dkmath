/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeDepthResidualFifthTrigger

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFifthDirectionGate"

/-!
## ParitySafeFifthDirectionGate

PRIM-L067 refines the L066 support-cardinality trigger into an actual fifth
active prime direction.  A five-direction collision seat supplies four
already separated directions from the L059 packet and a fifth direction from
the remaining active support.  The canonical first prime therefore enters a
strict fifth-power square-body gate.

The module also charges one additional unit of support cost for each such
collision seat and propagates that single charge to the full-cover frontier.
It does not construct a fifth-direction wave capacity, an injective packet
count, a descent, or a Legendre/RH conclusion.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
open scoped BigOperators

noncomputable section
local instance classicalDecidableFifthDirectionGate (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-! ### PRIM-L067.1: actual fifth support direction -/

/-- A five-direction collision seat contains five distinct ordered active
prime directions, including the canonical first prime. -/
theorem paritySafeRechargeDepthFiveDirectionCollision_fiveDirection_packet
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
    let p := paritySafeCanonicalSupportPrime n r
    ∃ q s u v,
      p ∈ paritySafeActiveSupport n r ∧
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r ∧
      u ∈ paritySafeActiveSupport n r ∧
      v ∈ paritySafeActiveSupport n r ∧
      p < q ∧ p < s ∧ p < u ∧ p < v ∧
      q ≠ s ∧ q ≠ u ∧ q ≠ v ∧
      s ≠ u ∧ s ≠ v ∧ u ≠ v ∧
      p * q * s * u * v ∣ n ^ 2 + r := by
  classical
  dsimp
  rcases paritySafeRechargeDepthFiberCollision_fourDirection_packet
      (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).1 with
    ⟨q, s, u, hq, hs, hu, hpq, hps, hpu, hqs, hqu, hsu, hdiv⟩
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats
      (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp
        (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).1).1 with
    ⟨bt, hbt⟩
  have hcovered := paritySafeRechargeExactDepthPair_mem_covered hbt
  have hcovered' := mem_paritySafeCoveredCandidates.mp hcovered
  have hcanon := paritySafeCanonicalSupportPrime_packet hcovered
  let S := paritySafeActiveSupport n r
  let T := insert (paritySafeCanonicalSupportPrime n r)
      (insert q (insert s ({u} : Finset ℕ)))
  have hnot : ¬ S ⊆ T := by
    intro hsub
    have hcardle := Finset.card_le_card hsub
    have hsmall : T.card ≤ 4 := by
      dsimp [T]
      calc
        (insert (paritySafeCanonicalSupportPrime n r)
            (insert q (insert s ({u} : Finset ℕ)))).card ≤
            (insert q (insert s ({u} : Finset ℕ))).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ (insert s ({u} : Finset ℕ)).card + 1 + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
        _ ≤ ({u} : Finset ℕ).card + 1 + 1 + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
        _ ≤ 4 := by simp
    have hlarge : 5 ≤ S.card := by
      exact (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).2
    omega
  obtain ⟨v, hv⟩ := Finset.sdiff_nonempty.mpr hnot
  have hvactive : v ∈ paritySafeActiveSupport n r := by
    exact (Finset.mem_sdiff.mp hv).1
  have hvnot : v ∉ T := (Finset.mem_sdiff.mp hv).2
  have hvp : v ≠ paritySafeCanonicalSupportPrime n r := by
    intro heq
    apply hvnot
    simp [T, heq]
  have hvq : v ≠ q := by
    intro heq
    apply hvnot
    simp [T, heq]
  have hvs : v ≠ s := by
    intro heq
    apply hvnot
    simp [T, heq]
  have hvu : v ≠ u := by
    intro heq
    apply hvnot
    simp [T, heq]
  have hnonempty := hcovered'.2
  have hpmin : paritySafeCanonicalSupportPrime n r =
      (paritySafeActiveSupport n r).min' hnonempty := by
    dsimp [paritySafeCanonicalSupportPrime]
    rw [dite_eq_left hnonempty]
  have hpv : paritySafeCanonicalSupportPrime n r < v := by
    apply lt_of_le_of_ne
    · rw [hpmin]
      exact Finset.min'_le _ _ hvactive
    · exact hvp.symm
  have hpactive := hcanon.2.2.2
  have hqprime : q ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hq
    exact (Finset.mem_filter.mp hq).1
  have hsprime : s ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hs
    exact (Finset.mem_filter.mp hs).1
  have huprime : u ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hu
    exact (Finset.mem_filter.mp hu).1
  have hvprime : v ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hvactive
    exact (Finset.mem_filter.mp hvactive).1
  have hvdiv : v ∣ n ^ 2 + r :=
    (mem_paritySafeActiveSupport_iff_dvd.mp hvactive).2
  have hcop : Nat.Coprime
      (paritySafeCanonicalSupportPrime n r * q * s * u) v := by
    have hpp := (mem_squareAnchorOddActivePrimes.mp hpactive).1
    have hqp := (mem_squareAnchorOddActivePrimes.mp hqprime).1
    have hsp := (mem_squareAnchorOddActivePrimes.mp hsprime).1
    have hup := (mem_squareAnchorOddActivePrimes.mp huprime).1
    have hvp' := (mem_squareAnchorOddActivePrimes.mp hvprime).1
    have h₁ := (Nat.coprime_primes hpp hvp').2 hvp.symm
    have h₂ := (Nat.coprime_primes hqp hvp').2 hvq.symm
    have h₃ := (Nat.coprime_primes hsp hvp').2 hvs.symm
    have h₄ := (Nat.coprime_primes hup hvp').2 hvu.symm
    exact (((h₁.mul_left h₂).mul_left h₃).mul_left h₄)
  have hfiveDiv := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdiv hvdiv
  exact ⟨q, s, u, v, hcanon.2.1, hq, hs, hu, hvactive,
    hpq, hps, hpu, hpv, hqs, hqu, hvq.symm, hsu, hvs.symm, hvu.symm,
    hfiveDiv⟩

/-! ### PRIM-L067.2: fifth-power gate -/

/-- Active primes whose fifth powers fit strictly inside the square body. -/
noncomputable def paritySafeFiveDirectionGatePrimes
    (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun p => p ^ 5 < squareBody n)

@[simp] theorem mem_paritySafeFiveDirectionGatePrimes
    {n p : ℕ} :
    p ∈ paritySafeFiveDirectionGatePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧ p ^ 5 < squareBody n := by
  simp [paritySafeFiveDirectionGatePrimes]

/-- The fifth-power gate refines the previously established fourth-power
gate. -/
theorem paritySafeFiveDirectionGatePrimes_subset_fourDirectionGatePrimes
    (n : ℕ) :
    paritySafeFiveDirectionGatePrimes n ⊆
      paritySafeFourDirectionGatePrimes n := by
  intro p hp
  have hp' := mem_paritySafeFiveDirectionGatePrimes.mp hp
  apply mem_paritySafeFourDirectionGatePrimes.mpr
  refine ⟨hp'.1, ?_⟩
  have hpos := (mem_squareAnchorOddActivePrimes.mp hp'.1).1.pos
  have htwo := (mem_squareAnchorOddActivePrimes.mp hp'.1).1.two_le
  have hfour : p ^ 4 < p ^ 5 := by
    calc
      p ^ 4 = p ^ 4 * 1 := by simp
      _ < p ^ 4 * p := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.pow_pos hpos)
      _ = p ^ 5 := by ring
  exact hfour.trans hp'.2

/-! ### PRIM-L067.3: collision canonical prime enters the fifth gate -/

/-- The canonical prime of a five-direction collision has a fifth power below
the square body. -/
theorem paritySafeRechargeDepthFiveDirectionCollision_canonicalPrime_mem_fiveDirectionGate
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
    paritySafeCanonicalSupportPrime n r ∈
      paritySafeFiveDirectionGatePrimes n := by
  classical
  rcases paritySafeRechargeDepthFiveDirectionCollision_fiveDirection_packet hr with
    ⟨q, s, u, v, hp, hq, hs, hu, hv, hpq, hps, hpu, hpv, hqs, hqu, hvq,
      hsu, hvs, hvu, hdiv⟩
  have hpair := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp
    (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).1).1
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats hpair with
    ⟨bt, hbt⟩
  have hcovered := paritySafeRechargeExactDepthPair_mem_covered hbt
  have hpactive := (paritySafeCanonicalSupportPrime_packet hcovered).2.2.2
  have hoff := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    (mem_paritySafeCoveredCandidates.mp hcovered).1
  have hpointpos : 0 < n ^ 2 + r := by
    dsimp [SquareOffset] at hoff
    omega
  have hprodle : paritySafeCanonicalSupportPrime n r * q * s * u * v ≤
      n ^ 2 + r := Nat.le_of_dvd hpointpos hdiv
  have hppos := (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
  have hqpos := (mem_squareAnchorOddActivePrimes.mp
    ((mem_paritySafeActiveSupport_iff_dvd.mp hq).1)).1.pos
  have hspos := (mem_squareAnchorOddActivePrimes.mp
    ((mem_paritySafeActiveSupport_iff_dvd.mp hs).1)).1.pos
  have hupos := (mem_squareAnchorOddActivePrimes.mp
    ((mem_paritySafeActiveSupport_iff_dvd.mp hu).1)).1.pos
  have hvpos := (mem_squareAnchorOddActivePrimes.mp
    ((mem_paritySafeActiveSupport_iff_dvd.mp hv).1)).1.pos
  have hpqsmall : paritySafeCanonicalSupportPrime n r ^ 3 <
      paritySafeCanonicalSupportPrime n r * q * s := by
    calc
      paritySafeCanonicalSupportPrime n r ^ 3 =
          paritySafeCanonicalSupportPrime n r *
            paritySafeCanonicalSupportPrime n r *
              paritySafeCanonicalSupportPrime n r := by ring
      _ < paritySafeCanonicalSupportPrime n r * q *
          paritySafeCanonicalSupportPrime n r := by
        exact Nat.mul_lt_mul_of_pos_right
          (Nat.mul_lt_mul_of_pos_left hpq hppos) hppos
      _ < paritySafeCanonicalSupportPrime n r * q * s := by
        exact Nat.mul_lt_mul_of_pos_left hps (Nat.mul_pos hppos hqpos)
  have hpfour : paritySafeCanonicalSupportPrime n r ^ 4 <
      paritySafeCanonicalSupportPrime n r * q * s * u := by
    calc
      paritySafeCanonicalSupportPrime n r ^ 4 =
          (paritySafeCanonicalSupportPrime n r ^ 3) *
            paritySafeCanonicalSupportPrime n r := by ring
      _ < (paritySafeCanonicalSupportPrime n r * q * s) *
          paritySafeCanonicalSupportPrime n r :=
        Nat.mul_lt_mul_of_pos_right hpqsmall hppos
      _ < (paritySafeCanonicalSupportPrime n r * q * s) * u :=
        Nat.mul_lt_mul_of_pos_left hpu
          (Nat.mul_pos (Nat.mul_pos hppos hqpos) hspos)
  have hpfive : paritySafeCanonicalSupportPrime n r ^ 5 <
      paritySafeCanonicalSupportPrime n r * q * s * u * v := by
    calc
      paritySafeCanonicalSupportPrime n r ^ 5 =
          (paritySafeCanonicalSupportPrime n r ^ 4) *
            paritySafeCanonicalSupportPrime n r := by ring
      _ < (paritySafeCanonicalSupportPrime n r * q * s * u) *
          paritySafeCanonicalSupportPrime n r :=
        Nat.mul_lt_mul_of_pos_right hpfour hppos
      _ < (paritySafeCanonicalSupportPrime n r * q * s * u) * v :=
        Nat.mul_lt_mul_of_pos_left hpv
          (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hppos hqpos) hspos) hupos)
  apply mem_paritySafeFiveDirectionGatePrimes.mpr
  exact ⟨hpactive, hpfive.trans_le (hprodle.trans
    (squarePoint_le_squareBody_of_squareOffset
      (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
        (mem_paritySafeCoveredCandidates.mp hcovered).1)))⟩

/-! ### PRIM-L067.4: global trigger -/

/-- Positive higher-support residual is equivalent to the existence of a
five-direction collision seat. -/
theorem paritySafeRechargeExactDepthHigherSupportResidualExcess_pos_iff_fiveDirectionCollision_nonempty
    (n : ℕ) :
    0 < paritySafeRechargeExactDepthHigherSupportResidualExcess n ↔
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).Nonempty := by
  have hzero :=
    paritySafeRechargeExactDepthHigherSupportResidualExcess_eq_zero_iff_no_fiveDirectionCollision n
  constructor
  · intro hpos
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact (Nat.ne_of_gt hpos) (hzero.mpr hempty)
  · intro hnonempty
    have hne := Finset.nonempty_iff_ne_empty.mp hnonempty
    have hzero' : paritySafeRechargeExactDepthHigherSupportResidualExcess n ≠ 0 := by
      intro hz
      exact hne (hzero.mp hz)
    omega

/-- A positive higher-support residual produces an actual canonical prime in
the fifth-power gate. -/
theorem exists_fiveDirectionGatePrime_of_higherSupportResidualExcess_pos
    {n : ℕ}
    (hpos : 0 < paritySafeRechargeExactDepthHigherSupportResidualExcess n) :
    ∃ r,
      r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n ∧
      paritySafeCanonicalSupportPrime n r ∈
        paritySafeFiveDirectionGatePrimes n := by
  rcases (paritySafeRechargeExactDepthHigherSupportResidualExcess_pos_iff_fiveDirectionCollision_nonempty n).mp
    hpos with ⟨r, hr⟩
  exact ⟨r, hr,
    paritySafeRechargeDepthFiveDirectionCollision_canonicalPrime_mem_fiveDirectionGate hr⟩

/-! ### PRIM-L067.5: one extra support-cost unit -/

/-- A five-direction collision seat has at least four units of local support
cost. -/
theorem paritySafeFiveDirectionCollision_localSupportCost_ge_four
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) :
    4 ≤ (paritySafeActiveSupport n r).card - 1 := by
  have hcard := (mem_paritySafeRechargeExactDepthFiveDirectionCollisionSeats.mp hr).2
  omega

/-! ### PRIM-L067.6: strengthened support ledger -/

/-- The collision support charge is three per collision plus one per genuine
five-direction seat, with each local support cost charged only once. -/
theorem three_mul_collision_add_fiveDirection_card_le_localSupportCost
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          ((paritySafeActiveSupport n r).card - 1) := by
  have hF := paritySafeRechargeExactDepthFiveDirectionCollisionSeats_subset_collision n
  have hindicator :
      (∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        if r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n then 1 else 0) =
        (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card := by
    calc
      (∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          if r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n then 1 else 0) =
          ∑ r ∈ (paritySafeRechargeExactDepthFiberCollisionSeats n).filter
            (fun r => r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n), 1 := by
        rw [Finset.sum_filter]
      _ = (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card := by
        have hfilter :
            (paritySafeRechargeExactDepthFiberCollisionSeats n).filter
              (fun r => r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n) =
              paritySafeRechargeExactDepthFiveDirectionCollisionSeats n := by
          ext r
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨_, hrf⟩
            exact hrf
          · intro hrf
            exact ⟨hF hrf, hrf⟩
        rw [hfilter]
        simp
  have hterm : ∀ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
      3 + (if r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n then 1 else 0) ≤
        (paritySafeActiveSupport n r).card - 1 := by
    intro r hr
    by_cases hf : r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n
    · have hfour := paritySafeFiveDirectionCollision_localSupportCost_ge_four hf
      simp [hf]
      omega
    · have hthree :=
        paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
      simp [hf]
      omega
  calc
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card =
        (∑ _r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n, 3) +
          ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
            if r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n then 1 else 0 := by
      rw [hindicator]
      simp [Nat.mul_comm]
    _ = ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          (3 + (if r ∈ paritySafeRechargeExactDepthFiveDirectionCollisionSeats n then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
          ((paritySafeActiveSupport n r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr

/-! ### PRIM-L067.7: terminal/collision charge and full-cover frontier -/

/-- The terminal and strengthened collision support charges fit in one
disjoint candidate-side support-excess sum. -/
theorem two_mul_terminalKeys_add_three_mul_collision_add_fiveDirection_le_supportExcess
    (n : ℕ) :
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
      3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card ≤
        paritySafeSupportExcess n := by
  have hdisjoint :=
    paritySafeTerminalFarProductSeats_disjoint_depthFiberCollisionSeats n
  have hsubset := paritySafeTerminalCollisionSeats_union_subset_candidate n
  have hcollision := three_mul_collision_add_fiveDirection_card_le_localSupportCost n
  have hunion_le :
      (∑ r ∈ paritySafeTerminalFarProductSeats n ∪
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1)) ≤
        ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          ((paritySafeActiveSupport n r).card - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro r _ _
    exact Nat.zero_le _
  calc
    2 * (paritySafeTerminalSurvivingFarProductKeys n).card +
        3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card =
        2 * (paritySafeTerminalFarProductSeats n).card +
          3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
          (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card := by
      rw [paritySafeTerminalFarProductSeats_card_eq_terminalKeys]
    _ = (∑ r ∈ paritySafeTerminalFarProductSeats n,
          ((paritySafeActiveSupport n r).card - 1)) +
          (3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
            (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card) := by
      rw [paritySafeTerminalFarProductSeats_supportCost_sum_eq]
      omega
    _ ≤ (∑ r ∈ paritySafeTerminalFarProductSeats n,
          ((paritySafeActiveSupport n r).card - 1)) +
          ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
            ((paritySafeActiveSupport n r).card - 1) := by
      exact Nat.add_le_add_left hcollision _
    _ = ∑ r ∈ paritySafeTerminalFarProductSeats n ∪
          paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
      rw [Finset.sum_union hdisjoint]
    _ ≤ ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
          ((paritySafeActiveSupport n r).card - 1) := hunion_le
    _ = paritySafeSupportExcess n := by
      rfl

/-- Full-cover frontier with one additional unit on the left for each
five-direction collision seat. -/
theorem two_mul_pairOverlap_add_fiveDirection_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * paritySafeIncidenceCount n +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  have hover := paritySafePrimePairOverlapCount_eq_supportExcess_add_residual n
  have hres :=
    paritySafeResidualPairMass_le_lowCostCapacity_add_terminal_add_depthResidualCapacity n
  have hcharge := two_mul_terminalKeys_add_three_mul_collision_add_fiveDirection_le_supportExcess n
  have hbalance := paritySafeCandidate_card_add_supportExcess_eq_incidence_of_fullyCovered hn hfull
  have hcard := card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul hn
  have hdecomp := paritySafeRechargeExactDepthResidualPairCapacityExcess_eq_twoCollision_add_higherSupport n
  omega

/-! ### PRIM-L067.8: reduced quotient consumer -/

/-- Reduced quotient-interval form of the L067 sharpened frontier. -/
theorem two_mul_pairOverlap_add_fiveDirection_add_threeTotient_le_reducedQuotient_fullCoverCapacity_add_collision_add_twoHigherSupportResidual
    {n : ℕ}
    (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    2 * paritySafePrimePairOverlapCount n +
      (paritySafeRechargeExactDepthFiveDirectionCollisionSeats n).card +
      3 * Nat.totient (2 * n) ≤
        3 * (∑ q ∈ squareAnchorOddActivePrimes n,
          (paritySafeReducedQuotientInterval n q).card) +
        2 * paritySafeLowCostResidualCapacity n +
        (paritySafeRechargeExactDepthFiberCollisionSeats n).card +
        2 * paritySafeRechargeExactDepthHigherSupportResidualExcess n := by
  have hfront :=
    two_mul_pairOverlap_add_fiveDirection_add_threeTotient_le_fullCoverCapacity_add_collision_add_twoHigherSupportResidual hn hfull
  rw [paritySafeIncidenceCount_eq_reducedQuotientInterval_sum] at hfront
  exact hfront

end
end DkMath.NumberTheory.Legendre

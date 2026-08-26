/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeRechargeDepthFiberResidualCapacity

#print "file: DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate"

/-!
## ParitySafeFourDirectionGate

PRIM-L059 combines the L058 four-support collision fact with the L055
canonical fourth-direction packet.  Both branches enter the same strict
first-prime gate `p ^ 4 < squareBody n`.

This is a finite four-direction frontier only.  It does not create a generic
four-hypergraph, provide an injective global count, introduce a fifth
direction, or prove Legendre's conjecture or RH.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidableFourDirectionGate (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L059.1: support-cost cleanup -/

/-- Collision-seat count charged to support excess.

This charges only one cost of three per collision seat.  It is deliberately
not a bound on the full depth-fiber excess, whose multiplicity is handled by
the L058 residual-pair capacity.
-/
theorem three_mul_depthFiberCollisionSeats_card_le_supportExcess
    (n : ℕ) :
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card ≤
      paritySafeSupportExcess n := by
  classical
  have hsub : paritySafeRechargeExactDepthFiberCollisionSeats n ⊆
      squareAnchorOddPointCoprimeOffsets n := by
    intro r hr
    have hseat := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
    rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats hseat with
      ⟨bt, hbt⟩
    exact (mem_paritySafeCoveredCandidates.mp
      (paritySafeRechargeExactDepthPair_mem_covered hbt)).1
  have hterm : ∀ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
      3 ≤ (paritySafeActiveSupport n r).card - 1 := by
    intro r hr
    have hfour := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
    omega
  unfold paritySafeSupportExcess
  calc
    3 * (paritySafeRechargeExactDepthFiberCollisionSeats n).card =
        ∑ _r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n, 3 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n,
        ((paritySafeActiveSupport n r).card - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      exact hterm r hr
    _ ≤ ∑ r ∈ squareAnchorOddPointCoprimeOffsets n,
        ((paritySafeActiveSupport n r).card - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro r _ _
      exact Nat.zero_le _

/-! ### PRIM-L059.2: fourth-power gate -/

/-- Active primes whose fourth powers fit strictly inside the square body. -/
noncomputable def paritySafeFourDirectionGatePrimes
    (n : ℕ) : Finset ℕ :=
  (squareAnchorOddActivePrimes n).filter
    (fun p => p ^ 4 < squareBody n)

@[simp] theorem mem_paritySafeFourDirectionGatePrimes
    {n p : ℕ} :
    p ∈ paritySafeFourDirectionGatePrimes n ↔
      p ∈ squareAnchorOddActivePrimes n ∧
        p ^ 4 < squareBody n := by
  simp [paritySafeFourDirectionGatePrimes]

/-- The fourth-power gate is a genuine refinement of the cubic gate. -/
theorem paritySafeFourDirectionGatePrimes_subset_tripleGatePrimes
    (n : ℕ) :
    paritySafeFourDirectionGatePrimes n ⊆
      paritySafeTripleGatePrimes n := by
  intro p hp
  have hp' := mem_paritySafeFourDirectionGatePrimes.mp hp
  apply mem_paritySafeTripleGatePrimes.mpr
  refine ⟨hp'.1, ?_⟩
  have hpos : 0 < p := (mem_squareAnchorOddActivePrimes.mp hp'.1).1.pos
  have htwo : 2 ≤ p := (mem_squareAnchorOddActivePrimes.mp hp'.1).1.two_le
  have hcube : p ^ 3 < p ^ 4 := by
    calc
      p ^ 3 = p ^ 3 * 1 := by simp
      _ < p ^ 3 * p := Nat.mul_lt_mul_of_pos_left (by omega)
        (Nat.pow_pos hpos)
      _ = p ^ 4 := by ring
  exact hcube.trans hp'.2

theorem paritySafeFourDirectionGatePrimes_card_le_tripleGatePrimes
    (n : ℕ) :
    (paritySafeFourDirectionGatePrimes n).card ≤
      (paritySafeTripleGatePrimes n).card :=
  Finset.card_le_card (paritySafeFourDirectionGatePrimes_subset_tripleGatePrimes n)

/-! ### PRIM-L059.3: local depth four-direction packet -/

private theorem paritySafeRechargeDepthFiberCollision_residual_incidence
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    ∃ p q s,
      p = paritySafeCanonicalSupportPrime n r ∧
      (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n := by
  have hseat := (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats hseat with
    ⟨bt, hbt⟩
  have hpacket := paritySafeRechargeExactKeyOfPair_farResidual_packet hbt
  rcases key : paritySafeRechargeExactKeyOfPair n bt with ⟨p, q, s⟩
  have hpacket' :
      (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n ∧
        paritySafeRechargeDualBaseKey n (p, (q, s)) = bt ∧
        p = paritySafeCanonicalSupportPrime n r ∧
        (q, s) ∈ paritySafeCanonicalResidualPairsAtSeat n r ∧
        r ∈ paritySafeCoveredCandidates n := by
    simpa [key] using hpacket
  rcases hpacket' with ⟨_, _, hp, hres, hcovered⟩
  have hres' := hres
  simp only [paritySafeCanonicalResidualPairsAtSeat, upperPairs,
    Finset.mem_filter, Finset.mem_offDiag] at hres'
  have hqerase := hres'.1.1
  have hserase := hres'.1.2.1
  have hlt : q < s := hres'.2
  have hactive := squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
    (mem_paritySafeCoveredCandidates.mp hcovered).1
  have hpcan := paritySafeCanonicalSupportPrime_packet hcovered
  have hqactive := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    hpcan.2.2.1 (Finset.erase_subset _ _ hqerase)
  have hsactive := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
    hpcan.2.2.1 (Finset.erase_subset _ _ hserase)
  rw [hactive] at hqactive hsactive
  have hqprime := (Finset.mem_filter.mp hqactive).1
  have hsprime := (Finset.mem_filter.mp hsactive).1
  have hinc : (r, (q, s)) ∈ paritySafeCanonicalResidualTripleIncidences n := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨hcovered, Finset.mem_product.mpr ⟨hqprime, hsprime⟩⟩,
      hlt, hqerase, hserase⟩
  exact ⟨p, q, s, hp, hinc⟩

theorem paritySafeRechargeDepthFiberCollision_fourDirection_packet
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    let p := paritySafeCanonicalSupportPrime n r
    ∃ q s u,
      q ∈ paritySafeActiveSupport n r ∧
      s ∈ paritySafeActiveSupport n r ∧
      u ∈ paritySafeActiveSupport n r ∧
      p < q ∧ p < s ∧ p < u ∧
      q ≠ s ∧ q ≠ u ∧ s ≠ u ∧
      p * q * s * u ∣ n ^ 2 + r := by
  classical
  obtain ⟨p, q, s, hp, hinc⟩ :=
    paritySafeRechargeDepthFiberCollision_residual_incidence hr
  subst p
  have hshell := paritySafeCanonicalResidualTripleIncidence_shell_packet hinc
  rcases hshell with ⟨hpq, hps, hqs, hdiv, _, hbody, _, _⟩
  have hpacket := paritySafeCanonicalResidualTripleIncidence_packet hinc
  rcases hpacket with ⟨_, _, _, _, hpqne, hpsne, hqsne, _, _⟩
  have hcard := paritySafeRechargeExactDepthFiberCollision_support_card_ge_four hr
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats
      (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1 with
    ⟨bt, hbt⟩
  have hcovered := paritySafeRechargeExactDepthPair_mem_covered hbt
  have hnonempty := (mem_paritySafeCoveredCandidates.mp hcovered).2
  have hsupport := squareOffsetAnchorNondivisorSupport_eq_paritySafeActiveSupport_of_candidate
    (mem_paritySafeCoveredCandidates.mp hcovered).1
  have hcanon := paritySafeCanonicalSupportPrime_packet hcovered
  have hinc' := Finset.mem_filter.mp hinc
  have hqerase := hinc'.2.2.1
  have hserase := hinc'.2.2.2
  have hqmem : q ∈ paritySafeActiveSupport n r := by
    have hqoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
      hcanon.2.2.1 (Finset.erase_subset _ _ hqerase)
    rw [hsupport] at hqoff
    exact hqoff
  have hsmem : s ∈ paritySafeActiveSupport n r := by
    have hsoff := squareQuotientAnchorNondivisorSupport_subset_offsetSupport
      hcanon.2.2.1 (Finset.erase_subset _ _ hserase)
    rw [hsupport] at hsoff
    exact hsoff
  have hpmem : paritySafeCanonicalSupportPrime n r ∈ paritySafeActiveSupport n r :=
    hcanon.2.1
  have hq' : q ∈ (paritySafeActiveSupport n r).erase
      (paritySafeCanonicalSupportPrime n r) :=
    Finset.mem_erase.mpr ⟨hpqne.symm, hqmem⟩
  have hs' : s ∈ ((paritySafeActiveSupport n r).erase
      (paritySafeCanonicalSupportPrime n r)).erase q :=
    Finset.mem_erase.mpr ⟨hqsne.symm, Finset.mem_erase.mpr ⟨hpsne.symm, hsmem⟩⟩
  let S := (((paritySafeActiveSupport n r).erase
      (paritySafeCanonicalSupportPrime n r)).erase q).erase s
  have hpos : 0 < S.card := by
    have hcardS : S.card = (paritySafeActiveSupport n r).card - 3 := by
      dsimp [S]
      rw [Finset.card_erase_of_mem hs',
        Finset.card_erase_of_mem hq', Finset.card_erase_of_mem hpmem]
      omega
    rw [hcardS]
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  change u ∈ (((paritySafeActiveSupport n r).erase
      (paritySafeCanonicalSupportPrime n r)).erase q).erase s at hu
  rcases Finset.mem_erase.mp hu with ⟨hsu, huq⟩
  rcases Finset.mem_erase.mp huq with ⟨hqu, hup⟩
  rcases Finset.mem_erase.mp hup with ⟨hpu, huactive⟩
  have hpmin : paritySafeCanonicalSupportPrime n r =
      (paritySafeActiveSupport n r).min' hnonempty := by
    dsimp [paritySafeCanonicalSupportPrime]
    rw [dif_pos hnonempty]
  have hple : paritySafeCanonicalSupportPrime n r ≤ u := by
    rw [hpmin]
    exact Finset.min'_le _ _ huactive
  have hpu_lt : paritySafeCanonicalSupportPrime n r < u :=
    lt_of_le_of_ne hple hpu.symm
  have hqprime : q ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hqmem
    exact (Finset.mem_filter.mp hqmem).1
  have hsprime : s ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hsmem
    exact (Finset.mem_filter.mp hsmem).1
  have huprime : u ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at huactive
    exact (Finset.mem_filter.mp huactive).1
  have hpcop : Nat.Coprime
      (paritySafeCanonicalSupportPrime n r * q * s) u := by
    have hpp : Nat.Prime (paritySafeCanonicalSupportPrime n r) :=
      (mem_squareAnchorOddActivePrimes.mp hcanon.2.2.2).1
    have hqp := (mem_squareAnchorOddActivePrimes.mp hqprime).1
    have hsp := (mem_squareAnchorOddActivePrimes.mp hsprime).1
    have hup := (mem_squareAnchorOddActivePrimes.mp huprime).1
    have hpu' := (Nat.coprime_primes hpp hup).2 hpu.symm
    have hqu' := (Nat.coprime_primes hqp hup).2 hqu.symm
    have hsu' := (Nat.coprime_primes hsp hup).2 hsu.symm
    exact (hpu'.mul_left hqu').mul_left hsu'
  have hudiv : u ∣ n ^ 2 + r := by
    exact (Finset.mem_filter.mp huactive).2
  have hquad := Nat.Coprime.mul_dvd_of_dvd_of_dvd hpcop hdiv hudiv
  exact ⟨q, s, u, hqmem, hsmem, huactive, hpq, hps, hpu_lt,
    hqsne, hqu.symm, hsu.symm, hquad⟩

/-! ### PRIM-L059.4: depth collision gate consumer -/

/-- The canonical prime of a depth collision passes the fourth-power gate. -/
theorem paritySafeRechargeDepthFiberCollision_canonicalPrime_mem_fourDirectionGate
    {n r : ℕ}
    (hr : r ∈ paritySafeRechargeExactDepthFiberCollisionSeats n) :
    paritySafeCanonicalSupportPrime n r ∈
      paritySafeFourDirectionGatePrimes n := by
  classical
  rcases paritySafeRechargeDepthFiberCollision_fourDirection_packet hr with
    ⟨q, s, u, hq, hs, hu, hpq, hps, hpu, hqs, hqu, hsu, hquad⟩
  rcases paritySafeRechargeExactDepthPairsAtSeat_nonempty_of_mem_depthSeats
      (mem_paritySafeRechargeExactDepthFiberCollisionSeats.mp hr).1 with
    ⟨bt, hbt⟩
  have hcovered := paritySafeRechargeExactDepthPair_mem_covered hbt
  have hpactive := (paritySafeCanonicalSupportPrime_packet hcovered).2.2.2
  have hoff := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
    (mem_paritySafeCoveredCandidates.mp hcovered).1
  have hpointpos : 0 < n ^ 2 + r := by
    dsimp [SquareOffset] at hoff
    omega
  have hprodle : paritySafeCanonicalSupportPrime n r * q * s * u ≤
      n ^ 2 + r := Nat.le_of_dvd hpointpos hquad
  have hppos : 0 < paritySafeCanonicalSupportPrime n r :=
    (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
  have hqprime : q ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hq
    exact (Finset.mem_filter.mp hq).1
  have hsprime : s ∈ squareAnchorOddActivePrimes n := by
    rw [paritySafeActiveSupport] at hs
    exact (Finset.mem_filter.mp hs).1
  have hqpos : 0 < q := (mem_squareAnchorOddActivePrimes.mp hqprime).1.pos
  have hspos : 0 < s := (mem_squareAnchorOddActivePrimes.mp hsprime).1.pos
  have hpqsmall :
      paritySafeCanonicalSupportPrime n r ^ 3 <
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
        exact Nat.mul_lt_mul_of_pos_left hps
          (Nat.mul_pos hppos hqpos)
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
  apply mem_paritySafeFourDirectionGatePrimes.mpr
  exact ⟨hpactive, hpfour.trans_le (hprodle.trans
    (squarePoint_le_squareBody_of_squareOffset
      (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets
        (mem_paritySafeCoveredCandidates.mp hcovered).1)))⟩

/-! ### PRIM-L059.5: exact fourth gate consumer -/

/-- The first prime of an exact fourth-direction witness passes the same gate. -/
theorem paritySafeRechargeExactFourth_firstPrime_mem_fourDirectionGate
    {n b t p q : ℕ}
    (hbt : (b, t) ∈ paritySafeRechargeExactFourthDirectionPairs n)
    (hwitness : ParitySafeRechargeExactPairWitness n b t p q) :
    p ∈ paritySafeFourDirectionGatePrimes n := by
  classical
  have hfourth := paritySafeRechargeExactFourthPrime_packet hbt hwitness
  dsimp at hfourth
  rcases hfourth with ⟨huprime, hut, huactive, hpu, huq, hus, hquad⟩
  rcases hwitness with ⟨hpw, hqw, hpq, hprod, hqs, hrough⟩
  let s := paritySafeRechargeOddShellQuotient n b t
  let u := paritySafeRechargeExactFourthPrime t
  have hps : p < s := lt_trans hpq hqs
  have hpair := (mem_paritySafeRechargeExactFourthDirectionPairs.mp hbt).1
  rcases paritySafeRechargeExactPair_seat_packet hpair with ⟨hr, hpoint⟩
  have hshellle : paritySafeRechargeExactShellPoint n b t ≤ squareBody n := by
    rw [← hpoint]
    exact squarePoint_le_squareBody_of_squareOffset
      (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr)
  have hoff := squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr
  have hshellpos : 0 < paritySafeRechargeExactShellPoint n b t := by
    rw [← hpoint]
    dsimp [SquareOffset] at hoff
    omega
  have hprodle : p * q * s * u ≤ paritySafeRechargeExactShellPoint n b t :=
    Nat.le_of_dvd hshellpos (by simpa [s, u] using hquad)
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hpw).1
  have hppos := (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
  have hqpos := (mem_squareAnchorOddActivePrimes.mp hqw).1.pos
  have hspos : 0 < s := by omega
  have hpqsmall : p ^ 3 < p * q * s := by
    calc
      p ^ 3 = p * p * p := by ring
      _ < p * q * p := Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left hpq hppos) hppos
      _ < p * q * s := Nat.mul_lt_mul_of_pos_left hps
        (Nat.mul_pos hppos hqpos)
  have hpfour : p ^ 4 < p * q * s * u := by
    calc
      p ^ 4 = (p ^ 3) * p := by ring
      _ < (p * q * s) * p := Nat.mul_lt_mul_of_pos_right hpqsmall hppos
      _ < (p * q * s) * u := Nat.mul_lt_mul_of_pos_left hpu
        (Nat.mul_pos (Nat.mul_pos hppos hqpos) hspos)
  apply mem_paritySafeFourDirectionGatePrimes.mpr
  exact ⟨hpactive, hpfour.trans_le (hprodle.trans hshellle)⟩

/-! ### PRIM-L059.6: arithmetic regressions -/

/-- The fourth-power gate is strictly smaller than the cubic gate at `n = 16`. -/
theorem paritySafeFourDirectionGate_strict_refinement_witness :
    5 ∈ paritySafeTripleGatePrimes 16 ∧
      5 ∉ paritySafeFourDirectionGatePrimes 16 := by
  have hw := paritySafeTripleProductGate_witness_16_17
  constructor
  · apply mem_paritySafeTripleGatePrimes.mpr
    refine ⟨?_, by norm_num [squareBody]⟩
    apply mem_squareAnchorOddActivePrimes.mpr
    norm_num
  · intro h
    have hfour := (mem_paritySafeFourDirectionGatePrimes.mp h).2
    norm_num [squareBody] at hfour

/-- The accepted `n = 58`, `r = 101` collision reaches the four-power gate. -/
theorem paritySafeRechargeDepthFiberCollision_fourDirection_gate_58 :
    paritySafeCanonicalSupportPrime 58 101 ∈
      paritySafeFourDirectionGatePrimes 58 := by
  have hw := paritySafeRechargeExactDepthFiber_collision_witness_58
  rcases hw with ⟨h15, _h21, hseat15, _hseat21, hcard⟩
  apply paritySafeRechargeDepthFiberCollision_canonicalPrime_mem_fourDirectionGate
  exact mem_paritySafeRechargeExactDepthFiberCollisionSeats.mpr
    ⟨Finset.mem_image.mpr ⟨(15, 21), h15, hseat15⟩, hcard⟩

end
end DkMath.NumberTheory.Legendre

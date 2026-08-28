/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeFarProductKeyRecharge

#print "file: DkMath.NumberTheory.Legendre.ParitySafeRechargePairProduct"

/-!
## ParitySafeRechargePairProduct

PRIM-L051 returns the product of the first ordered prime pair of a surviving
recharge key to the same finite cofactor base.  The key-level inequality is
obtained from the shell bound and the L050 rough-cofactor lower bound.  The
module then records the corresponding pair-product fibers and their exact
finite cardinality decomposition.

The return is deliberately same-anchor bookkeeping.  It does not make a
recharge key injective, introduce a smaller anchor or descent, or prove a
global contradiction or Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open DkMath.NumberTheory.Legendre.Internal
noncomputable section
local instance classicalDecidablePairProduct (p : Prop) : Decidable p :=
  Classical.propDecidable p
open scoped BigOperators

/-! ### PRIM-L051.1: first-pair product and scale return -/

/-- The product of the first two ordered active primes of a recharge key. -/
def paritySafeRechargeFirstPairProduct
    (key : ℕ × (ℕ × ℕ)) : ℕ :=
  key.1 * key.2.1

private theorem paritySafeRechargeSurvivingFarProductKey_firstPrime_le_nextQuotient
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p ≤ paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := hsurv.1
  have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hgate).mpr
    ⟨hsurv.2.1, rfl⟩
  have hrough : paritySafeFarProductWaveNextSeat n (p, (q, s)) ∈
      paritySafeFarProductWaveRoughOffsets n (p, (q, s)) := by
    exact (mem_paritySafeFarProductWaveRoughOffsets_iff_survives_and_eq_nextSeat
      hgate).mpr ⟨hsurv.2, rfl⟩
  have hcofactor := paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient
    hgate hsurv.2.1
  have htgt' : 1 < paritySafeFarProductWaveCofactor n (p, (q, s))
      (paritySafeFarProductWaveNextSeat n (p, (q, s))) := by
    rw [hcofactor]
    exact hrecharge.2
  have hfloor := paritySafeFarProductWaveRough_nontrivial_cofactor_ge_key
    hgate hrough htgt'
  rw [hcofactor] at hfloor
  exact hfloor

/-!
The product proof uses `p ≤ t₀` from the rough selector and `q < s` from
the ordered far gate.  Thus `(p*q)^2` lies strictly below the shell product.
-/

/-- The first prime-pair product of a recharge key is at most the anchor. -/
theorem paritySafeRechargeSurvivingFarProductKey_firstPairProduct_le_anchor
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p * q ≤ n := by
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hqprime := (mem_squareAnchorOddActivePrimes.mp hq).1
  have hsprime := (mem_squareAnchorOddActivePrimes.mp hs).1
  have hppos := (mem_squareAnchorOddActivePrimes.mp hpactive).1.pos
  have hqpos := hqprime.pos
  have hspq : p * q < s *
      paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
    have hq_lt : q < s := hqs
    have hp_le :=
      paritySafeRechargeSurvivingFarProductKey_firstPrime_le_nextQuotient hkey
    have hmul : p * q <
        paritySafeFarProductWaveNextQuotient n (p, (q, s)) * s := by
      have hfirst : p * q ≤
          paritySafeFarProductWaveNextQuotient n (p, (q, s)) * q :=
        Nat.mul_le_mul_right q hp_le
      have hsecond : paritySafeFarProductWaveNextQuotient n (p, (q, s)) * q <
          paritySafeFarProductWaveNextQuotient n (p, (q, s)) * s := by
        exact Nat.mul_lt_mul_left (Nat.zero_lt_succ _) |>.mpr hq_lt
      calc
        p * q ≤ paritySafeFarProductWaveNextQuotient n (p, (q, s)) * q := hfirst
        _ < paritySafeFarProductWaveNextQuotient n (p, (q, s)) * s := hsecond
    simpa [Nat.mul_comm] using hmul
  have hpair_sq_lt : (p * q) ^ 2 <
      (p * q * s) * paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
    calc
      (p * q) ^ 2 = (p * q) * (p * q) := by ring
      _ < (p * q) * (s *
          paritySafeFarProductWaveNextQuotient n (p, (q, s))) := by
        exact Nat.mul_lt_mul_left (Nat.mul_pos hppos hqpos) |>.mpr hspq
      _ = (p * q * s) * paritySafeFarProductWaveNextQuotient n (p, (q, s)) := by
        ring
  have hupper :
      (p * q * s) * paritySafeFarProductWaveNextQuotient n (p, (q, s)) ≤
        n ^ 2 + 2 * n := by
    have hfit := hsurv.2.1
    unfold ParitySafeFarProductKeyFitsShell at hfit
    simpa [paritySafeTripleProductModulus] using hfit
  have hpair_succ : (p * q) ^ 2 < (n + 1) ^ 2 := by
    nlinarith
  by_contra hnot
  have hnp : n < p * q := Nat.lt_of_not_ge hnot
  have hnplus : n + 1 ≤ p * q := by omega
  have hsq := Nat.mul_self_le_mul_self hnplus
  nlinarith

/-! ### PRIM-L051.2: reduced-base return -/

/-- The first pair-product is a reduced residue modulo `2*n`. -/
theorem paritySafeRechargeSurvivingFarProductKey_firstPairProduct_coprime_two_mul
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    Nat.Coprime (2 * n) (p * q) := by
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  rcases hgate with ⟨hp, hq, hs, hpq, hqs⟩
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hp).1
  have hqactive := hq
  have hpcop := (activePrime_reducedResidue_packet hpactive).2.2.2.2
  have hqcop := (activePrime_reducedResidue_packet hqactive).2.2.2.2
  exact hpcop.mul_right hqcop

/-- The first pair-product returns to the finite same-anchor cofactor base. -/
theorem paritySafeRechargeSurvivingFarProductKey_firstPairProduct_mem_farCofactorBase
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    p * q ∈ paritySafeFarCofactorBaseOffsets n := by
  apply mem_paritySafeFarCofactorBaseOffsets.mpr
  refine ⟨?_,
    paritySafeRechargeSurvivingFarProductKey_firstPairProduct_le_anchor hkey,
    paritySafeRechargeSurvivingFarProductKey_firstPairProduct_coprime_two_mul hkey⟩
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := mem_paritySafeTripleGateTriples.mp
    (Finset.mem_filter.mp hsurv.1).1
  have hpactive := (mem_paritySafeTripleGatePrimes.mp hgate.1).1
  have hpprime := (mem_squareAnchorOddActivePrimes.mp hpactive).1
  exact Nat.succ_le_of_lt (Nat.mul_pos hpprime.pos
    ((mem_squareAnchorOddActivePrimes.mp hgate.2.1).1.pos))

/-- The surviving recharge quotient also lies in the same finite base. -/
theorem paritySafeRechargeSurvivingFarProductKey_nextQuotient_mem_farCofactorBase
    {n p q s : ℕ}
    (hkey : (p, (q, s)) ∈ paritySafeRechargeSurvivingFarProductKeys n) :
    paritySafeFarProductWaveNextQuotient n (p, (q, s)) ∈
      paritySafeFarCofactorBaseOffsets n := by
  apply mem_paritySafeFarCofactorBaseOffsets.mpr
  have hrecharge := mem_paritySafeRechargeSurvivingFarProductKeys.mp hkey
  have hsurv := mem_paritySafeSurvivingFarProductKeys.mp hrecharge.1
  have hgate := hsurv.1
  have hwave := (mem_squareWaveOffsets_farKey_iff_eq_nextSeat hgate).mpr
    ⟨hsurv.2.1, rfl⟩
  have hpacket := paritySafeFarProductWaveCofactor_packet hgate hwave
  have hcop := hsurv.2.2.1
  have hhalf := hpacket.2.2
  have hqle : paritySafeFarProductWaveNextQuotient n (p, (q, s)) ≤ n := by
    rw [← paritySafeFarProductWaveCofactor_nextSeat_eq_nextQuotient hgate
      hsurv.2.1]
    omega
  exact ⟨by omega, hqle, hcop⟩

/-! ### PRIM-L051.3: pair-product fibers -/

/-- Recharge keys grouped by the product of their first two primes. -/
noncomputable def paritySafeRechargeFarProductKeysAtPairProduct
    (n b : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (paritySafeRechargeSurvivingFarProductKeys n).filter
    (fun key => key.1 * key.2.1 = b)

@[simp] theorem mem_paritySafeRechargeFarProductKeysAtPairProduct
    {n b : ℕ} {key : ℕ × (ℕ × ℕ)} :
    key ∈ paritySafeRechargeFarProductKeysAtPairProduct n b ↔
      key ∈ paritySafeRechargeSurvivingFarProductKeys n ∧
        key.1 * key.2.1 = b := by
  simp [paritySafeRechargeFarProductKeysAtPairProduct]

/-- A pair-product fiber outside the reduced base is empty. -/
theorem paritySafeRechargeFarProductKeysAtPairProduct_eq_empty_of_not_mem_base
    {n b : ℕ}
    (hb : b ∉ paritySafeFarCofactorBaseOffsets n) :
    paritySafeRechargeFarProductKeysAtPairProduct n b = ∅ := by
  ext key
  constructor
  · intro hkey
    have hfiber := mem_paritySafeRechargeFarProductKeysAtPairProduct.mp hkey
    have hbase :=
      paritySafeRechargeSurvivingFarProductKey_firstPairProduct_mem_farCofactorBase
        hfiber.1
    exact False.elim (hb (by simpa [hfiber.2] using hbase))
  · intro hkey
    simp at hkey

/-- The recharge card is exactly the sum of the pair-product fibers over the
same-anchor reduced cofactor base. -/
theorem paritySafeRechargeSurvivingFarProductKeys_card_eq_pairProductBase_fiber_sum
    (n : ℕ) :
    (paritySafeRechargeSurvivingFarProductKeys n).card =
      ∑ b ∈ paritySafeFarCofactorBaseOffsets n,
        (paritySafeRechargeFarProductKeysAtPairProduct n b).card := by
  have hfilter :
      (paritySafeRechargeSurvivingFarProductKeys n).filter
          (fun key => key.1 * key.2.1 ∈ paritySafeFarCofactorBaseOffsets n) =
        paritySafeRechargeSurvivingFarProductKeys n := by
    ext key
    constructor
    · intro hkey
      exact (Finset.mem_filter.mp hkey).1
    · intro hkey
      apply Finset.mem_filter.mpr
      refine ⟨hkey, ?_⟩
      exact paritySafeRechargeSurvivingFarProductKey_firstPairProduct_mem_farCofactorBase
        hkey
  rw [← hfilter]
  simpa [paritySafeRechargeFarProductKeysAtPairProduct] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (paritySafeRechargeSurvivingFarProductKeys n)
      (paritySafeFarCofactorBaseOffsets n)
      (fun key => key.1 * key.2.1)).symm

/-! ### PRIM-L051.4: exact global residual rearrangement -/

/-- The L050 terminal/recharge split after pair-product fiberization. -/
theorem paritySafeCanonicalFarResidual_card_eq_terminal_add_pairProductFibers
    (n : ℕ) :
    (paritySafeCanonicalFarResidualTripleIncidences n).card =
      (paritySafeTerminalSurvivingFarProductKeys n).card +
      ∑ b ∈ paritySafeFarCofactorBaseOffsets n,
        (paritySafeRechargeFarProductKeysAtPairProduct n b).card := by
  rw [paritySafeCanonicalFarResidual_card_eq_terminal_add_recharge]
  rw [paritySafeRechargeSurvivingFarProductKeys_card_eq_pairProductBase_fiber_sum]

/-! ### PRIM-L051.5: arithmetic witnesses -/

/-- Numeric checks for the two recharge scale examples and the terminal false
beam from the instruction. -/
theorem paritySafeRechargePairProduct_sanity_witnesses :
    3 * 5 ≤ 17 ∧ 3 * 5 ≤ 62 ∧ 3 * 7 > 16 := by
  norm_num

end
end DkMath.NumberTheory.Legendre

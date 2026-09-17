/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicIdealOwnership
import DkMath.FLT.Kummer.CyclotomicPrincipalization
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectCyclotomicChosenTail"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

open SevenRealCubicInt
open SevenCyclotomicDegreeSixInt
open scoped BigOperators

/-- The `j`-th nontrivial direct cyclotomic phase. -/
def directCyclotomicPhaseFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) (j : ℕ) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ofReal (r.summit.endpointLeft : SevenRealCubicInt) -
    zeta ^ j * ofReal (r.summit.endpointRight : SevenRealCubicInt)

/-- The finite geometric sum attached to a direct cyclotomic phase. -/
def directCyclotomicPhaseSum (j : ℕ) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ∑ k ∈ Finset.range j, zeta ^ k

/-- The explicit quotient after extracting the common ramified uniformizer. -/
def directCyclotomicPhaseQuotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) (j : ℕ) :
    SevenCyclotomicDegreeSixInt.Ring :=
  directRamifiedGapTail r +
    directCyclotomicPhaseSum j *
      ofReal (r.summit.endpointRight : SevenRealCubicInt)

theorem one_sub_zeta_pow_eq_uniformizer_mul_phaseSum (j : ℕ) :
    1 - zeta ^ j =
      ramifiedUniformizer * directCyclotomicPhaseSum j := by
  induction j with
  | zero => simp [directCyclotomicPhaseSum, ramifiedUniformizer]
  | succ j ih =>
      rw [pow_succ, directCyclotomicPhaseSum, Finset.sum_range_succ]
      calc
        1 - zeta ^ j * zeta =
            (1 - zeta ^ j) + zeta ^ j * (1 - zeta) := by ring
        _ = ramifiedUniformizer * directCyclotomicPhaseSum j +
              zeta ^ j * ramifiedUniformizer := by
          rw [ih, ramifiedUniformizer]
        _ = ramifiedUniformizer *
              (directCyclotomicPhaseSum j + zeta ^ j) := by
          simp only [ramifiedUniformizer]
          ring

theorem directCyclotomicPhaseQuotient_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicPhaseQuotient r 1 = directRamifiedQuotient r := by
  simp only [directCyclotomicPhaseQuotient, directCyclotomicPhaseSum,
    directRamifiedQuotient, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero]
  ring

theorem directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) (j : ℕ) :
    directCyclotomicPhaseFactor r j =
      ramifiedUniformizer * directCyclotomicPhaseQuotient r j := by
  calc
    directCyclotomicPhaseFactor r j =
        (ofReal (r.summit.endpointLeft : SevenRealCubicInt) -
          ofReal (r.summit.endpointRight : SevenRealCubicInt)) +
          (1 - zeta ^ j) *
            ofReal (r.summit.endpointRight : SevenRealCubicInt) := by
      simp only [directCyclotomicPhaseFactor]
      ring
    _ = ramifiedUniformizer ^ 36 * ramifiedSevenUnit ^ 6 *
          ofReal (r.summit.gapRoot : SevenRealCubicInt) ^ 7 +
          (ramifiedUniformizer * directCyclotomicPhaseSum j) *
            ofReal (r.summit.endpointRight : SevenRealCubicInt) := by
      rw [directGap_eq_uniformizer_pow,
        one_sub_zeta_pow_eq_uniformizer_mul_phaseSum]
    _ = ramifiedUniformizer * directCyclotomicPhaseQuotient r j := by
      simp only [directCyclotomicPhaseQuotient, directRamifiedGapTail]
      ring

theorem ramifiedEval_directCyclotomicPhaseQuotient
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) (j : ℕ) :
    ramifiedEval (directCyclotomicPhaseQuotient r j) =
      (j : ZMod 7) * (r.summit.endpointRight : ZMod 7) := by
  rw [directCyclotomicPhaseQuotient, map_add]
  have htail : ramifiedEval (directRamifiedGapTail r) = 0 := by
    simp [directRamifiedGapTail, ramifiedEval_uniformizer]
  rw [htail, zero_add, map_mul]
  simp [directCyclotomicPhaseSum, map_sum, map_pow,
    ramifiedEval_zeta, ramifiedEval_ofReal,
    thetaResidue, thetaConstModSeven]

theorem directCyclotomicPhaseFactor_mem_ramifiedPrime
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) (j : ℕ) :
    directCyclotomicPhaseFactor r j ∈ ramifiedPrime := by
  rw [directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient]
  change ramifiedEval
      (ramifiedUniformizer * directCyclotomicPhaseQuotient r j) = 0
  rw [map_mul, ramifiedEval_uniformizer, zero_mul]

theorem directCyclotomicPhaseQuotient_not_mem_ramifiedPrime_of_lt_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < 7) :
    directCyclotomicPhaseQuotient r j ∉ ramifiedPrime := by
  intro hmem
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  change ramifiedEval (directCyclotomicPhaseQuotient r j) = 0 at hmem
  rw [ramifiedEval_directCyclotomicPhaseQuotient] at hmem
  have hright : (r.summit.endpointRight : ZMod 7) ≠ 0 := by
    intro hzero
    apply r.summit.endpointRight_not_seven_dvd
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero
  have hj : (j : ZMod 7) ≠ 0 := by
    intro hzero
    have hdiv : (7 : ℤ) ∣ (j : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hzero
    omega
  exact mul_ne_zero hj hright hmem

theorem directCyclotomicPhaseFactor_not_mem_ramifiedPrime_sq_of_lt_seven
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < 7) :
    directCyclotomicPhaseFactor r j ∉ ramifiedPrime ^ 2 := by
  intro hsquare
  rw [ramifiedPrime_eq_span_uniformizer,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hsquare
  rcases hsquare with ⟨c, hc⟩
  have hcancel :
      ramifiedUniformizer * directCyclotomicPhaseQuotient r j =
        ramifiedUniformizer * (ramifiedUniformizer * c) := by
    rw [← directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient r j, hc]
    ring
  have hquotient :
      directCyclotomicPhaseQuotient r j = ramifiedUniformizer * c :=
    mul_left_cancel₀ ramifiedUniformizer_ne_zero hcancel
  exact directCyclotomicPhaseQuotient_not_mem_ramifiedPrime_of_lt_seven
    r hjpos hjlt (by
      change ramifiedEval (directCyclotomicPhaseQuotient r j) = 0
      rw [hquotient, map_mul, ramifiedEval_uniformizer, zero_mul])

theorem prime_eq_ramified_of_mem_chosen_and_other_phase
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    {P : Ideal SevenCyclotomicDegreeSixInt.Ring} (hP : P.IsPrime)
    {j : ℕ} (hj2 : 2 ≤ j) (hj7 : j < 7)
    (h1 : directCyclotomicPhaseFactor r 1 ∈ P)
    (hj : directCyclotomicPhaseFactor r j ∈ P) :
    P = ramifiedPrime := by
  have hright :
      ofReal (r.summit.endpointRight : SevenRealCubicInt) ≠ 0 := by
    intro hzero
    apply r.summit.endpointRight_ne_zero
    have hzero' :
        (r.summit.endpointRight : SevenRealCubicInt) = 0 := by
      apply ofReal_injective
      simpa using hzero
    have hfst := congrArg SevenRealCubicInt.fst hzero'
    simpa [SevenRealCubicInt.ofInt] using hfst
  have hdisj := commonPrimeDvdsSubOneOrY
    (R := SevenCyclotomicDegreeSixInt.Ring) (p := 7) (ζ := zeta)
    zeta_isPrimitiveRoot (by norm_num) hright hP (by norm_num)
    (by simpa [directCyclotomicPhaseFactor, pow_one] using h1)
    ⟨j, by omega, hj7, by
      simpa [directCyclotomicPhaseFactor] using hj⟩
  rcases hdisj with hpi | hrightmem
  · have huniformizer : ramifiedUniformizer ∈ P := by
      simpa [ramifiedUniformizer, sub_eq_add_neg, add_comm] using
        P.neg_mem hpi
    have hle : ramifiedPrime ≤ P := by
      rw [ramifiedPrime_eq_span_uniformizer]
      rw [Ideal.span_singleton_le_iff_mem]
      exact huniformizer
    exact (ramifiedPrime_isMaximal.eq_of_le hP.ne_top hle).symm
  · have hleftmem :
        ofReal (r.summit.endpointLeft : SevenRealCubicInt) ∈ P := by
      have hmul :
          zeta * ofReal (r.summit.endpointRight : SevenRealCubicInt) ∈ P :=
        P.mul_mem_left zeta hrightmem
      have hchosen :
          ofReal (r.summit.endpointLeft : SevenRealCubicInt) -
              zeta * ofReal (r.summit.endpointRight : SevenRealCubicInt) ∈ P := by
        simpa [directCyclotomicPhaseFactor, pow_one] using h1
      simpa only [sub_add_cancel] using P.add_mem hchosen hmul
    rcases r.summit.endpoint_coprime with ⟨a, b, hab⟩
    have hbezout :
        ofReal (a : SevenRealCubicInt) *
              ofReal (r.summit.endpointLeft : SevenRealCubicInt) +
            ofReal (b : SevenRealCubicInt) *
              ofReal (r.summit.endpointRight : SevenRealCubicInt) = 1 := by
      have hbezout' := congrArg
        (fun q : ℤ => ofReal (q : SevenRealCubicInt)) hab
      calc
        ofReal (a : SevenRealCubicInt) *
              ofReal (r.summit.endpointLeft : SevenRealCubicInt) +
            ofReal (b : SevenRealCubicInt) *
              ofReal (r.summit.endpointRight : SevenRealCubicInt) =
            ofReal ((1 : ℤ) : SevenRealCubicInt) := by
              simpa only [Int.cast_mul, Int.cast_add, map_mul, map_add] using hbezout'
        _ = 1 := by rfl
    have hone : (1 : SevenCyclotomicDegreeSixInt.Ring) ∈ P := by
      rw [← hbezout]
      exact P.add_mem
        (P.mul_mem_left
          (ofReal (a : SevenRealCubicInt)) hleftmem)
        (P.mul_mem_left
          (ofReal (b : SevenRealCubicInt)) hrightmem)
    exact False.elim (hP.ne_top (by
      apply top_unique
      intro q hq
      simpa using P.mul_mem_left q hone))

theorem directCyclotomicPhaseQuotients_one_isCoprime_with
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source)
    {j : ℕ} (hj2 : 2 ≤ j) (hj7 : j < 7) :
    IsCoprime
      (Ideal.span
        ({directCyclotomicPhaseQuotient r 1} :
          Set SevenCyclotomicDegreeSixInt.Ring))
      (Ideal.span
        ({directCyclotomicPhaseQuotient r j} :
          Set SevenCyclotomicDegreeSixInt.Ring)) := by
  refine spanSingletons_isCoprime_of_noCommonPrime ?_
  intro P hP hq1 hqj
  have hF1 : directCyclotomicPhaseFactor r 1 ∈ P := by
    rw [directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient]
    exact P.mul_mem_left ramifiedUniformizer hq1
  have hFj : directCyclotomicPhaseFactor r j ∈ P := by
    rw [directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient]
    exact P.mul_mem_left ramifiedUniformizer hqj
  have hP_eq : P = ramifiedPrime :=
    prime_eq_ramified_of_mem_chosen_and_other_phase r hP hj2 hj7 hF1 hFj
  rw [hP_eq] at hq1
  exact directCyclotomicPhaseQuotient_not_mem_ramifiedPrime_of_lt_seven
    r (by norm_num) (by norm_num) hq1

/-- The five-phase tail indexed by the phases `2, ..., 6`. -/
def directCyclotomicOtherPhaseIndices : Finset ℕ :=
  ({2, 3, 4, 5, 6} : Finset ℕ)

def directCyclotomicTail
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    SevenCyclotomicDegreeSixInt.Ring :=
  ∏ j ∈ directCyclotomicOtherPhaseIndices,
    directCyclotomicPhaseQuotient r j

theorem directCyclotomicPhaseQuotient_one_isCoprime_with_tail
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    IsCoprime
      (Ideal.span
        ({directCyclotomicPhaseQuotient r 1} :
          Set SevenCyclotomicDegreeSixInt.Ring))
      (Ideal.span ({directCyclotomicTail r} :
        Set SevenCyclotomicDegreeSixInt.Ring)) := by
  rw [directCyclotomicTail]
  rw [← span_singleton_finset_prod]
  apply idealIsCoprime_prod_of_forall
  intro j hj
  have hj' : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by
    simpa [directCyclotomicOtherPhaseIndices] using hj
  rcases hj' with rfl | rfl | rfl | rfl | rfl <;>
    exact directCyclotomicPhaseQuotients_one_isCoprime_with r
      (by norm_num) (by norm_num)

theorem directCyclotomicOtherPhaseProduct_eq_uniformizer_pow_mul_tail
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    (∏ j ∈ directCyclotomicOtherPhaseIndices,
      directCyclotomicPhaseFactor r j) =
      ramifiedUniformizer ^ 5 * directCyclotomicTail r := by
  classical
  calc
    (∏ j ∈ directCyclotomicOtherPhaseIndices,
        directCyclotomicPhaseFactor r j) =
        ∏ j ∈ directCyclotomicOtherPhaseIndices,
          (ramifiedUniformizer * directCyclotomicPhaseQuotient r j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient r j
    _ = (∏ _ ∈ directCyclotomicOtherPhaseIndices, ramifiedUniformizer) *
          directCyclotomicTail r := by
      rw [Finset.prod_mul_distrib]
      rfl
    _ = ramifiedUniformizer ^ 5 * directCyclotomicTail r := by
      congr 1

def directCyclotomicSixPhaseProduct
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    SevenCyclotomicDegreeSixInt.Ring :=
  directCyclotomicPhaseFactor r 1 *
    ∏ j ∈ directCyclotomicOtherPhaseIndices,
      directCyclotomicPhaseFactor r j

theorem directCyclotomicSixPhaseProduct_eq_uniformizer_pow_mul_quotients
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicSixPhaseProduct r =
      ramifiedUniformizer ^ 6 *
        (directCyclotomicPhaseQuotient r 1 * directCyclotomicTail r) := by
  rw [directCyclotomicSixPhaseProduct,
    directCyclotomicPhaseFactor_eq_uniformizer_mul_quotient,
    directCyclotomicOtherPhaseProduct_eq_uniformizer_pow_mul_tail]
  ring

private theorem rotateEquiv_intCast (n : ℤ) :
    SevenRealCubicInt.rotateEquiv (n : SevenRealCubicInt) = n := by
  simpa using
    (map_intCast
      (SevenRealCubicInt.rotateEquiv :
        SevenRealCubicInt →+* SevenRealCubicInt) n)

theorem rotateEquiv_directCyclotomicPhaseFactor
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) (j : ℕ) :
    SevenCyclotomicDegreeSixInt.rotateEquiv
        (directCyclotomicPhaseFactor r j) =
      directCyclotomicPhaseFactor r (2 * j) := by
  rw [directCyclotomicPhaseFactor, map_sub, map_mul, map_pow,
    rotateEquiv_ofReal, rotateEquiv_ofReal, rotateEquiv_zeta]
  rw [rotateEquiv_intCast, rotateEquiv_intCast]
  simp only [← pow_mul]
  rfl

theorem star_directCyclotomicPhaseFactor_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    star (directCyclotomicPhaseFactor r 1) =
      directCyclotomicPhaseFactor r 6 := by
  simp only [directCyclotomicPhaseFactor, star_sub, star_mul,
    star_ofReal, star_zeta, pow_one, zetaInv_eq_pow_six]
  ring

theorem star_directCyclotomicPhaseFactor_two
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    star (directCyclotomicPhaseFactor r 2) =
      directCyclotomicPhaseFactor r 5 := by
  simp only [directCyclotomicPhaseFactor, star_sub, star_mul, star_pow,
    star_ofReal, star_zeta]
  rw [zetaInv_eq_pow_six, ← pow_mul]
  rw [show (6 * 2 : ℕ) = 7 + 5 by norm_num, pow_add, zeta_pow_seven]
  simp
  ring

theorem star_directCyclotomicPhaseFactor_four
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    star (directCyclotomicPhaseFactor r 4) =
      directCyclotomicPhaseFactor r 3 := by
  simp only [directCyclotomicPhaseFactor, star_sub, star_mul, star_pow,
    star_ofReal, star_zeta]
  rw [zetaInv_eq_pow_six, ← pow_mul]
  rw [show (6 * 4 : ℕ) = 7 + 17 by norm_num, pow_add, zeta_pow_seven]
  rw [show (17 : ℕ) = 7 + 10 by norm_num, pow_add, zeta_pow_seven]
  rw [show (10 : ℕ) = 7 + 3 by norm_num, pow_add, zeta_pow_seven]
  simp
  ring

theorem sixPhaseProduct_directLinearFactor_eq_directCyclotomicSixPhaseProduct
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    sixPhaseProduct (directLinearFactor r) =
      directCyclotomicSixPhaseProduct r := by
  have hrot1 :
      rotateEquiv (directLinearFactor r) =
        directCyclotomicPhaseFactor r 2 := by
    simpa [directLinearFactor, directCyclotomicPhaseFactor] using
      (rotateEquiv_directCyclotomicPhaseFactor r 1)
  have hrot2 :
      rotateEquiv (rotateEquiv (directLinearFactor r)) =
        directCyclotomicPhaseFactor r 4 := by
    calc
      rotateEquiv (rotateEquiv (directLinearFactor r)) =
          rotateEquiv (directCyclotomicPhaseFactor r 2) := by rw [hrot1]
      _ = directCyclotomicPhaseFactor r 4 := by
        simpa using (rotateEquiv_directCyclotomicPhaseFactor r 2)
  have hstar1 :
      star (directLinearFactor r) =
        directCyclotomicPhaseFactor r 6 := by
    simpa [directLinearFactor, directCyclotomicPhaseFactor] using
      (star_directCyclotomicPhaseFactor_one r)
  have hstar2 :
      star (rotateEquiv (directLinearFactor r)) =
        directCyclotomicPhaseFactor r 5 := by
    rw [hrot1]
    exact star_directCyclotomicPhaseFactor_two r
  have hstar4 :
      star (rotateEquiv (rotateEquiv (directLinearFactor r))) =
        directCyclotomicPhaseFactor r 3 := by
    rw [hrot2]
    exact star_directCyclotomicPhaseFactor_four r
  have htail :
      (∏ j ∈ directCyclotomicOtherPhaseIndices,
        directCyclotomicPhaseFactor r j) =
        directCyclotomicPhaseFactor r 2 *
          directCyclotomicPhaseFactor r 3 *
          directCyclotomicPhaseFactor r 4 *
          directCyclotomicPhaseFactor r 5 *
          directCyclotomicPhaseFactor r 6 := by
    norm_num [directCyclotomicOtherPhaseIndices]
    ring
  have hphase1 :
      directLinearFactor r = directCyclotomicPhaseFactor r 1 := by
    simp [directLinearFactor, directCyclotomicPhaseFactor]
  rw [sixPhaseProduct, hrot2, hrot1, hstar1,
    star_directCyclotomicPhaseFactor_two,
    star_directCyclotomicPhaseFactor_four,
    directCyclotomicSixPhaseProduct, htail, hphase1]
  ring

theorem directCyclotomicSixPhaseProduct_eq_seven_residual_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicSixPhaseProduct r =
      (7 * (r.summit.residualRoot : ℤ) ^ 7 :
        SevenCyclotomicDegreeSixInt.Ring) := by
  rw [← sixPhaseProduct_directLinearFactor_eq_directCyclotomicSixPhaseProduct]
  exact sixPhaseProduct_directLinearFactor r

theorem directCyclotomicQuotientProduct_eq_unit_mul_residual_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    directCyclotomicPhaseQuotient r 1 * directCyclotomicTail r =
      ramifiedSevenUnit *
        ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7 := by
  have hfactor :=
    directCyclotomicSixPhaseProduct_eq_uniformizer_pow_mul_quotients r
  have hseven := ofReal_seven_eq_uniformizer_pow_six_mul_unit
  have hBcast :
      ((r.summit.residualRoot : ℤ) :
        SevenCyclotomicDegreeSixInt.Ring) =
      ofReal (r.summit.residualRoot : SevenRealCubicInt) := by
    rfl
  have h7cast :
      (7 : SevenCyclotomicDegreeSixInt.Ring) =
        ofReal (7 : SevenRealCubicInt) := by
    rfl
  have hEq :
      ramifiedUniformizer ^ 6 *
          (directCyclotomicPhaseQuotient r 1 * directCyclotomicTail r) =
        ramifiedUniformizer ^ 6 *
          (ramifiedSevenUnit *
            ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7) := by
    calc
      ramifiedUniformizer ^ 6 *
          (directCyclotomicPhaseQuotient r 1 * directCyclotomicTail r) =
          directCyclotomicSixPhaseProduct r := hfactor.symm
      _ = (7 * (r.summit.residualRoot : ℤ) ^ 7 :
          SevenCyclotomicDegreeSixInt.Ring) :=
        directCyclotomicSixPhaseProduct_eq_seven_residual_pow r
      _ = ofReal (7 : SevenRealCubicInt) *
          ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7 := by
        rw [h7cast, hBcast]
      _ = ramifiedUniformizer ^ 6 *
          (ramifiedSevenUnit *
            ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7) := by
        rw [hseven]
        ring
  exact mul_left_cancel₀ (pow_ne_zero 6 ramifiedUniformizer_ne_zero) hEq

theorem directCyclotomicQuotientIdealProduct_eq_residual_pow
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    Ideal.span
          ({directCyclotomicPhaseQuotient r 1} :
            Set SevenCyclotomicDegreeSixInt.Ring) *
        Ideal.span ({directCyclotomicTail r} :
          Set SevenCyclotomicDegreeSixInt.Ring) =
      Ideal.span
          ({ofReal (r.summit.residualRoot : SevenRealCubicInt)} :
            Set SevenCyclotomicDegreeSixInt.Ring) ^ 7 := by
  have heq := directCyclotomicQuotientProduct_eq_unit_mul_residual_pow r
  have hspanUnit :
      Ideal.span
          ({ramifiedSevenUnit *
              ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7} :
            Set SevenCyclotomicDegreeSixInt.Ring) =
        Ideal.span
          ({ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7} :
            Set SevenCyclotomicDegreeSixInt.Ring) := by
    apply (Ideal.span_singleton_eq_span_singleton).2
    exact associated_unit_mul_left _ _ ramifiedSevenUnit_isUnit
  calc
    Ideal.span
          ({directCyclotomicPhaseQuotient r 1} :
            Set SevenCyclotomicDegreeSixInt.Ring) *
        Ideal.span ({directCyclotomicTail r} :
          Set SevenCyclotomicDegreeSixInt.Ring) =
        Ideal.span
          ({directCyclotomicPhaseQuotient r 1 *
              directCyclotomicTail r} :
            Set SevenCyclotomicDegreeSixInt.Ring) := by
      rw [Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span
          ({ramifiedSevenUnit *
              ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7} :
            Set SevenCyclotomicDegreeSixInt.Ring) := by rw [heq]
    _ = Ideal.span
          ({ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7} :
            Set SevenCyclotomicDegreeSixInt.Ring) := hspanUnit
    _ = Ideal.span
          ({ofReal (r.summit.residualRoot : SevenRealCubicInt)} :
            Set SevenCyclotomicDegreeSixInt.Ring) ^ 7 := by
      rw [Ideal.span_singleton_pow]

theorem directCyclotomicChosenQuotient_ideal_is_seventh_power
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ∃ I : Ideal SevenCyclotomicDegreeSixInt.Ring,
      Ideal.span
          ({directCyclotomicPhaseQuotient r 1} :
            Set SevenCyclotomicDegreeSixInt.Ring) = I ^ 7 := by
  have hq1_ne : directCyclotomicPhaseQuotient r 1 ≠ 0 := by
    intro hzero
    apply directCyclotomicPhaseQuotient_not_mem_ramifiedPrime_of_lt_seven
      (j := 1) r (by norm_num) (by norm_num)
    change ramifiedEval (directCyclotomicPhaseQuotient r 1) = 0
    rw [hzero, map_zero]
  have hq1_ideal_ne :
      Ideal.span
          ({directCyclotomicPhaseQuotient r 1} :
            Set SevenCyclotomicDegreeSixInt.Ring) ≠ ⊥ := by
    intro hbot
    apply hq1_ne
    exact (Ideal.span_singleton_eq_bot.mp hbot)
  have hB_ne :
      ofReal (r.summit.residualRoot : SevenRealCubicInt) ≠ 0 := by
    intro hzero
    have hzero' :
        (r.summit.residualRoot : SevenRealCubicInt) = 0 := by
      apply ofReal_injective
      simpa using hzero
    have hfst := congrArg SevenRealCubicInt.fst hzero'
    have hBint : (r.summit.residualRoot : ℤ) = 0 := by
      simpa [SevenRealCubicInt.ofInt] using hfst
    have hBnat : r.summit.residualRoot = 0 := by
      exact_mod_cast hBint
    exact (Nat.ne_of_gt r.summit.residualRoot_pos) hBnat
  have htail_ne : directCyclotomicTail r ≠ 0 := by
    have hunit_ne : ramifiedSevenUnit ≠ 0 :=
      ramifiedSevenUnit_isUnit.ne_zero
    have hnonzero :
        ramifiedSevenUnit *
            ofReal (r.summit.residualRoot : SevenRealCubicInt) ^ 7 ≠ 0 :=
      mul_ne_zero hunit_ne (pow_ne_zero 7 hB_ne)
    intro hzero
    apply hnonzero
    have heq := directCyclotomicQuotientProduct_eq_unit_mul_residual_pow r
    rw [hzero, mul_zero] at heq
    exact heq.symm
  exact dedekindIdealEqPowOfMulEqPowOfIsCoprime
    hq1_ideal_ne
    (by
      intro hbot
      apply htail_ne
      exact (Ideal.span_singleton_eq_bot.mp hbot))
    (directCyclotomicPhaseQuotient_one_isCoprime_with_tail r)
    (directCyclotomicQuotientIdealProduct_eq_residual_pow r)

theorem directLinearFactor_span_eq_ramifiedPrime_mul_seventh_power
    {x y z : ℕ} {source : CounterexamplePack x y z}
    (r : PrimitiveCounterexampleRamifiedProvenance source) :
    ∃ I : Ideal SevenCyclotomicDegreeSixInt.Ring,
      Ideal.span ({directLinearFactor r} :
        Set SevenCyclotomicDegreeSixInt.Ring) =
        ramifiedPrime * I ^ 7 := by
  obtain ⟨I, hI⟩ := directCyclotomicChosenQuotient_ideal_is_seventh_power r
  refine ⟨I, ?_⟩
  calc
    Ideal.span ({directLinearFactor r} :
        Set SevenCyclotomicDegreeSixInt.Ring) =
        Ideal.span ({ramifiedUniformizer *
          directCyclotomicPhaseQuotient r 1} :
          Set SevenCyclotomicDegreeSixInt.Ring) := by
      rw [directLinearFactor_eq_uniformizer_mul_quotient,
        directCyclotomicPhaseQuotient_one]
    _ = Ideal.span ({ramifiedUniformizer} :
          Set SevenCyclotomicDegreeSixInt.Ring) *
        Ideal.span ({directCyclotomicPhaseQuotient r 1} :
          Set SevenCyclotomicDegreeSixInt.Ring) := by
      rw [Ideal.span_singleton_mul_span_singleton]
    _ = ramifiedPrime * I ^ 7 := by
      rw [ramifiedPrime_eq_span_uniformizer, hI]

end
end DkMath.FLT.Seven

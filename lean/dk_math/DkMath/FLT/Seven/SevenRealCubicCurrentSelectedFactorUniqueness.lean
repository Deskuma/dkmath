/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentSelectedFactorFiber

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentSelectedFactorUniqueness"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open UniqueFactorizationMonoid
open scoped NumberField

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! A deliberately small Associates/count wrapper for the current local
    quotient argument.  This is kept here rather than introducing a general
    valuation layer. -/

def currentIdealPrimeMultiplicity
    (P I : Ideal O) : ℕ :=
  (Associates.mk P).count (Associates.mk I).factors

private theorem currentIdealPrimeMultiplicity_mul
    (P I J : Ideal O) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    currentIdealPrimeMultiplicity P (I * J) =
      currentIdealPrimeMultiplicity P I +
        currentIdealPrimeMultiplicity P J := by
  let hp : Irreducible (Associates.mk P) :=
    Associates.irreducible_mk.mpr
      (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [currentIdealPrimeMultiplicity, ← Associates.mk_mul_mk]
  exact Associates.count_mul
    (Associates.mk_ne_zero.mpr hI)
    (Associates.mk_ne_zero.mpr hJ) hp

private theorem currentIdealPrimeMultiplicity_pow
    (P I : Ideal O) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hI : I ≠ ⊥) (n : ℕ) :
    currentIdealPrimeMultiplicity P (I ^ n) =
      n * currentIdealPrimeMultiplicity P I := by
  let hp : Irreducible (Associates.mk P) :=
    Associates.irreducible_mk.mpr
      (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [currentIdealPrimeMultiplicity, Associates.mk_pow]
  exact Associates.count_pow
    (Associates.mk_ne_zero.mpr hI) hp n

section CurrentBetaUniqueness

variable {q : ℕ} [Fact (Nat.Prime q)]

private theorem orderOf_ne_of_pow_eq_one
    (r : (ZMod q)ˣ) (hr : orderOf r = 7)
    {d : ℕ} (hdpos : 0 < d) (hd : d < 7) (hpow : r ^ d = 1) : False := by
  have hdiv : orderOf r ∣ d := orderOf_dvd_of_pow_eq_one hpow
  rw [hr] at hdiv
  exact (Nat.not_dvd_of_pos_of_lt hdpos hd) hdiv

private theorem currentBeta_one_ne_two
    (r : (ZMod q)ˣ) (hr : orderOf r = 7) :
    currentBeta r 1 ≠ currentBeta r 2 := by
  intro h
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have hpoly : (t - 1) * (t ^ 3 - 1) = 0 := by
    rw [currentBeta_one, currentBeta_two] at h
    have h' : 1 + t + t⁻¹ = 1 + t ^ 2 + (t ^ 2)⁻¹ := by
      simpa only [t] using h
    field_simp [ht0] at h'
    linear_combination -h'
  rcases mul_eq_zero.mp hpoly with h1 | h3
  · exact orderOf_ne_of_pow_eq_one r hr (d := 1) (by norm_num) (by norm_num) (by
      apply Units.ext
      simpa [t] using sub_eq_zero.mp h1)
  · exact orderOf_ne_of_pow_eq_one r hr (d := 3) (by norm_num) (by norm_num) (by
      apply Units.ext
      simpa [t] using sub_eq_zero.mp h3)

private theorem currentBeta_one_ne_three
    (r : (ZMod q)ˣ) (hr : orderOf r = 7) :
    currentBeta r 1 ≠ currentBeta r 3 := by
  intro h
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have hpoly : (t ^ 2 - 1) * (t ^ 4 - 1) = 0 := by
    rw [currentBeta_one, currentBeta_three] at h
    have h' : 1 + t + t⁻¹ = 1 + t ^ 3 + (t ^ 3)⁻¹ := by
      simpa only [t] using h
    field_simp [ht0] at h'
    linear_combination -h'
  rcases mul_eq_zero.mp hpoly with h2 | h4
  · exact orderOf_ne_of_pow_eq_one r hr (d := 2) (by norm_num) (by norm_num) (by
      apply Units.ext
      simpa [t] using sub_eq_zero.mp h2)
  · exact orderOf_ne_of_pow_eq_one r hr (d := 4) (by norm_num) (by norm_num) (by
      apply Units.ext
      simpa [t] using sub_eq_zero.mp h4)

private theorem currentBeta_two_ne_three
    (r : (ZMod q)ˣ) (hr : orderOf r = 7) :
    currentBeta r 2 ≠ currentBeta r 3 := by
  intro h
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have hpoly : (t - 1) * (t ^ 5 - 1) = 0 := by
    rw [currentBeta_two, currentBeta_three] at h
    have h' : 1 + t ^ 2 + (t ^ 2)⁻¹ = 1 + t ^ 3 + (t ^ 3)⁻¹ := by
      simpa only [t] using h
    field_simp [ht0] at h'
    linear_combination -h'
  rcases mul_eq_zero.mp hpoly with h1 | h5
  · exact orderOf_ne_of_pow_eq_one r hr (d := 1) (by norm_num) (by norm_num) (by
      apply Units.ext
      simpa [t] using sub_eq_zero.mp h1)
  · exact orderOf_ne_of_pow_eq_one r hr (d := 5) (by norm_num) (by norm_num) (by
      apply Units.ext
      simpa [t] using sub_eq_zero.mp h5)

theorem currentBeta_pairwise_ne
    (r : (ZMod q)ˣ) (hr : orderOf r = 7) :
    currentBeta r 1 ≠ currentBeta r 2 ∧
      currentBeta r 1 ≠ currentBeta r 3 ∧
      currentBeta r 2 ≠ currentBeta r 3 := by
  exact ⟨currentBeta_one_ne_two r hr,
    currentBeta_one_ne_three r hr, currentBeta_two_ne_three r hr⟩

end CurrentBetaUniqueness

section CurrentBetaEvaluation

variable {q : ℕ} [Fact (Nat.Prime q)]

private theorem currentBeta_two_eq_square_sub_two
    (r : (ZMod q)ˣ) :
    currentBeta r 2 = currentBeta r 1 ^ 2 - 2 * currentBeta r 1 := by
  rw [currentBeta_one, currentBeta_two]
  field_simp [r.ne_zero]
  ring

private theorem currentBeta_three_eq_neg_square_add_two
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    currentBeta r 3 = -currentBeta r 1 ^ 2 + currentBeta r 1 + 2 := by
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have ht7 : t ^ 7 = 1 := congrArg Units.val hr7
  have ht1 : t ≠ 1 := by
    intro h
    apply hr1
    exact Units.ext h
  have hsum :
      t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1 = 0 := by
    have hprod :
        (t - 1) * (t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1) = 0 := by
      linear_combination ht7
    exact (mul_eq_zero.mp hprod).resolve_left
      (sub_ne_zero.mpr ht1)
  rw [currentBeta_one, currentBeta_three]
  change 1 + t ^ 3 + (t ^ 3)⁻¹ =
    -(1 + t + t⁻¹) ^ 2 + (1 + t + t⁻¹) + 2
  field_simp [ht0]
  ring_nf
  linear_combination hsum

private theorem currentBeta_sum_eq_two
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    currentBeta r 1 + currentBeta r 2 + currentBeta r 3 = 2 := by
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have ht7 : t ^ 7 = 1 := congrArg Units.val hr7
  have ht1 : t ≠ 1 := by
    intro h
    apply hr1
    exact Units.ext h
  have hsum :
      t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1 = 0 := by
    have hprod :
        (t - 1) * (t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3 +
          t ^ 2 + t + 1) = 0 := by
      linear_combination ht7
    exact (mul_eq_zero.mp hprod).resolve_left
      (sub_ne_zero.mpr ht1)
  rw [currentBeta_one, currentBeta_two, currentBeta_three]
  change (1 + t + t⁻¹) +
      (1 + t ^ 2 + (t ^ 2)⁻¹) +
      (1 + t ^ 3 + (t ^ 3)⁻¹) = 2
  field_simp [ht0]
  linear_combination hsum

private theorem currentBeta_two_sq_sub_two_eq_three
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) :
    currentBeta r 3 = currentBeta r 2 ^ 2 - 2 * currentBeta r 2 := by
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have ht7 : t ^ 7 = 1 := congrArg Units.val hr7
  rw [currentBeta_two, currentBeta_three]
  change 1 + t ^ 3 + (t ^ 3)⁻¹ =
    (1 + t ^ 2 + (t ^ 2)⁻¹) ^ 2 -
      2 * (1 + t ^ 2 + (t ^ 2)⁻¹)
  field_simp [ht0]
  ring_nf
  have ht8 : t ^ 8 = t := by
    calc
      t ^ 8 = t ^ 7 * t := by ring
      _ = t := by rw [ht7, one_mul]
  have ht9 : t ^ 9 = t ^ 2 := by
    calc
      t ^ 9 = t ^ 7 * t ^ 2 := by ring
      _ = t ^ 2 := by rw [ht7, one_mul]
  rw [ht7, ht8]
  ring

private theorem currentBeta_three_sq_sub_two_eq_one
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) :
    currentBeta r 1 = currentBeta r 3 ^ 2 - 2 * currentBeta r 3 := by
  let t : ZMod q := r
  have ht0 : t ≠ 0 := r.ne_zero
  have ht7 : t ^ 7 = 1 := congrArg Units.val hr7
  rw [currentBeta_one, currentBeta_three]
  change 1 + t + t⁻¹ =
    (1 + t ^ 3 + (t ^ 3)⁻¹) ^ 2 -
      2 * (1 + t ^ 3 + (t ^ 3)⁻¹)
  field_simp [ht0]
  ring_nf
  have ht11 : t ^ 11 = t ^ 4 := by
    calc
      t ^ 11 = t ^ 7 * t ^ 4 := by ring
      _ = t ^ 4 := by rw [ht7, one_mul]
  have ht12 : t ^ 12 = t ^ 5 := by
    calc
      t ^ 12 = t ^ 7 * t ^ 5 := by ring
      _ = t ^ 5 := by rw [ht7, one_mul]
  rw [ht12, ht7]
  ring

private theorem currentBeta_one_eq_neg_square_add_two
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    currentBeta r 1 = -currentBeta r 2 ^ 2 + currentBeta r 2 + 2 := by
  have hsum := currentBeta_sum_eq_two r hr7 hr1
  have hsq := currentBeta_two_sq_sub_two_eq_three r hr7
  rw [show currentBeta r 1 =
      2 - currentBeta r 2 - currentBeta r 3 by
        linear_combination hsum]
  rw [hsq]
  ring

private theorem currentBeta_two_eq_neg_square_add_two
    (r : (ZMod q)ˣ) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    currentBeta r 2 = -currentBeta r 3 ^ 2 + currentBeta r 3 + 2 := by
  have hsum := currentBeta_sum_eq_two r hr7 hr1
  have hsq := currentBeta_three_sq_sub_two_eq_one r hr7
  rw [show currentBeta r 2 =
      2 - currentBeta r 3 - currentBeta r 1 by
        linear_combination hsum]
  rw [hsq]
  ring

end CurrentBetaEvaluation

section CurrentCyclicAlphaEvaluation

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

private theorem eval_currentCyclicAlpha_one
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    {b : ZMod q}
    (ha : c.residue.evalReal alpha = b) :
    c.residue.evalReal (currentCyclicAlpha 0) = b := by
  simpa [currentCyclicAlpha] using ha

private theorem eval_currentCyclicAlpha_two
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    {b : ZMod q}
    (ha : c.residue.evalReal alpha = b) :
    c.residue.evalReal (currentCyclicAlpha 1) = b ^ 2 - 2 * b := by
  rw [show currentCyclicAlpha 1 = alpha ^ 2 - 2 * alpha by
    simp [currentCyclicAlpha]]
  simp only [map_sub, map_pow, map_mul]
  rw [ha]
  rw [map_ofNat]

private theorem eval_currentCyclicAlpha_three
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    {b : ZMod q}
    (ha : c.residue.evalReal alpha = b) :
    c.residue.evalReal (currentCyclicAlpha 2) = -b ^ 2 + b + 2 := by
  rw [show currentCyclicAlpha 2 = -alpha ^ 2 + alpha + 2 by
    simp [currentCyclicAlpha]]
  simp only [map_add, map_neg, map_pow, map_ofNat]
  rw [ha]

theorem CurrentCommonPrimeCyclotomicPacket.currentCyclicAlpha_eval_phase_zero
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    (hphase : c.phase = 0) :
    c.residue.evalReal (currentCyclicAlpha 0) = currentBeta c.tau 1 ∧
      c.residue.evalReal (currentCyclicAlpha 1) = currentBeta c.tau 2 ∧
      c.residue.evalReal (currentCyclicAlpha 2) = currentBeta c.tau 3 := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  have ha := c.phase_eq
  rw [hphase] at ha
  change c.residue.evalReal alpha = currentBeta c.tau 1 at ha
  refine ⟨eval_currentCyclicAlpha_one c ha, ?_, ?_⟩
  · rw [eval_currentCyclicAlpha_two c ha]
    exact (currentBeta_two_eq_square_sub_two c.tau).symm
  · rw [eval_currentCyclicAlpha_three c ha]
    exact (currentBeta_three_eq_neg_square_add_two c.tau
      c.tau_pow_seven c.tau_ne_one).symm

theorem CurrentCommonPrimeCyclotomicPacket.currentCyclicAlpha_eval_phase_one
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    (hphase : c.phase = 1) :
    c.residue.evalReal (currentCyclicAlpha 0) = currentBeta c.tau 2 ∧
      c.residue.evalReal (currentCyclicAlpha 1) = currentBeta c.tau 3 ∧
      c.residue.evalReal (currentCyclicAlpha 2) = currentBeta c.tau 1 := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  have ha := c.phase_eq
  rw [hphase] at ha
  change c.residue.evalReal alpha = currentBeta c.tau 2 at ha
  refine ⟨eval_currentCyclicAlpha_one c ha, ?_, ?_⟩
  · rw [eval_currentCyclicAlpha_two c ha]
    exact (currentBeta_two_sq_sub_two_eq_three c.tau
      c.tau_pow_seven).symm
  · rw [eval_currentCyclicAlpha_three c ha]
    exact (currentBeta_one_eq_neg_square_add_two c.tau
      c.tau_pow_seven c.tau_ne_one).symm

theorem CurrentCommonPrimeCyclotomicPacket.currentCyclicAlpha_eval_phase_two
    (c : CurrentCommonPrimeCyclotomicPacket h q)
    (hphase : c.phase = 2) :
    c.residue.evalReal (currentCyclicAlpha 0) = currentBeta c.tau 3 ∧
      c.residue.evalReal (currentCyclicAlpha 1) = currentBeta c.tau 1 ∧
      c.residue.evalReal (currentCyclicAlpha 2) = currentBeta c.tau 2 := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  have ha := c.phase_eq
  rw [hphase] at ha
  change c.residue.evalReal alpha = currentBeta c.tau 3 at ha
  refine ⟨eval_currentCyclicAlpha_one c ha, ?_, ?_⟩
  · rw [eval_currentCyclicAlpha_two c ha]
    exact (currentBeta_three_sq_sub_two_eq_one c.tau
      c.tau_pow_seven).symm
  · rw [eval_currentCyclicAlpha_three c ha]
    exact (currentBeta_two_eq_neg_square_add_two c.tau
      c.tau_pow_seven c.tau_ne_one).symm

theorem CurrentCommonPrimeCyclotomicPacket.currentCyclicAlpha_eval_selected
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.residue.evalReal
        (currentCyclicAlpha (phaseTraceIndex c.phase)) =
      currentBeta c.tau 1 := by
  by_cases h0 : c.phase = 0
  · simpa [h0, phaseTraceIndex] using
      c.currentCyclicAlpha_eval_phase_zero h0 |>.1
  by_cases h1 : c.phase = 1
  · simpa [h1, phaseTraceIndex] using
      c.currentCyclicAlpha_eval_phase_one h1 |>.2.2
  have h2 : c.phase = 2 := by
    apply Fin.eq_of_val_eq
    omega
  simpa [h2, phaseTraceIndex] using
    c.currentCyclicAlpha_eval_phase_two h2 |>.2.1

theorem CurrentCommonPrimeCyclotomicPacket.currentRealPairCarrier_eval
    (c : CurrentCommonPrimeCyclotomicPacket h q) (i : Fin 3) :
    c.residue.evalReal
        (currentRealPairCarrier i (rotateEquiv p.rho) p.rho) =
      c.residue.evalReal p.rho ^ 2 *
        ((c.tau : ZMod q) *
            (currentBeta c.tau 1 -
              c.residue.evalReal (currentCyclicAlpha i))) := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  have hval := congrArg Units.val c.tau_eq
  change (c.tau : ZMod q) =
    c.residue.evalReal (rotateEquiv p.rho) /
      c.residue.evalReal p.rho at hval
  have hrel := (div_eq_iff c.residue.rho_ne_zero).mp hval.symm
  have hinv : (c.tau : ZMod q) * (c.tau : ZMod q)⁻¹ = 1 := by
    exact mul_inv_cancel₀ c.tau.ne_zero
  rw [currentRealPairCarrier]
  simp only [map_sub, map_add, map_pow, map_mul]
  rw [hrel, currentBeta_one]
  calc
    (c.tau * c.residue.evalReal p.rho) ^ 2 +
        (c.tau * c.residue.evalReal p.rho) *
          c.residue.evalReal p.rho + c.residue.evalReal p.rho ^ 2 -
        c.residue.evalReal (currentCyclicAlpha i) *
          (c.tau * c.residue.evalReal p.rho * c.residue.evalReal p.rho) =
      c.residue.evalReal p.rho ^ 2 *
        ((c.tau : ZMod q) ^ 2 + (c.tau : ZMod q) + 1 -
          c.residue.evalReal (currentCyclicAlpha i) * c.tau) := by ring
    _ = c.residue.evalReal p.rho ^ 2 *
        ((c.tau : ZMod q) *
          (1 + (c.tau : ZMod q) +
            (c.tau : ZMod q)⁻¹ -
            c.residue.evalReal (currentCyclicAlpha i))) := by
      congr 1
      calc
        (c.tau : ZMod q) ^ 2 + (c.tau : ZMod q) + 1 -
            c.residue.evalReal (currentCyclicAlpha i) * c.tau =
          (c.tau : ZMod q) ^ 2 + (c.tau : ZMod q) +
            (c.tau : ZMod q) *
              (c.tau : ZMod q)⁻¹ -
            c.residue.evalReal (currentCyclicAlpha i) * c.tau := by
              rw [hinv]
        _ = (c.tau : ZMod q) *
            (1 + (c.tau : ZMod q) +
              (c.tau : ZMod q)⁻¹ -
              c.residue.evalReal (currentCyclicAlpha i)) := by ring

private theorem currentCyclicAlpha_eval_eq_beta_one_iff
    (c : CurrentCommonPrimeCyclotomicPacket h q) (i : Fin 3) :
    c.residue.evalReal (currentCyclicAlpha i) = currentBeta c.tau 1 ↔
      i = phaseTraceIndex c.phase := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  by_cases h0 : c.phase = 0
  · have ht := c.currentCyclicAlpha_eval_phase_zero h0
    rcases show i = 0 ∨ i = 1 ∨ i = 2 by omega with hi | hi | hi
    · subst i
      constructor
      · intro _
        simp only [h0, phaseTraceIndex, Fin.isValue,
          ↓reduceIte]
      · intro _
        simpa only [h0, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
          ↓reduceIte] using ht.1
    · subst i
      constructor
      · intro heq
        exfalso
        apply (currentBeta_pairwise_ne c.tau c.tau_orderOf).1
        exact heq.symm.trans ht.2.1
      · intro hi
        simp only [h0, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
          ↓reduceIte] at hi
    · subst i
      constructor
      · intro heq
        exfalso
        apply (currentBeta_pairwise_ne c.tau c.tau_orderOf).2.1
        exact heq.symm.trans ht.2.2
      · intro hi
        simp only [h0, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
          ↓reduceIte] at hi
  · by_cases h1 : c.phase = 1
    · have ht := c.currentCyclicAlpha_eval_phase_one h1
      rcases show i = 0 ∨ i = 1 ∨ i = 2 by omega with hi | hi | hi
      · subst i
        constructor
        · intro heq
          exfalso
          apply (currentBeta_pairwise_ne c.tau c.tau_orderOf).1
          exact heq.symm.trans ht.1
        · intro hi
          simp only [h1, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte] at hi
      · subst i
        constructor
        · intro heq
          exfalso
          apply (currentBeta_pairwise_ne c.tau c.tau_orderOf).2.1
          exact heq.symm.trans ht.2.1
        · intro hi
          simp only [h1, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte] at hi
      · subst i
        constructor
        · intro _
          simp only [h1, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte]
        · intro _
          simpa only [h1, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte] using ht.2.2
    · have h2 : c.phase = 2 := by
        apply Fin.eq_of_val_eq
        omega
      have ht := c.currentCyclicAlpha_eval_phase_two h2
      rcases show i = 0 ∨ i = 1 ∨ i = 2 by omega with hi | hi | hi
      · subst i
        constructor
        · intro heq
          exfalso
          apply (currentBeta_pairwise_ne c.tau c.tau_orderOf).2.1
          exact heq.symm.trans ht.1
        · intro hi
          simp only [h2, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte] at hi
      · subst i
        constructor
        · intro _
          simp only [h2, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte]
        · intro _
          simpa only [h2, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte] using ht.2.1
      · subst i
        constructor
        · intro heq
          exfalso
          apply (currentBeta_pairwise_ne c.tau c.tau_orderOf).1
          exact heq.symm.trans ht.2.2
        · intro hi
          simp only [h2, phaseTraceIndex, Fin.isValue, Fin.reduceEq,
            ↓reduceIte] at hi

theorem CurrentCommonPrimeCyclotomicPacket.currentRealPairCarrier_eval_zero_iff
    (c : CurrentCommonPrimeCyclotomicPacket h q) (i : Fin 3) :
    c.residue.evalReal
        (currentRealPairCarrier i (rotateEquiv p.rho) p.rho) = 0 ↔
      i = phaseTraceIndex c.phase := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  rw [c.currentRealPairCarrier_eval]
  have hpow : c.residue.evalReal p.rho ^ 2 ≠ 0 :=
    pow_ne_zero 2 c.residue.rho_ne_zero
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hpowzero | hinner
    · exact (hpow hpowzero).elim
    · have hdiff : currentBeta c.tau 1 -
          c.residue.evalReal (currentCyclicAlpha i) = 0 := by
        exact (mul_eq_zero.mp hinner).resolve_left c.tau.ne_zero
      exact (currentCyclicAlpha_eval_eq_beta_one_iff c i).mp
        (sub_eq_zero.mp hdiff).symm
  · intro hi
    apply mul_eq_zero.mpr
    exact Or.inr (mul_eq_zero.mpr (Or.inr
      (sub_eq_zero.mpr
        ((currentCyclicAlpha_eval_eq_beta_one_iff c i).mpr hi).symm)))

theorem CurrentCommonPrimeCyclotomicPacket.currentRealPairCarrier_mem_Q_iff
    (c : CurrentCommonPrimeCyclotomicPacket h q) (i : Fin 3) :
    modelEquivRingOfIntegers
        (currentRealPairCarrier i (rotateEquiv p.rho) p.rho) ∈ c.residue.Q ↔
      i = phaseTraceIndex c.phase := by
  constructor
  · intro hmem
    apply (c.currentRealPairCarrier_eval_zero_iff i).mp
    exact (c.residue.evalReal_zero_iff _).mpr hmem
  · intro hi
    exact (c.residue.evalReal_zero_iff _).mp
      ((c.currentRealPairCarrier_eval_zero_iff i).mpr hi)

end CurrentCyclicAlphaEvaluation

section CurrentExactMultiplicity

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

def currentPrincipalIdeal (a : SevenRealCubicInt) : Ideal O :=
  Ideal.span {modelEquivRingOfIntegers a}

private theorem currentPrincipalIdeal_ne_bot
    {a : SevenRealCubicInt} (ha : a ≠ 0) :
    currentPrincipalIdeal a ≠ (⊥ : Ideal O) := by
  intro hzero
  have hmem :
      modelEquivRingOfIntegers a ∈ currentPrincipalIdeal a :=
    Ideal.mem_span_singleton_self _
  rw [hzero, Ideal.mem_bot] at hmem
  exact ha (modelEquivRingOfIntegers.injective
    (by simpa using hmem))

private theorem current_quotientSquareRoot_ne_zero
    (t : DirectOrbitSquareRefinementPacket p) :
    t.quotientSquareRoot ≠ 0 := by
  intro hz
  have hpos :=
    directOrbitSquareRefinement_quotient_square_norm_pos t
  rw [hz] at hpos
  norm_num [SevenRealCubicInt.norm] at hpos

private theorem CurrentCommonPrimeCyclotomicPacket.eisensteinAxis_not_mem_Q
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    modelEquivRingOfIntegers eisensteinAxis ∉ c.residue.Q := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  intro hmem
  have hzero :
      c.residue.evalReal eisensteinAxis = 0 :=
    (c.residue.evalReal_zero_iff _).mpr hmem
  have halpha :
      c.residue.evalReal alpha = 3 := by
    rw [eisensteinAxis_eq, map_sub, map_ofNat] at hzero
    exact sub_eq_zero.mp hzero
  have hcube := congrArg c.residue.evalReal alpha_cube
  simp only [map_pow, map_mul, map_add, map_sub, map_one,
    map_ofNat] at hcube
  have hpoly :
      c.residue.evalReal alpha ^ 3 -
          2 * c.residue.evalReal alpha ^ 2 -
            c.residue.evalReal alpha + 1 = 0 := by
    linear_combination hcube
  have hseven : (7 : ZMod q) = 0 := by
    rw [halpha] at hpoly
    norm_num at hpoly
    exact hpoly
  have hseven_ne : (7 : ZMod q) ≠ 0 := by
    intro hz
    have hd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).mp hz
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with hq1 | hq7
    · exact c.residue.q_prime.ne_one hq1
    · exact c.residue.q_ne_seven hq7
  exact hseven_ne hseven

theorem directOrbitQuotient_eq_currentAxis_cube_unit_mul_squareRoot_pow
    (t : DirectOrbitSquareRefinementPacket p) :
    ∃ U : SevenRealCubicIntˣ,
      directOrbitQuotient p =
        eisensteinAxis ^ 3 * (U : SevenRealCubicInt) *
          t.quotientSquareRoot ^ 14 := by
  refine ⟨t.powerSplit.quotientUnit *
      t.quotientSquareUnit ^ 7, ?_⟩
  rw [t.powerSplit.quotient_eq,
    t.powerSplit.quotientCore_eq, t.quotientRoot_eq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem current_quotient_span_eq_axis_cube_mul_squareRoot_pow
    (t : DirectOrbitSquareRefinementPacket p) (U : SevenRealCubicIntˣ)
    (hU :
      directOrbitQuotient p =
        eisensteinAxis ^ 3 * (U : SevenRealCubicInt) *
          t.quotientSquareRoot ^ 14) :
    currentPrincipalIdeal (directOrbitQuotient p) =
      currentPrincipalIdeal eisensteinAxis ^ 3 *
        currentPrincipalIdeal t.quotientSquareRoot ^ 14 := by
  have hUO : IsUnit
      (modelEquivRingOfIntegers (U : SevenRealCubicInt)) :=
    IsUnit.map modelEquivRingOfIntegers.toRingHom U.isUnit
  have hEq := congrArg modelEquivRingOfIntegers hU
  simp only [map_mul, map_pow] at hEq
  rw [currentPrincipalIdeal, hEq]
  calc
    Ideal.span
        {modelEquivRingOfIntegers eisensteinAxis ^ 3 *
          modelEquivRingOfIntegers (U : SevenRealCubicInt) *
            modelEquivRingOfIntegers t.quotientSquareRoot ^ 14} =
      Ideal.span
          {modelEquivRingOfIntegers eisensteinAxis ^ 3 *
            modelEquivRingOfIntegers (U : SevenRealCubicInt)} *
        Ideal.span {modelEquivRingOfIntegers t.quotientSquareRoot ^ 14} := by
          rw [← Ideal.span_singleton_mul_span_singleton]
    _ =
      (Ideal.span {modelEquivRingOfIntegers eisensteinAxis ^ 3} *
          Ideal.span {modelEquivRingOfIntegers (U : SevenRealCubicInt)}) *
        Ideal.span {modelEquivRingOfIntegers t.quotientSquareRoot ^ 14} := by
          rw [← Ideal.span_singleton_mul_span_singleton]
    _ =
      Ideal.span {modelEquivRingOfIntegers eisensteinAxis ^ 3} *
        Ideal.span {modelEquivRingOfIntegers t.quotientSquareRoot ^ 14} := by
          rw [Ideal.span_singleton_eq_top.mpr hUO, Ideal.mul_top]
    _ =
      currentPrincipalIdeal eisensteinAxis ^ 3 *
        currentPrincipalIdeal t.quotientSquareRoot ^ 14 := by
          rw [← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
          rfl

private theorem currentIdealPrimeMultiplicity_eq_zero_of_not_mem
    (P : Ideal O) (a : SevenRealCubicInt) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (ha : a ≠ 0)
    (hamem : modelEquivRingOfIntegers a ∉ P) :
    currentIdealPrimeMultiplicity P (currentPrincipalIdeal a) = 0 := by
  by_contra hcount
  let hp : Irreducible P :=
    (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hdiv : P ∣ currentPrincipalIdeal a :=
    (Associates.count_ne_zero_iff_dvd
      (currentPrincipalIdeal_ne_bot ha) hp).mp hcount
  exact hamem ((Ideal.dvd_iff_le.mp hdiv)
    (Ideal.mem_span_singleton_self _))

private theorem currentPrincipalIdeal_mem_prime_pow_iff
    (P : Ideal O) (a : SevenRealCubicInt) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (ha : a ≠ 0) (k : ℕ) :
    modelEquivRingOfIntegers a ∈ P ^ k ↔
      k ≤ currentIdealPrimeMultiplicity P (currentPrincipalIdeal a) := by
  let hp : Irreducible (Associates.mk P) :=
    Associates.irreducible_mk.mpr
      (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hspan0 : currentPrincipalIdeal a ≠ ⊥ :=
    currentPrincipalIdeal_ne_bot ha
  constructor
  · intro hmem
    have hdiv : P ^ k ∣ currentPrincipalIdeal a :=
      (Ideal.dvd_iff_le.mpr
        ((Ideal.span_singleton_le_iff_mem (P ^ k)).mpr hmem))
    have hle :
        Associates.mk P ^ k ≤
          Associates.mk (currentPrincipalIdeal a) := by
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd]
      exact hdiv
    exact (Associates.prime_pow_dvd_iff_le
      (Associates.mk_ne_zero.mpr hspan0) hp).mp hle
  · intro hle
    have hle' :
        Associates.mk P ^ k ≤
          Associates.mk (currentPrincipalIdeal a) :=
      (Associates.prime_pow_dvd_iff_le
        (Associates.mk_ne_zero.mpr hspan0) hp).mpr hle
    have hdiv : P ^ k ∣ currentPrincipalIdeal a := by
      rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at hle'
      exact hle'
    exact (Ideal.span_singleton_le_iff_mem (P ^ k)).mp
      (Ideal.dvd_iff_le.mp hdiv)

private theorem CurrentCommonPrimeCyclotomicPacket.Q_ne_bot
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    c.residue.Q ≠ (⊥ : Ideal O) := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hbase0 : base ≠ (⊥ : Ideal ℤ) := by
    simpa [base] using (Int.ofNat_ne_zero.mpr c.residue.q_prime.ne_zero)
  letI : c.residue.Q.LiesOver base := by
    simpa [base] using c.residue.Q_liesOver
  exact Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 c.residue.Q

theorem CurrentCommonPrimeCyclotomicPacket.currentQuotientSquareRootMultiplicity_pos
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    0 <
      currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
  letI : Fact (Nat.Prime q) := ⟨c.residue.q_prime⟩
  have hS0 := current_quotientSquareRoot_ne_zero h.squareRefinement
  have hmem :
      modelEquivRingOfIntegers
          h.squareRefinement.quotientSquareRoot ∈ c.residue.Q :=
    (c.residue.evalReal_zero_iff _).mp c.residue.quotientRoot_zero
  have hdiv :
      c.residue.Q ∣
        currentPrincipalIdeal h.squareRefinement.quotientSquareRoot :=
    Ideal.dvd_iff_le.mpr
      ((Ideal.span_singleton_le_iff_mem c.residue.Q).mpr hmem)
  have hcount :
      currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) ≠ 0 := by
    let hp : Irreducible c.residue.Q :=
      (Ideal.prime_of_isPrime c.Q_ne_bot c.residue.Q_prime).irreducible
    exact (Associates.count_ne_zero_iff_dvd
      (currentPrincipalIdeal_ne_bot hS0) hp).mpr hdiv
  exact Nat.pos_of_ne_zero hcount

theorem CurrentCommonPrimeCyclotomicPacket.currentQuotientMultiplicity_eq_fourteen_mul
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal (directOrbitQuotient p)) =
      14 *
        currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
  let t := h.squareRefinement
  obtain ⟨U, hU⟩ :=
    directOrbitQuotient_eq_currentAxis_cube_unit_mul_squareRoot_pow t
  rw [current_quotient_span_eq_axis_cube_mul_squareRoot_pow t U hU]
  have haxis0 : currentPrincipalIdeal eisensteinAxis ≠ (⊥ : Ideal O) :=
    currentPrincipalIdeal_ne_bot eisensteinAxis_prime.ne_zero
  have hS0 : currentPrincipalIdeal t.quotientSquareRoot ≠ (⊥ : Ideal O) :=
    currentPrincipalIdeal_ne_bot (current_quotientSquareRoot_ne_zero t)
  have hQ0 := c.Q_ne_bot
  have haxis_mult :
      currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal eisensteinAxis) = 0 :=
    currentIdealPrimeMultiplicity_eq_zero_of_not_mem
      c.residue.Q eisensteinAxis c.residue.Q_prime hQ0
      eisensteinAxis_prime.ne_zero (c.eisensteinAxis_not_mem_Q)
  rw [currentIdealPrimeMultiplicity_mul
      c.residue.Q (currentPrincipalIdeal eisensteinAxis ^ 3)
      (currentPrincipalIdeal t.quotientSquareRoot ^ 14)
      c.residue.Q_prime hQ0
      (pow_ne_zero 3 haxis0) (pow_ne_zero 14 hS0),
    currentIdealPrimeMultiplicity_pow
      c.residue.Q (currentPrincipalIdeal eisensteinAxis)
      c.residue.Q_prime hQ0 haxis0 3,
    currentIdealPrimeMultiplicity_pow
      c.residue.Q (currentPrincipalIdeal t.quotientSquareRoot)
      c.residue.Q_prime hQ0 hS0 14,
    haxis_mult]
  simp [t]

private theorem currentRealPairCarrier_ne_zero
    (h : DirectOrbitCanonicalCommonFactorPacket p) (i : Fin 3) :
    currentRealPairCarrier i (rotateEquiv p.rho) p.rho ≠ 0 := by
  have hD0 : directOrbitQuotient p ≠ 0 := by
    obtain ⟨U, hU⟩ :=
      directOrbitQuotient_eq_currentAxis_cube_unit_mul_squareRoot_pow
        h.squareRefinement
    rw [hU]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero 3 eisensteinAxis_prime.ne_zero)
        (IsUnit.ne_zero U.isUnit))
      (pow_ne_zero 14
        (current_quotientSquareRoot_ne_zero h.squareRefinement))
  intro hzero
  have hprod := currentRealPairCarrier_product_direct (p := p)
  fin_cases i
  · change currentRealPairCarrier (0 : Fin 3) (rotateEquiv p.rho) p.rho = 0 at hzero
    have hzero' :
        currentRealPairCarrier (0 : Fin 3) (rotateHom p.rho) p.rho = 0 := by
      simpa only [rotateEquiv_apply] using hzero
    simp [hzero'] at hprod
    exact hD0 hprod.symm
  · change currentRealPairCarrier (1 : Fin 3) (rotateEquiv p.rho) p.rho = 0 at hzero
    have hzero' :
        currentRealPairCarrier (1 : Fin 3) (rotateHom p.rho) p.rho = 0 := by
      simpa only [rotateEquiv_apply] using hzero
    simp [hzero'] at hprod
    exact hD0 hprod.symm
  · change currentRealPairCarrier (2 : Fin 3) (rotateEquiv p.rho) p.rho = 0 at hzero
    have hzero' :
        currentRealPairCarrier (2 : Fin 3) (rotateHom p.rho) p.rho = 0 := by
      simpa only [rotateEquiv_apply] using hzero
    simp [hzero'] at hprod
    exact hD0 hprod.symm

theorem CurrentCommonPrimeCyclotomicPacket.selectedRealPairCarrier_multiplicity_eq_fourteen_mul
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentIdealPrimeMultiplicity c.residue.Q
        (currentPrincipalIdeal (selectedRealPairCarrier c)) =
      14 *
        currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
  let F (i : Fin 3) :=
    currentPrincipalIdeal
      (currentRealPairCarrier i (rotateEquiv p.rho) p.rho)
  have hF0 : F 0 ≠ (⊥ : Ideal O) :=
    currentPrincipalIdeal_ne_bot (currentRealPairCarrier_ne_zero h 0)
  have hF1 : F 1 ≠ (⊥ : Ideal O) :=
    currentPrincipalIdeal_ne_bot (currentRealPairCarrier_ne_zero h 1)
  have hF2 : F 2 ≠ (⊥ : Ideal O) :=
    currentPrincipalIdeal_ne_bot (currentRealPairCarrier_ne_zero h 2)
  have hprod :
      currentPrincipalIdeal (directOrbitQuotient p) = F 0 * F 1 * F 2 := by
    let hprodR := currentRealPairCarrier_product_direct (p := p)
    calc
      currentPrincipalIdeal (directOrbitQuotient p) =
          Ideal.span
            {modelEquivRingOfIntegers (directOrbitQuotient p)} := rfl
      _ = Ideal.span
            {modelEquivRingOfIntegers
              (currentRealPairCarrier 0 (rotateEquiv p.rho) p.rho *
                currentRealPairCarrier 1 (rotateEquiv p.rho) p.rho *
                currentRealPairCarrier 2 (rotateEquiv p.rho) p.rho)} := by
          rw [hprodR]
      _ = F 0 * F 1 * F 2 := by
          simp only [currentPrincipalIdeal, F, map_mul,
            Ideal.span_singleton_mul_span_singleton]
  have hcount :
      currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal (directOrbitQuotient p)) =
        currentIdealPrimeMultiplicity c.residue.Q (F 0) +
          currentIdealPrimeMultiplicity c.residue.Q (F 1) +
            currentIdealPrimeMultiplicity c.residue.Q (F 2) := by
    rw [hprod,
      currentIdealPrimeMultiplicity_mul
        c.residue.Q (F 0 * F 1) (F 2)
        c.residue.Q_prime c.Q_ne_bot
        (mul_ne_zero hF0 hF1) hF2,
      currentIdealPrimeMultiplicity_mul
        c.residue.Q (F 0) (F 1)
        c.residue.Q_prime c.Q_ne_bot hF0 hF1]
  have hzero_other {i : Fin 3} (hi : i ≠ phaseTraceIndex c.phase) :
      currentIdealPrimeMultiplicity c.residue.Q (F i) = 0 := by
    apply currentIdealPrimeMultiplicity_eq_zero_of_not_mem
      c.residue.Q
      (currentRealPairCarrier i (rotateEquiv p.rho) p.rho)
      c.residue.Q_prime c.Q_ne_bot
      (currentRealPairCarrier_ne_zero h i)
    exact fun hmem =>
      hi ((c.currentRealPairCarrier_mem_Q_iff i).mp hmem)
  have hsel :
      currentIdealPrimeMultiplicity c.residue.Q (F (phaseTraceIndex c.phase)) =
        currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal (directOrbitQuotient p)) := by
    have hs : phaseTraceIndex c.phase = 0 ∨
        phaseTraceIndex c.phase = 1 ∨
        phaseTraceIndex c.phase = 2 := by omega
    rcases hs with hs | hs | hs
    · have h1 := hzero_other (i := (1 : Fin 3)) (by omega)
      have h2 := hzero_other (i := (2 : Fin 3)) (by omega)
      rw [hs, hcount, h1, h2]
      simp
    · have h0 := hzero_other (i := (0 : Fin 3)) (by omega)
      have h2 := hzero_other (i := (2 : Fin 3)) (by omega)
      rw [hs, hcount, h0, h2]
      simp
    · have h0 := hzero_other (i := (0 : Fin 3)) (by omega)
      have h1 := hzero_other (i := (1 : Fin 3)) (by omega)
      rw [hs, hcount, h0, h1]
      simp
  simpa [selectedRealPairCarrier, F] using
    hsel.trans (c.currentQuotientMultiplicity_eq_fourteen_mul (p := p))

theorem CurrentCommonPrimeCyclotomicPacket.selectedRealPairCarrier_mem_Q_pow_iff
    (c : CurrentCommonPrimeCyclotomicPacket h q) (k : ℕ) :
    modelEquivRingOfIntegers (selectedRealPairCarrier c) ∈ c.residue.Q ^ k ↔
      k ≤ 14 *
        currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
  have hsel0 : selectedRealPairCarrier c ≠ 0 := by
    simpa [selectedRealPairCarrier] using
      (currentRealPairCarrier_ne_zero h (phaseTraceIndex c.phase))
  calc
    modelEquivRingOfIntegers (selectedRealPairCarrier c) ∈ c.residue.Q ^ k ↔
        k ≤ currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal (selectedRealPairCarrier c)) := by
      exact currentPrincipalIdeal_mem_prime_pow_iff
        c.residue.Q (selectedRealPairCarrier c) c.residue.Q_prime
        c.Q_ne_bot hsel0 k
    _ ↔ k ≤ 14 *
        currentIdealPrimeMultiplicity c.residue.Q
          (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) := by
      rw [c.selectedRealPairCarrier_multiplicity_eq_fourteen_mul (p := p)]

theorem CurrentCommonPrimeCyclotomicPacket.selectedRealPairCarrier_mem_Q_pow
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    modelEquivRingOfIntegers (selectedRealPairCarrier c) ∈
        c.residue.Q ^
          (14 * currentIdealPrimeMultiplicity c.residue.Q
            (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot)) := by
  rw [c.selectedRealPairCarrier_mem_Q_pow_iff (p := p)]

theorem CurrentCommonPrimeCyclotomicPacket.selectedRealPairCarrier_not_mem_Q_pow_succ
    (c : CurrentCommonPrimeCyclotomicPacket h q) :
    modelEquivRingOfIntegers (selectedRealPairCarrier c) ∉
        c.residue.Q ^
          (14 * currentIdealPrimeMultiplicity c.residue.Q
            (currentPrincipalIdeal h.squareRefinement.quotientSquareRoot) + 1) := by
  rw [c.selectedRealPairCarrier_mem_Q_pow_iff (p := p)]
  omega

end CurrentExactMultiplicity

end SevenRealCubic
end
end DkMath.FLT.Seven

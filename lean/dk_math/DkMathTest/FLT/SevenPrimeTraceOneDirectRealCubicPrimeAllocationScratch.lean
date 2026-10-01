/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation

#print "file: DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationScratch"

namespace DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationScratch

noncomputable section

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubicInt
open scoped NumberField Pointwise

abbrev sigma : Gal(Field / ℚ) := fieldRotateEquiv

example : sigma ^ 3 = 1 := by
  ext x
  change fieldRotateEquiv (fieldRotateEquiv (fieldRotateEquiv x)) = x
  exact fieldRotateEquiv_three x

example : sigma ≠ 1 := by
  change fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field)
  exact fieldRotateEquiv_ne_one

example : sigma ^ 2 ≠ 1 := by
  intro h
  apply (show sigma ≠ 1 from by
    change fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field)
    exact fieldRotateEquiv_ne_one)
  calc
    sigma = sigma * 1 := by simp
    _ = sigma * sigma ^ 2 := by rw [h]
    _ = sigma ^ 3 := by simp [pow_succ, mul_assoc]
    _ = 1 := by
      ext x
      change fieldRotateEquiv (fieldRotateEquiv (fieldRotateEquiv x)) = x
      exact fieldRotateEquiv_three x

example : sigma ≠ sigma ^ 2 := by
  intro h
  have h' := congrArg (fun g : Gal(Field / ℚ) => sigma⁻¹ * g) h
  have hone : (1 : Gal(Field / ℚ)) = sigma := by
    simpa [pow_two, mul_assoc] using h'
  exact (show sigma ≠ 1 from by
    change fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field)
    exact fieldRotateEquiv_ne_one) hone.symm

example (g : Gal(Field/ℚ)) :
    g = 1 ∨ g = sigma ∨ g = sigma ^ 2 := by
  classical
  have h1 : sigma ≠ 1 := by
    change fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field)
    exact fieldRotateEquiv_ne_one
  have h2 : sigma ^ 2 ≠ 1 := by
    intro h
    apply h1
    calc
      sigma = sigma * 1 := by simp
      _ = sigma * sigma ^ 2 := by rw [h]
      _ = sigma ^ 3 := by simp [pow_succ, mul_assoc]
      _ = 1 := by
        ext x
        change fieldRotateEquiv (fieldRotateEquiv (fieldRotateEquiv x)) = x
        exact fieldRotateEquiv_three x
  have h12 : sigma ≠ sigma ^ 2 := by
    intro h
    have h' := congrArg (fun u : Gal(Field / ℚ) => sigma⁻¹ * u) h
    have hone : (1 : Gal(Field / ℚ)) = sigma := by
      simpa [pow_two, mul_assoc] using h'
    exact h1 hone.symm
  let s : Finset (Gal(Field / ℚ)) :=
    insert (sigma ^ 2) (insert sigma ({1} : Finset (Gal(Field / ℚ))))
  have hs : s.card = 3 := by
    simp [s, h1, h2, h12.symm]
  have hcard : Fintype.card (Gal(Field / ℚ)) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact galois_group_card_three
  have hs_univ : s = Finset.univ :=
    Finset.eq_univ_of_card s (hs.trans hcard.symm)
  have hg : g ∈ s := by
    rw [hs_univ]
    simp
  rcases (by simpa [s] using hg) with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h

example {base : Ideal ℤ} {P Q : Ideal O}
    (hPprime : P.IsPrime) (hQprime : Q.IsPrime)
    (hPover : P.LiesOver base) (hQover : Q.LiesOver base)
    (hneq : P ≠ Q) :
    Q = sigma • P ∨ Q = sigma ^ 2 • P := by
  classical
  let : P.IsPrime := hPprime
  let : Q.IsPrime := hQprime
  let : P.LiesOver base := hPover
  let : Q.LiesOver base := hQover
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq ℤ O (Gal(Field / ℚ)) P Q
      (hPover.over.symm.trans hQover.over)
  have hclass : g = 1 ∨ g = sigma ∨ g = sigma ^ 2 := by
    have h1 : sigma ≠ 1 := by
      change fieldRotateEquiv ≠ (AlgEquiv.refl : Field ≃ₐ[ℚ] Field)
      exact fieldRotateEquiv_ne_one
    have h2 : sigma ^ 2 ≠ 1 := by
      intro h
      apply h1
      calc
        sigma = sigma * 1 := by simp
        _ = sigma * sigma ^ 2 := by rw [h]
        _ = sigma ^ 3 := by simp [pow_succ, mul_assoc]
        _ = 1 := by
          ext x
          change fieldRotateEquiv (fieldRotateEquiv (fieldRotateEquiv x)) = x
          exact fieldRotateEquiv_three x
    have h12 : sigma ≠ sigma ^ 2 := by
      intro h
      have h' := congrArg (fun u : Gal(Field / ℚ) => sigma⁻¹ * u) h
      have hone : (1 : Gal(Field / ℚ)) = sigma := by
        simpa [pow_two, mul_assoc] using h'
      exact h1 hone.symm
    let s : Finset (Gal(Field / ℚ)) :=
      insert (sigma ^ 2) (insert sigma ({1} : Finset (Gal(Field / ℚ))))
    have hs : s.card = 3 := by
      simp [s, h1, h2, h12.symm]
    have hcard : Fintype.card (Gal(Field / ℚ)) = 3 := by
      rw [← Nat.card_eq_fintype_card]
      exact galois_group_card_three
    have hs_univ : s = Finset.univ :=
      Finset.eq_univ_of_card s (hs.trans hcard.symm)
    have hg' : g ∈ s := by
      rw [hs_univ]
      simp
    rcases (by simpa [s] using hg') with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  rcases hclass with h | h | h
  · have hPQ : Q = P := by simpa [h] using hg
    exact (hneq hPQ.symm).elim
  · exact Or.inl (h ▸ hg)
  · exact Or.inr (h ▸ hg)

#check (fieldRotateEquiv : Gal(Field / ℚ))
#check fieldRotateEquiv_three
#check fieldRotateEquiv_ne_one
#check ringOfIntegersRotateEquiv_three
#check ringOfIntegersRotateEquiv_apply
#check Algebra.IsInvariant.orbit_eq_primesOver
#check Algebra.IsInvariant.exists_smul_of_under_eq
#check Ideal.pointwise_smul_def
#check Ideal.pointwise_smul_eq_comap
#check Finset.eq_univ_of_card
#check Fintype.card_congr
#check Nat.card_eq_fintype_card
#check Set.ncard_eq_toFinset_card
#synth MulSemiringAction (Gal(Field / ℚ)) O
#synth Algebra.IsInvariant ℤ O (Gal(Field / ℚ))
#synth SMulCommClass (Gal(Field / ℚ)) ℤ O
#print NumberField.RingOfIntegers.instMulSemiringAction

example (x : O) :
    (MulSemiringAction.toRingHom (Gal(Field / ℚ)) O fieldRotateEquiv) x =
      ringOfIntegersRotateEquiv x := by
  apply NumberField.RingOfIntegers.coe_injective
  change fieldRotateEquiv (algebraMap O Field x) =
    algebraMap O Field (ringOfIntegersRotateEquiv x)
  exact DkMath.FLT.Seven.SevenRealCubic.fieldRotateEquiv_algebraMap_ringOfIntegers x

example (P : Ideal O) (x : O) :
    x ∈ sigma • P ↔
      (MulSemiringAction.toRingAut (Gal(Field / ℚ)) O sigma).symm x ∈ P := by
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]

example (P : Ideal O) (x : O) :
    x ∈ sigma • P ↔ ringOfIntegersRotateEquiv.symm x ∈ P := by
  have hact :
      MulSemiringAction.toRingAut (Gal(Field / ℚ)) O sigma =
        ringOfIntegersRotateEquiv := by
    ext y
    change fieldRotateEquiv (algebraMap O Field y) =
      algebraMap O Field (ringOfIntegersRotateEquiv y)
    exact DkMath.FLT.Seven.SevenRealCubic.fieldRotateEquiv_algebraMap_ringOfIntegers y
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap, hact]

example (x : SevenRealCubicInt) :
    ringOfIntegersRotateEquiv (modelEquivRingOfIntegers x) =
      modelEquivRingOfIntegers (rotateEquiv x) := by
  rw [ringOfIntegersRotateEquiv_apply,
    modelEquivRingOfIntegers.symm_apply_apply]

example (P : Ideal O) (x : SevenRealCubicInt) :
    modelEquivRingOfIntegers (rotateEquiv x) ∈ sigma • P ↔
      modelEquivRingOfIntegers x ∈ P := by
  rw [Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  have hact :
      MulSemiringAction.toRingAut (Gal(Field / ℚ)) O sigma =
        ringOfIntegersRotateEquiv := by
    ext y
    change fieldRotateEquiv (algebraMap O Field y) =
      algebraMap O Field (ringOfIntegersRotateEquiv y)
    exact DkMath.FLT.Seven.SevenRealCubic.fieldRotateEquiv_algebraMap_ringOfIntegers y
  rw [hact]
  have hrot :
      ringOfIntegersRotateEquiv (modelEquivRingOfIntegers x) =
        modelEquivRingOfIntegers (rotateEquiv x) := by
    rw [ringOfIntegersRotateEquiv_apply,
      modelEquivRingOfIntegers.symm_apply_apply]
  rw [← hrot, RingEquiv.symm_apply_apply]

example (P : Ideal O) (x : SevenRealCubicInt) :
    modelEquivRingOfIntegers x ∈ sigma ^ 2 • P ↔
      modelEquivRingOfIntegers (rotateEquiv x) ∈ P := by
  rw [show sigma ^ 2 • P = sigma • (sigma • P) by
    rw [pow_two, mul_smul]]
  have hsecond :=
    (show modelEquivRingOfIntegers x ∈
        sigma • (sigma • P) ↔
      modelEquivRingOfIntegers (rotateEquiv (rotateEquiv x)) ∈ sigma • P from by
      have hh := directOrbitGaloisSigma_model_rotate_mem_iff (sigma • P)
        (rotateEquiv (rotateEquiv x))
      rw [SevenRealCubicInt.rotateEquiv_three] at hh
      exact hh)
  have hfirst := directOrbitGaloisSigma_model_rotate_mem_iff P (rotateEquiv x)
  simpa [SevenRealCubicInt.rotateEquiv_three] using hsecond.trans hfirst

example
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (P : Ideal O) (hPprime : P.IsPrime)
    (h0 : modelEquivRingOfIntegers t.gapSquareRoot ∈ P)
    (h1 : modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot) ∈ P) :
    modelEquivRingOfIntegers
        (rotateEquiv (rotateEquiv t.gapSquareRoot)) ∈ P := by
  let c0 : O := modelEquivRingOfIntegers
    (directOrbitSquareTwistCoeff0 t : SevenRealCubicInt)
  let c1 : O := modelEquivRingOfIntegers
    (directOrbitSquareTwistCoeff1 t : SevenRealCubicInt)
  let c2 : O := modelEquivRingOfIntegers
    (directOrbitSquareTwistCoeff2 t : SevenRealCubicInt)
  let r0 : O := modelEquivRingOfIntegers t.gapSquareRoot
  let r1 : O := modelEquivRingOfIntegers (rotateEquiv t.gapSquareRoot)
  let r2 : O := modelEquivRingOfIntegers
    (rotateEquiv (rotateEquiv t.gapSquareRoot))
  have hEq := congrArg modelEquivRingOfIntegers
    (directOrbit_squareTwist_twisted_eq t)
  have hEqO : c0 * (r0 ^ 7) ^ 2 + c1 * (r1 ^ 7) ^ 2 +
      c2 * (r2 ^ 7) ^ 2 = 0 := by
    simpa only [c0, c1, c2, r0, r1, r2, map_add, map_mul, map_pow,
      map_zero, Units.val_mul, Units.val_pow_eq_pow_val] using hEq
  have h0' : r0 ∈ P := h0
  have h1' : r1 ∈ P := h1
  have ht0 : c0 * (r0 ^ 7) ^ 2 ∈ P := by
    apply P.mul_mem_left
    exact P.pow_mem_of_mem (P.pow_mem_of_mem h0' 7 (by norm_num)) 2 (by norm_num)
  have ht1 : c1 * (r1 ^ 7) ^ 2 ∈ P := by
    apply P.mul_mem_left
    exact P.pow_mem_of_mem (P.pow_mem_of_mem h1' 7 (by norm_num)) 2 (by norm_num)
  have ht2 : c2 * (r2 ^ 7) ^ 2 ∈ P := by
    have hrewrite : c2 * (r2 ^ 7) ^ 2 =
        -(c0 * (r0 ^ 7) ^ 2 + c1 * (r1 ^ 7) ^ 2) := by
      linear_combination hEqO
    rw [hrewrite]
    exact P.neg_mem (P.add_mem ht0 ht1)
  have hc2 : IsUnit c2 := by
    exact IsUnit.map modelEquivRingOfIntegers.toRingHom
      (directOrbitSquareTwistCoeff2 t).isUnit
  have hpow : (r2 ^ 7) ^ 2 ∈ P :=
    (P.unit_mul_mem_iff_mem hc2).mp ht2
  have hpow' : r2 ^ 14 ∈ P := by
    have heq : r2 ^ 14 = (r2 ^ 7) ^ 2 := by
      calc
        r2 ^ 14 = r2 ^ (7 * 2) := by norm_num
        _ = (r2 ^ 7) ^ 2 := by rw [pow_mul]
    rw [heq]
    exact hpow
  have hroot : r2 ∈ P := hPprime.mem_of_pow_mem 14 hpow'
  exact hroot

#check Set.ncard_eq_one
#check Set.ncard_sdiff
#check Set.ncard_eq_toFinset_card
#check Set.ncard_insert_of_notMem
#check Set.ncard_singleton

end
end DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicPrimeAllocationScratch

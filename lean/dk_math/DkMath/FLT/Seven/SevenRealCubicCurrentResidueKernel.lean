/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRealCubicCurrentQuotientGapOrientation

#print "file: DkMath.FLT.Seven.SevenRealCubicCurrentResidueKernel"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

namespace SevenRealCubic

set_option linter.style.longLine false
set_option linter.style.haveILetI false

theorem zmod_ringHom_eq_of_ker_eq
    {R : Type*} [CommRing R]
    {q : ℕ} [Fact q.Prime]
    (f g : R →+* ZMod q)
    (hker : RingHom.ker f = RingHom.ker g) :
    f = g := by
  ext x
  let n : ℕ := (f x).val
  have hfn : f (x - n) = 0 := by
    rw [map_sub, map_natCast]
    rw [show (n : ZMod q) = f x by
      simp [n]]
    exact sub_self _
  have hgn : g (x - n) = 0 := by
    apply (show x - n ∈ RingHom.ker g from ?_)
    rw [← hker]
    exact hfn
  have hgn' : g x - (n : ZMod q) = 0 := by
    simpa only [map_sub, map_natCast] using hgn
  have hfn' : f x - (n : ZMod q) = 0 := by
    simpa only [map_sub, map_natCast] using hfn
  have hfn'' : f x = (n : ZMod q) := sub_eq_zero.mp hfn'
  have hgn'' : g x = (n : ZMod q) := sub_eq_zero.mp hgn'
  exact hfn''.trans hgn''.symm

section CurrentPackets

variable {x y z : ℕ} {source : CounterexamplePack x y z}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

private theorem rotate_inv_model_eq (u : SevenRealCubicInt) :
    ringOfIntegersRotateEquiv.symm (modelEquivRingOfIntegers u) =
      modelEquivRingOfIntegers (rotateEquiv.symm u) := by
  apply ringOfIntegersRotateEquiv.injective
  simp only [RingEquiv.apply_symm_apply]
  rw [directOrbitGaloisSigma_model_rotate]
  simp

private theorem rotate_inv_twice_eq (u : SevenRealCubicInt) :
    rotateEquiv.symm (rotateEquiv.symm u) = rotateEquiv u := by
  have hinv (v : SevenRealCubicInt) :
      rotateEquiv.symm v = rotateEquiv (rotateEquiv v) := by
    apply rotateEquiv.injective
    simp only [RingEquiv.apply_symm_apply, rotateEquiv_three]
  rw [hinv, hinv, rotateEquiv_three]

theorem CurrentOrientedGapPrimeTransport.f0_zero_iff
    (b : CurrentOrientedGapPrimeTransport h q) (u : SevenRealCubicInt) :
    b.f0 u = 0 ↔ modelEquivRingOfIntegers u ∈ b.P := by
  letI : b.P.IsPrime := b.P_prime
  constructor
  · intro hu
    have hu' : algebraMap O b.P.ResidueField
        (modelEquivRingOfIntegers u) = 0 := by
      simpa [b.f0_formula, directOrbitCommonPrimeEval] using
        congrArg b.evalEquiv.symm hu
    exact Ideal.algebraMap_residueField_eq_zero.mp hu'
  · intro hu
    have hu' : modelToRingOfIntegers u ∈ b.P := by
      simpa only [modelEquivRingOfIntegers_apply] using hu
    simpa [b.f0_formula, directOrbitCommonPrimeEval] using
      congrArg b.evalEquiv
        (Ideal.algebraMap_residueField_eq_zero.mpr hu')

theorem CurrentOrientedGapPrimeTransport.f1_zero_iff
    (b : CurrentOrientedGapPrimeTransport h q) (u : SevenRealCubicInt) :
    b.f1 u = 0 ↔
      modelEquivRingOfIntegers u ∈
        (directOrbitGaloisSigma : Gal(Field / ℚ)) • b.P := by
  have hmem : modelEquivRingOfIntegers u ∈
        (directOrbitGaloisSigma : Gal(Field / ℚ)) • b.P ↔
      modelEquivRingOfIntegers (rotateEquiv.symm u) ∈ b.P := by
    rw [directOrbitGaloisSigma_mem_iff, rotate_inv_model_eq]
  change b.f0 (rotateEquiv.symm u) = 0 ↔ _
  rw [b.f0_zero_iff, hmem]

theorem CurrentOrientedGapPrimeTransport.f2_zero_iff
    (b : CurrentOrientedGapPrimeTransport h q) (u : SevenRealCubicInt) :
    b.f2 u = 0 ↔
      modelEquivRingOfIntegers u ∈
        (directOrbitGaloisSigma : Gal(Field / ℚ)) ^ 2 • b.P := by
  change b.f0 (rotateEquiv.symm (rotateEquiv.symm u)) = 0 ↔ _
  rw [rotate_inv_twice_eq, b.f0_zero_iff]
  exact (directOrbitGaloisSigma_sq_model_mem_iff b.P u).symm

theorem CurrentCommonPrimeResiduePacket.evalReal_zero_iff
    (a : CurrentCommonPrimeResiduePacket h q) (u : SevenRealCubicInt) :
    a.evalReal u = 0 ↔ modelEquivRingOfIntegers u ∈ a.Q := by
  letI : a.Q.IsPrime := a.Q_prime
  constructor
  · intro hu
    have hu' : algebraMap O a.Q.ResidueField
        (modelEquivRingOfIntegers u) = 0 := by
      simpa [a.evalReal_formula, directOrbitCommonPrimeEval] using
        congrArg a.evalEquiv.symm hu
    exact Ideal.algebraMap_residueField_eq_zero.mp hu'
  · intro hu
    have hu' : modelToRingOfIntegers u ∈ a.Q := by
      simpa only [modelEquivRingOfIntegers_apply] using hu
    simpa [a.evalReal_formula, directOrbitCommonPrimeEval] using
      congrArg a.evalEquiv
        (Ideal.algebraMap_residueField_eq_zero.mpr hu')

theorem CurrentOrientedGapPrimeTransport.f0_kernel_eq
    (b : CurrentOrientedGapPrimeTransport h q) :
    RingHom.ker b.f0 = Ideal.comap modelEquivRingOfIntegers b.P := by
  ext u
  change b.f0 u = 0 ↔ modelEquivRingOfIntegers u ∈ b.P
  exact b.f0_zero_iff u

theorem CurrentOrientedGapPrimeTransport.f1_kernel_eq
    (b : CurrentOrientedGapPrimeTransport h q) :
    RingHom.ker b.f1 = Ideal.comap modelEquivRingOfIntegers
      ((directOrbitGaloisSigma : Gal(Field / ℚ)) • b.P) := by
  ext u
  change b.f1 u = 0 ↔
    modelEquivRingOfIntegers u ∈
      (directOrbitGaloisSigma : Gal(Field / ℚ)) • b.P
  exact b.f1_zero_iff u

theorem CurrentOrientedGapPrimeTransport.f2_kernel_eq
    (b : CurrentOrientedGapPrimeTransport h q) :
    RingHom.ker b.f2 = Ideal.comap modelEquivRingOfIntegers
      ((directOrbitGaloisSigma : Gal(Field / ℚ)) ^ 2 • b.P) := by
  ext u
  change b.f2 u = 0 ↔
    modelEquivRingOfIntegers u ∈
      (directOrbitGaloisSigma : Gal(Field / ℚ)) ^ 2 • b.P
  exact b.f2_zero_iff u

theorem CurrentCommonPrimeResiduePacket.evalReal_kernel_eq
    (a : CurrentCommonPrimeResiduePacket h q) :
    RingHom.ker a.evalReal = Ideal.comap modelEquivRingOfIntegers a.Q := by
  ext u
  change a.evalReal u = 0 ↔ modelEquivRingOfIntegers u ∈ a.Q
  exact a.evalReal_zero_iff u

theorem currentCommonPrime_evalReal_eq_f1
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q)
    (hQ : a.Q = (directOrbitGaloisSigma : Gal(Field/ℚ)) • b.P) :
    a.evalReal = b.f1 := by
  letI : Fact q.Prime := ⟨a.q_prime⟩
  apply zmod_ringHom_eq_of_ker_eq
  rw [a.evalReal_kernel_eq, b.f1_kernel_eq, hQ]

theorem currentCommonPrime_evalReal_eq_f2
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q)
    (hQ : a.Q = (directOrbitGaloisSigma : Gal(Field/ℚ)) ^ 2 • b.P) :
    a.evalReal = b.f2 := by
  letI : Fact q.Prime := ⟨a.q_prime⟩
  apply zmod_ringHom_eq_of_ker_eq
  rw [a.evalReal_kernel_eq, b.f2_kernel_eq, hQ]

theorem currentCommonPrime_evalReal_eq_f1_or_f2
    (a : CurrentCommonPrimeResiduePacket h q)
    (b : CurrentOrientedGapPrimeTransport h q) :
    a.evalReal = b.f1 ∨ a.evalReal = b.f2 := by
  rcases currentCommonPrime_quotient_oriented_gap_orbit a b with hQ | hQ
  · exact Or.inl (currentCommonPrime_evalReal_eq_f1 a b hQ)
  · exact Or.inr (currentCommonPrime_evalReal_eq_f2 a b hQ)

end CurrentPackets

end SevenRealCubic
end
end DkMath.FLT.Seven

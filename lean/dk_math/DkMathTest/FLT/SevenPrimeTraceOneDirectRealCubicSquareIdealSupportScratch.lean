import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicSquarePrimeSupport
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic

open scoped NumberField

open DkMath.FLT.Seven
open DkMath.FLT.Seven.SevenRealCubicInt
open Module

#check Algebra.norm_eq_of_equiv_equiv
#check Basis
#check Ideal.absNorm_span_singleton
#check Ideal.exists_isMaximal_dvd_of_dvd_absNorm'
#check Ideal.dvd_iff_le
#check Ideal.isCoprime_iff_sup_eq
#check Set.ncard_le_ncard
#check Set.ncard_pair
#check Ideal.IsMaximal.isPrime
#check Ideal.IsMaximal.ne_top
#check Ideal.LiesOver

namespace DkMath.FLT.Seven

noncomputable section

private def scratchCoordinateAddEquiv :
    SevenRealCubicInt ≃+ (Fin 3 → ℤ) where
  toFun x i :=
    if i = 0 then x.fst else
    if i = 1 then x.snd else x.thd
  invFun f := ⟨f 0, f 1, f 2⟩
  left_inv x := by
    ext <;> simp
  right_inv f := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp

private def scratchCoordinateBasis :
    Basis (Fin 3) ℤ SevenRealCubicInt :=
  Basis.ofEquivFun scratchCoordinateAddEquiv.toIntLinearEquiv

local instance scratchModuleFree :
    Module.Free ℤ SevenRealCubicInt :=
  Module.Free.of_basis scratchCoordinateBasis

local instance scratchModuleFinite :
    Module.Finite ℤ SevenRealCubicInt :=
  Module.Finite.of_basis scratchCoordinateBasis

private theorem scratch_algebraNorm_eq_norm (x : SevenRealCubicInt) :
    Algebra.norm ℤ x = SevenRealCubicInt.norm x := by
  rw [Algebra.norm_eq_matrix_det scratchCoordinateBasis,
    Matrix.det_fin_three]
  simp [Algebra.leftMulMatrix_eq_repr_mul,
    scratchCoordinateBasis, scratchCoordinateAddEquiv,
    SevenRealCubicInt.norm]
  ring

theorem scratch_model_norm_transport (x : SevenRealCubicInt) :
    Algebra.norm ℤ (SevenRealCubic.modelEquivRingOfIntegers x) =
      SevenRealCubicInt.norm x := by
  have h := Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl ℤ) SevenRealCubic.modelEquivRingOfIntegers (by
      ext n
      simp) x
  simpa [scratch_algebraNorm_eq_norm] using h.symm

end
end DkMath.FLT.Seven

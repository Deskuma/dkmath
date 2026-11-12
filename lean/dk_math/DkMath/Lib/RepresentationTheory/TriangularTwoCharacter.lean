/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PadicCharacterLimit
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

#print "file: DkMath.Lib.RepresentationTheory.TriangularTwoCharacter"

/-!
# 実際の上三角2次作用の二つの指標と積公式

群からの実際の行列準同型を使う。対角成分の可逆性は群の逆元から導き、
非対角成分が零・完全列が分裂するとは主張しない。
-/
namespace DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
noncomputable section
variable {Γ R : Type*} [Group Γ] [CommRing R]
    (ρ : Γ →* Matrix (Fin 2) (Fin 2) R) (ht : ∀ g, ρ g 1 0 = 0)

/-- 第一対角成分の実際の乗法性。 -/
def firstHom : Γ →* R where
  toFun g := ρ g 0 0
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ht h, mul_zero, add_zero]

/-- 第二対角成分の実際の乗法性。 -/
def secondHom : Γ →* R where
  toFun g := ρ g 1 1
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ht g, zero_mul, zero_add]

/-- 対角成分の単元性は群の逆元を写して得る。 -/
def first : Γ →* Rˣ := (firstHom ρ ht).toHomUnits
def second : Γ →* Rˣ := (secondHom ρ ht).toHomUnits

/-- 非対角成分は二つの指標を伴う積公式を満たす。 -/
theorem offDiagonal_mul (g h : Γ) :
    ρ (g * h) 0 1 = (first ρ ht g : R) * ρ h 0 1 + ρ g 0 1 * (second ρ ht h : R) := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/-- 実際の行列式は二つの同じ対角指標の積。算術的な同定は別の課題。 -/
theorem determinant (g : Γ) :
    (ρ g).det = (first ρ ht g : R) * (second ρ ht g : R) := by
  rw [Matrix.det_fin_two, ht, mul_zero, sub_zero]
  rfl

end
end DkMath.Lib.RepresentationTheory.TriangularTwoCharacter

namespace DkMath.Lib.Algebra.PadicCharacterLimit
noncomputable section
variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ]

/-- p 進指標の全ての標準有限剰余。 -/
def reductions (d : Γ →* ℤ_[p]ˣ) (n : ℕ) : Γ →* (ZMod (p ^ (n + 1)))ˣ :=
  (Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom).comp d

/-- p 進指標から取った有限剰余は標準剰余写像で両立する。 -/
theorem reductions_compatible (d : Γ →* ℤ_[p]ˣ) (n : ℕ) (g : Γ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1)))).toMonoidHom (reductions d (n + 1) g) = reductions d n g := by
  apply Units.ext
  exact congrArg (fun f : ℤ_[p] →+* ZMod (p ^ (n + 1)) => f (d g : ℤ_[p]))
    (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _))

/-- 有限剰余の開核を実際に供給すれば、同じ p 進指標は連続。無限核の開性は不要。 -/
theorem continuous_of_reduction_kernels [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (d : Γ →* ℤ_[p]ˣ) (hopen : ∀ n, IsOpen ((reductions d n).ker : Set Γ)) : Continuous d := by
  have he := character_unique (reductions d) (reductions_compatible d) d (fun _ _ => rfl)
  rw [← he]
  exact character_continuous _ _ hopen

end
end DkMath.Lib.Algebra.PadicCharacterLimit

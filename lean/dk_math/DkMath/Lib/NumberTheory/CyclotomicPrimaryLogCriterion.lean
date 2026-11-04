/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryLog
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion"

/-!
# Λ による primary 単元消滅の明示的な二つの残条件

同じ ω² 単元空間の次元1と、その空間内の元 g の Λ(g)≠0 が与えられた場合、
局所冪空間の消滅を証明する。次元計算・円分単元の射影・非零評価は証明しない。
Λ を任意の写像に取り替えず、指定された原始根の実際の3次商と単元商を使う。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion

open CyclotomicPrimaryLog CyclotomicPrimaryUnitSpace CyclotomicKernelField
open CyclotomicKummerWeight KummerSelmerExact
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- 実際の Λ は、一次元の部分空間上で一つの非零評価があれば単射になる。 -/
theorem eq_zero_of_rank_one_of_log_eq_zero (hp5 : 5 ≤ p)
    (W : Submodule (ZMod p) (Additive (UnitClass (𝓞 F) p)))
    (hrank : Module.finrank (ZMod p) W = 1)
    (g : W) (hdetect : primaryLog hζ hp5 g ≠ 0)
    (x : W) (hx : primaryLog hζ hp5 x = 0) : x = 0 := by
  have hg : g ≠ 0 := by
    intro h
    apply hdetect
    simp [h]
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hrank hg x
  have he : scalarMap hζ hp5 a * primaryLog hζ hp5 g = 0 := by
    rw [← primaryLog_smul]
    exact (congrArg (fun y : W => primaryLog hζ hp5 y) ha).trans hx
  have ha0 : a = 0 := by
    by_contra hn
    have hm := congrArg (fun z => scalarMap hζ hp5 a⁻¹ * z) he
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul, mul_zero] at hm
    exact hdetect hm
  simpa only [ha0, zero_smul] using ha.symm

end

section RootField

variable {p : ℕ} [Fact p.Prime] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 局所冪空間の元は、選び直していない同じ根の Λ の核に入る。 -/
theorem primaryWeightSquareSpace_log_eq_zero (hp5 : 5 ≤ p)
    (x : Additive (UnitClass (𝓞 (rootField ζ)) p))
    (hx : x ∈ primaryWeightSquareSpace hζ) :
    let := rootField_isCyclotomic hζ
    primaryLog (baseRoot_primitive hζ) hp5 x = 0 := by
  let := rootField_isCyclotomic hζ
  exact primaryLog_eq_zero_of_mem_localPowerSpace (baseRoot_primitive hζ) hp5 x hx.2

/-- 次元1・実際の Λ の非零評価から hunit を構成する。
この二つの算術入力は残条件であり、この定理自身の無条件の結論ではない。 -/
theorem primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection (hp5 : 5 ≤ p)
    (hrank : Module.finrank (ZMod p) (weightSquareSpace hζ) = 1)
    (g : weightSquareSpace hζ)
    (hdetect : letI := rootField_isCyclotomic hζ
      primaryLog (baseRoot_primitive hζ) hp5 g ≠ 0) :
    primaryWeightSquareSpace hζ = ⊥ := by
  let := rootField_isCyclotomic hζ
  apply (Submodule.eq_bot_iff (primaryWeightSquareSpace hζ)).mpr
  intro x hx
  have he := eq_zero_of_rank_one_of_log_eq_zero (baseRoot_primitive hζ) hp5
    (weightSquareSpace hζ) hrank g hdetect ⟨x, hx.1⟩
    (primaryWeightSquareSpace_log_eq_zero hζ hp5 x hx)
  exact congrArg Subtype.val he

end RootField
end DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion

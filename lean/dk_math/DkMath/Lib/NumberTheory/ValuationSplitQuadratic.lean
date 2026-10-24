/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.ValuationResidue
import DkMath.Lib.NumberTheory.ValuationTameCharacter

#print "file: DkMath.Lib.NumberTheory.ValuationSplitQuadratic"

/-!
# NOTE-032-005A: 標数2の分裂二次式と分解群の合同

[DkMath.Lib] z²+z=0の根は0または1なので、任意の剰余体自己同型に固定される。
その根へ還元する整元zについては、分解群元σによる差σz−zが非単元となる。
これは整元自体の固定性ではない。実際の固定性には同じ二次式の根条件と分離を追加する。
-/
namespace DkMath.Lib.NumberTheory.ValuationSplitQuadratic
open IsLocalRing ValuationTameCharacter.TameCharacter

/-- [DkMath.Lib] 標数2の分裂式z²+z=0の根を、素体の二元0,1へ分類する。 -/
theorem eq_zero_or_one {k : Type*} [Field k] [CharP k 2] {z : k}
    (hz : z ^ 2 + z = 0) : z = 0 ∨ z = 1 := by
  have hf : z * (z + 1) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl h
  · right
    have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
    linear_combination h - h2

/-- [DkMath.Lib] 剰余が0か1の整元は、全分解群元によって剰余を固定される。
慣性所属やFrobeniusの指定は不要だが、σz=zとは結論しない。 -/
theorem apply_sub_mem_nonunits {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [CharP (ResidueField A) 2]
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A)
    (hquad : residue A (⟨z, hz⟩ : A) ^ 2 + residue A (⟨z, hz⟩ : A) = 0) :
    σ z - z ∈ A.nonunits := by
  have hσz : σ z ∈ A := (apply_mem_iff hσ z).mpr hz
  apply (ValuationResidue.residue_eq_residue_iff_sub_mem_nonunits A hσz hz).mp
  let g : A.decompositionSubgroup K := ⟨σ, hσ⟩
  have he : residue A (⟨σ z, hσz⟩ : A) = g • residue A (⟨z, hz⟩ : A) := by
    change residue A (g • (⟨z, hz⟩ : A)) = g • residue A (⟨z, hz⟩ : A)
    rw [ResidueField.residue_smul]
  rw [he]
  rcases eq_zero_or_one hquad with h | h <;> rw [h] <;> simp

end DkMath.Lib.NumberTheory.ValuationSplitQuadratic

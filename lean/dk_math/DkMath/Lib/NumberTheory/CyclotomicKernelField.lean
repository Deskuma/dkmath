/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicInertia
import DkMath.Lib.NumberTheory.ValuationPrimeExistence
import DkMath.Lib.NumberTheory.ValuationTameCharacter
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.GroupTheory.Index

#print "file: DkMath.Lib.NumberTheory.CyclotomicKernelField"

/-!
# 円分指標の核が固定する実際の円分体

原始 `p` 乗根 `ζ` を同じ代数閉包内で固定する。
`ker χ_p` は `ℚ(ζ)` の実際の fixing subgroup であり、開部分群である。
固定体との一致、円分拡大性、次数 `p-1` を実際の Galois 対応から供給する。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKernelField

-- The absolute Galois group is a named definition of the same AlgEquiv group.
-- Allow elaboration to unfold that definition when crossing the field-theory API.
set_option backward.isDefEq.respectTransparency false

open CyclotomicRootModule ValuationInertia ValuationTameCharacter.TameCharacter
noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- 同じ代数閉包内の、指定した根で生成する実際の体。 -/
abbrev rootField (ζ : AlgebraicClosure ℚ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ {ζ}

omit [Fact p.Prime] in
/-- 同じ具体的な体は数体でもあり、整数環・類群の API に渡せる。 -/
theorem rootField_numberField (ζ : AlgebraicClosure ℚ) : NumberField (rootField ζ) := by
  let : FiniteDimensional ℚ (rootField ζ) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  exact NumberField.of_module_finite ℚ (rootField ζ)

/-- 原始根を固定することと、円分指標値が1であることは同値。 -/
theorem character_eq_one_iff_fix_root {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (σ : Field.absoluteGaloisGroup ℚ) : cyclotomicCharacter p σ = 1 ↔ σ.toAlgHom ζ = ζ := by
  have hp : p.Prime := Fact.out
  let : NeZero p := ⟨hp.ne_zero⟩
  have he := cyclotomicCharacter_spec (K := ℚ) p σ hζ.toRootsOfUnity
  change σ.toAlgHom ζ = ζ ^ (cyclotomicCharacter p σ : ZMod p).val at he
  constructor
  · intro h
    simpa only [h, Units.val_one, ZMod.val_one, pow_one] using he
  · intro h
    have hv : (cyclotomicCharacter p σ : ZMod p).val = 1 :=
      hζ.pow_inj (ZMod.val_lt _) hp.one_lt (by simpa only [pow_one] using he.symm.trans h)
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (cyclotomicCharacter p σ : ZMod p), hv, Nat.cast_one]
    rfl

/-- 同じ根で生成する体の全元の固定性を、根の固定性で判定する。 -/
theorem fixingSubgroup_eq_kernel {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    (rootField ζ).fixingSubgroup = (cyclotomicCharacter (K := ℚ) p).ker := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker]
  refine Iff.trans ?_ (character_eq_one_iff_fix_root hζ σ).symm
  change (∀ x ∈ IntermediateField.adjoin ℚ {ζ}, σ • x = x) ↔ σ • ζ = ζ
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  simp only [Set.mem_singleton_iff, forall_eq]

/-- 指標核と、同じ円分体上の実際の Galois 群との群同型。 -/
def kernelEquiv {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    (cyclotomicCharacter (K := ℚ) p).ker ≃*
      ((AlgebraicClosure ℚ) ≃ₐ[rootField ζ] (AlgebraicClosure ℚ)) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_eq_kernel hζ).symm).trans
    (IntermediateField.fixingSubgroupEquiv (rootField ζ))

/-- この同型は、同じ代数的数への作用を保存する。 -/
theorem kernelEquiv_apply {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (g : (cyclotomicCharacter (K := ℚ) p).ker) (x : AlgebraicClosure ℚ) :
    kernelEquiv hζ g x = g.val.toAlgHom x := rfl

/-- 同じ付値環の分解群は、円分体に基底を移しても同じ元を保つ。 -/
theorem kernelEquiv_mem_decomposition_iff {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (g : (cyclotomicCharacter (K := ℚ) p).ker) :
    kernelEquiv hζ g ∈ A.decompositionSubgroup (rootField ζ) ↔ g.val ∈ A.decompositionSubgroup ℚ := by
  constructor <;> intro h
  · exact ValuationTameCharacter.TameCharacter.mem_decompositionSubgroup_of_forall
      (fun x => ValuationTameCharacter.TameCharacter.apply_mem_iff h x)
  · exact ValuationTameCharacter.TameCharacter.mem_decompositionSubgroup_of_forall
      (fun x => ValuationTameCharacter.TameCharacter.apply_mem_iff h x)

/-- 慣性の所属も同じ整元の剰余合同を用いて双方向に保存する。 -/
theorem kernelEquiv_mem_inertia_iff {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (g : (cyclotomicCharacter (K := ℚ) p).ker) :
    kernelEquiv hζ g ∈ inertiaSubgroupIn A (rootField ζ) ↔ g.val ∈ inertiaSubgroupIn A ℚ := by
  constructor <;> intro h
  · exact mem_inertiaSubgroupIn_of_forall
      (fun x => apply_mem_iff (mem_inertiaSubgroupIn_iff.mp h).1 x)
      (fun _ hx => apply_sub_self_mem_nonunits h hx)
  · exact mem_inertiaSubgroupIn_of_forall
      (fun x => apply_mem_iff (mem_inertiaSubgroupIn_iff.mp h).1 x)
      (fun _ hx => apply_sub_self_mem_nonunits h hx)

/-- 円分指標の核は Krull 位相で実際に開く。 -/
theorem kernel_isOpen : IsOpen ((cyclotomicCharacter (K := ℚ) p).ker : Set (Field.absoluteGaloisGroup ℚ)) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  let : FiniteDimensional ℚ (rootField ζ) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hs := IntermediateField.fixingSubgroup_isOpen (rootField ζ)
  rw [fixingSubgroup_eq_kernel hζ] at hs
  exact hs

/-- 同じ体は実際の `p` 円分拡大である。 -/
theorem rootField_isCyclotomic {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    IsCyclotomicExtension {p} ℚ (rootField ζ) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ)

/-- 実際の円分体は指標核の固定体そのもの。 -/
theorem fixedField_kernel_eq {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    IntermediateField.fixedField (cyclotomicCharacter (K := ℚ) p).ker = rootField ζ := by
  rw [← fixingSubgroup_eq_kernel hζ]
  exact InfiniteGalois.fixedField_fixingSubgroup (rootField ζ)

/-- 指標の全射性は、指定した全ての単元を実際の `p` 上の慣性で実現して得る。 -/
theorem character_surjective : Function.Surjective (cyclotomicCharacter (K := ℚ) p) := by
  obtain ⟨A, hA⟩ := ValuationPrimeExistence.exists_liesOverPrime (L := AlgebraicClosure ℚ) (Fact.out : p.Prime)
  intro a
  obtain ⟨σ, _, hσ⟩ := CyclotomicInertia.exists_inertia_cyclotomic_eq A hA a
  exact ⟨σ, hσ⟩

/-- 指標核の指数は `p-1`。 -/
theorem kernel_index : (cyclotomicCharacter (K := ℚ) p).ker.index = p - 1 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr character_surjective,
    Nat.card_congr (Subgroup.topEquiv (G := (ZMod p)ˣ)).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_units, ZMod.card]

/-- 固定体・指数の実際の Galois 対応から、同じ体の次数を確定する。 -/
theorem rootField_finrank {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    Module.finrank ℚ (rootField ζ) = p - 1 := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, fixingSubgroup_eq_kernel hζ, kernel_index]

end
end DkMath.Lib.NumberTheory.CyclotomicKernelField

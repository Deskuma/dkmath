/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicKernelField
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

#print "file: DkMath.Lib.NumberTheory.CyclotomicCharacterField"

/-!
# 円分指標核上の有限加法指標から実際の次数 `p` の拡大へ

指標の核を絶対 Galois 群へ埋め込み、その固定体を構成する。
開核から有限性、全射性から次数、逆指標の共役則から正規性を得る。
固定体を別の存在仮定へ移さず、元の指標の同じ核を保つ。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicCharacterField

open CyclotomicRootModule CyclotomicKernelField
set_option backward.isDefEq.respectTransparency false
noncomputable section

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)

/-- 同じ指標核を絶対 Galois 群に埋め込んだ実際の部分群。 -/
def kernelInGalois : Subgroup (Field.absoluteGaloisGroup ℚ) :=
  ψ.ker.map (cyclotomicCharacter (K := ℚ) p).ker.subtype

omit [Module (ZMod p) C] in
theorem kernelInGalois_le : kernelInGalois ψ ≤ (cyclotomicCharacter (K := ℚ) p).ker := by
  rintro _ ⟨u, _, rfl⟩
  exact u.property

omit [Module (ZMod p) C] in
/-- 埋込みで元の核を変えない。 -/
theorem mem_kernelInGalois (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    u.val ∈ kernelInGalois ψ ↔ ψ u = 1 := by
  constructor
  · rintro ⟨w, hw, he⟩
    have hwu : w = u := Subtype.ext he
    exact hwu ▸ hw
  · intro h
    exact ⟨u, h, rfl⟩

omit [Module (ZMod p) C] in
/-- 開いた指標核の像は、円分核自身が開くため絶対 Galois 群でも開く。 -/
theorem kernelInGalois_isOpen (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker)) :
    IsOpen (kernelInGalois ψ : Set (Field.absoluteGaloisGroup ℚ)) :=
  kernel_isOpen.isOpenMap_subtype_val _ hopen

/-- 逆指標の共役則から、同じ核は絶対 Galois 群全体で正規になる。 -/
theorem kernelInGalois_normal
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd) :
    (kernelInGalois ψ).Normal := by
  constructor
  rintro _ ⟨u, hu, rfl⟩ σ
  have hχ : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1 := by
    rw [map_mul, map_mul, MonoidHom.mem_ker.mp u.property, mul_one, map_inv, mul_inv_cancel]
  apply (mem_kernelInGalois ψ ⟨σ * u.val * σ⁻¹, hχ⟩).mpr
  have h := hweight σ u hχ
  change ψ u = 1 at hu
  rw [hu] at h
  apply Multiplicative.toAdd.injective
  change (ψ ⟨σ * u.val * σ⁻¹, hχ⟩).toAdd = (0 : C)
  change (ψ ⟨σ * u.val * σ⁻¹, hχ⟩).toAdd = _ • (0 : C) at h
  simpa only [smul_zero] using h

/-- 指標から構成した同じ固定体。 -/
def characterField : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.fixedField (kernelInGalois ψ)

omit [Module (ZMod p) C] in
/-- 零指標なら固定体は元の円分体のままであり、次数 `p` の拡大とはならない。 -/
theorem characterField_one_eq_rootField {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    characterField (1 : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C) = rootField ζ := by
  change IntermediateField.fixedField
    ((1 : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C).ker.map
      (cyclotomicCharacter (K := ℚ) p).ker.subtype) = _
  rw [MonoidHom.ker_one, Subgroup.map_top, Subgroup.range_subtype, fixedField_kernel_eq hζ]

omit [Module (ZMod p) C] in
/-- 開核は閉じてもいるので、無限 Galois 対応で元の核へ正確に戻る。 -/
theorem fixingSubgroup_characterField
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker)) :
    (characterField ψ).fixingSubgroup = kernelInGalois ψ :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨kernelInGalois ψ, (kernelInGalois ψ).isClosed_of_isOpen (kernelInGalois_isOpen ψ hopen)⟩

omit [Module (ZMod p) C] in
/-- 同じ円分体は構成した固定体に含まれる。 -/
theorem rootField_le_characterField {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    rootField ζ ≤ characterField ψ := by
  rw [← fixedField_kernel_eq hζ]
  exact IntermediateField.fixedField_le (kernelInGalois_le ψ)

omit [Module (ZMod p) C] in
/-- 有限性は開核から内部供給する。 -/
theorem characterField_finite
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker)) :
    FiniteDimensional ℚ (characterField ψ) := by
  apply (InfiniteGalois.isOpen_iff_finite (characterField ψ)).mp
  rw [fixingSubgroup_characterField ψ hopen]
  exact kernelInGalois_isOpen ψ hopen

omit [Module (ZMod p) C] in
/-- 構成体の数体構造も、同じ開核から供給する。 -/
theorem characterField_numberField
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker)) :
    NumberField (characterField ψ) := by
  let : FiniteDimensional ℚ (characterField ψ) := characterField_finite ψ hopen
  exact NumberField.of_module_finite ℚ (characterField ψ)

omit [Module (ZMod p) C] in
/-- 指標が全射なら、絶対次数は実際に `#C * (p-1)`。 -/
theorem characterField_finrank
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hsurj : Function.Surjective ψ) :
    Module.finrank ℚ (characterField ψ) = Nat.card C * (p - 1) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, fixingSubgroup_characterField ψ hopen]
  change (ψ.ker.map (cyclotomicCharacter (K := ℚ) p).ker.subtype).index = _
  rw [Subgroup.index_map_subtype, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Nat.card_congr (Subgroup.topEquiv (G := Multiplicative C)).toEquiv, kernel_index]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative C ≃ C)]

/-- 共役則を保つ指標は、実際の有限 Galois 拡大を与える。 -/
theorem characterField_isGalois
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd) :
    IsGalois ℚ (characterField ψ) := by
  apply (InfiniteGalois.normal_iff_isGalois (characterField ψ)).mp
  rw [fixingSubgroup_characterField ψ hopen]
  exact kernelInGalois_normal ψ hweight

/-- 同じ包含による円分体上の拡大構造。 -/
@[instance_reducible] def extensionAlgebra {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) :
    Algebra (rootField ζ) (characterField ψ) :=
  (IntermediateField.inclusion (rootField_le_characterField ψ hζ)).toRingHom.toAlgebra

omit [Module (ZMod p) C] in
/-- 相対次数も同じ実際の包含で計算する。 -/
theorem relative_finrank {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hsurj : Function.Surjective ψ) :
    letI := extensionAlgebra ψ hζ
    Module.finrank (rootField ζ) (characterField ψ) = Nat.card C := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext q; rfl)
  let : FiniteDimensional ℚ (rootField ζ) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let : FiniteDimensional ℚ (characterField ψ) := characterField_finite ψ hopen
  have h := Module.finrank_mul_finrank ℚ (rootField ζ) (characterField ψ)
  rw [rootField_finrank hζ, characterField_finrank ψ hopen hsurj] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (h.trans (Nat.mul_comm _ _))

/-- 同じ包含の上で円分体に基底を変えても Galois 拡大である。 -/
theorem relative_isGalois {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd) :
    letI := extensionAlgebra ψ hζ
    IsGalois (rootField ζ) (characterField ψ) := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext q; rfl)
  let : IsGalois ℚ (characterField ψ) := characterField_isGalois ψ hopen hweight
  exact IsGalois.tower_top_of_isGalois ℚ (rootField ζ) (characterField ψ)

/-- 相対 Galois 群の位数も、元の指標の値域の個数に一致する。 -/
theorem relative_card_aut {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hsurj : Function.Surjective ψ)
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd) :
    letI := extensionAlgebra ψ hζ
    Nat.card ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) = Nat.card C := by
  let := extensionAlgebra ψ hζ
  let : IsScalarTower ℚ (rootField ζ) (characterField ψ) :=
    IsScalarTower.of_algebraMap_eq' (by ext q; rfl)
  let : FiniteDimensional ℚ (characterField ψ) := characterField_finite ψ hopen
  let : IsGalois (rootField ζ) (characterField ψ) := relative_isGalois ψ hζ hopen hweight
  let : FiniteDimensional (rootField ζ) (characterField ψ) :=
    Module.Finite.of_restrictScalars_finite ℚ (rootField ζ) (characterField ψ)
  rw [IsGalois.card_aut_eq_finrank, relative_finrank ψ hζ hopen hsurj]

/-- 位数 `p` の値域へ全射するなら、実際の相対 Galois 群は巡回 `p` 群。 -/
theorem relative_isCyclic {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hsurj : Function.Surjective ψ) (hC : Nat.card C = p)
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd) :
    letI := extensionAlgebra ψ hζ
    IsCyclic ((characterField ψ) ≃ₐ[rootField ζ] (characterField ψ)) := by
  let := extensionAlgebra ψ hζ
  exact isCyclic_of_prime_card ((relative_card_aut ψ hζ hopen hsurj hweight).trans hC)

end
end DkMath.Lib.NumberTheory.CyclotomicCharacterField

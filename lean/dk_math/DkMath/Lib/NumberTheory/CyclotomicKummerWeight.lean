/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicCharacterKummer
import DkMath.Lib.NumberTheory.KummerRadicalCharacter
import DkMath.Lib.Algebra.PowerSubgroup

#print "file: DkMath.Lib.NumberTheory.CyclotomicKummerWeight"

/-!
# 元の指標の Kummer 類の円分二乗作用

同じ指標核の固定体の同じ Kummer 根で比を取り、元の指標を通じて因子化する。
底体を動かす絶対自己同型について、`σ(α)/α^r` が同じ円分体に戻ることを示す。
その `p` 乗から `σ(b)=b^r c^p` を得る。`r` は円分指標の二乗の標準代表元。
これは Kummer 類の重みであって、定数そのものの固有性や算術的消滅ではない。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicKummerWeight

open CyclotomicRootModule CyclotomicKernelField CyclotomicCharacterField CyclicKummer
open DkMath.Lib.Algebra
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- 底体の乗法群を `p` 乗部分群で割った実際の Kummer 類の群。 -/
abbrev KummerClass (F : Type*) [Field F] (p : ℕ) := Fˣ ⧸ powerSubgroup Fˣ p

/-- Kummer 類は全て `p` 乗で1となる。類群の捩れの仮定ではなく、商の定義から従う。 -/
theorem class_pow (F : Type*) [Field F] (p : ℕ) (x : KummerClass F p) : x ^ p = 1 := by
  induction x using Quotient.inductionOn with
  | h u =>
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨u, rfl⟩

/-- 根の空間と同様に、Kummer 類を積を加法とする `F_p` 加群として読む。 -/
instance kummerModule (F : Type*) [Field F] (p : ℕ) :
    Module (ZMod p) (Additive (KummerClass F p)) :=
  AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact class_pow F p x.toMul)

/-- 底体の自己同型が冪部分群を保つことで得る、実際の類への作用。 -/
def classMap {F : Type*} [Field F] (p : ℕ) (f : F →+* F) :
    KummerClass F p →* KummerClass F p :=
  QuotientGroup.map (powerSubgroup Fˣ p) (powerSubgroup Fˣ p) (Units.map f.toMonoidHom) (by
    rintro x ⟨y, rfl⟩
    exact ⟨Units.map f.toMonoidHom y, (map_pow (Units.map f.toMonoidHom) y p).symm⟩)

theorem classMap_mk {F : Type*} [Field F] (p : ℕ) (f : F →+* F) (b : Fˣ) :
    classMap p f (b : KummerClass F p) =
      (QuotientGroup.mk' (powerSubgroup Fˣ p)) (Units.map f.toMonoidHom b) := rfl

/-- 同じ底体自己同型の作用を `F_p` 線形写像として読む。 -/
def classLinearMap {F : Type*} [Field F] (p : ℕ) (f : F →+* F) :
    Additive (KummerClass F p) →ₗ[ZMod p] Additive (KummerClass F p) :=
  (classMap p f).toAdditive.toZModLinearMap p

variable {p : ℕ} [Fact p.Prime] {C : Type*} [AddCommGroup C] [Module (ZMod p) C]
    (ψ : (cyclotomicCharacter (K := ℚ) p).ker →* Multiplicative C)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)

local instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- 同じ原始根を円分体の元として読む。 -/
def baseRoot (ζ : AlgebraicClosure ℚ) : rootField ζ :=
  ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩

include hζ in
omit [Fact p.Prime] in
theorem baseRoot_primitive : IsPrimitiveRoot (baseRoot ζ) p :=
  hζ.of_map_of_injective (rootField ζ).val.injective

/-- 底体の実際の Galois 群上の円分指標。 -/
def baseCharacter : ((rootField ζ) ≃ₐ[ℚ] (rootField ζ)) →* (ZMod p)ˣ :=
  (baseRoot_primitive hζ).autToPow ℚ

/-- 底体の自己同型の実際の絶対持ち上げは、円分指標を保つ。 -/
theorem baseCharacter_lift (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    baseCharacter hζ γ = cyclotomicCharacter p (γ.liftNormal (AlgebraicClosure ℚ)) := by
  have hb := (baseRoot_primitive hζ).autToPow_spec ℚ γ
  have hl := γ.liftNormal_commutes (AlgebraicClosure ℚ) (baseRoot ζ)
  have hc := cyclotomicCharacter_spec (K := ℚ) p
    (γ.liftNormal (AlgebraicClosure ℚ)) hζ.toRootsOfUnity
  have he := congrArg Subtype.val hb
  change ζ ^ (baseCharacter hζ γ : ZMod p).val = (γ (baseRoot ζ)).val at he
  change γ.liftNormal (AlgebraicClosure ℚ) ζ = (γ (baseRoot ζ)).val at hl
  have hp : ζ ^ (baseCharacter hζ γ : ZMod p).val =
      ζ ^ (cyclotomicCharacter p (γ.liftNormal (AlgebraicClosure ℚ)) : ZMod p).val :=
    he.trans (hl.symm.trans hc)
  apply Units.ext
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hp)

variable (P : (letI := extensionAlgebra ψ hζ; Presentation p (rootField ζ) (characterField ψ)))

omit [Module (ZMod p) C] in
/-- 根の `p` 乗は同じ底体の同じ定数である。 -/
theorem radical_pow : letI := extensionAlgebra ψ hζ
    P.radical.val ^ p = P.constant.val := by
  let := extensionAlgebra ψ hζ
  exact congrArg Subtype.val P.radical_pow

omit [Module (ZMod p) C] in
/-- 円分指標核は同じ根の `p` 乗を固定する。 -/
theorem radical_pow_fixed (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    letI := extensionAlgebra ψ hζ
    u.val.toAlgHom (P.radical.val ^ p) = P.radical.val ^ p := by
  let := extensionAlgebra ψ hζ
  rw [radical_pow ψ hζ P]
  exact (kernelEquiv hζ u).commutes P.constant

/-- 同じ根から比を取る実際の `μ_p` 値指標。 -/
def presentationCharacter : (cyclotomicCharacter (K := ℚ) p).ker →*
    rootsOfUnity p (AlgebraicClosure ℚ) := by
  let := extensionAlgebra ψ hζ
  exact KummerRadicalCharacter.radicalCharacter P.radical.val
    (fun h => P.radical_ne_zero (Fact.out : p.Prime).one_lt (Subtype.ext h))
    (radical_pow_fixed ψ hζ P)

omit [Module (ZMod p) C] in
theorem presentationCharacter_coe (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    letI := extensionAlgebra ψ hζ
    ((presentationCharacter ψ hζ P u).val : AlgebraicClosure ℚ) =
      u.val.toAlgHom P.radical.val / P.radical.val := rfl

omit [Module (ZMod p) C] in
/-- Kummer 比の核は、元の加法指標の核と正確に一致する。 -/
theorem presentationCharacter_kernel
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker)) :
    (presentationCharacter ψ hζ P).ker = ψ.ker := by
  let := extensionAlgebra ψ hζ
  ext u
  change presentationCharacter ψ hζ P u = 1 ↔ ψ u = 1
  exact (KummerRadicalCharacter.radicalCharacter_eq_one_iff P.radical.val
    (fun h => P.radical_ne_zero (Fact.out : p.Prime).one_lt (Subtype.ext h))
    (radical_pow_fixed ψ hζ P) u).trans
    (CyclotomicCharacterKummer.character_eq_one_iff_fix_radical ψ hζ hopen P u).symm

variable (hsurj : Function.Surjective ψ)
    (hopen : IsOpen (ψ.ker : Set (cyclotomicCharacter (K := ℚ) p).ker))
    (hweight : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ u : (cyclotomicCharacter (K := ℚ) p).ker,
      ∀ hu : cyclotomicCharacter p (σ * u.val * σ⁻¹) = 1,
      (ψ ⟨σ * u.val * σ⁻¹, hu⟩).toAdd = (cyclotomicCharacter p σ⁻¹ : ZMod p) • (ψ u).toAdd)

include hsurj hopen hweight in
/-- 二つの円分因子を保った、同じ根の共役比の公式。 -/
theorem conjugate_ratio (σ : Field.absoluteGaloisGroup ℚ)
    (u : (cyclotomicCharacter (K := ℚ) p).ker) :
    letI := extensionAlgebra ψ hζ
    u.val.toAlgHom (σ.toAlgHom P.radical.val) / σ.toAlgHom P.radical.val =
      (u.val.toAlgHom P.radical.val / P.radical.val) ^
        ((cyclotomicCharacter p σ : ZMod p) ^ 2).val := by
  let := extensionAlgebra ψ hζ
  exact KummerRadicalCharacter.conjugate_ratio P.radical.val
    (fun h => P.radical_ne_zero (Fact.out : p.Prime).one_lt (Subtype.ext h))
    (radical_pow_fixed ψ hζ P) ψ hsurj
    (presentationCharacter_kernel ψ hζ P hopen).ge hweight σ u

include hsurj hopen hweight in
/-- `σ(α)/α^r` は全ての円分指標核で固定され、同じ円分体に降りる。 -/
theorem conjugate_radical_div_mem (σ : Field.absoluteGaloisGroup ℚ) :
    letI := extensionAlgebra ψ hζ
    σ.toAlgHom P.radical.val / P.radical.val ^
      ((cyclotomicCharacter p σ : ZMod p) ^ 2).val ∈ rootField ζ := by
  let := extensionAlgebra ψ hζ
  let α := P.radical.val
  let r := ((cyclotomicCharacter p σ : ZMod p) ^ 2).val
  have hα : α ≠ 0 := fun h => P.radical_ne_zero (Fact.out : p.Prime).one_lt (Subtype.ext h)
  apply (fixedField_kernel_eq hζ).le
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  intro g hg
  let u : (cyclotomicCharacter (K := ℚ) p).ker := ⟨g, hg⟩
  have hu : u.val.toAlgHom α ≠ 0 := (map_ne_zero u.val.toAlgHom).mpr hα
  have hσ : σ.toAlgHom α ≠ 0 := (map_ne_zero σ.toAlgHom).mpr hα
  have he := conjugate_ratio ψ hζ P hsurj hopen hweight σ u
  change u.val.toAlgHom (σ.toAlgHom α) / σ.toAlgHom α =
    (u.val.toAlgHom α / α) ^ r at he
  change u.val.toAlgHom (σ.toAlgHom α / α ^ r) = σ.toAlgHom α / α ^ r
  rw [map_div₀, map_pow]
  rw [div_pow] at he
  field_simp at he ⊢
  exact he

include hsurj hopen hweight in
/-- Kummer 定数の円分二乗則。補正因子は同じ円分体の実際の非零元。 -/
theorem constant_weight_square (σ : Field.absoluteGaloisGroup ℚ) :
    letI := extensionAlgebra ψ hζ
    ∃ c : rootField ζ, c ≠ 0 ∧
      σ.toAlgHom P.constant.val = P.constant.val ^
        ((cyclotomicCharacter p σ : ZMod p) ^ 2).val * c.val ^ p := by
  let := extensionAlgebra ψ hζ
  let α := P.radical.val
  let r := ((cyclotomicCharacter p σ : ZMod p) ^ 2).val
  let c : rootField ζ := ⟨σ.toAlgHom α / α ^ r,
    conjugate_radical_div_mem ψ hζ P hsurj hopen hweight σ⟩
  have hα : α ≠ 0 := fun h => P.radical_ne_zero (Fact.out : p.Prime).one_lt (Subtype.ext h)
  have hc : c ≠ 0 := by
    intro h
    have hz := congrArg Subtype.val h
    change σ.toAlgHom α / α ^ r = 0 at hz
    exact div_ne_zero ((map_ne_zero σ.toAlgHom).mpr hα) (pow_ne_zero r hα) hz
  refine ⟨c, hc, ?_⟩
  have hp : α ^ p = P.constant.val := radical_pow ψ hζ P
  change σ.toAlgHom P.constant.val = P.constant.val ^ r * (σ.toAlgHom α / α ^ r) ^ p
  rw [div_pow, ← pow_mul, Nat.mul_comm r p, pow_mul, hp, ← map_pow, hp]
  exact (mul_div_cancel₀ _ (pow_ne_zero r
    (fun h => P.constant_ne_zero (Fact.out : p.Prime).one_lt (Subtype.ext h)))).symm

include hsurj hopen hweight in
/-- 底体の任意の自己同型について、同じ Kummer 定数が二乗の重みを持つ。
絶対持ち上げと指標の一致は内部で供給する。 -/
theorem base_constant_weight_square (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    letI := extensionAlgebra ψ hζ
    ∃ c : rootField ζ, c ≠ 0 ∧ γ P.constant =
      P.constant ^ ((baseCharacter hζ γ : ZMod p) ^ 2).val * c ^ p := by
  let := extensionAlgebra ψ hζ
  let σ : Field.absoluteGaloisGroup ℚ := γ.liftNormal (AlgebraicClosure ℚ)
  obtain ⟨c, hc, he⟩ := constant_weight_square ψ hζ P hsurj hopen hweight σ
  refine ⟨c, hc, ?_⟩
  apply Subtype.ext
  have hl := γ.liftNormal_commutes (AlgebraicClosure ℚ) P.constant
  change σ.toAlgHom P.constant.val = (γ P.constant).val at hl
  rw [hl, ← baseCharacter_lift hζ γ] at he
  exact he

/-- 同じ非零定数を、底体の実際の乗法群の元として読む。 -/
def constantUnit : (rootField ζ)ˣ := by
  let := extensionAlgebra ψ hζ
  exact Units.mk0 P.constant (P.constant_ne_zero (Fact.out : p.Prime).one_lt)

/-- 根の選択で得た同じ定数の Kummer 類。 -/
def constantClass : KummerClass (rootField ζ) p :=
  (constantUnit ψ hζ P : KummerClass (rootField ζ) p)

omit [Module (ZMod p) C] in
/-- 既約表示から得た類は自明でない。零類の消滅を入力にしない。 -/
theorem constantClass_ne_one : constantClass ψ hζ P ≠ 1 := by
  let := extensionAlgebra ψ hζ
  intro h
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff (constantUnit ψ hζ P)).mp h
  have he := congrArg (fun u : (rootField ζ)ˣ => (u : rootField ζ)) hc
  exact P.constant_not_pow (Fact.out : p.Prime).ne_one (c : rootField ζ) he

include hsurj hopen hweight in
/-- 同じ非自明 Kummer 類は、底体の全自己同型について円分指標の二乗で変換する。 -/
theorem constantClass_weight_square (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    classMap p γ.toRingHom (constantClass ψ hζ P) =
      constantClass ψ hζ P ^ ((baseCharacter hζ γ : ZMod p) ^ 2).val := by
  let := extensionAlgebra ψ hζ
  obtain ⟨c, hc, he⟩ := base_constant_weight_square ψ hζ P hsurj hopen hweight γ
  let u : (rootField ζ)ˣ := Units.mk0 c hc
  have hu : Units.map γ.toRingHom.toMonoidHom (constantUnit ψ hζ P) =
      constantUnit ψ hζ P ^ ((baseCharacter hζ γ : ZMod p) ^ 2).val * u ^ p := by
    apply Units.ext
    exact he
  change (QuotientGroup.mk' (powerSubgroup (rootField ζ)ˣ p))
    (Units.map γ.toRingHom.toMonoidHom (constantUnit ψ hζ P)) = _
  change (↑(Units.map γ.toRingHom.toMonoidHom (constantUnit ψ hζ P)) :
    KummerClass (rootField ζ) p) = _
  rw [hu, QuotientGroup.mk_mul, QuotientGroup.mk_pow]
  have hp : (u ^ p : (rootField ζ)ˣ) ∈ powerSubgroup (rootField ζ)ˣ p := ⟨u, rfl⟩
  rw [(QuotientGroup.eq_one_iff _).mpr hp, mul_one]
  rfl

/-- 同じ Kummer 類を加法的な空間のベクトルとして読む。 -/
def constantVector : Additive (KummerClass (rootField ζ) p) :=
  Additive.ofMul (constantClass ψ hζ P)

omit [Module (ZMod p) C] in
theorem constantVector_ne_zero : constantVector ψ hζ P ≠ 0 := by
  intro h
  exact constantClass_ne_one ψ hζ P (congrArg Additive.toMul h)

include hsurj hopen hweight in
/-- 同じ非零ベクトルに対する、`F_p` 線形な `ω²` 固有条件。 -/
theorem constantVector_weight_square (γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ)) :
    classLinearMap p γ.toRingHom (constantVector ψ hζ P) =
      (baseCharacter hζ γ : ZMod p) ^ 2 • constantVector ψ hζ P := by
  apply Additive.toMul.injective
  let a : ZMod p := (baseCharacter hζ γ : ZMod p) ^ 2
  have hs (x : Additive (KummerClass (rootField ζ) p)) :
      (a • x).toMul = x.toMul ^ a.val := by
    rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, toMul_nsmul]
    simp only [ZMod.natCast_zmod_val]
  change classMap p γ.toRingHom (constantClass ψ hζ P) =
    (a • constantVector ψ hζ P).toMul
  rw [hs]
  exact constantClass_weight_square ψ hζ P hsurj hopen hweight γ

end
end DkMath.Lib.NumberTheory.CyclotomicKummerWeight

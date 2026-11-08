# NOTE-032 教科書 — 安定付値から tail 体の正確な冪根へ

日付: 2026-11-08。最新レビューと模範解答を照合し、5段階を実装した。
今回は実際の tail 体 E∞ と、その任意の実際の上位中間体 E について

    ∀a∈E, ∀n≥0, ∃b∈E, b^(p^n)=a

を証明する。p,q は異なる素数、A は ℚ̄ の q 上の付値環。
E∞=ℚ(K₀,{z | ∃n,z^(p^n)=q})、K₀=ℚ̄^I は前回構成した同じ体である。
**無条件一般 hno は未完成。体の乗法群の p 可除性と、慣性群の p 可除性は異なる命題である。**

以下の5 Lean ブロックは production の全文と一致する。
全ブロックの import 直後に `#print "file: 正確なモジュール名"` を保持した。
DkMath の Lake 環境で、各ブロックを別ファイルにコピーして検査できる。
5モジュールは全て汎用 Lib 層に置き、FLT モジュールに依存しない。

## 1. 元の付値環を保存することを証明する

分解群 D は Krull 位相で閉である。各代数的元の開固定部分群の剰余類を使い、
{σ | σ(x)∈A} の閉性を示す。A の元全体と逆作用について交差すれば D の閉性を得る。
I⊆D と無限 Galois 対応から、K₀ の固定部分群は D に含まれる。
従って K₀⊆E の上の自己同型は A を保存する。
`overfield_stable` は安定性を仮定せず、実際の固定体包含から導く。

## 2. 引き戻した環 B=A∩E の Hensel 性

一般補題は明示的な安定性から Hensel 性を証明する。
単根の持ち上げを仮定するのではなく、代数閉包内でモニック多項式を分解する。
全ての根は整性から A に属する。剰余根の重複度が1なので、指定された剰余を持つ根は一つ。
E 上の任意の自己同型がその根を保つため、無限 Galois 対応で根が E に降下する。
`overfield_henselian` は第1段階で安定性を内部供給し、実際の B の Hensel 性を証明する。

## 3. 単元近似を正確な単元根に変える

f=X^p-u、f'=pX^(p-1) を使う。
p≠q より p は B の単元であり、近似根 z も単元なので f'(z) が可逆。
前回の z^p-u∈𝔪_B と第2段階を合わせ、w^p=u を得る。
一般 Hensel 補題は w-z∈𝔪_B も保持する。
`exact_unit_pRoot` の公開入力には、Henselian 性や近似根 provider はない。
元の A、q 上の住所、固定体包含、元の単元だけで正確な根を構成する。

## 4. 値群の p 可除性を根の塔から得る

有理係数の消去多項式の項の付値を比較する。和が零なので最大値を取る項が一つだけにはならない。
二つの項の値の等式と有理数の q 付値から

    v(a)^n=v(q)^m, n>0, m∈ℤ

を得る。n=p^j n'、p∤n' と分解し、r^(p^(j+1))=q を同じ体内から選ぶ。
値群に非自明な有限位数元がないことと Bezout 係数を使い、

    ∃b₀≠0, v(a)=v(b₀)^p

を証明する。この一般補題の根の塔仮定と代数性は明示する。
実際の endpoint では、同じ tail 体の定義と ℚ̄ の代数性から内部供給する。

## 5. tail 体と全上位体での正確な冪根

a≠0 に対し u=a/b₀^p と置くと v(u)=1、従って u は B の単元。
正確な単元根 w^p=u を取り、b=b₀w とすれば b^p=a。
`tailOverfield_exact_pRoot` は、一般降下補題の安定性・代数性・根の塔・単元近似を全て内部供給する。
公開入力は p,q の素数性、p≠q、実際の q 上の住所、E∞⊆E、a≠0 のみ。
特に hstab/hres/hroot/halg/hhenselian/hclass のような追加 provider を要求しない。
零の場合を加えた `tailOverfield_power_surjective` と、その反復による
`tailOverfield_primePower_surjective` も実装した。各根は同じ E 内に属する。

## 証明境界と次の算術課題

完了: 同じ固定体上の付値安定性、実際の引き戻し環の Hensel 性、正確な単元根、
値の正規化、実際の tail 上位体の全正 p 冪写像の全射性。

未完了: tail を固定する慣性部分群の p 可除性への Galois/Kummer 輸送、
根指標の核から Frey 共通商核への包含、共通商 H の巡回性と単一評価、
連続 H¹ 比較、hclass の算術的供給、大域算術排除、一般 hno の無条件閉鎖。
体内で冪根が存在するだけで、群内の冪根や核包含を結論していない。

25個の新規宣言について再帰依存・標準公理監査を追加した。
実際の endpoint 8個では追加 provider がないことも公開 binder で検査する。
検証結果は `evidence/validation-note032-exact-radical-roots.txt`。
模範解答の参照コミットと SHA-256 は同じ evidence の reference audit に記録する。

## 教科書 Lean コード全文

### 1. DkMath.Lib.NumberTheory.InertiaFixedValuationStability

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalTailField
import Mathlib.FieldTheory.Galois.Infinite

#print "file: DkMath.Lib.NumberTheory.InertiaFixedValuationStability"

/-! # 慣性固定体上の付値安定性
分解群の Krull 閉性から導く。安定性を新しい入力として要求しない。 -/
namespace DkMath.Lib.NumberTheory.InertiaStability
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
theorem isClosed_apply_mem [Algebra.IsIntegral K L] (A : ValuationSubring L) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | σ x ∈ A} := by
  rw [← isOpen_compl_iff]
  have hcompl : {σ : L ≃ₐ[K] L | σ x ∈ A}ᶜ =
      ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | σ x ∉ A},
        σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro h
      refine ⟨σ, h, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      intro hA
      apply h₀
      have : σ₀ x = σ x := by simpa [AlgEquiv.smul_def] using hx.symm
      rwa [this]
  rw [hcompl]
  exact isOpen_biUnion fun σ₀ _ =>
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_decompositionSubgroup [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) := by
  have hS : IsClosed {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    have hset : {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} =
        ⋂ x ∈ (A : Set L), {σ : L ≃ₐ[K] L | σ x ∈ A} := by
      ext σ; simp
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_apply_mem A x
  have hset : ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) =
      {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} ∩
        (fun σ : L ≃ₐ[K] L => σ⁻¹) ⁻¹' {σ : L ≃ₐ[K] L | ∀ x ∈ A, σ x ∈ A} := by
    ext σ
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · intro hσ
      have h : σ • A = A := hσ
      constructor
      · intro x hx
        have hmem : σ • x ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ x A hx
        rw [h] at hmem
        simpa [AlgEquiv.smul_def] using hmem
      · intro x hx
        rw [← h] at hx
        have := ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.mp hx
        simpa [AlgEquiv.smul_def] using this
    · rintro ⟨h₁, h₂⟩
      change σ • A = A
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      constructor
      · intro hy
        have := h₁ _ hy
        simpa [AlgEquiv.smul_def, smul_inv_smul] using this
      · intro hy
        simpa [AlgEquiv.smul_def] using h₂ y hy
  rw [hset]
  exact hS.inter (hS.preimage continuous_inv)

theorem fixingSubgroup_fixedField_map_inertia_le [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) :
    (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup ≤
      A.decompositionSubgroup K := by
  have hle : (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ≤
      A.decompositionSubgroup K := by
    rintro σ ⟨τ, _, rfl⟩
    exact τ.2
  have hff : IntermediateField.fixedField (A.decompositionSubgroup K) ≤
      IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype) :=
    IntermediateField.fixedField_le hle
  have hfix := IntermediateField.fixingSubgroup_antitone hff
  refine hfix.trans (le_of_eq ?_)
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨A.decompositionSubgroup K, isClosed_decompositionSubgroup A⟩

theorem smul_eq_self_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField
        ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype)).fixingSubgroup) :
    σ • A = A :=
  fixingSubgroup_fixedField_map_inertia_le A hσ


/-- 元の慣性固定体を含む中間体上の自己同型は、元の付値環を保存する。 -/
theorem overfield_stable (A : ValuationSubring (AlgebraicClosure ℚ))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : InertiaResidue.fixedField A ≤ E)
    (σ : AlgebraicClosure ℚ ≃ₐ[E] AlgebraicClosure ℚ)
    (x : AlgebraicClosure ℚ) (hx : x ∈ A) : σ x ∈ A := by
  let σ₀ := σ.restrictScalars ℚ
  have hfix : σ₀ ∈ (InertiaResidue.fixedField A).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    change σ y = y
    have he : y = algebraMap E (AlgebraicClosure ℚ) ⟨y, hE hy⟩ := rfl
    rw [he, AlgEquiv.commutes]
  have hs : σ₀ • A = A := smul_eq_self_of_mem_fixingSubgroup A σ₀ hfix
  have hm := ValuationSubring.smul_mem_pointwise_smul σ₀ x A hx
  rw [hs] at hm
  exact hm
end DkMath.Lib.NumberTheory.InertiaStability

```

### 2. DkMath.Lib.NumberTheory.StableValuationHenselian

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.InertiaFixedValuationStability
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

#print "file: DkMath.Lib.NumberTheory.StableValuationHenselian"

/-! # 安定付値の Hensel 性
単根の全ての共役を比較し、唯一の剰余根を固定体へ降下する。 -/
namespace DkMath.Lib.NumberTheory.StableValuation
noncomputable section
open Polynomial
variable {L : Type*} [Field L]

theorem isUnit_iff_inv_mem (P : ValuationSubring L) (y : P) (hy : (y : L) ≠ 0) :
    IsUnit y ↔ (y : L)⁻¹ ∈ P := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : Pˣ) : P) * y = 1 := by rw [← hu, Units.inv_mul]
    have h1' := congrArg ((↑) : P → L) h1
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1'
    have h2 : (((u⁻¹ : Pˣ) : P) : L) = (y : L)⁻¹ := eq_inv_of_mul_eq_one_left h1'
    rw [← h2]; exact SetLike.coe_mem _
  · intro h
    exact IsUnit.of_mul_eq_one ⟨(y : L)⁻¹, h⟩ (Subtype.ext (mul_inv_cancel₀ hy))

theorem mem_maximalIdeal_iff (P : ValuationSubring L) (y : P) :
    y ∈ IsLocalRing.maximalIdeal P ↔ (y : L) = 0 ∨ (y : L)⁻¹ ∉ P := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  by_cases hy : (y : L) = 0
  · have : y = 0 := Subtype.ext hy
    simp [this]
  · rw [isUnit_iff_inv_mem P y hy]; simp [hy]

variable {K : Type*} [Field K] [Algebra K L]

theorem mem_maximalIdeal_iff_map (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P) (σ : L ≃ₐ[K] L) (y : L) (hy : y ∈ P) :
    (⟨y, hy⟩ : P) ∈ IsLocalRing.maximalIdeal P ↔ (⟨σ y, hstab σ y hy⟩ : P) ∈ IsLocalRing.maximalIdeal P := by
  rw [mem_maximalIdeal_iff, mem_maximalIdeal_iff]
  change (y = 0 ∨ y⁻¹ ∉ P) ↔ (σ y = 0 ∨ (σ y)⁻¹ ∉ P)
  have h0 : σ y = 0 ↔ y = 0 := ⟨fun h => σ.injective (h.trans (map_zero σ).symm), fun h => by rw [h, map_zero]⟩
  rw [h0, ← map_inv₀]
  apply or_congr Iff.rfl
  rw [not_iff_not]
  constructor
  · exact hstab σ _
  · intro h
    have := hstab σ.symm _ h
    rwa [AlgEquiv.symm_apply_apply] at this

theorem hensel_of_stable [IsAlgClosed L] [IsGalois K L] (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P) (R : ValuationSubring K)
    (hR : ∀ k : K, k ∈ R ↔ algebraMap K L k ∈ P) (f : R[X]) (hf : f.Monic) (a₀ : R)
    (ha₀ : f.eval a₀ ∈ IsLocalRing.maximalIdeal R) (hunit : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  classical
  let ψ : R →+* P :=
    { toFun := fun k => ⟨algebraMap K L k, (hR k).mp k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hψ : ∀ k : R, ((ψ k : P) : L) = algebraMap K L k := fun k => rfl
  let θ : R →+* L := P.subtype.comp ψ
  have hθ : ∀ k : R, θ k = algebraMap K L k := fun k => rfl
  have hθinj : Function.Injective θ := fun a b h => Subtype.ext ((algebraMap K L).injective h)
  have hrefl : ∀ k : R, IsUnit (ψ k) → IsUnit k := by
    intro k hk
    have hk0 : ((ψ k : P) : L) ≠ 0 := by
      intro h0
      have : ψ k = 0 := Subtype.ext h0
      rw [this] at hk
      exact not_isUnit_zero hk
    have hinv : (algebraMap K L k)⁻¹ ∈ P := (isUnit_iff_inv_mem P (ψ k) hk0).mp hk
    have hk0' : (k : K) ≠ 0 := by
      intro h; apply hk0; rw [hψ, h, map_zero]
    have hmem : (k : K)⁻¹ ∈ R := by
      rw [hR, map_inv₀]; exact hinv
    exact IsUnit.of_mul_eq_one ⟨(k : K)⁻¹, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hk0'))
  have hmax : ∀ k : R, k ∈ IsLocalRing.maximalIdeal R → ψ k ∈ IsLocalRing.maximalIdeal P := by
    intro k hk
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hk ⊢
    exact fun h => hk (hrefl k h)
  set fP : P[X] := f.map ψ with hfP
  set fL : L[X] := f.map θ with hfL
  have hfLP : fL = fP.map P.subtype := by rw [hfP, Polynomial.map_map]
  have hfLmonic : fL.Monic := hf.map θ
  have hfL0 : fL ≠ 0 := hfLmonic.ne_zero
  have hsplit : fL.Splits := IsAlgClosed.splits fL
  have hInt : P.valuation.Integers P :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => P.valuation_le_one x
      exists_of_le_one := fun r hr => ⟨⟨r, (P.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have hrootP : ∀ α ∈ fL.roots, α ∈ P := by
    intro α hα
    have hint : IsIntegral P α := by
      refine ⟨fP, hf.map ψ, ?_⟩
      have := (mem_roots hfL0).mp hα
      rwa [IsRoot.def, hfLP, eval_map] at this
    have := hInt.mem_of_integral hint
    rw [Valuation.mem_integer_iff] at this
    exact (P.valuation_le_one_iff α).mp this
  set S : Multiset L := fL.roots with hS
  obtain ⟨SP, hSPmap⟩ : ∃ SP : Multiset P, SP.map P.subtype = S :=
    ⟨S.attach.map fun x => (⟨x.1, hrootP x.1 x.2⟩ : P), by
      rw [Multiset.map_map]; exact Multiset.attach_map_val S⟩
  have hmemSP : ∀ (x : L) (hx : x ∈ P), x ∈ S → (⟨x, hx⟩ : P) ∈ SP := by
    intro x hx hxS
    rw [← hSPmap, Multiset.mem_map] at hxS
    obtain ⟨b, hb, hbx⟩ := hxS
    have : b = ⟨x, hx⟩ := Subtype.ext hbx
    rwa [this] at hb
  have hfPprod : fP = (SP.map fun b => X - C b).prod := by
    apply Polynomial.map_injective P.subtype Subtype.val_injective
    rw [← hfLP, Polynomial.map_multiset_prod, Multiset.map_map]
    have hcomp : ((fun x => Polynomial.map P.subtype x) ∘ fun b : P => X - C b) =
        (fun a : L => X - C a) ∘ P.subtype := by
      funext b; simp
    rw [hcomp, ← Multiset.map_map, hSPmap]
    exact hsplit.eq_prod_roots_of_monic hfLmonic
  let π : P →+* IsLocalRing.ResidueField P := IsLocalRing.residue P
  set fk := fP.map π with hfk
  have hfkprod : fk = ((SP.map π).map fun c => X - C c).prod := by
    rw [hfk, hfPprod, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp
  have hfkroots : fk.roots = SP.map π := by rw [hfkprod, roots_multiset_prod_X_sub_C]
  have hfk0 : fk ≠ 0 := ((hf.map ψ).map π).ne_zero
  set abar := π (ψ a₀) with habar
  have heval : fk.eval abar = 0 := by
    rw [hfk, eval_map, eval₂_hom, hfP, eval_map, eval₂_hom]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (hmax _ ha₀)
  have hderiv : fk.derivative.eval abar ≠ 0 := by
    rw [hfk, derivative_map, eval_map, eval₂_hom, hfP, derivative_map, eval_map, eval₂_hom, Ne,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hunit.map ψ
  have hmult : fk.rootMultiplicity abar = 1 := by
    have hpos : 0 < fk.rootMultiplicity abar := (rootMultiplicity_pos hfk0).mpr heval
    have hle : ¬ 1 < fk.rootMultiplicity abar := by
      rw [one_lt_rootMultiplicity_iff_isRoot hfk0, not_and_or]
      exact Or.inr hderiv
    omega
  have hcount : (SP.map π).count abar = 1 := by rw [← hfkroots, count_roots, hmult]
  rw [Multiset.count_map] at hcount
  obtain ⟨b₁, hb₁⟩ := Multiset.card_eq_one.mp hcount
  have hb₁mem : b₁ ∈ SP.filter (fun b => abar = π b) := by rw [hb₁]; exact Multiset.mem_singleton_self _
  rw [Multiset.mem_filter] at hb₁mem
  obtain ⟨hb₁S, hb₁red⟩ := hb₁mem
  have hb₁root : (b₁ : L) ∈ S := by rw [← hSPmap]; exact Multiset.mem_map_of_mem _ hb₁S
  have hb₁sub : b₁ - ψ a₀ ∈ IsLocalRing.maximalIdeal P := Ideal.Quotient.eq.mp hb₁red.symm
  have hfix : ∀ σ : L ≃ₐ[K] L, σ (b₁ : L) = b₁ := by
    intro σ
    have hmapfL : fL.map (σ : L →+* L) = fL := by
      rw [hfL, Polynomial.map_map]
      congr 1
      ext k
      simp [hθ]
    have hσroot : σ (b₁ : L) ∈ S := by
      have hSσ : S.map (σ : L →+* L) = S := by
        rw [hS, ← hsplit.roots_map_of_injective (σ : L →+* L).injective, hmapfL]
      rw [← hSσ]
      exact Multiset.mem_map_of_mem _ hb₁root
    have hσP : σ (b₁ : L) ∈ P := hstab σ _ b₁.2
    have hσred : π ⟨σ (b₁ : L), hσP⟩ = abar := by
      have h2 := (mem_maximalIdeal_iff_map P hstab σ ((b₁ - ψ a₀ : P) : L) (b₁ - ψ a₀).2).mp
        (by
          simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb₁sub
          exact hb₁sub)
      have h3 : (⟨σ (b₁ : L), hσP⟩ : P) - ψ a₀ ∈ IsLocalRing.maximalIdeal P := by
        convert h2 using 1
        apply Subtype.ext
        simp [hψ, map_sub]
      exact (Ideal.Quotient.eq.mpr h3)
    have hmemT : (⟨σ (b₁ : L), hσP⟩ : P) ∈ SP.filter (fun b => abar = π b) := by
      rw [Multiset.mem_filter]
      refine ⟨?_, hσred.symm⟩
      exact hmemSP _ hσP hσroot
    rw [hb₁, Multiset.mem_singleton] at hmemT
    exact congrArg Subtype.val hmemT
  have hbot : (b₁ : L) ∈ (⊥ : IntermediateField K L) := by
    rw [← InfiniteGalois.fixedField_bot, IntermediateField.mem_fixedField_iff]
    exact fun σ _ => hfix σ
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
  have hkR : k ∈ R := by
    rw [hR, hk]; exact b₁.2
  have hψk : ψ ⟨k, hkR⟩ = b₁ := Subtype.ext hk
  refine ⟨⟨k, hkR⟩, ?_, ?_⟩
  · apply hθinj
    rw [map_zero, ← eval₂_hom, ← eval_map]
    change fL.eval (algebraMap K L k) = 0
    rw [hk]
    exact (mem_roots hfL0).mp hb₁root
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hm : ψ (⟨k, hkR⟩ - a₀) ∈ IsLocalRing.maximalIdeal P := by
      rw [map_sub, hψk]; exact hb₁sub
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm (hu.map ψ)

theorem henselianLocalRing_comap [IsAlgClosed L] [IsGalois K L] (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P) :
    HenselianLocalRing (P.comap (algebraMap K L)) where
  is_henselian f hf a₀ ha₀ hunit :=
    hensel_of_stable P hstab (P.comap (algebraMap K L)) (fun _ => Iff.rfl) f hf a₀ ha₀ hunit


/-- 実際の慣性固定体の上位体で Hensel 性を内部供給する。 -/
theorem overfield_henselian (A : ValuationSubring (AlgebraicClosure ℚ))
    (E : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : InertiaResidue.fixedField A ≤ E) :
    HenselianLocalRing (A.comap (algebraMap E (AlgebraicClosure ℚ))) :=
  henselianLocalRing_comap A (InertiaStability.overfield_stable A E hE)
end
end DkMath.Lib.NumberTheory.StableValuation

```

### 3. DkMath.Lib.NumberTheory.InertiaUnitExactRoots

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.StableValuationHenselian

#print "file: DkMath.Lib.NumberTheory.InertiaUnitExactRoots"

/-! # 単元近似から体内の正確な p 乗根へ
p ≠ q が導関数の可逆性を保証する。 -/
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open Polynomial ValuationInertia
theorem exists_pow_eq_of_pow_sub_mem {R : Type*} [CommRing R] [HenselianLocalRing R] (n : ℕ)
    (hn : IsUnit (n : R)) (u z : R) (hu : IsUnit u) (hz : z ^ n - u ∈ IsLocalRing.maximalIdeal R) :
    ∃ v : R, v ^ n = u ∧ v - z ∈ IsLocalRing.maximalIdeal R := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hn
    exact not_isUnit_zero hn
  have hzn : IsUnit (z ^ n) := by
    by_contra h
    have hmem : z ^ n ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
    have : u ∈ IsLocalRing.maximalIdeal R := by
      have := Ideal.sub_mem _ hmem hz
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hu
  have hzu : IsUnit z := (isUnit_pow_iff hn0).mp hzn
  have hmonic : (X ^ n - C u : R[X]).Monic := monic_X_pow_sub_C u hn0
  have heval : (X ^ n - C u : R[X]).eval z ∈ IsLocalRing.maximalIdeal R := by
    simpa using hz
  have hderiv : IsUnit ((X ^ n - C u : R[X]).derivative.eval z) := by
    have : (X ^ n - C u : R[X]).derivative.eval z = (n : R) * z ^ (n - 1) := by
      simp [derivative_X_pow]
    rw [this]
    exact hn.mul (hzu.pow _)
  obtain ⟨v, hv, hvz⟩ := HenselianLocalRing.is_henselian (X ^ n - C u) hmonic z heval hderiv
  refine ⟨v, ?_, hvz⟩
  have := hv
  rw [IsRoot.def] at this
  simpa [sub_eq_zero] using this


/-- 異なる剰余標数の素数は、引き戻した付値環でも単元。 -/
theorem prime_isUnit_comap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsUnit (p : A.comap (algebraMap E (AlgebraicClosure ℚ))) := by
  let R := A.comap (algebraMap E (AlgebraicClosure ℚ))
  have hv := InertiaRadical.valuation_prime_eq_one hp hq hpq A hA
  have hi : (p : E)⁻¹ ∈ R := by
    change algebraMap E (AlgebraicClosure ℚ) (p : E)⁻¹ ∈ A
    rw [map_inv₀, map_natCast, ← A.valuation_le_one_iff, map_inv₀, hv, inv_one]
  exact IsUnit.of_mul_eq_one ⟨(p : E)⁻¹, hi⟩
    (Subtype.ext (mul_inv_cancel₀ (by exact_mod_cast hp.ne_zero)))

/-- 元の固定体の上位体に属する、正確な単元 p 乗根。Hensel 入力は内部で証明する。 -/
theorem exact_unit_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : fixedField A ≤ E)
    (u : A.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ w : A.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit w ∧ w ^ p = u := by
  let := StableValuation.overfield_henselian A E hE
  obtain ⟨z, hz⟩ := approximate_unit_pRoot hp hq hpq A hA E hE u hu
  obtain ⟨w, hw, _⟩ := exists_pow_eq_of_pow_sub_mem p
    (prime_isUnit_comap hp hq hpq A hA E) u z hu hz
  exact ⟨w, (isUnit_pow_iff hp.ne_zero).mp (hw.symm ▸ hu), hw⟩
end
end DkMath.Lib.NumberTheory.InertiaResidue

```

### 4. DkMath.Lib.NumberTheory.ValuationRadicalDivisibility

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.InertiaUnitExactRoots

#print "file: DkMath.Lib.NumberTheory.ValuationRadicalDivisibility"

/-! # 代数的付値の有理関係と根の塔による値群 p 可除性
消去多項式の最大項を比較し、Bezout 係数で値を正規化する。 -/
namespace DkMath.Lib.NumberTheory
noncomputable section
open Polynomial
namespace RationalValue

variable {L : Type*} [Field L]

theorem valuation_natCast_eq_one (P : ValuationSubring L) (q : ℕ)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (n : ℕ) (hn : Nat.Coprime n q) :
    P.valuation (n : L) = 1 := by
  have hunit : IsUnit ((n : ℕ) : P) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hm
    obtain ⟨a, b, hab⟩ := Nat.Coprime.cast (R := P) hn
    apply (IsLocalRing.maximalIdeal.isMaximal P).ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hq)
  have := (P.valuation_eq_one_iff _).mp hunit
  simpa using this

theorem valuation_intCast (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (z : ℤ) (hz : z ≠ 0) :
    ∃ e : ℕ, P.valuation (z : L) = P.valuation (q : L) ^ e := by
  obtain ⟨e, n', hnd, habs⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hz) q hqp.one_lt.ne'
  have hn' : Nat.Coprime n' q := ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hnd).symm
  refine ⟨e, ?_⟩
  have habs' : ((z.natAbs : ℕ) : L) = (q : L) ^ e * (n' : L) := by rw [habs]; push_cast; ring
  have hzabs : P.valuation (z : L) = P.valuation ((z.natAbs : ℕ) : L) := by
    rcases Int.natAbs_eq z with h | h
    · conv_lhs => rw [h]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h]
      rw [Int.cast_neg, Valuation.map_neg, Int.cast_natCast]
  rw [hzabs, habs', map_mul, map_pow, valuation_natCast_eq_one P q hq n' hn', mul_one]

theorem valuation_ratCast [CharZero L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (c : ℚ) (hc : c ≠ 0) :
    ∃ m : ℤ, P.valuation (c : L) = P.valuation (q : L) ^ m := by
  have hq0 : P.valuation (q : L) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hqp.ne_zero
  obtain ⟨e₁, h₁⟩ := valuation_intCast P q hqp hq c.num (Rat.num_ne_zero.mpr hc)
  obtain ⟨e₂, h₂⟩ := valuation_intCast P q hqp hq c.den (by exact_mod_cast c.den_ne_zero)
  refine ⟨e₁ - e₂, ?_⟩
  rw [Rat.cast_def, map_div₀, h₁]
  have : P.valuation ((c.den : ℕ) : L) = P.valuation (q : L) ^ e₂ := by simpa using h₂
  rw [this, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]

theorem exists_valuation_pow_eq [CharZero L] (P : ValuationSubring L) (q : ℕ) (hqp : q.Prime)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P) (x : L) (hx : x ≠ 0) (halg : IsAlgebraic ℚ x) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, P.valuation x ^ n = P.valuation (q : L) ^ m := by
  classical
  set v := P.valuation with hv
  have hq0 : v (q : L) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact_mod_cast hqp.ne_zero
  have hx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
  have key : ∀ (i j : ℕ) (mi mj : ℤ), i < j →
      v (q : L) ^ mi * v x ^ i = v (q : L) ^ mj * v x ^ j →
      ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, v x ^ n = v (q : L) ^ m := by
    intro i j mi mj hij h
    refine ⟨j - i, Nat.sub_pos_of_lt hij, mi - mj, ?_⟩
    have hsplit : v x ^ j = v x ^ (j - i) * v x ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [hsplit, ← mul_assoc] at h
    have h' : v (q : L) ^ mi = v (q : L) ^ mj * v x ^ (j - i) := mul_right_cancel₀ (pow_ne_zero _ hx0) h
    rw [zpow_sub₀ hq0, eq_div_iff (zpow_ne_zero _ hq0), mul_comm]
    exact h'.symm
  obtain ⟨p, hp0, hpx⟩ := halg
  let f : ℕ → L := fun i => (p.coeff i : L) * x ^ i
  have hsum : ∑ i ∈ p.support, f i = 0 := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def] at hpx
    simpa [f] using hpx
  have hs : p.support.Nonempty :=
    Finset.nonempty_of_ne_empty (by rwa [Ne, Polynomial.support_eq_empty])
  obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image p.support (fun i => v (f i)) hs
  have hcj : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hfj0 : v (f j) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact mul_ne_zero (by exact_mod_cast hcj) (pow_ne_zero _ hx)
  have hex : ∃ i ∈ p.support, i ≠ j ∧ v (f i) = v (f j) := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hlt : ∀ i ∈ p.support \ {j}, v (f i) < v (f j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hjmax i hi.1) (hne i hi.1 hi.2)
    have heq := Valuation.map_sum_eq_of_lt v hj hlt
    rw [hsum, map_zero] at heq
    exact hfj0 heq.symm
  obtain ⟨i, hi, hij, hvij⟩ := hex
  have hci : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  obtain ⟨mi, hmi⟩ := valuation_ratCast P q hqp hq _ hci
  obtain ⟨mj, hmj⟩ := valuation_ratCast P q hqp hq _ hcj
  rw [← hv] at hmi hmj
  have hvij' : v (q : L) ^ mi * v x ^ i = v (q : L) ^ mj * v x ^ j := by
    simpa [f, map_mul, map_pow, hmi, hmj] using hvij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j mi mj h hvij'
  · exact key j i mj mi h hvij'.symm

end RationalValue

namespace RadicalValue

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem eq_one_of_pow_eq_one (u : Γ₀) {k : ℕ} (hk : k ≠ 0) (h : u ^ k = 1) : u = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rcases lt_trichotomy u 1 with hlt | heq | hgt
  · exfalso
    have h1 : u ^ k ≤ 1 := pow_le_one' hlt.le k
    have h2 : u ^ (k + 1) ≤ u := by
      rw [pow_succ]
      calc u ^ k * u ≤ 1 * u := mul_le_mul' h1 le_rfl
        _ = u := one_mul u
    rw [h] at h2
    exact absurd (lt_of_le_of_lt h2 hlt) (lt_irrefl 1)
  · exact heq
  · exfalso
    have h1 : 1 ≤ u ^ k := one_le_pow_of_one_le' hgt.le k
    have h2 : u ≤ u ^ (k + 1) := by
      rw [pow_succ]
      calc u = 1 * u := (one_mul u).symm
        _ ≤ u ^ k * u := mul_le_mul' h1 le_rfl
    rw [h] at h2
    exact absurd (lt_of_lt_of_le hgt h2) (lt_irrefl 1)

variable {K : Type*} [Field K]

theorem exists_valuation_eq_pow (v : Valuation K Γ₀) (p : ℕ) (hp : p.Prime) (q : K) (hq : q ≠ 0)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = q) (a : K) (ha : a ≠ 0)
    (hrat : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, v a ^ n = v q ^ m) :
    ∃ b : K, b ≠ 0 ∧ v a = v b ^ p := by
  obtain ⟨n, hn, m, hnm⟩ := hrat
  obtain ⟨j, n', hnd, hnj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.one_lt.ne'
  obtain ⟨r, hr⟩ := hroot (j + 1)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hp.ne_zero)] at hr
    exact hq hr.symm
  set α := v a with hα
  set ρ := v r with hρ
  have hα0 : α ≠ 0 := (Valuation.ne_zero_iff v).mpr ha
  have hρ0 : ρ ≠ 0 := (Valuation.ne_zero_iff v).mpr hr0
  have hγ : v q = ρ ^ (p ^ (j + 1)) := by rw [← hr, map_pow]
  have h1 : α ^ n' = ρ ^ ((p : ℤ) * m) := by
    have hx : (α ^ n' / ρ ^ ((p : ℤ) * m)) ^ (p ^ j) = 1 := by
      rw [div_pow, ← pow_mul, mul_comm n' (p ^ j), ← hnj, hnm, hγ, ← zpow_natCast, ← zpow_natCast,
        ← zpow_mul, ← zpow_mul]
      rw [show (p : ℤ) * m * ((p ^ j : ℕ) : ℤ) = ((p ^ (j + 1) : ℕ) : ℤ) * m by push_cast; ring,
        div_self (zpow_ne_zero _ hρ0)]
    have := eq_one_of_pow_eq_one _ (pow_ne_zero _ hp.ne_zero) hx
    rwa [div_eq_one_iff_eq (zpow_ne_zero _ hρ0)] at this
  have hcop : IsCoprime (n' : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
  obtain ⟨s, t, hst⟩ := hcop
  refine ⟨r ^ (m * s) * a ^ t, mul_ne_zero (zpow_ne_zero _ hr0) (zpow_ne_zero _ ha), ?_⟩
  rw [map_mul, map_zpow₀, map_zpow₀, ← hρ, ← hα]
  calc α = α ^ ((1 : ℤ)) := (zpow_one α).symm
    _ = α ^ (s * n' + t * p) := by rw [hst]
    _ = (α ^ n') ^ s * (α ^ t) ^ (p : ℤ) := by
        rw [zpow_add₀ hα0, mul_comm s, zpow_mul, zpow_mul, zpow_natCast]
    _ = (ρ ^ ((p : ℤ) * m)) ^ s * (α ^ t) ^ (p : ℤ) := by rw [h1]
    _ = (ρ ^ (m * s) * α ^ t) ^ p := by
        rw [← zpow_natCast, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul,
          show (p : ℤ) * m * s = m * s * (p : ℤ) by ring]

end RadicalValue

end
end DkMath.Lib.NumberTheory

```

### 5. DkMath.Lib.NumberTheory.InertiaRadicalExactRoots

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.ValuationRadicalDivisibility

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalExactRoots"

/-! # 実際の tail 上位体における正確な p 乗根
一般降下補題の入力を、同じ付値環・同じ tail 体から全て内部供給する。
これは体の乗法群の p 可除性であり、慣性群や Frey 共通商の巡回性は別の命題である。 -/
namespace DkMath.Lib.NumberTheory.RadicalDescent
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem exists_pow_eq [IsAlgClosed L] [IsGalois K L] [CharZero L] (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P)
    (p q : ℕ) (hp : p.Prime) (hqp : q.Prime) (hpq : p ≠ q)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P)
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = (q : K))
    (hres : ∀ u : P.comap (algebraMap K L), IsUnit u →
      ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)))
    (a : K) (ha : a ≠ 0) : ∃ b : K, b ^ p = a := by
  have : CharZero K := (algebraMap K L).charZero
  set R : ValuationSubring K := P.comap (algebraMap K L) with hR
  have hmemR : ∀ k : K, k ∈ R ↔ algebraMap K L k ∈ P := fun _ => Iff.rfl
  set v := P.valuation with hv
  let vK : Valuation K P.ValueGroup := v.comap (algebraMap K L)
  have hvK : ∀ k : K, vK k = v (algebraMap K L k) := fun _ => rfl
  have hmem_of_le : ∀ k : K, vK k ≤ 1 → k ∈ R := fun k hk => (hmemR k).mpr ((P.valuation_le_one_iff _).mp hk)
  have hunit_of_eq : ∀ (k : K) (hk : vK k = 1), IsUnit (⟨k, hmem_of_le k hk.le⟩ : R) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, map_zero] at hk; exact zero_ne_one hk
    have hinv : vK k⁻¹ ≤ 1 := by rw [map_inv₀, hk, inv_one]
    exact IsUnit.of_mul_eq_one ⟨k⁻¹, hmem_of_le _ hinv⟩ (Subtype.ext (mul_inv_cancel₀ hk0))
  have hq0L : (q : L) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hq0K : (q : K) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr hpq
  have hvp : vK (p : K) = 1 := by rw [hvK, map_natCast]; exact RationalValue.valuation_natCast_eq_one P q hq p hcop
  have hpunit : IsUnit ((p : ℕ) : R) := by
    have h := hunit_of_eq (p : K) hvp
    have e : (⟨(p : K), hmem_of_le _ hvp.le⟩ : R) = ((p : ℕ) : R) := Subtype.ext (by simp)
    rwa [e] at h
  have hx0 : algebraMap K L a ≠ 0 := (_root_.map_ne_zero (algebraMap K L)).mpr ha
  obtain ⟨n, hn, m, hnm⟩ := RationalValue.exists_valuation_pow_eq P q hqp hq (algebraMap K L a) hx0 (halg _)
  have hrat : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, vK a ^ n = vK (q : K) ^ m := by
    refine ⟨n, hn, m, ?_⟩
    rw [hvK, hvK, map_natCast]; exact hnm
  obtain ⟨b₀, hb₀, hvb⟩ := RadicalValue.exists_valuation_eq_pow vK p hp (q : K) hq0K hroot a ha hrat
  set u : K := a / b₀ ^ p with hu
  have hbp0 : b₀ ^ p ≠ 0 := pow_ne_zero _ hb₀
  have hvu : vK u = 1 := by rw [hu, map_div₀, map_pow, hvb, div_self (pow_ne_zero _ ((Valuation.ne_zero_iff vK).mpr hb₀))]
  have hau : a = b₀ ^ p * u := by rw [hu, mul_div_cancel₀ _ hbp0]
  have : HenselianLocalRing R := StableValuation.henselianLocalRing_comap P hstab
  set uR : R := ⟨u, hmem_of_le u hvu.le⟩ with huR
  obtain ⟨z, hz⟩ := hres uR (hunit_of_eq u hvu)
  obtain ⟨w, hw, -⟩ := InertiaResidue.exists_pow_eq_of_pow_sub_mem p hpunit uR z (hunit_of_eq u hvu) hz
  refine ⟨b₀ * (w : K), ?_⟩
  have hwK : (w : K) ^ p = u := by
    have := congrArg ((↑) : R → K) hw
    simpa using this
  rw [mul_pow, hwK, ← hau]


end
end DkMath.Lib.NumberTheory.RadicalDescent
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open ValuationInertia
/-- tail 体の任意の実際の上位体で、非零元は正確な p 乗根を持つ。 -/
theorem tailOverfield_exact_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (a : E) (ha : a ≠ 0) : ∃ b : E, b ^ p = a := by
  have hfixed := (fixedField_le_tailField A p q).trans hE
  have hqmax : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hA.2 (((A.valuation_eq_one_iff _).mp hu).ge)
  have hroot (k : ℕ) : ∃ r : E, r ^ (p ^ k) = (q : E) := by
    refine ⟨⟨InertiaRadical.radical p q hp k, hE (tower_mem_tailField A hp k)⟩, ?_⟩
    apply Subtype.ext
    exact PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) k
  exact RadicalDescent.exists_pow_eq A (InertiaStability.overfield_stable A E hfixed)
    p q hp hq hpq hqmax (fun x => Algebra.IsAlgebraic.isAlgebraic x) hroot
    (fun u hu => approximate_unit_pRoot hp hq hpq A hA E hfixed u hu) a ha

/-- 元の tail 体そのものの正確な非零 p 乗根。 -/
theorem tailField_exact_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (a : tailField A p q) (ha : a ≠ 0) : ∃ b : tailField A p q, b ^ p = a :=
  tailOverfield_exact_pRoot hp hq hpq A hA _ le_rfl a ha
/-- 零を含む冪写像の全射性。実際の tail 上位体だけを入力する。 -/
theorem tailOverfield_power_surjective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (a : E) : ∃ b : E, b ^ p = a := by
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, zero_pow hp.ne_zero]⟩
  · exact tailOverfield_exact_pRoot hp hq hpq A hA E hE a ha

/-- 同じ上位体内で任意の有限深さの p 冪根を構成する。 -/
theorem tailOverfield_primePower_surjective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (n : ℕ) (a : E) : ∃ b : E, b ^ (p ^ n) = a := by
  induction n generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := tailOverfield_power_surjective hp hq hpq A hA E hE a
    obtain ⟨b, hb⟩ := ih c
    exact ⟨b, by rw [pow_succ, pow_mul, hb, hc]⟩
end
end DkMath.Lib.NumberTheory.InertiaResidue

```


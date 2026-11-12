# NOTE-032 教科書 — Kummer 有限商排除から慣性 tail の冪根と Frey 核消滅へ

日付: 2026-11-08。最新レビューを参考に模範解答の依存経路を照合し、次の5段階を実装した。
今回は前回の「全 tail 上位体の体内冪根」を、実際の慣性群の元ごとの冪根へ輸送する。
さらに全根固定 tail の元が、同じ実際の Frey 共通商で消えることまで証明した。
**無条件一般 hno は未完成。有限一段の根を固定することと、全ての段の根を固定することは区別する。**

全5 Lean ブロックは production の全文と一致する。
各 import 群直後の必須 `#print "file: 正確なモジュール名"` を保持する。
既存 DkMath の Lake 環境で、各ブロックを別ファイルにコピーして検査できる。
1〜4は汎用 Lib 層（FLT 非依存）、5は実際の Frey Source と同じ係数核を消費する FLT 層である。

## 記号と今回の結論

p,q は異なる素数、A は ℚ̄ の q 上の同じ付値環、I は同じ実際の慣性群。
K₀=ℚ̄^I、E∞=ℚ(K₀,{α | ∃k,α^(p^k)=q}) は前回構成した体。
J=Gal(ℚ̄/E∞) を ℚ 自己同型群の実際の部分群として考える。
今回の結論は

    g∈J ⇒ ∀n, ∃w∈I∩J, w^(p^n)=g

である。J⊆I も内部証明するので、w と g は同じ tail 固定群に属する。
慣性元 g について J 所属は、同じ q の全 p 冪根の固定と同値。
同じ Frey 共通射影 π:I→H と既存の h^(p^(n+3))=1 を使うと

    g∈I かつ 全ての q の p 冪根を固定 ⇒ π(g)=1

となる。追加の安定性、指数互除性、巡回性、群内冪根 provider は不要である。
元の hclass の算術的供給は、この局所結果からは導いていない。

## 1. 慣性群の Krull 閉性と固定体の固定群

代数的元 x の開固定部分群の剰余類を使い、任意の述語 Q に対し {σ | Q(σx)} が開かつ閉であることを示す。
慣性への所属は「分解群に属し、全 a∈A で v(σa-a)<1」と同値。
従って慣性は閉分解群と全ての閉合同条件の交差となり、Krull 閉である。
一般の部分群については Fix(Fix(H))=closure(H) しか成立しないため、先にこの閉性を証明する。
その上で

    fixingSubgroup(K₀)=I

を得る。元の慣性群とその閉包を同一視するための未証明仮定は追加していない。

## 2. Kummer 理論による全有限 Galois 商の p 因子排除

一般の Galois 拡大 L/K で、K に原始 p 乗根の1があり、全有限中間体 K' の非零元が K' 内に p 乗根を持つとする。
開正規部分群 N の指数に p が現れたと仮定する。その固定体 M/K は有限 Galois 拡大であり、
Cauchy の定理から Gal(M/K) に位数 p の部分群 C がある。
M/M^C は巡回 p 次拡大なので、Kummer 理論によって α^p=a₀、M=M^C(α) と書ける。
全有限中間体の根の存在を M^C に適用し、b₀^p=a₀ を M^C 内で得る。
α/b₀ は p 乗根の1なので、基礎体にある原始根の冪となり、α 自身が M^C に入って矛盾する。
従って

    ∀N open normal, gcd([G:N],p)=1

が成立する。**基礎体 K だけの p 可除性を使った推論ではない。**
レビューの注意に対する橋は、全ての有限上位体での正確な根を使うこの部分である。
H¹ の消滅だけから群内冪根を結論する手順は採用していない。

## 3. 有限商の冪根をコンパクト性で群内へ戻す

副有限群 G の全ての開正規部分群 N の指数が p と素なら、各 G/N の p^n 冪写像は全射。
各 N に対し C_N={x | (x^(p^n))⁻¹g∈N} と置く。
C_N は非空閉集合であり、N∩M によって有向な有限交差条件を持つ。
コンパクト性から全 C_N の交差に点 w が存在する。
開正規部分群が元を分離するので、w^(p^n)=g が従う。
可換性は仮定していない。有限商の位数が p と素であることが本質的な入力である。

## 4. 実際の tail 群内の冪根

前回の `tailOverfield_exact_pRoot` を、E∞ 上の中間体を ℚ 上へ制限して適用する。
全有限上位体の根を内部供給し、p 乗根の1も元の慣性固定性から E∞ に構成する。
第2・第3段階を実際の Gal(ℚ̄/E∞) に適用し、同じ群内で正確な根を得る。
`fixingSubgroupEquiv` で ℚ 自己同型群へ戻し、第1段階によって根が元の I に属することを証明する。

`tailFixing_inertia_pRoot` は w∈I と w∈J を両方保持する。
`allRadicals_inertia_pRoot` は全根を固定する元に対して、I の部分型内での正確な等式を返す。
`allRadicals_map_eq_one` は一様 p 冪指数を持つ任意の群への準同型にこの結果を輸送する。
この一般補題では対象群の指数条件を明示し、Frey への適用では既存の証明で内部充足する。

## 5. 同じ Frey 共通商・評価・有限捩れ差分での消滅

元の共通射影 π と同じ一様指数 p^(n+3) を使用する。
全根固定の慣性元 σ に w^(p^(n+3))=σ となる同じ慣性元 w を取り、

    π(σ)=π(w)^(p^(n+3))=1

と示す。既存の核所属の同値条件から、全 k の ev_σ(k)=0 と元の全有限捩れ差分=1 を得る。
実際の subgroupOf を使った J⊆ker π も証明した。
共通商や評価を別の模型に置き換えていない。

## 残る証明境界

完了: 慣性の閉性、Kummer 有限商の p 因子排除、副有限群内の根、
同じ全根固定 tail の群内 p 可除性、tail の実際の Frey 共通商での消滅。

未完了: 有限一段の根を固定する補正元の有限段冪分解、
ker χ_(n+3)⊆ker π、H の巡回性、同じ生成元による単一評価、連続 H¹ 比較、
hclass の算術的供給、大域算術排除、一般 hno の無条件閉鎖。
J は全段の根を固定する群であり、ker χ_(n+3) と同一視しない。
今回の J⊆ker π を、未証明の有限段核包含として報告しない。

## 検証と模範解答

24新規宣言の再帰依存・標準公理監査と、実際の入口11件の公開入力監査を通常テストへ接続した。
全根固定条件 hr/hg と Frey 固有の住所条件を保持し、未証明の冪根・指数互除性・巡回性 provider は要求しない。
汎用補題の hdiv/hidx/hexp は数学的入力として明示し、実際の適用では証明済み算術から供給する。
検証: `evidence/validation-note032-inertia-tail-roots.txt`。
参照: `evidence/note032-inertia-tail-roots-reference-audit.json` に模範解答のコミットと SHA-256 を記録。

## 教科書 Lean コード全文

### 1. DkMath.Lib.NumberTheory.InertiaKrullClosed

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import DkMath.Lib.NumberTheory.InertiaFixedValuationStability

#print "file: DkMath.Lib.NumberTheory.InertiaKrullClosed"

/-! # 慣性群の Krull 閉性と固定体の回収
根を固定する群から元の慣性へ戻すため、閉包との混同を排除する。 -/
namespace DkMath.Lib.NumberTheory.InertiaClosed
open scoped Pointwise
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
theorem fixedField_topologicalClosure_eq [Algebra.IsIntegral K L]
    (H : Subgroup (L ≃ₐ[K] L)) :
    IntermediateField.fixedField H.topologicalClosure = IntermediateField.fixedField H := by
  refine le_antisymm (IntermediateField.fixedField_le (Subgroup.le_topologicalClosure H)) ?_
  intro x hx
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  have hstab : (↑H : Set (L ≃ₐ[K] L)) ⊆
      (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    intro τ hτ
    simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hx τ hτ
  have hclosed : IsClosed (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral (K := K) x)
  have hsub : closure (↑H : Set (L ≃ₐ[K] L)) ⊆
      (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    closure_minimal hstab hclosed
  have hσ' : σ ∈ closure (↑H : Set (L ≃ₐ[K] L)) := by
    rwa [← Subgroup.topologicalClosure_coe]
  simpa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] using hsub hσ'

theorem fixingSubgroup_fixedField_eq_topologicalClosure [IsGalois K L]
    [Algebra.IsIntegral K L] (H : Subgroup (L ≃ₐ[K] L)) :
    (IntermediateField.fixedField H).fixingSubgroup = H.topologicalClosure := by
  rw [← fixedField_topologicalClosure_eq H]
  exact InfiniteGalois.fixingSubgroup_fixedField
    ⟨H.topologicalClosure, Subgroup.isClosed_topologicalClosure H⟩

theorem exists_mem_apply_eq_of_mem_fixingSubgroup [IsGalois K L] [Algebra.IsIntegral K L]
    (H : Subgroup (L ≃ₐ[K] L)) (σ : L ≃ₐ[K] L)
    (hσ : σ ∈ (IntermediateField.fixedField H).fixingSubgroup) (x : L) :
    ∃ τ ∈ H, τ x = σ x := by
  have hσc : σ ∈ closure (↑H : Set (L ≃ₐ[K] L)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact (fixingSubgroup_fixedField_eq_topologicalClosure H) ▸ hσ
  have hU : IsOpen (σ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L))) :=
    (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ
  have hσU : σ ∈ σ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp
  obtain ⟨τ, hτU, hτH⟩ := mem_closure_iff.mp hσc _ hU hσU
  refine ⟨τ, hτH, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hτU
  have : (σ⁻¹ * τ) • x = x := hτU
  rw [mul_smul] at this
  have := congrArg (σ • ·) this
  simpa [smul_smul, AlgEquiv.smul_def] using this

theorem isOpen_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsOpen {σ : L ≃ₐ[K] L | Q (σ x)} := by
  have h : {σ : L ≃ₐ[K] L | Q (σ x)} = ⋃ σ₀ ∈ {σ : L ≃ₐ[K] L | Q (σ x)},
      σ₀ • (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hσ
      refine ⟨σ, hσ, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp
    · rintro ⟨σ₀, h₀, hmem⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem] at hmem
      have hfix : (σ₀⁻¹ * σ) • x = x := hmem
      rw [mul_smul] at hfix
      have hx : σ • x = σ₀ • x := by
        have := congrArg (σ₀ • ·) hfix
        simpa [smul_smul] using this
      have : σ x = σ₀ x := by simpa [AlgEquiv.smul_def] using hx
      rw [this]
      exact h₀
  rw [h]
  exact isOpen_biUnion fun σ₀ _ => (stabilizer_isOpen_of_isIntegral (K := K) x).smul σ₀

theorem isClosed_setOf_apply [Algebra.IsIntegral K L] (Q : L → Prop) (x : L) :
    IsClosed {σ : L ≃ₐ[K] L | Q (σ x)} := by
  rw [← isOpen_compl_iff]
  have : {σ : L ≃ₐ[K] L | Q (σ x)}ᶜ = {σ : L ≃ₐ[K] L | ¬ Q (σ x)} := by ext; simp
  rw [this]
  exact isOpen_setOf_apply (fun y => ¬ Q y) x

theorem mem_inertia_map_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype ↔
      σ ∈ A.decompositionSubgroup K ∧ ∀ a : A, A.valuation (σ a - a) < 1 := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨τ.2, fun a => ?_⟩
    change τ ∈ MonoidHom.ker (MulSemiringAction.toRingAut (A.decompositionSubgroup K)
      (IsLocalRing.ResidueField A)) at hτ
    rw [MonoidHom.mem_ker] at hτ
    have h1 : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := RingEquiv.congr_fun hτ _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff] at h1
    exact h1
  · rintro ⟨hD, hv⟩
    refine ⟨⟨σ, hD⟩, ?_, rfl⟩
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) ∈ MonoidHom.ker (MulSemiringAction.toRingAut
      (A.decompositionSubgroup K) (IsLocalRing.ResidueField A))
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, hD⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hv a

theorem isClosed_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    IsClosed (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) := by
  have hset : (((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype : Subgroup (L ≃ₐ[K] L)) :
      Set (L ≃ₐ[K] L)) =
      ((A.decompositionSubgroup K : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) ∩
        ⋂ a : A, {σ : L ≃ₐ[K] L | A.valuation (σ a - a) < 1} := by
    ext σ
    rw [SetLike.mem_coe, mem_inertia_map_iff, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_iInter]
    rfl
  rw [hset]
  exact (InertiaStability.isClosed_decompositionSubgroup A).inter
    (isClosed_iInter fun a => isClosed_setOf_apply (fun y => A.valuation (y - a) < 1) a)

theorem topologicalClosure_inertia_map [Algebra.IsIntegral K L] (A : ValuationSubring L) :
    ((A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype).topologicalClosure =
      (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype :=
  le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_inertia_map A))
    (Subgroup.le_topologicalClosure _)


/-- 実際の慣性固定体の固定群は、閉包ではなく元の慣性群そのもの。 -/
theorem fixingSubgroup_fixedField_inertia [IsGalois K L] [Algebra.IsIntegral K L]
    (A : ValuationSubring L) :
    (IntermediateField.fixedField (ValuationInertia.inertiaSubgroupIn A K)).fixingSubgroup =
      ValuationInertia.inertiaSubgroupIn A K := by
  rw [fixingSubgroup_fixedField_eq_topologicalClosure]
  exact topologicalClosure_inertia_map A
end DkMath.Lib.NumberTheory.InertiaClosed

```

### 2. DkMath.Lib.NumberTheory.KummerPrimeQuotientExclusion

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import DkMath.Lib.NumberTheory.InertiaKrullClosed
import Mathlib.FieldTheory.KummerExtension

#print "file: DkMath.Lib.NumberTheory.KummerPrimeQuotientExclusion"

/-! # 全有限上位体の冪根存在から有限 Galois 商の p 因子を排除
基礎体だけの p 可除性ではなく、全有限中間体での根の存在を使う。 -/
namespace DkMath.Lib.NumberTheory.KummerPrimeQuotient
open IntermediateField
/-- 全有限中間体が p 冪根を持てば、どの有限 Galois 商の位数にも p は現れない。 -/
theorem index_coprime_of_forall_pow_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hdiv : ∀ K' : IntermediateField K L, FiniteDimensional K K' →
      ∀ a : K', a ≠ 0 → ∃ b : K', b ^ p = a)
    (N : OpenNormalSubgroup (L ≃ₐ[K] L)) :
    (N.toSubgroup.index).Coprime p := by
  by_contra hcop
  have hdvd : p ∣ N.toSubgroup.index := by
    by_contra hnd
    exact hcop (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd))
  have hNc : IsClosed ((N.toSubgroup : Subgroup (L ≃ₐ[K] L)) : Set (L ≃ₐ[K] L)) :=
    N.toOpenSubgroup.isClosed
  set M : IntermediateField K L := IntermediateField.fixedField N.toSubgroup with hM
  have hfix : M.fixingSubgroup = N.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨N.toSubgroup, hNc⟩
  have hfin : FiniteDimensional K M := by
    rw [← InfiniteGalois.isOpen_iff_finite M]
    rw [hfix]
    exact N.toOpenSubgroup.isOpen'
  have hgal : IsGalois K ↥M := by
    rw [← InfiniteGalois.normal_iff_isGalois M]
    rw [hfix]
    exact N.isNormal'
  have : (⟨N.toSubgroup, hNc⟩ : ClosedSubgroup (L ≃ₐ[K] L)).Normal := N.isNormal'
  have hcard : Nat.card (↥M ≃ₐ[K] ↥M) = N.toSubgroup.index := by
    rw [Subgroup.index_eq_card]
    exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient
      ⟨N.toSubgroup, hNc⟩).toEquiv).symm
  -- 有限商に p が現れると、Cauchy により位数 p の部分群が得られる。
  have hdvd' : p ∣ Fintype.card (↥M ≃ₐ[K] ↥M) := by
    rw [← Nat.card_eq_fintype_card, hcard]
    exact hdvd
  have := Fact.mk hp
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card p hdvd'
  set C : Subgroup (↥M ≃ₐ[K] ↥M) := Subgroup.zpowers τ with hC
  set K' : IntermediateField K ↥M := IntermediateField.fixedField C with hK'
  have hrank : Module.finrank ↥K' ↥M = p := by
    rw [hK', IntermediateField.finrank_fixedField_eq_card, hC, Nat.card_eq_fintype_card,
      Fintype.card_zpowers, hτ]
  have : IsCyclic ↥C := by
    rw [hC]
    infer_instance
  have hcyc : IsCyclic (↥M ≃ₐ[↥K'] ↥M) := by
    have hKc : IntermediateField.fixingSubgroup K' = C :=
      IntermediateField.fixingSubgroup_fixedField C
    have : IsCyclic ↥(IntermediateField.fixingSubgroup K') := by rw [hKc]; infer_instance
    exact isCyclic_of_surjective (IntermediateField.fixingSubgroupEquiv K').toMonoidHom
      (IntermediateField.fixingSubgroupEquiv K').surjective
  have hζ' : IsPrimitiveRoot (algebraMap K ↥K' ζ) p :=
    hζ.map_of_injective (algebraMap K ↥K').injective
  have hK : (primitiveRoots (Module.finrank ↥K' ↥M) ↥K').Nonempty := by
    rw [hrank]
    exact ⟨algebraMap K ↥K' ζ, (mem_primitiveRoots hp.pos).mpr hζ'⟩
  -- その固定体上の巡回 p 次拡大を Kummer 生成元で表示する。
  obtain ⟨α, hαmem, hadj⟩ := exists_root_adjoin_eq_top_of_isCyclic ↥K' ↥M hK
  rw [hrank] at hαmem
  obtain ⟨a₀, ha₀⟩ := hαmem
  have hbotM : α ∈ (⊥ : IntermediateField ↥K' ↥M) → False := by
    intro hα
    have htop : (⊤ : IntermediateField ↥K' ↥M) = ⊥ :=
      le_antisymm (hadj ▸ IntermediateField.adjoin_simple_le_iff.mpr hα) bot_le
    have h1 : Module.finrank ↥K' ↥M = 1 := by
      rw [← IntermediateField.finrank_bot' (F := ↥K') (E := ↥M), ← htop,
        IntermediateField.finrank_top]
    rw [hrank] at h1
    exact hp.one_lt.ne' h1
  by_cases ha₀0 : a₀ = 0
  · apply hbotM
    have : α ^ p = 0 := by rw [← ha₀, ha₀0, map_zero]
    have hα0 : α = 0 := pow_eq_zero_iff hp.ne_zero |>.mp this
    rw [hα0]
    exact zero_mem ⊥
  · have : FiniteDimensional K ↥(K'.map M.val) :=
      Module.Finite.equiv (IntermediateField.equivMap K' M.val).toLinearEquiv
    -- 正確な体内根を下の固定体から供給し、Kummer 生成元を降下させる。
    obtain ⟨b₁, hb₁⟩ := hdiv (K'.map M.val) inferInstance
      (IntermediateField.equivMap K' M.val a₀)
      (by simpa using (IntermediateField.equivMap K' M.val).injective.ne ha₀0)
    set b₀ : ↥K' := (IntermediateField.equivMap K' M.val).symm b₁ with hb₀
    have hb₀p : b₀ ^ p = a₀ := by
      apply (IntermediateField.equivMap K' M.val).injective
      rw [map_pow, hb₀, AlgEquiv.apply_symm_apply, hb₁]
    have hb₀0 : b₀ ≠ 0 := by
      intro h
      apply ha₀0
      rw [← hb₀p, h, zero_pow hp.ne_zero]
    set β : ↥M := algebraMap ↥K' ↥M b₀ with hβdef
    have hβ0 : β ≠ 0 := by
      simpa [hβdef] using (algebraMap ↥K' ↥M).injective.ne hb₀0
    have hβp : β ^ p = α ^ p := by
      rw [hβdef, ← map_pow, hb₀p, ha₀]
    have hα0 : α ≠ 0 := by
      intro h
      apply ha₀0
      apply (algebraMap ↥K' ↥M).injective
      rw [ha₀, h, zero_pow hp.ne_zero, map_zero]
    have hquot : (α / β) ^ p = 1 := by
      rw [div_pow, hβp, div_self (pow_ne_zero p hα0)]
    have : NeZero p := ⟨hp.ne_zero⟩
    have hζM : IsPrimitiveRoot (algebraMap K ↥M ζ) p :=
      hζ.map_of_injective (algebraMap K ↥M).injective
    obtain ⟨i, _, hi⟩ := hζM.eq_pow_of_pow_eq_one hquot
    apply hbotM
    rw [IntermediateField.mem_bot]
    refine ⟨algebraMap K ↥K' ζ ^ i * b₀, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply K ↥K' ↥M, hi, ← hβdef,
      div_mul_cancel₀ α hβ0]


end DkMath.Lib.NumberTheory.KummerPrimeQuotient

```

### 3. DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement

#print "file: DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots"

/-! # 全有限商で p と素な位数を持つ副有限群の p 冪根
有限商での根を閉集合として交差し、コンパクト性で正確な根を得る。 -/
namespace DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- 開正規部分群は副有限群の元を分離する。 -/
theorem eq_one_of_forall_mem_openNormalSubgroup [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [T2Space G]
    (y : G) (hy : ∀ N : OpenNormalSubgroup G, y ∈ N) : y = 1 := by
  by_contra hne
  have hU : IsOpen ({y}ᶜ : Set G) := isClosed_singleton.isOpen_compl
  have h1 : (1 : G) ∈ ({y}ᶜ : Set G) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun h => hne h.symm
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  exact (hN (hy N)) rfl

/-- 有限商の位数と素な冪写像の全射性を、商を法とする根に戻す。 -/
theorem exists_pow_mul_inv_mem (N : OpenNormalSubgroup G) {p : ℕ}
    (hcop : (N.toSubgroup.index).Coprime p) (g : G) (k : ℕ) :
    ∃ x : G, (x ^ p ^ k)⁻¹ * g ∈ N.toSubgroup := by
  have hcard : (Nat.card (G ⧸ N.toSubgroup)).Coprime (p ^ k) := by
    rw [← Subgroup.index_eq_card]
    exact hcop.pow_right k
  obtain ⟨xbar, hxbar⟩ := (powCoprime hcard).surjective ((g : G ⧸ N.toSubgroup))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  refine ⟨x, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_pow]
  exact hxbar

/-- 全有限商での根と閉集合の有向交差から、群内の正確な根を得る。 -/
theorem exists_pow_pow_eq [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    [T2Space G] {p : ℕ}
    (hidx : ∀ N : OpenNormalSubgroup G, (N.toSubgroup.index).Coprime p)
    (g : G) (k : ℕ) :
    ∃ w : G, w ^ p ^ k = g := by
  have : Nonempty (OpenNormalSubgroup G) :=
    ⟨⟨⟨⊤, isOpen_univ⟩, inferInstanceAs ((⊤ : Subgroup G).Normal)⟩⟩
  have hcont : Continuous fun x : G => (x ^ p ^ k)⁻¹ * g :=
    ((continuous_pow (p ^ k)).inv).mul continuous_const
  set C : OpenNormalSubgroup G → Set G :=
    fun N => (fun x : G => (x ^ p ^ k)⁻¹ * g) ⁻¹' (N.toSubgroup : Set G) with hCdef
  have hclosed : ∀ N, IsClosed (C N) := fun N =>
    (N.toOpenSubgroup.isClosed).preimage hcont
  have hne : ∀ N, (C N).Nonempty := fun N => by
    obtain ⟨x, hx⟩ := exists_pow_mul_inv_mem N (hidx N) g k
    exact ⟨x, hx⟩
  have hdir : Directed (· ⊇ ·) C := by
    intro N M
    refine ⟨N ⊓ M, ?_, ?_⟩
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).1
    · intro x hx
      exact (Subgroup.mem_inf.mp hx).2
  -- 全ての有限商の合同条件を同時に満たす点を選ぶ。
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun N => (hclosed N).isCompact) hclosed
  refine ⟨x, ?_⟩
  have hy : ∀ N : OpenNormalSubgroup G, (x ^ p ^ k)⁻¹ * g ∈ N :=
    fun N => Set.mem_iInter.mp hx N
  have h1 : (x ^ p ^ k)⁻¹ * g = 1 := eq_one_of_forall_mem_openNormalSubgroup _ hy
  exact (inv_mul_eq_one.mp h1)


end DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots

```

### 4. DkMath.Lib.NumberTheory.InertiaTailGaloisRoots

```lean
/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: closed inertia, Kummer prime-to-p quotients and actual inertia-tail roots.
-/

import DkMath.Lib.NumberTheory.InertiaRadicalExactRoots
import DkMath.Lib.NumberTheory.KummerPrimeQuotientExclusion
import DkMath.Lib.NumberTheory.ProfiniteCoprimeRoots

#print "file: DkMath.Lib.NumberTheory.InertiaTailGaloisRoots"

/-! # 同じ tail 体を固定する実際の慣性元の p 冪根
Kummer 有限商排除と副有限コンパクト性を、実際の体内根で内部充足する。
単一有限段の根の固定から全根の固定は結論しない。 -/
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open ValuationInertia IntermediateField

/-- tail 体上の中間体を ℚ 上へ制限し、前回の正確な根定理を適用する。 -/
theorem tailIntermediate_exact_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (F : IntermediateField (tailField A p q) (AlgebraicClosure ℚ))
    (a : F) (ha : a ≠ 0) : ∃ b : F, b ^ p = a := by
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) := F.restrictScalars ℚ
  have hE : tailField A p q ≤ E := fun x hx => F.algebraMap_mem ⟨x, hx⟩
  exact tailOverfield_exact_pRoot hp hq hpq A hA E hE a ha

/-- 同じ tail 体に原始 p 乗根の1が実在する。 -/
theorem tailField_primitiveRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) :
    ∃ ζ : tailField A p q, IsPrimitiveRoot ζ p := by
  let : NeZero (p : AlgebraicClosure ℚ) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hfix : ζ ∈ fixedField A := by
    rw [fixedField, IntermediateField.mem_fixedField_iff]
    intro σ hσ
    apply InertiaRadical.inertia_fixes_primePower_root hp hq hpq A hA ⟨σ, hσ⟩ 1 ζ
    simpa using hζ.pow_eq_one
  exact ⟨⟨ζ, fixedField_le_tailField A p q hfix⟩,
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (tailField A p q) (AlgebraicClosure ℚ))
      hζ (algebraMap (tailField A p q) (AlgebraicClosure ℚ)).injective⟩

/-- 実際の tail Galois 群の各開正規部分群の指数は p と素。 -/
theorem tailGalois_index_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (N : OpenNormalSubgroup (AlgebraicClosure ℚ ≃ₐ[tailField A p q] AlgebraicClosure ℚ)) :
    N.toSubgroup.index.Coprime p := by
  obtain ⟨ζ, hζ⟩ := tailField_primitiveRoot hp hq hpq A hA
  exact KummerPrimeQuotient.index_coprime_of_forall_pow_surjective hp hζ
    (fun F _ a ha => tailIntermediate_exact_pRoot hp hq hpq A hA F a ha) N

/-- tail を固定する自己同型の p 冪根は、同じ tail 固定群かつ元の慣性群に属する。 -/
theorem tailFixing_inertia_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (n : ℕ) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hg : g ∈ (tailField A p q).fixingSubgroup) :
    ∃ w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      w ∈ inertiaSubgroupIn A ℚ ∧ w ∈ (tailField A p q).fixingSubgroup ∧ w ^ (p ^ n) = g := by
  let E := tailField A p q
  let g' : AlgebraicClosure ℚ ≃ₐ[E] AlgebraicClosure ℚ := fixingSubgroupEquiv E ⟨g, hg⟩
  let : T2Space (AlgebraicClosure ℚ ≃ₐ[E] AlgebraicClosure ℚ) := krullTopology_t2
  obtain ⟨w', hw'⟩ := ProfiniteCoprimeRoots.exists_pow_pow_eq
    (tailGalois_index_coprime hp hq hpq A hA) g' n
  let w : E.fixingSubgroup := (fixingSubgroupEquiv E).symm w'
  have hwI : (w : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ inertiaSubgroupIn A ℚ := by
    have hf := IntermediateField.fixingSubgroup_le (fixedField_le_tailField A p q) w.2
    rw [fixedField, InertiaClosed.fixingSubgroup_fixedField_inertia] at hf
    exact hf
  refine ⟨w, hwI, w.2, ?_⟩
  have he : (fixingSubgroupEquiv E).symm (w' ^ (p ^ n)) = w ^ (p ^ n) := map_pow _ _ _
  rw [hw', show (fixingSubgroupEquiv E).symm g' = ⟨g, hg⟩ from MulEquiv.symm_apply_apply _ _] at he
  exact (congrArg (fun x : E.fixingSubgroup => (x : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) he).symm

/-- 慣性元が tail を固定することと、同じ q の全 p 冪根を固定することは同値。 -/
theorem mem_tailFixing_iff_all_radicals {p q : ℕ}
    (A : ValuationSubring (AlgebraicClosure ℚ)) (g : inertiaSubgroupIn A ℚ) :
    g.val ∈ (tailField A p q).fixingSubgroup ↔
      ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α := by
  constructor
  · intro hg α k hk
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg α (radical_mem_tailField A hk)
  · intro hr
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hs : tailField A p q ≤ IntermediateField.fixedField (Subgroup.zpowers g.val) := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro α hα
      rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hfix : g.val α = α := by
        rcases hα with hα | ⟨k, hk⟩
        · exact (IntermediateField.mem_fixedField_iff _ _).mp hα g.val g.property
        · exact hr α k hk
      have hle : Subgroup.zpowers g.val ≤ MulAction.stabilizer (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) α := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact hfix
      exact hle hσ
    exact (IntermediateField.mem_fixedField_iff _ _).mp (hs hx) g.val (Subgroup.mem_zpowers _)

/-- 同じ全根を固定する慣性元は、元の慣性群内に任意の有限深さの冪根を持つ。 -/
theorem allRadicals_inertia_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (n : ℕ) (g : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α) :
    ∃ w : inertiaSubgroupIn A ℚ, w ^ (p ^ n) = g := by
  obtain ⟨w, hwI, _, hw⟩ := tailFixing_inertia_pRoot hp hq hpq A hA n g.val
    ((mem_tailFixing_iff_all_radicals A g).mpr hr)
  exact ⟨⟨w, hwI⟩, Subtype.ext hw⟩

/-- 任意の一様 p 冪指数の商は、同じ全根を固定する慣性元を消す。 -/
theorem allRadicals_map_eq_one {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {H : Type*} [Group H] (f : inertiaSubgroupIn A ℚ →* H)
    (n : ℕ) (hexp : ∀ h : H, h ^ (p ^ n) = 1) (g : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g.val α = α) :
    f g = 1 := by
  obtain ⟨w, hw⟩ := allRadicals_inertia_pRoot hp hq hpq A hA n g hr
  rw [← hw, map_pow]
  exact hexp _
end
end DkMath.Lib.NumberTheory.InertiaResidue

```

### 5. DkMath.FLT.FreyTailKernelVanishing

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalKernelComparison
import DkMath.Lib.NumberTheory.InertiaTailGaloisRoots

#print "file: DkMath.FLT.FreyTailKernelVanishing"

/-!
# 全根固定 tail の Frey 共通商における消滅

体内根 → 有限商の p 因子排除 → 群内根という証明済みの経路を消費する。
元の共通商の一様指数で tail を消す。有限一段だけを固定する補正元はまだ対象外。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 元の全 q 根を固定する慣性元は、同じ実際の Frey 共通商で消える。 -/
theorem ResidualCyclicStage.allRadicals_commonProjection_eq_one (σ : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α) :
    T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ = 1 :=
  InertiaResidue.allRadicals_map_eq_one (Fact.out : p.Prime) hq hqp.symm A hA
    (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA) (n + 3)
    (T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA) σ hr

/-- 全根固定 tail は、元の全係数核の評価で零となる。 -/
theorem ResidualCyclicStage.allRadicals_evaluations_eq_zero (σ : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α)
    (k : T.fixedH1CoefficientKernel A) : T.fixedKernelEvaluation A σ k = 0 :=
  (T.mem_commonProjection_kernel_iff_evaluations A hp5 hq hqp haddr hA σ).mp
    (T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ hr) k

/-- 同じ tail による元の全有限捩れ点の固定差分も消える。 -/
theorem ResidualCyclicStage.allRadicals_fixed_differences_eq_one (σ : inertiaSubgroupIn A ℚ)
    (hr : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α)
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ = 1 :=
  (T.mem_commonProjection_kernel_iff_fixed_differences A hp5 hq hqp haddr hA σ).mp
    (T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ hr) x

/-- 全根固定体の核に対する実際の包含。有限段の根指標の核包含とは区別する。 -/
theorem ResidualCyclicStage.tailFixing_le_commonProjection_kernel :
    (InertiaResidue.tailField A p q).fixingSubgroup.subgroupOf (inertiaSubgroupIn A ℚ) ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker := by
  intro σ hσ
  exact T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ
    ((InertiaResidue.mem_tailFixing_iff_all_radicals A σ).mp hσ)
end
end DkMath.FLT.Frey.Source
```


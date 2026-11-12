# NOTE-032 教科書 — 有限段根核包含・Frey 共通商の巡回性・単一評価

日付: 2026-11-08。最新レビューを参考に、次の5段階を実装した。
**指定した有限段 ker χ_(n+3)⊆ker π、実際の H の巡回性、同じ具体的な γ による単一評価の単射性まで証明した。**
一般 hno の無条件閉鎖は未完成。hclass の算術的供給など、残る大域算術と区別する。

以下の5 Lean ブロックは production の全文と一致する。
各 import 群直後に、必須の `#print "file: 正確なモジュール名"` を保持した。
DkMath の Lake 環境で各ブロックを別ファイルにコピーして検査できる。
第2段階は FLT 非依存の Lib、他の4段階は元の Frey Source を保持する FLT 層に置いた。

## 記号と公開入力

I は q 上の付値環 A の同じ実際の慣性群、χ_m は同じ q の選んだ p^m 乗根 α_m の作用比指標。
K_m=ker χ_m、J は同じ q の全 p 冪根を固定する tail、π:I→H は既存の実際の共通射影である。
γ は既存の `InertiaRadical.generator`。この同じ γ の χ_(m+1) 値は全ての m で原始 p^(m+1) 乗根となる。
元の段 T、p≥5、p,q の素数性、p≠q、局所住所と A が q 上にある条件を保持する。
新しい hgen/hcyclic/hcompare/hopen/hcontinuous を公開入力にしない。

## 1. 元の共通射影の開核

π は I→I/W→H という既存の合成である。
共通値族 f:I/W→(K→Multiplicative F) の核は既存の有限性・連続性によって開。
商への射影は連続なので

    ker π = quotientMk⁻¹(ker f)

も元の I の Krull 部分群位相で開となる。
H に新しい離散位相を仮定する必要はない。元の値族と元の商位相から導く。

## 2. 根指標の閉核・減少性・全根固定 tail の交叉表示

χ_(i+d)(σ)^(p^d)=χ_i(σ) より、i≤j なら K_j⊆K_i。
K_m は元の α_m の固定条件で表せるので、Krull 位相で閉である。
ℚ̄ の位相を離散とする新しい入力や、指標の連続性 provider は置かない。

全ての選んだ根 α_m を固定する慣性元は、同じ q の任意の p 冪根 β も固定する。
β/α_m は p^m 乗根の1で、元の慣性が既にそれを固定するからである。
従って

    ⋂_m K_m = J

を、集合の等式と全称命題の同値の両方で証明した。
I 自身のコンパクト性は、前回の慣性の Krull 閉性と絶対 Galois 群のコンパクト性から供給する。

同じ Lib モジュールに一般補題 `CompactKernel.exists_subset_open` を実装した。
コンパクト空間の減少閉集合 C_m の交叉が開集合 U に含まれれば、ある C_M が U に含まれる。
もし全ての C_m∩Uᶜ が非空なら、それらは有向な非空閉集合族。
コンパクト性で共通点が存在し、交叉の包含に矛盾する。

## 3. 全根固定 tail の消滅を有限段で検出

前回の J⊆ker π、第1段階の開核、第2段階の閉性・減少性・コンパクト性を合わせ、

    ∃M, K_M⊆ker π

を証明した。M の存在を新しい算術入力として仮定していない。
この段階の M は存在量化であり、まだ n+3 と同一視しない。

## 4. 指定した n+3 段まで引き下ろす

r=n+3 と置く。第3段階の M より深い段 D=M+n+4 を選ぶ。
K_D⊆K_M⊆ker π、かつ D≥r。
σ∈K_r を取り、同じ全段原始生成元による D 段の補正分解を使うと

    σ=γ^j ε, ε∈K_D

となる。ε∈K_r でもあるので、χ_r(σ)=1 から χ_r(γ)^j=1。
χ_r(γ) の原始性により p^r∣j を得る。
元の共通商の一様指数 h^(p^r)=1 と π(ε)=1 より

    π(σ)=π(γ)^j π(ε)=1

となる。これが指定した有限段の核包含

    ker χ_(n+3)⊆ker π

そのものである。全根を固定するという強い条件を σ に追加していない。
既存の核比較同値条件を消費し、指定した根を固定する σ の全係数核評価も零とした。

## 5. 同じ H の巡回性と同じ具体的な γ での単一評価

任意の h∈H を同じ π の全射性で h=π(σ) と持ち上げる。
r 段で σ=γ^j ε と分解すると、ε∈K_r は第4段階で消える。
従って h=π(γ)^j であり、元の同じ共通商 H は π(γ) により生成される。

`commonTame_isCyclic` は、巡回性や生成性を仮定せずにその結論を与える。
既存の `fixedKernelCommon_generator_evaluation_injective` にこの生成性を供給し、
同じ具体的な `InertiaRadical.generator` における元の評価 ev_γ:K→F の単射性を証明する。
さらに同じ核の濃度について |K|∣|F| を得た。
任意に取り直した模型の群や評価に置き換えていない。

## 模範解答との照合

外部模範の `exists_tame_generator` は、原始作用とコンパクト性で
σ=γ^j x^(p^r) w^(p^r) という強い慣性群内分解を直接構成する。
その証明で、原始根から指数の可除性を得て高段の誤差を下げる手順と、全根固定誤差に群内根を取る箇所を確認した。

今回の DkMath 実装は、レビュー提案に従い、すでに証明した tail 消滅と実際の π の開核から有限検出を先に得る。
その後、同じ原始生成元と指数上界で指定段に下げる。模範の強い三因子分解自体を移植したとは主張しない。
新規ファイルはこの DkMath 固有の組合せの証明であり、外部 P2M/P2MW の import や結論 provider は使っていない。
参照コミット・ソースの SHA-256・レビュー SHA-256 は reference audit に記録する。

## 現在の証明境界と検証

今回解消: 共通射影の開核、全根核の交叉表示、有限段検出、指定段の核包含、
実際の H の巡回性、同じ γ の単一評価、|K|∣|F|。

未完了: hclass の算術的供給、共鳴する局所障害の排除、連続 H¹ との比較、
大域算術矛盾と一般 hno の無条件閉鎖。核の濃度の可除性だけから矛盾は結論しない。
模範の強い三因子冪分解も今回の独立した結論にはしていない。

新規16宣言の再帰依存・標準公理監査と公開入力15件の監査を通常テスト入口へ接続した。
コンパクト性と指数上界の必要性を示す境界例も追加した。
検証: `evidence/validation-note032-finite-kernel-closure.txt`。
進捗の一次記録は STATUS、ROADMAP の冒頭表も今回の到達点に更新した。

## 教科書 Lean コード全文

### 1. DkMath.FLT.FreyCommonProjectionTopology

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTailKernelVanishing

#print "file: DkMath.FLT.FreyCommonProjectionTopology"

/-! # 元の共通射影の開核
元の Krull 部分群位相と、既存の tame 値族の開核を接続する。 -/
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

/-- 元の共通射影の核は、既存の tame 値族の核の逆像。 -/
theorem ResidualCyclicStage.commonProjection_kernel_eq_preimage :
    ((T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker : Set (inertiaSubgroupIn A ℚ)) =
      (QuotientGroup.mk : inertiaSubgroupIn A ℚ → tameInertiaQuotient A) ⁻¹'
        ((T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker : Set (tameInertiaQuotient A)) := by
  ext σ
  exact QuotientGroup.eq_one_iff _

/-- 追加の連続性 provider を要求せず、同じ慣性群の位相で開核を得る。 -/
theorem ResidualCyclicStage.commonProjection_kernel_isOpen :
    IsOpen ((T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker : Set (inertiaSubgroupIn A ℚ)) := by
  rw [T.commonProjection_kernel_eq_preimage A hp5 hq hqp haddr hA]
  exact (T.fixedKernelTameFamily_kernel_isOpen A hp5 hq hqp haddr hA).preimage QuotientGroup.continuous_mk
end
end DkMath.FLT.Frey.Source

```

### 2. DkMath.Lib.NumberTheory.InertiaRadicalKernelTopology

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.InertiaTailGaloisRoots
import DkMath.Lib.NumberTheory.InertiaRadicalCorrection

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalKernelTopology"

/-! # 根指標の閉核・減少性・交叉とコンパクト抽出
全段を固定する条件を、同じ根指標の全核への所属として正確に記述する。 -/
namespace DkMath.Lib.NumberTheory.CompactKernel
/-- 減少閉集合の交叉が開集合に含まれれば、有限段ですでに含まれる。 -/
theorem exists_subset_open {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (C : ℕ → Set X) (hc : ∀ n, IsClosed (C n)) (hanti : Antitone C)
    (U : Set X) (hu : IsOpen U) (hsub : (⋂ n, C n) ⊆ U) : ∃ n, C n ⊆ U := by
  by_contra hn
  have hne : ∀ n, (C n ∩ Uᶜ).Nonempty := by
    intro n
    have hnot : ¬ C n ⊆ U := fun h => hn ⟨n, h⟩
    obtain ⟨x, hx, hxu⟩ := Set.not_subset.mp hnot
    exact ⟨x, hx, hxu⟩
  have hd : Directed (· ⊇ ·) (fun n => C n ∩ Uᶜ) := by
    intro n m
    exact ⟨max n m, fun x hx => ⟨hanti (le_max_left _ _) hx.1, hx.2⟩,
      fun x hx => ⟨hanti (le_max_right _ _) hx.1, hx.2⟩⟩
  have hclosed (n : ℕ) : IsClosed (C n ∩ Uᶜ) := (hc n).inter hu.isClosed_compl
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun n => C n ∩ Uᶜ) hd hne (fun n => (hclosed n).isCompact) hclosed
  have hall := Set.mem_iInter.mp hx
  exact (hall 0).2 (hsub (Set.mem_iInter.mpr (fun n => (hall n).1)))
end DkMath.Lib.NumberTheory.CompactKernel

namespace DkMath.Lib.NumberTheory.InertiaRadical
open ValuationInertia
noncomputable section
variable {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ実際の慣性群は、元の Krull 位相でコンパクト。 -/
theorem inertia_compactSpace : CompactSpace (inertiaSubgroupIn A ℚ) :=
  isCompact_iff_compactSpace.mp (InertiaClosed.isClosed_inertia_map A).isCompact

/-- 同じ根指標の核は高い段ほど小さい。 -/
theorem character_kernel_antitone : Antitone (fun k => (character hp hq hpq A hA k).ker) := by
  intro i j hij σ hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  change character hp hq hpq A hA i σ = 1
  rw [← character_compat hp hq hpq A hA i d σ, hs, one_pow]

/-- 指標値に代数閉包の離散位相を導入せず、根の開固定群から閉核を得る。 -/
theorem character_kernel_isClosed (k : ℕ) :
    IsClosed ((character hp hq hpq A hA k).ker : Set (inertiaSubgroupIn A ℚ)) := by
  have he : ((character hp hq hpq A hA k).ker : Set (inertiaSubgroupIn A ℚ)) =
      Subtype.val ⁻¹' {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
        σ (radical p q hp k) = radical p q hp k} := by
    ext σ
    exact character_eq_one_iff_root_fixed hp hq hpq A hA k σ
  rw [he]
  exact (InertiaClosed.isClosed_setOf_apply (fun y => y = radical p q hp k)
    (radical p q hp k)).preimage continuous_subtype_val

include hq hpq hA in
/-- 全ての選んだ根を固定すれば、同じ q の任意の p 冪根を固定する。 -/
theorem all_radicals_fixed_of_tower (σ : inertiaSubgroupIn A ℚ)
    (hs : ∀ k, σ.val (radical p q hp k) = radical p q hp k)
    (α : AlgebraicClosure ℚ) (k : ℕ) (hα : α ^ (p ^ k) = (q : AlgebraicClosure ℚ)) : σ.val α = α := by
  let β := radical p q hp k
  have hβ : β ≠ 0 := radical_ne_zero hp hq k
  have hratio : (α / β) ^ (p ^ k) = 1 := by
    rw [div_pow, hα, PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) k]
    exact div_self (by exact_mod_cast hq.ne_zero)
  have hf := inertia_fixes_primePower_root hp hq hpq A hA σ k (α / β) hratio
  have he : α = (α / β) * β := (div_mul_cancel₀ _ hβ).symm
  calc σ.val α = σ.val (α / β) * σ.val β := by conv_lhs => rw [he]; rw [map_mul]
       _ = (α / β) * β := by rw [hf, hs k]
       _ = α := div_mul_cancel₀ _ hβ

/-- 全根指標の核の交叉は、実際の全根固定 tail と同じ条件。 -/
theorem forall_character_kernel_iff_all_radicals (σ : inertiaSubgroupIn A ℚ) :
    (∀ k, σ ∈ (character hp hq hpq A hA k).ker) ↔
      ∀ α k, α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → σ.val α = α := by
  constructor
  · intro hs
    exact all_radicals_fixed_of_tower hp hq hpq A hA σ
      (fun k => (character_eq_one_iff_root_fixed hp hq hpq A hA k σ).mp (hs k))
  · intro hs k
    exact (character_eq_one_iff_root_fixed hp hq hpq A hA k σ).mpr
      (hs _ k (PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) k))

/-- 集合としても同じ tail 核を回収する。 -/
theorem iInter_character_kernel_eq_tail :
    (⋂ k, ((character hp hq hpq A hA k).ker : Set (inertiaSubgroupIn A ℚ))) =
      {σ | σ.val ∈ (InertiaResidue.tailField A p q).fixingSubgroup} := by
  ext σ
  simp only [Set.mem_iInter, SetLike.mem_coe, Set.mem_ofPred_eq]
  exact (forall_character_kernel_iff_all_radicals hp hq hpq A hA σ).trans
    (InertiaResidue.mem_tailFixing_iff_all_radicals A σ).symm
end
end DkMath.Lib.NumberTheory.InertiaRadical

```

### 3. DkMath.FLT.FreyRadicalFiniteDetection

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonProjectionTopology
import DkMath.Lib.NumberTheory.InertiaRadicalKernelTopology

#print "file: DkMath.FLT.FreyRadicalFiniteDetection"

/-! # 全根固定 tail の消滅から有限段核包含を抽出
新しい有限段消滅仮定を置かず、開核とコンパクト性を消費する。 -/
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

/-- ある実際の有限段の根核が、元の共通射影核に含まれる。 -/
theorem ResidualCyclicStage.exists_radical_kernel_le_common :
    ∃ M : ℕ, (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA M).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker := by
  let := InertiaRadical.inertia_compactSpace A
  apply CompactKernel.exists_subset_open
    (fun M => ((InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA M).ker : Set _))
    (InertiaRadical.character_kernel_isClosed (Fact.out : p.Prime) hq hqp.symm A hA)
    (InertiaRadical.character_kernel_antitone (Fact.out : p.Prime) hq hqp.symm A hA)
    _ (T.commonProjection_kernel_isOpen A hp5 hq hqp haddr hA)
  intro σ hs
  apply T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ
  exact (InertiaRadical.forall_character_kernel_iff_all_radicals
    (Fact.out : p.Prime) hq hqp.symm A hA σ).mp (Set.mem_iInter.mp hs)
end
end DkMath.FLT.Frey.Source

```

### 4. DkMath.FLT.FreyRadicalKernelClosure

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalFiniteDetection

#print "file: DkMath.FLT.FreyRadicalKernelClosure"

/-! # 有限段検出を指定した n+3 段まで引き下ろす
同じ全段原始生成元と元の共通商の指数を用い、有限段根核の包含を証明する。 -/
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

/-- 指定した有限段の根核が、同じ実際の共通射影核に含まれる。 -/
theorem ResidualCyclicStage.radical_kernel_le_commonProjection_kernel :
    (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA (n + 3)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker := by
  let hp : p.Prime := Fact.out
  let γ := InertiaRadical.generator hp hq hqp.symm A hA
  obtain ⟨M, hM⟩ := T.exists_radical_kernel_le_common A hp5 hq hqp haddr hA
  let d := M + n + 3
  have hdeep : (InertiaRadical.character hp hq hqp.symm A hA (d + 1)).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker :=
    (InertiaRadical.character_kernel_antitone hp hq hqp.symm A hA (by dsimp [d]; omega)).trans hM
  intro σ hs
  obtain ⟨j, _, ε, he, hε, _⟩ := InertiaRadical.correction_of_primitive hp hq hqp.symm A hA d γ
    (InertiaRadical.generator_primitive hp hq hqp.symm A hA d) σ
  have hεlow : InertiaRadical.character hp hq hqp.symm A hA (n + 3) ε = 1 :=
    InertiaRadical.character_kernel_antitone hp hq hqp.symm A hA (by dsimp [d]; omega) hε
  have hj : p ^ (n + 3) ∣ j := by
    have hσ := hs
    change InertiaRadical.character hp hq hqp.symm A hA (n + 3) σ = 1 at hσ
    rw [he, map_mul, map_pow, hεlow, mul_one] at hσ
    have hpow := congrArg Units.val hσ
    exact (InertiaRadical.generator_primitive hp hq hqp.symm A hA (n + 2)).pow_eq_one_iff_dvd j |>.mp hpow
  change T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ = 1
  rw [he, map_mul, map_pow, show T.fixedKernelCommonProjection A hp5 hq hqp haddr hA ε = 1 from hdeep hε, mul_one]
  obtain ⟨t, rfl⟩ := hj
  rw [pow_mul, T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA, one_pow]

/-- 有限一段を固定する元の全係数核の評価も零となる。 -/
theorem ResidualCyclicStage.radical_fixed_evaluations_eq_zero (σ : inertiaSubgroupIn A ℚ)
    (hs : σ.val (InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3)) =
      InertiaRadical.radical p q (Fact.out : p.Prime) (n + 3))
    (k : T.fixedH1CoefficientKernel A) : T.fixedKernelEvaluation A σ k = 0 :=
  (T.radical_kernel_comparison_iff_evaluations A hp5 hq hqp haddr hA).mp
    (T.radical_kernel_le_commonProjection_kernel A hp5 hq hqp haddr hA) σ hs k
end
end DkMath.FLT.Frey.Source

```

### 5. DkMath.FLT.FreyCommonTameCyclicClosure

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyRadicalKernelClosure

#print "file: DkMath.FLT.FreyCommonTameCyclicClosure"

/-! # 実際の共通商の巡回性と同じ生成元による単一評価
未証明の巡回性や有限段分解を公開入力にしない。 -/
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

/-- 元の全段原始慣性生成元の像が、同じ H を生成する。 -/
theorem ResidualCyclicStage.commonProjection_generator_generates :
    ∀ h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA,
      h ∈ Subgroup.zpowers (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA
        (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)) := by
  intro h
  obtain ⟨σ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
  obtain ⟨j, _, ε, he, hε, _⟩ := InertiaRadical.correction_of_primitive
    (Fact.out : p.Prime) hq hqp.symm A hA (n + 2) _
    (InertiaRadical.generator_primitive (Fact.out : p.Prime) hq hqp.symm A hA (n + 2)) σ
  have hkill := T.radical_kernel_le_commonProjection_kernel A hp5 hq hqp haddr hA hε
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨(j : ℤ), ?_⟩
  rw [zpow_natCast, he, map_mul, map_pow, show T.fixedKernelCommonProjection A hp5 hq hqp haddr hA ε = 1 from hkill, mul_one]

/-- 追加の hcyclic/hgen なしで、実際の Frey 共通商は巡回。 -/
theorem ResidualCyclicStage.commonTame_isCyclic :
    IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨T.fixedKernelCommonProjection A hp5 hq hqp haddr hA
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA), eq_top_iff.mpr ?_⟩
  intro h _
  exact T.commonProjection_generator_generates A hp5 hq hqp haddr hA h

/-- 同じ具体的な γ での単一慣性評価が、元の全係数核上で単射。 -/
theorem ResidualCyclicStage.generator_evaluation_injective :
    Function.Injective (T.fixedKernelEvaluation A
      (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)) :=
  T.fixedKernelCommon_generator_evaluation_injective A hp5 hq hqp haddr hA _
    (T.commonProjection_generator_generates A hp5 hq hqp haddr hA)

/-- 同じ核の濃度は、同じ固定係数群の濃度を割る。 -/
theorem ResidualCyclicStage.kernel_card_dvd_fixed_of_radical_generator :
    Nat.card (T.fixedH1CoefficientKernel A) ∣ Nat.card (T.inertiaFixedUpperQuotient A) :=
  AddSubgroup.card_dvd_of_injective (T.fixedKernelEvaluation A
    (InertiaRadical.generator (Fact.out : p.Prime) hq hqp.symm A hA)).toAddMonoidHom
    (T.generator_evaluation_injective A hp5 hq hqp haddr hA)
end
end DkMath.FLT.Frey.Source

```


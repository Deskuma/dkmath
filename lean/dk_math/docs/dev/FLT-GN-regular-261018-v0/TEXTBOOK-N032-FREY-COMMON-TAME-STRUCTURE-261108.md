# NOTE-032 教科書 — 共通有限商の可換 p 群構造と単一評価への生成元判定

日付: 2026-11-08。レビューの R1（共通有限商の構造）を証明し、
R2（生成元から単一評価）の消費側を5ステップで形式化した。
**有限段生成元の存在、または共通商の巡回性そのものは、今回も未証明である。**
後半の5つの Lean ブロックは対応する production ソースの全文。
各 import 群直後の正確な `#print "file: モジュール名"` を省略しない。
既存 DkMath の Lake 環境で、それぞれ別ファイルへコピペして検査できる。

## 元の群と作用を保持する

元の Frey 曲線、巡回段 T、有限捩れ商 Q、慣性群 I、固定部分群 F=Q^I、
実際の通常 H¹ の係数核 K を使う。局所条件 p≥5、素数 q≠p、悪い住所と q の上の付値環 A を保つ。
同じ野生合同部分群 W と同じ J=I/W、以前の全核指標の族 Ψ を使う。

    H=J/ker Ψ,  Values:H→∏(k∈K), Multiplicative F

この H は以前の実際の群商そのもの。
元の Group 構造を別の群の構造へ取り替えず、その上に可換性を追加する。
最終存在定理の算術入力は以前と同じ hclass と Cofixed である。

## 1. 同じ値写像の忠実性と同じ H の可換性

同じ Values の単射性を、実際の商の等式と Ψ の核の定義から証明する。
値域の積は可換群なので

    Values(uv)=Values(u)Values(v)=Values(v)Values(u)=Values(vu)

となり、単射性から uv=vu を得る。
同じ元・同じ積・同じ逆元・同じ冪を使う CommGroup 構造を構成した。
この構造は名前付きの定義として公開し、曖昧な仮定付きの大域 instance は追加しない。

さらに、元の I から J と H への合成射 π:I→H を構成し、全射性と

    Values(π(σ))(k)=χ_k(σ)

を保持する。後の生成元を元の実際の慣性元へ持ち上げるための射である。

## 2. 同じ H の p 群性と零化冪

単射な Values に Lagrange を使い

    |H| divides |F|^|K|

を得る。元の |K|·|F|=p^(n+3) から |F|=p^r、r≤n+3。
従ってある m≤r·|K| に対して |H|=p^m となり、Mathlib の IsPGroup を構成できる。
ここでは H が自明である可能性も残すので、r,m の正性はまだ要求しない。

各 F の元はその濃度 |F| で消える。
全指標値と Values の単射性から、H の各元 u について

    u^|F|=1,  u^(p^r)=1

を証明した。さらに r≤n+3 より、有限段生成元の消費に使う一様な式

    u^(p^(n+3))=1

も得る。共通商の可換性・p 群性・指数上界は、新しい provider を要求しない構造定理である。
**これだけでは巡回性は従わない。**

## 3. H と K の両側で元を識別する評価

各 u∈H の値を用いて

    E_u:K→ₗ[ℤ]F

を構成する。u を同じ全射 π で元の σ∈I に持ち上げると、
以前の整数線形な慣性評価 ev_σ を回収するので、加法と整数スカラーを保つ。
同じ u について別の持ち上げを選ぶことによる値の曖昧さは、元の Values の因子化で消えている。

    E_(π(σ))=ev_σ,  E_1=0

を証明した。また k を固定した H→Multiplicative F の準同型も構成し、同じ値を回収する。

二つの分離性を明示した。

    (∀u∈H, E_u(k₁)=E_u(k₂)) → k₁=k₂
    (∀k∈K, E_u(k)=E_v(k)) → u=v

これは二つの群の同型や完全な双対同型を主張するものではない。

## 4. 生成元・有限段分解の消費側（条件付き）

同じ H の元 g が生成元、つまり全ての H の元が g の整数冪であるなら、
H 上の準同型は g における値で決まる。
両側評価のうち K 側の分離性を使うと E_g が単射になる。

従って **IsCyclic H が別途証明された場合**、g を π で実際の γ∈I に持ち上げて

    ev_γ:K→ₗ[ℤ]F is injective,  |K| divides |F|

を得る。この補題の公開入力 hcyclic は明示的に条件付きである。
今回の実装が IsCyclic H を証明したという意味ではない。

模範解答型の有限段分解の消費も、具体的に証明した。
ある γ∈I について

    ∀τ∈I, ∃j:ℕ, ∃x,w∈I, τ=γ^j·x^(p^(n+3))·w^(p^(n+3))

という **分解 hgen が別途得られた場合**、同じ π と第2段階の一様な零化冪により

    π(τ)=π(γ)^j

となる。従って同じ π(γ) が H を生成し、H の巡回性と **同じ γ** の評価の単射性が従う。
この分解の存在は今回証明していない。条件付き補題の hgen を、最終存在定理の新しい入力にはしていない。

## 5. 同じ障害慣性元の非自明像と算術証明書

元の同じ障害証明書 h の慣性元 τ の像 hτ=π(τ) を保持する。
元の同じ障害核元 k と固定差分 d について

    E_(hτ)(k)=d,  addOrderOf(d)=p

を使い、hτ≠1 を証明した。従って H の濃度指数も正となる。
前回の |F| の鋭い上界と合わせ

    |F|=p^r,  |H|=p^m,
    1≤r≤n+2,  1≤m≤r·|K|,
    ∀u∈H, u^(p^r)=1

を得る。**元の π(τ) 自身の厳密位数が p だとは主張しない。**
その一つの指標値が位数 p でも、他の核指標の値により共通商での位数は大きくなり得る。

巡回性が別途得られた場合の数値帰結も独立した条件付き補題にした。
単一評価の単射性と元の |K|=p^s、r+s=n+3 から

    s≤r,  n+3≤2r

が従う。

最終定理 `residual_exists_nontrivial_common_tame_pGroup` は、元の hclass と Cofixed から
同じ n,T,q,A,τ,y,h と非単位元 π(τ)、有限性、可換性、IsPGroup、正の指数と零化冪を出力する。
さらに「IsCyclic H なら上の単一評価と数値制約」という **含意** を出力する。
最終定理の入力に hcyclic/hgen はなく、結論にも無条件の単一生成元の存在はない。

## 模範解答との照合と残る経路

ローカル模範解答の有限段生成元の結論と、その tail の冪根存在の消費箇所を再照合した。
参照 HEAD は 115356cbc627159d0d16add0da6e9a2bb3655ed8。
模範は任意の段 m について τ=γ^j·x^(p^m)·w^(p^m) を構成する。
今回の消費側では具体的に m=n+3 を使い、冪誤差が実際の同じ H で消えるところを証明した。

ただし、付値環における tail の冪根存在と、有限段生成元 γ の算術的構成は今回移植していない。
模範の P2M/P2MW や既存 FLT 終点を import していない。
参照ファイルと Mathlib の SHA-256 は evidence の参照監査に保存する。

R1 は今回完成。R2 は消費側を実装した段階で、存在側は未完成。
通常の H¹ と元の連続指標を使い、連続 H¹ との比較同型はまだ構成していない。
大域算術・共鳴障害の排除・hclass の供給は、この局所構造定理とは別に残る。
**無条件の一般 hno は引き続き未完成である。**

## 回帰検査と検証記録

(ZMod5)² は有限可換 p 群かつ5乗で1になるが、巡回でないことを位数・濃度から検査する。
逆に巡回な検出群があって単一評価が単射でも、非零 K を持つ配置 r=2,s=1,n=0 は整合する。
さらに ZMod5×ZMod3 で、実際の段冪125の誤差を伴う分解を検査し、
商で消える冪誤差を元の慣性群での単位元と取り違えないようにする。

新規30宣言の再帰依存監査、30件の公開入力監査、全宣言の公理出力を通常入口へ接続する。
条件付き補題では hg/hgen/hcyclic を必須入力として検査し、他の構造定理と最終存在定理では禁止する。
検証結果は `evidence/validation-note032-frey-common-tame-structure.txt`。

## コピペ用 Lean 全文

### 1. DkMath.FLT.FreyCommonTameFaithful

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelFiniteDetector

#print "file: DkMath.FLT.FreyCommonTameFaithful"

/-!
# 実際の共通馴分岐商の忠実な値写像と可換群構造

元の群商 H=J/ker Ψ と群演算を保持する。別の可換群へ取り替えず、
元の全指標値への写像の単射性から同じ H の可換性を証明する。
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

/-- 元の共通商から、元の全指標値への写像は単射。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameValues_injective :
    Function.Injective (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA) := by
  intro x y he
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  apply QuotientGroup.eq.mpr
  change (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) (t⁻¹ * s) = 1
  change (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) t =
    (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) s at he
  rw [map_mul, map_inv, he, inv_mul_cancel]

/-- 元の同じ H の群演算は可換である。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_mul_comm
    (x y : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) : x * y = y * x := by
  apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
  rw [map_mul, map_mul, mul_comm]

/-- 元の Group 構造をそのまま拡張した、同じ H の可換群構造。 -/
@[instance_reducible]
def ResidualCyclicStage.fixedKernelCommonTameCommGroup :
    CommGroup (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :=
  { (inferInstance : Group (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)) with
    mul_comm := T.fixedKernelCommonTame_mul_comm A hp5 hq hqp haddr hA }

/-- 元の I から同じ J と同じ共通商 H への合成。 -/
def ResidualCyclicStage.fixedKernelCommonProjection :
    inertiaSubgroupIn A ℚ →* T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA :=
  (QuotientGroup.mk' (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker).comp
    (QuotientGroup.mk' (wildInertiaSubgroup A))

/-- 元の慣性群から同じ H への合成は全射。 -/
theorem ResidualCyclicStage.fixedKernelCommonProjection_surjective :
    Function.Surjective (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA) :=
  QuotientGroup.mk_surjective.comp QuotientGroup.mk_surjective

/-- 同じ I の元の共通商像で、元の同じ核指標値を回収する。 -/
theorem ResidualCyclicStage.fixedKernelCommonProjection_value
    (σ : inertiaSubgroupIn A ℚ) (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ) k = T.fixedKernelCharacter A k σ := rfl

end
end DkMath.FLT.Frey.Source
```

### 2. DkMath.FLT.FreyCommonTamePGroup

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameFaithful

#print "file: DkMath.FLT.FreyCommonTamePGroup"

/-!
# 同じ共通有限商の p 群性・濃度・指数上界

忠実な値写像と元の F の濃度から計算する。巡回性は含めない。
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

/-- 同じ H の濃度は、同じ F の |K| 個の積の濃度を割る。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_card_dvd :
    Nat.card (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) ∣
      Nat.card (T.inertiaFixedUpperQuotient A) ^ Nat.card (T.fixedH1CoefficientKernel A) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  have hd := Subgroup.card_dvd_of_injective (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA)
    (T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA)
  simpa only [Nat.card_fun, Nat.card_congr
    (Multiplicative.toAdd : Multiplicative (T.inertiaFixedUpperQuotient A) ≃ T.inertiaFixedUpperQuotient A)] using hd

/-- 同じ共通商の各元は、元の固定係数群 F の濃度乗で 1 になる。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_pow_card_fixed
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :
    h ^ Nat.card (T.inertiaFixedUpperQuotient A) = 1 := by
  apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
  rw [map_pow, map_one]
  apply funext
  intro k
  exact pow_card_eq_one'

/-- 元の F と同じ共通商 H の p 冪濃度を内部計算する。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_prime_power_profile :
    ∃ r m, r ≤ n + 3 ∧ m ≤ r * Nat.card (T.fixedH1CoefficientKernel A) ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) = p ^ m := by
  have hdF : Nat.card (T.inertiaFixedUpperQuotient A) ∣ p ^ (n + 3) := by
    refine ⟨Nat.card (T.fixedH1CoefficientKernel A), ?_⟩
    rw [mul_comm]
    exact (T.fixedKernel_card_mul_fixed A hp5 hq hqp haddr hA).symm
  obtain ⟨r, hr, hF⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdF
  have hdH := T.fixedKernelCommonTame_card_dvd A hp5 hq hqp haddr hA
  rw [hF, ← pow_mul] at hdH
  obtain ⟨m, hm, hH⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdH
  exact ⟨r, m, hr, hm, hF, hH⟩

/-- 同じ実際の共通商は p 群である。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_isPGroup :
    IsPGroup p (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  obtain ⟨_, _, _, _, _, hH⟩ := T.fixedKernelCommonTame_prime_power_profile A hp5 hq hqp haddr hA
  exact IsPGroup.of_card hH

/-- 共通商の指数は、元の F の p 冪濃度で一様に抑えられる。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_exponent_profile :
    ∃ r ≤ n + 3, Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      ∀ h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA, h ^ (p ^ r) = 1 := by
  obtain ⟨r, _, hr, _, hF, _⟩ := T.fixedKernelCommonTame_prime_power_profile A hp5 hq hqp haddr hA
  exact ⟨r, hr, hF, fun h => hF ▸ T.fixedKernelCommonTame_pow_card_fixed A hp5 hq hqp haddr hA h⟩

/-- 有限段生成元の消費に使う、段数だけで決まる一様な零化冪。 -/
theorem ResidualCyclicStage.fixedKernelCommonTame_pow_stage
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) : h ^ (p ^ (n + 3)) = 1 := by
  obtain ⟨r, hr, _, he⟩ := T.fixedKernelCommonTame_exponent_profile A hp5 hq hqp haddr hA
  exact orderOf_dvd_iff_pow_eq_one.mp
    (dvd_trans (orderOf_dvd_of_pow_eq_one (he h)) (pow_dvd_pow p hr))

end
end DkMath.FLT.Frey.Source
```

### 3. DkMath.FLT.FreyCommonTameEvaluation

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTamePGroup

#print "file: DkMath.FLT.FreyCommonTameEvaluation"

/-!
# 同じ H と K の両側で元を識別する評価

共通商 H の元で評価しても、K→F は整数線形。H 側の積に関しては準同型となる。
元の商と元の指標値を保持した二つの分離性を公開する。
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

/-- 同じ共通商 H の元による K の実際の整数線形評価。 -/
def ResidualCyclicStage.fixedKernelCommonEvaluation
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :
    T.fixedH1CoefficientKernel A →ₗ[ℤ] T.inertiaFixedUpperQuotient A where
  toFun k := Multiplicative.toAdd (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA h k)
  map_add' x y := by
    obtain ⟨σ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
    exact (T.fixedKernelEvaluation A σ).map_add x y
  map_smul' m x := by
    obtain ⟨σ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
    exact (T.fixedKernelEvaluation A σ).map_smul' m x

/-- 同じ I の元からの像による評価は、以前の同じ慣性評価。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_projection (σ : inertiaSubgroupIn A ℚ) :
    T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA σ) = T.fixedKernelEvaluation A σ := rfl

/-- H の単位元での評価は零写像。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_one :
    T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA 1 = 0 := by
  apply LinearMap.ext
  intro k
  change Multiplicative.toAdd (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA 1 k) = 0
  rw [map_one]
  rfl

/-- K の元を固定した、同じ H 上の乗法記法の準同型。 -/
def ResidualCyclicStage.fixedKernelCommonCharacter (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA →* Multiplicative (T.inertiaFixedUpperQuotient A) :=
  (Pi.evalMonoidHom (fun _ : T.fixedH1CoefficientKernel A => Multiplicative (T.inertiaFixedUpperQuotient A)) k).comp
    (T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA)

/-- H 側の指標と K 側の線形評価は同じ値を持つ。 -/
theorem ResidualCyclicStage.fixedKernelCommonCharacter_apply (k : T.fixedH1CoefficientKernel A)
    (h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) :
    Multiplicative.toAdd (T.fixedKernelCommonCharacter A hp5 hq hqp haddr hA k h) =
      T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h k := rfl

/-- H 側の全評価が一致すれば、同じ K の元が一致する。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_separates_kernel
    (x y : T.fixedH1CoefficientKernel A)
    (he : ∀ h, T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h x =
      T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h y) : x = y := by
  apply T.fixedKernelCommonTameValues_separates A hp5 hq hqp haddr hA x y
  intro h
  exact congrArg Multiplicative.ofAdd (he h)

/-- K 側の全評価が一致すれば、同じ H の元が一致する。 -/
theorem ResidualCyclicStage.fixedKernelCommonEvaluation_separates_quotient
    (h g : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)
    (he : ∀ k, T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA h k =
      T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA g k) : h = g := by
  apply T.fixedKernelCommonTameValues_injective A hp5 hq hqp haddr hA
  apply funext
  intro k
  exact congrArg Multiplicative.ofAdd (he k)

end
end DkMath.FLT.Frey.Source
```

### 4. DkMath.FLT.FreyCommonTameGeneratorCriterion

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameEvaluation

#print "file: DkMath.FLT.FreyCommonTameGeneratorCriterion"

/-!
# 実際の共通商の生成元から単一慣性評価へ

このモジュールは生成元の消費側。巡回性や有限段分解の存在はここでは証明しない。
条件付き補題の入力を明示し、共通商の有限性だけから巡回性を推論しない。
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

/-- 同じ H の生成元での評価は、同じ K 全体で単射。 -/
theorem ResidualCyclicStage.fixedKernelCommon_generator_evaluation_injective
    (g : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)
    (hg : ∀ h, h ∈ Subgroup.zpowers g) :
    Function.Injective (T.fixedKernelCommonEvaluation A hp5 hq hqp haddr hA g) := by
  intro x y he
  apply T.fixedKernelCommonTameValues_separates A hp5 hq hqp haddr hA x y
  intro h
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg h)
  change T.fixedKernelCommonCharacter A hp5 hq hqp haddr hA x (g ^ j) =
    T.fixedKernelCommonCharacter A hp5 hq hqp haddr hA y (g ^ j)
  rw [map_zpow, map_zpow]
  exact congrArg (fun v => v ^ j) (congrArg Multiplicative.ofAdd he)

/-- 巡回性が別途得られれば、実際の慣性元 γ による単一評価を構成できる。 -/
theorem ResidualCyclicStage.exists_single_evaluation_of_common_isCyclic
    (hcyclic : IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)) :
    ∃ γ : inertiaSubgroupIn A ℚ, Function.Injective (T.fixedKernelEvaluation A γ) ∧
      Nat.card (T.fixedH1CoefficientKernel A) ∣ Nat.card (T.inertiaFixedUpperQuotient A) := by
  let := hcyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA)
  obtain ⟨γ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA g
  have hi := T.fixedKernelCommon_generator_evaluation_injective A hp5 hq hqp haddr hA _ hg
  change Function.Injective (T.fixedKernelEvaluation A γ) at hi
  exact ⟨γ, hi, AddSubgroup.card_dvd_of_injective (T.fixedKernelEvaluation A γ).toAddMonoidHom hi⟩

/-- 模範解答型の有限段分解が得られれば、同じ γ の像が H を生成する。 -/
theorem ResidualCyclicStage.commonProjection_generates_of_power_decomposition
    (γ : inertiaSubgroupIn A ℚ)
    (hgen : ∀ τ : inertiaSubgroupIn A ℚ, ∃ (j : ℕ) (x w : inertiaSubgroupIn A ℚ),
      τ = γ ^ j * x ^ (p ^ (n + 3)) * w ^ (p ^ (n + 3))) :
    ∀ h : T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA,
      h ∈ Subgroup.zpowers (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ) := by
  intro h
  obtain ⟨τ, rfl⟩ := T.fixedKernelCommonProjection_surjective A hp5 hq hqp haddr hA h
  obtain ⟨j, x, w, he⟩ := hgen τ
  have hv : T.fixedKernelCommonProjection A hp5 hq hqp haddr hA τ =
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ) ^ j := by
    rw [he, map_mul, map_mul, map_pow, map_pow, map_pow,
      T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA,
      T.fixedKernelCommonTame_pow_stage A hp5 hq hqp haddr hA, mul_one, mul_one]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(j : ℤ), (zpow_natCast _ j).trans hv.symm⟩

/-- 有限段分解を仮定する条件付き巡回性。分解の存在は別途必要。 -/
theorem ResidualCyclicStage.common_isCyclic_of_power_decomposition
    (γ : inertiaSubgroupIn A ℚ)
    (hgen : ∀ τ : inertiaSubgroupIn A ℚ, ∃ (j : ℕ) (x w : inertiaSubgroupIn A ℚ),
      τ = γ ^ j * x ^ (p ^ (n + 3)) * w ^ (p ^ (n + 3))) :
    IsCyclic (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨T.fixedKernelCommonProjection A hp5 hq hqp haddr hA γ, eq_top_iff.mpr ?_⟩
  intro h _
  exact T.commonProjection_generates_of_power_decomposition A hp5 hq hqp haddr hA γ hgen h

/-- 有限段分解が得られれば、同じ γ の単一慣性評価が単射。 -/
theorem ResidualCyclicStage.single_evaluation_of_power_decomposition
    (γ : inertiaSubgroupIn A ℚ)
    (hgen : ∀ τ : inertiaSubgroupIn A ℚ, ∃ (j : ℕ) (x w : inertiaSubgroupIn A ℚ),
      τ = γ ^ j * x ^ (p ^ (n + 3)) * w ^ (p ^ (n + 3))) :
    Function.Injective (T.fixedKernelEvaluation A γ) :=
  T.fixedKernelCommon_generator_evaluation_injective A hp5 hq hqp haddr hA _
    (T.commonProjection_generates_of_power_decomposition A hp5 hq hqp haddr hA γ hgen)

end
end DkMath.FLT.Frey.Source
```

### 5. DkMath.FLT.FreyCommonTameStructureCertificate

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonTameGeneratorCriterion

#print "file: DkMath.FLT.FreyCommonTameStructureCertificate"

/-!
# 非自明な共通有限可換 p 群と、巡回性が得られた場合の数値制約

元の障害慣性元の像を保持し、H の非自明性を同じ位数 p の差分で検出する。
最終定理は巡回性を仮定しない。巡回性が別途証明された場合の帰結は含意として出力する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} {T : S.ResidualCyclicStage L n}
    {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ障害慣性元の、同じ共通有限商での像。 -/
def NarrowAbsorptionObstruction.commonInertiaElement
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :=
  T.fixedKernelCommonProjection A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩

/-- この同じ共通商元による同じ核元の評価は、元の同じ固定差分。 -/
theorem NarrowAbsorptionObstruction.commonInertiaElement_evaluation
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    T.fixedKernelCommonEvaluation A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
      (h.commonInertiaElement hp5)
      (T.fixedCosetKernelElement hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩) =
      h.fixedDifference hp5 := h.fixedKernelEvaluation_obstruction hp5

/-- 位数 p の同じ差分を検出するので、元の慣性像は H の単位元ではない。 -/
theorem NarrowAbsorptionObstruction.commonInertiaElement_ne_one
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) : h.commonInertiaElement hp5 ≠ 1 := by
  intro hz
  have he := h.commonInertiaElement_evaluation hp5
  rw [hz, T.fixedKernelCommonEvaluation_one A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over] at he
  have hd : h.fixedDifference hp5 = 0 := he.symm
  have ho := h.fixedDifference_order_eq_prime hp5
  rw [hd, addOrderOf_zero] at ho
  exact (Fact.out : p.Prime).ne_one ho.symm

/-- 同じ障害により、H の p 冪濃度指数も正。元の F の指数上界は n+2。 -/
theorem NarrowAbsorptionObstruction.commonTame_positive_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    ∃ r m, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ m ∧ m ≤ r * Nat.card (T.fixedH1CoefficientKernel A) ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) = p ^ m ∧
      ∀ u : T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
        u ^ (p ^ r) = 1 := by
  obtain ⟨r, _, hr, hrb, _, _, _, hF, _⟩ := h.fixed_kernel_sharp_profile hp5
  have hd := T.fixedKernelCommonTame_card_dvd A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
  rw [hF, ← pow_mul] at hd
  obtain ⟨m, hm, hH⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  have hm0 : m ≠ 0 := by
    intro hz
    have hc1 := hH.trans (by rw [hz, pow_zero])
    have hu := (Nat.card_eq_one_iff_unique.mp hc1).1
    exact h.commonInertiaElement_ne_one hp5 (hu.elim _ 1)
  exact ⟨r, m, hr, hrb, by omega, hm, hF, hH,
    fun u => hF ▸ T.fixedKernelCommonTame_pow_card_fixed A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over u⟩

/-- 巡回性が別途得られれば、単一評価と r+s=n+3、s≤r、n+3≤2r が従う。 -/
theorem NarrowAbsorptionObstruction.single_evaluation_profile_of_common_isCyclic
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p)
    (hcyclic : IsCyclic (T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over)) :
    ∃ (γ : inertiaSubgroupIn A ℚ) (r s : ℕ), Function.Injective (T.fixedKernelEvaluation A γ) ∧
      1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧ s ≤ r ∧ n + 3 ≤ 2 * r ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s := by
  obtain ⟨γ, hi, hd⟩ := T.exists_single_evaluation_of_common_isCyclic A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over hcyclic
  obtain ⟨r, s, hr, hs, hsum, hF, hK⟩ := h.fixed_kernel_balanced_profile hp5
  rw [hF, hK] at hd
  have hsr := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨γ, r, s, hi, hr, hs, hsum, hsr, by omega, hF, hK⟩

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)

include hline hζ hp5 hclass in
/-- 元の同じ証明書から、非自明な有限可換 p 群と、巡回性を得た場合の含意を出力する。 -/
theorem residual_exists_nontrivial_common_tame_pGroup
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let H := T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over
      h.commonInertiaElement hp5 ≠ 1 ∧ Finite H ∧ IsPGroup p H ∧ (∀ u v : H, u * v = v * u) ∧
      (∃ r m, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ m ∧ m ≤ r * Nat.card (T.fixedH1CoefficientKernel A) ∧
        Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧ Nat.card H = p ^ m ∧ ∀ u : H, u ^ (p ^ r) = 1) ∧
      (IsCyclic H → ∃ (γ : inertiaSubgroupIn A ℚ) (r s : ℕ), Function.Injective (T.fixedKernelEvaluation A γ) ∧
        1 ≤ r ∧ 1 ≤ s ∧ r + s = n + 3 ∧ s ≤ r ∧ n + 3 ≤ 2 * r ∧
        Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧ Nat.card (T.fixedH1CoefficientKernel A) = p ^ s) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, h.commonInertiaElement_ne_one hp5,
    T.fixedKernelCommonTameQuotient_finite A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    T.fixedKernelCommonTame_isPGroup A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    T.fixedKernelCommonTame_mul_comm A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    h.commonTame_positive_profile hp5, h.single_evaluation_profile_of_common_isCyclic hp5⟩

end
end DkMath.FLT.Frey.Source
```


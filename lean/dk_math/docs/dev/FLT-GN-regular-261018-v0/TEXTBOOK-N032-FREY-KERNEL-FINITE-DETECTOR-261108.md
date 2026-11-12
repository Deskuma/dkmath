# NOTE-032 教科書 — 係数核全体の連続馴分岐指標と有限慣性検出

日付: 2026-11-08。最新レビューを参考に、評価像の包含からの指数制約、
任意の核元の連続性、野生零性と馴分岐降下、共通有限商、有限検出集合を5ステップ実装した。
後半の5つの Lean ブロックは対応する production ソースの全文である。
各 import 群直後の正確な `#print "file: モジュール名"` を省略しない。
既存 DkMath の Lake 環境で、それぞれ別ファイルへコピペして検査できる。

## 元の対象を保持する

元の Frey 曲線、巡回段 T、有限捩れ商 Q=E[p^(n+2)]/T、慣性群 I と固定部分群 F=Q^I、
実際の通常のコホモロジー係数写像の核

    K = ker(H¹(I,F) → H¹(I,Q))

を使う。元の p≥5、素数 q≠p、悪い住所、q の上の付値環 A という局所条件を維持する。
同じ野生合同部分群を W、既存の実際の商 I/W を J と書く。
K の評価 ev_σ:K→ₗ[ℤ]F、元の障害点 y に対応する同じ k と同じ慣性元 τ を保持する。
K と F は取り替えず、同型・有限性・連続性・野生零性・生成元を新しい provider にしない。

## 1. 評価像の包含が与える追加の指数制約

同じ τ の評価像 B は実際の F の部分加群なので、Lagrange により |B| は |F| を割る。
前回の |F|=p^r、|B|=p^t、評価核 U の |U|=p^u と r+t+u=n+3 に合わせて

    1≤t≤r≤n+2,  u≤n+1,  n+3-2r≤u

を得る。最後の減算は自然数の切り捨て減算である。
単一評価が単射であるとは仮定しない。

## 2. 任意の核元を元の有限捩れ差分で表す

前回の Q/F≃ₗ[ℤ]K と二つの商写像の全射性から、任意の k∈K について

    ∃ x∈E[p^(n+2)],  fixedCosetKernelElement(x)=k

を証明した。x は核元を表すための有限捩れ点であり、任意の x に障害点 y と同じ
p•y∈T や非吸収条件があるとは主張しない。存在証明にはそれらを必要としない。

自明係数の標準 H¹ 同型から得られる同じ準同型 χ_k:I→Multiplicative F を定義し、
上の x で表すと χ_k が元の同じ固定差分指標 c_x に一致することを証明する。
元の有限捩れ指標の連続性を移すことで

    ∀ k∈K, Continuous χ_k

を回収した。通常 H¹(I,F) 全体の任意の類についての主張ではない。

## 3. 核全体の野生零性・馴分岐降下・実際の inflation

同じ有限捩れ表示と既存の野生固定性により

    ∀ k∈K, W≤ker χ_k

を証明する。そこで既存の同じ J=I/W への商準同型を通じて χ̄_k を構成し、
標準商位相に対する連続性、元の同じ慣性値の保持を証明した。

さらに χ̄_k の通常 H¹ 類 β_k を構成し、以前の実際の inflation を使って

    inflation(β_k)=k.val

を任意の k∈K に対して証明した。一つの障害類だけの結果から、係数核全体へ広げた。
ここでも新しい inflation provider や cochain の選択を入力にしていない。

## 4. 核の全指標に共通する実際の有限商

J の元 t について、全ての k の指標値を同時に記録する準同型

    Ψ:J→∏(k∈K), Multiplicative F,    Ψ(t)(k)=χ̄_k(t)

を構成する。N=ker Ψ は同じ実際の正規部分群。
K の有限性を前回の実際の p 冪濃度から証明する。
F も元の有限商 Q の部分群で有限かつ離散なので、K 個の有限積は離散。
全ての χ̄_k の連続性から Ψ は連続、N は開である。

第一同型定理により、同じ実際の群商

    H=J/N

は有限となる。全ての核指標の値はこの H 上へ同時に因子化する。
H 上の全ての値が二つの核元について一致すれば、その核元は一致することも証明した。
**有限 H の巡回性、または一元生成性は証明していない。**

## 5. 元の τ を含む有限検出集合と測定数の制約

全評価分離性により、K の任意の非零元 k はある実際の σ∈I で検出できる。
有限 K の各非零元についてそのような σ を選び、指定した σ₀ も加える。
重複を除いた有限集合 Ω を構成すると

    σ₀∈Ω,  |Ω|≤|K|,
    Eval_Ω:K→ₗ[ℤ](Ω→F),  Eval_Ω(k)(σ)=ev_σ(k)

は単射となる。零元には検出元を選ばないので、指定元の追加後も |K| の上界を保つ。
元の障害証明書には σ₀=τ を使い、以前の同じ障害値を検出集合に残す。

単射の一般的な濃度帰結として |K| は |F|^|Ω| を割る。
前回の指数を入れると

    t+u≤r·|Ω|

となる。単射性の仮定を取るのはこの一般的な濃度補題だけである。
最終定理では単射な Ω を内部構成してその補題を適用し、追加の単射性入力は要求しない。

最終定理 `residual_exists_finitely_detected_coefficient_kernel` は元の hclass と Cofixed から
同じ n,T,q,A,τ,y,h を取り、τ を含む実際の Ω、有限評価の単射性、共通商の有限性、
全ての核指標の連続性と同じ inflation の値、上の指数制約を出力する。

## 模範解答との比較と次の未解決箇所

ローカル模範解答の `S_ValuationSubring_exists_tame_generator_inertiaSubgroupIn` の
有限段の生成元構成を読み、次の結論と、その内部の tail の冪根存在の証明への依存を確認した。
参照 HEAD は 115356cbc627159d0d16add0da6e9a2bb3655ed8。

    ∃ γ∈I, ∀ τ∈I, ∃ j:ℕ, ∃ x,w∈I, τ=γ^j·x^(p^m)·w^(p^m)

これは単に「J は procyclic」と仮定して済ませる経路ではなく、有限段の冪誤差を伴う
具体的な分解を算術的に構成する経路である。DkMath には、この生成元存在と必要な
付値環上の tail の冪根存在を今回移植していない。未証明の hgen/htail としても加えない。
W と標準的な野生慣性との同定も今回の成果に含めない。

今回の有限集合 Ω と共通有限商 H は、これらの生成元存在を使わず内部構成したもの。
Ω を一つの適切な元へ縮約するには、さらにその有限段生成構造との接続が必要となる。
元の障害元 τ 自体が生成元であるという保証もない。

今回も通常の群コホモロジーを使い、K の各類に実際の連続な代表指標を与えた。
連続 H¹ との比較同型や、その理論全体は構成していない。
大域類群への同定・hclass の供給・共鳴障害の算術的排除は残る。
**無条件の一般 hno は引き続き未完成である。**

## 検証の範囲

ZMod5 の二次元空間の実際の双線形評価族を回帰検査に使う。
全評価は単射だが、任意の単一線形評価から ZMod5 へは濃度の差で単射になれないことを検査する。
実際の共通核による商の濃度25、p 倍零性も確認し、有限性から一元生成を推論する誤りを防ぐ。
新規28宣言の再帰依存監査、28件の公開入力監査、全宣言の公理出力を通常入口へ接続する。
検証結果は `evidence/validation-note032-frey-kernel-finite-detector.txt`、
モデルと Mathlib の参照 SHA-256 は `evidence/note032-frey-kernel-finite-detector-reference-audit.json` に保存する。

## コピペ用 Lean 全文

### 1. DkMath.FLT.FreyKernelEvaluationConstraints

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationCertificate

#print "file: DkMath.FLT.FreyKernelEvaluationConstraints"

/-!
# 実際の評価像の包含による指数制約

評価像 B は元の F の部分群。従って |B|=p^t, |F|=p^r なら t≤r。
同じ指数収支と合わせ、評価核の下界も得る。単一評価の単射性は仮定しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 実際の評価像の濃度は、元の固定係数群 F の濃度を割る。 -/
theorem ResidualCyclicStage.fixedEvaluation_image_card_dvd (σ : inertiaSubgroupIn A ℚ) :
    Nat.card (LinearMap.range (T.fixedKernelEvaluation A σ)) ∣
      Nat.card (T.inertiaFixedUpperQuotient A) :=
  (LinearMap.range (T.fixedKernelEvaluation A σ)).toAddSubgroup.card_addSubgroup_dvd_card

variable {T A} {q : ℕ} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の同じ三指数に t≤r と評価核の下界を加える。 -/
theorem NarrowAbsorptionObstruction.fixed_evaluation_constrained_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
    ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ r ∧ u ≤ n + 1 ∧
      n + 3 - 2 * r ≤ u ∧ r + t + u = n + 3 ∧
      Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
      Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
      Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  obtain ⟨r, t, u, hr, hrb, ht, _, hu, hsum, hF, hB, hU, hK⟩ :=
    h.fixed_evaluation_balanced_profile hp5
  have hd := T.fixedEvaluation_image_card_dvd A ⟨τ, h.inertia⟩
  rw [hB, hF] at hd
  have htr := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨r, t, u, hr, hrb, ht, htr, hu, by omega, hsum, hF, hB, hU, hK⟩

end
end DkMath.FLT.Frey.Source
```

### 2. DkMath.FLT.FreyKernelCharacterContinuity

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelEvaluationConstraints

#print "file: DkMath.FLT.FreyKernelCharacterContinuity"

/-!
# 係数核の全ての元を元の有限捩れ差分で表し、連続性を回収する

通常 H¹ 全体の連続性は主張しない。実際の係数核 K の元だけを、既存の
Q/F≃K と二つの商写像の全射性により元の有限捩れ点へ戻す。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 同じ通常 H¹ 同型による、核の元 k に対応する準同型。 -/
def ResidualCyclicStage.fixedKernelCharacter (k : T.fixedH1CoefficientKernel A) :
    inertiaSubgroupIn A ℚ →* Multiplicative (T.inertiaFixedUpperQuotient A) where
  toFun σ := Multiplicative.ofAdd (T.fixedKernelEvaluation A σ k)
  map_one' := (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom k.val |>.map_zero
  map_mul' σ τ := (groupCohomology.H1IsoOfIsTrivial
    (TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))).hom k.val |>.map_add
      (Additive.ofMul σ) (Additive.ofMul τ)

/-- 核指標の値は、以前構成した実際の評価値そのもの。 -/
theorem ResidualCyclicStage.fixedKernelCharacter_apply (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.fixedKernelCharacter A k σ) = T.fixedKernelEvaluation A σ k := rfl

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)

/-- K の任意の元は、元の有限捩れ点 x の同じ連結像で表せる。 -/
theorem ResidualCyclicStage.exists_torsion_fixedKernelElement (k : T.fixedH1CoefficientKernel A) :
    ∃ x : Torsion S.rationalCurve (p ^ (n + 1 + 1)),
      T.fixedCosetKernelElement hp5 hq hqp haddr A hA x = k := by
  obtain ⟨z, rfl⟩ := (T.quotientConnectingKernelEquiv A hp5 hq hqp haddr hA).surjective k
  obtain ⟨u, rfl⟩ := (T.fixedCoefficientSubmodule A).mkQ_surjective z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  exact ⟨x, (T.quotientKernelEquiv_coset A hp5 hq hqp haddr hA x).symm⟩

/-- 核元を有限捩れ点で表すと、指標全体が元の同じ固定差分指標になる。 -/
theorem ResidualCyclicStage.fixedKernelCharacter_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedKernelCharacter A (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
      T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x := by
  apply MonoidHom.ext
  intro σ
  exact congrArg Multiplicative.ofAdd (T.fixedKernelEvaluation_coset A hp5 hq hqp haddr hA x σ)

include hp5 hq hqp haddr hA in
/-- K の全ての元の指標は、元の Krull 部分群位相から連続である。 -/
theorem ResidualCyclicStage.fixedKernelCharacter_continuous (k : T.fixedH1CoefficientKernel A) :
    Continuous (T.fixedKernelCharacter A k) := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]
  exact T.inertiaFixedDifferenceCharacter_continuous hp5 hq hqp haddr A hA x

end
end DkMath.FLT.Frey.Source
```

### 3. DkMath.FLT.FreyKernelTameDescent

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelCharacterContinuity

#print "file: DkMath.FLT.FreyKernelTameDescent"

/-!
# 実際の係数核全体の野生零性・馴分岐降下・通常 H¹ inflation

一つの障害類だけでなく K の任意の元を、同じ野生合同部分群 W で割った J=I/W へ降ろす。
W と標準的な野生慣性との同定や J の procyclic 性は使わない。
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

/-- K の全ての指標は、以前の同じ野生合同部分群上で零になる。 -/
theorem ResidualCyclicStage.wild_le_fixedKernelCharacter_kernel (k : T.fixedH1CoefficientKernel A) :
    wildInertiaSubgroup A ≤ (T.fixedKernelCharacter A k).ker := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]
  exact T.wildInertia_le_fixed_character_kernel hp5 hq hqp haddr A hA x

/-- 任意の同じ核元の指標を、元の実際の商 J=I/W へ降ろす。 -/
def ResidualCyclicStage.fixedKernelTameCharacter (k : T.fixedH1CoefficientKernel A) :
    tameInertiaQuotient A →* Multiplicative (T.inertiaFixedUpperQuotient A) :=
  QuotientGroup.lift (wildInertiaSubgroup A) (T.fixedKernelCharacter A k)
    (T.wild_le_fixedKernelCharacter_kernel A hp5 hq hqp haddr hA k)

/-- 商に降ろしても、同じ慣性元における同じ値を保持する。 -/
theorem ResidualCyclicStage.fixedKernelTameCharacter_mk (k : T.fixedH1CoefficientKernel A)
    (σ : inertiaSubgroupIn A ℚ) :
    T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k (QuotientGroup.mk σ) =
      T.fixedKernelCharacter A k σ := rfl

/-- K の全ての降下指標は、同じ標準商位相から連続。 -/
theorem ResidualCyclicStage.fixedKernelTameCharacter_continuous (k : T.fixedH1CoefficientKernel A) :
    Continuous (T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k) := by
  apply continuous_quot_lift
  exact T.fixedKernelCharacter_continuous A hp5 hq hqp haddr hA k

/-- 元の有限捩れ点で表された場合、以前の同じ馴分岐指標を回収する。 -/
theorem ResidualCyclicStage.fixedKernelTameCharacter_coset
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedKernelTameCharacter A hp5 hq hqp haddr hA
      (T.fixedCosetKernelElement hp5 hq hqp haddr A hA x) =
      T.fixedTameCharacter hp5 hq hqp haddr A hA x := by
  apply MonoidHom.ext
  intro t
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective t
  change T.fixedKernelCharacter A _ σ = _
  rw [T.fixedKernelCharacter_coset A hp5 hq hqp haddr hA x]
  rfl

/-- 全ての核元に対する、降下指標の通常の H¹ 類。 -/
def ResidualCyclicStage.fixedKernelTameClass (k : T.fixedH1CoefficientKernel A) :=
  TrivialCharacterH1.cohomologyClass (T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k)

/-- 同じ実際の inflation が、任意の同じ核元の値を回収する。 -/
theorem ResidualCyclicStage.fixedKernelTameClass_inflation (k : T.fixedH1CoefficientKernel A) :
    T.fixedH1Inflation A (T.fixedKernelTameClass A hp5 hq hqp haddr hA k) = k.val := by
  obtain ⟨x, rfl⟩ := T.exists_torsion_fixedKernelElement A hp5 hq hqp haddr hA k
  unfold fixedKernelTameClass
  rw [T.fixedKernelTameCharacter_coset A hp5 hq hqp haddr hA x]
  exact (T.fixedTameClass_inflation hp5 hq hqp haddr A hA x).trans
    (T.fixedCosetKernelElement_val hp5 hq hqp haddr A hA x).symm

end
end DkMath.FLT.Frey.Source
```

### 4. DkMath.FLT.FreyKernelCommonTameQuotient

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelTameDescent

#print "file: DkMath.FLT.FreyKernelCommonTameQuotient"

/-!
# 核全体の全指標に共通する、実際の有限な馴分岐商

同じ J=I/W から全ての核指標の値を同時に記録する。核 K と F の実際の有限性から
共通核は開で、商は有限。有限商の巡回性や一元生成性は主張しない。
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

/-- 元の Q/F との同型から、実際の係数核全体は有限である。 -/
theorem ResidualCyclicStage.fixedKernel_finite : Finite (T.fixedH1CoefficientKernel A) := by
  obtain ⟨s, _, hc⟩ := T.fixedKernel_prime_power_profile A hp5 hq hqp haddr hA
  exact Nat.finite_of_card_ne_zero (hc.trans_ne (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

/-- 同じ J の元について、同じ全ての核指標の値を同時に記録する準同型。 -/
def ResidualCyclicStage.fixedKernelTameFamily :
    tameInertiaQuotient A →* (T.fixedH1CoefficientKernel A → Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  MonoidHom.pi (fun k => T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k)

/-- 共通核への所属は、全ての同じ核指標の値が 1 になること。 -/
theorem ResidualCyclicStage.mem_fixedKernelTameFamily_kernel (t : tameInertiaQuotient A) :
    t ∈ (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker ↔
      ∀ k, T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k t = 1 := by
  change (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) t = 1 ↔ _
  exact ⟨fun he k => congrFun he k, fun he => funext he⟩

/-- 全ての同じ馴分岐値の族も、元の商位相から連続。 -/
theorem ResidualCyclicStage.fixedKernelTameFamily_continuous :
    Continuous (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) :=
  continuous_pi fun k => T.fixedKernelTameCharacter_continuous A hp5 hq hqp haddr hA k

/-- K の有限性と離散有限係数により、この共通正規核は開。 -/
theorem ResidualCyclicStage.fixedKernelTameFamily_kernel_isOpen :
    IsOpen ((T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker : Set (tameInertiaQuotient A)) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  change IsOpen ((T.fixedKernelTameFamily A hp5 hq hqp haddr hA) ⁻¹' {1})
  exact (isOpen_discrete _).preimage (T.fixedKernelTameFamily_continuous A hp5 hq hqp haddr hA)

/-- 同じ全指標の共通核で割った、実際の J の群商。 -/
abbrev ResidualCyclicStage.fixedKernelCommonTameQuotient :=
  (tameInertiaQuotient A) ⧸ (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker

/-- 第一同型定理と実際の有限係数により、共通馴分岐商は有限。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameQuotient_finite :
    Finite (T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA) := by
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange
    (T.fixedKernelTameFamily A hp5 hq hqp haddr hA)).symm.toEquiv

/-- 全指標の値を、同じ実際の有限商上へ因子化する。 -/
def ResidualCyclicStage.fixedKernelCommonTameValues :
    T.fixedKernelCommonTameQuotient A hp5 hq hqp haddr hA →*
      (T.fixedH1CoefficientKernel A → Multiplicative (T.inertiaFixedUpperQuotient A)) :=
  QuotientGroup.lift (T.fixedKernelTameFamily A hp5 hq hqp haddr hA).ker
    (T.fixedKernelTameFamily A hp5 hq hqp haddr hA) le_rfl

/-- 共通商でも、元の同じ指標の同じ値を保つ。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameValues_mk (t : tameInertiaQuotient A)
    (k : T.fixedH1CoefficientKernel A) :
    T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA (QuotientGroup.mk t) k =
      T.fixedKernelTameCharacter A hp5 hq hqp haddr hA k t := rfl

/-- 有限商上の全ての評価が一致すれば、元の係数核の元が一致する。 -/
theorem ResidualCyclicStage.fixedKernelCommonTameValues_separates
    (x y : T.fixedH1CoefficientKernel A)
    (he : ∀ t, T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA t x =
      T.fixedKernelCommonTameValues A hp5 hq hqp haddr hA t y) : x = y := by
  apply T.fixedKernelEvaluation_separates A x y
  intro σ
  exact congrArg Multiplicative.toAdd (he (QuotientGroup.mk (QuotientGroup.mk σ)))

end
end DkMath.FLT.Frey.Source
```

### 5. DkMath.FLT.FreyKernelFiniteDetector

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyKernelCommonTameQuotient

#print "file: DkMath.FLT.FreyKernelFiniteDetector"

/-!
# 同じ核を識別する有限個の実際の慣性元

有限 K の各非零元を検出する実際の慣性元を選び、指定された元も保持する。
生成元の存在や単一評価の単射性を仮定せず、有限評価写像の単射性を構成する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 指定した有限集合 Ω の元による、元の実際の評価のベクトル。 -/
def ResidualCyclicStage.fixedFiniteEvaluation (Ω : Finset (inertiaSubgroupIn A ℚ)) :
    T.fixedH1CoefficientKernel A →ₗ[ℤ] (Ω → T.inertiaFixedUpperQuotient A) where
  toFun k σ := T.fixedKernelEvaluation A σ.val k
  map_add' x y := by funext σ; exact map_add (T.fixedKernelEvaluation A σ.val) x y
  map_smul' m x := by funext σ; exact (T.fixedKernelEvaluation A σ.val).map_smul' m x

/-- 有限評価が単射なら、実際の核の濃度は |F|^|Ω| を割る。 -/
theorem ResidualCyclicStage.fixedFiniteEvaluation_card_dvd
    (Ω : Finset (inertiaSubgroupIn A ℚ)) (hinj : Function.Injective (T.fixedFiniteEvaluation A Ω)) :
    Nat.card (T.fixedH1CoefficientKernel A) ∣ Nat.card (T.inertiaFixedUpperQuotient A) ^ Ω.card := by
  have hd := AddSubgroup.card_dvd_of_injective (T.fixedFiniteEvaluation A Ω).toAddMonoidHom hinj
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_coe] using hd

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- 指定した σ₀ を含む有限集合を構成し、全核をその評価で識別する。 -/
theorem ResidualCyclicStage.exists_finite_inertia_detector (σ₀ : inertiaSubgroupIn A ℚ) :
    ∃ Ω : Finset (inertiaSubgroupIn A ℚ), σ₀ ∈ Ω ∧
      Ω.card ≤ Nat.card (T.fixedH1CoefficientKernel A) ∧
      Function.Injective (T.fixedFiniteEvaluation A Ω) := by
  classical
  let := T.fixedKernel_finite A hp5 hq hqp haddr hA
  let := Fintype.ofFinite (T.fixedH1CoefficientKernel A)
  have hex (k : T.fixedH1CoefficientKernel A) (hk : k ≠ 0) :
      ∃ σ, T.fixedKernelEvaluation A σ k ≠ 0 := by
    by_contra! he
    apply hk
    apply T.fixedKernelEvaluation_separates A k 0
    intro σ
    exact (he σ).trans (map_zero _).symm
  let g : T.fixedH1CoefficientKernel A → inertiaSubgroupIn A ℚ :=
    fun k => if hk : k = 0 then 1 else Classical.choose (hex k hk)
  have hg (k : T.fixedH1CoefficientKernel A) (hk : k ≠ 0) :
      T.fixedKernelEvaluation A (g k) k ≠ 0 := by
    simpa only [g, dite_eq_right hk] using Classical.choose_spec (hex k hk)
  let D := (Finset.univ.erase (0 : T.fixedH1CoefficientKernel A)).image g
  let Ω := insert σ₀ D
  have hdet (k : T.fixedH1CoefficientKernel A)
      (he : ∀ σ ∈ Ω, T.fixedKernelEvaluation A σ k = 0) : k = 0 := by
    by_contra hk
    apply hg k hk
    apply he
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ _⟩, rfl⟩
  have hD : D.card ≤ Fintype.card (T.fixedH1CoefficientKernel A) - 1 := by
    calc
      D.card ≤ (Finset.univ.erase (0 : T.fixedH1CoefficientKernel A)).card := Finset.card_image_le
      _ = Fintype.card (T.fixedH1CoefficientKernel A) - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hΩ := Finset.card_insert_le σ₀ D
  have hpos : 0 < Fintype.card (T.fixedH1CoefficientKernel A) := Fintype.card_pos
  refine ⟨Ω, Finset.mem_insert_self _ _, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    change (insert σ₀ D).card ≤ _
    omega
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hdet
    intro σ hσ
    rw [map_sub, sub_eq_zero]
    exact congrFun hxy ⟨σ, hσ⟩

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
/-- 元の障害元を保持し、全核の有限検出・連続性・inflation 回収・指数制約を出力する。 -/
theorem residual_exists_finitely_detected_coefficient_kernel
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let ev := T.fixedKernelEvaluation A ⟨τ, h.inertia⟩
      ∃ Ω : Finset (inertiaSubgroupIn A ℚ), ⟨τ, h.inertia⟩ ∈ Ω ∧
        Ω.card ≤ Nat.card (T.fixedH1CoefficientKernel A) ∧
        Function.Injective (T.fixedFiniteEvaluation A Ω) ∧
        Finite (T.fixedKernelCommonTameQuotient A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over) ∧
        (∀ k : T.fixedH1CoefficientKernel A, Continuous (T.fixedKernelCharacter A k) ∧
          T.fixedH1Inflation A (T.fixedKernelTameClass A hp5 h.prime h.ne_torsion_prime
            (Or.inr h.support) h.lies_over k) = k.val) ∧
        ∃ r t u, 1 ≤ r ∧ r ≤ n + 2 ∧ 1 ≤ t ∧ t ≤ r ∧ u ≤ n + 1 ∧
          n + 3 - 2 * r ≤ u ∧ r + t + u = n + 3 ∧ t + u ≤ r * Ω.card ∧
          Nat.card (T.inertiaFixedUpperQuotient A) = p ^ r ∧
          Nat.card (LinearMap.range ev) = p ^ t ∧ Nat.card (LinearMap.ker ev) = p ^ u ∧
          Nat.card (T.fixedH1CoefficientKernel A) = p ^ (t + u) := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  obtain ⟨Ω, hτ, hΩ, hi⟩ := T.exists_finite_inertia_detector A hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) h.lies_over ⟨τ, h.inertia⟩
  obtain ⟨r, t, u, hr, hrb, ht, htr, hu, hul, hsum, hF, hB, hU, hK⟩ :=
    h.fixed_evaluation_constrained_profile hp5
  have hd := T.fixedFiniteEvaluation_card_dvd A Ω hi
  rw [hK, hF, ← pow_mul] at hd
  have hmeasure := (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hd
  exact ⟨n, T, q, A, τ, y, h, Ω, hτ, hΩ, hi,
    T.fixedKernelCommonTameQuotient_finite A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over,
    fun k => ⟨T.fixedKernelCharacter_continuous A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k,
      T.fixedKernelTameClass_inflation A hp5 h.prime h.ne_torsion_prime (Or.inr h.support) h.lies_over k⟩,
    r, t, u, hr, hrb, ht, htr, hu, hul, hsum, hmeasure, hF, hB, hU, hK⟩

end
end DkMath.FLT.Frey.Source
```


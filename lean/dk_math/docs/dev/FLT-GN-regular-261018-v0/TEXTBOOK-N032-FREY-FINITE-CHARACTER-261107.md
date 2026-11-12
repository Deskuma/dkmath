# NOTE-032 教科書 — 同じ有限慣性差分の像・連続性・開核

日付: 2026-11-07。`__REVIEW.md` の連続性・有限像の提案を参考に、次の4ステップを実装した。
この文書の4つの Lean ブロックは、それぞれ production ファイルの全文である。
import 直後の `#print "file: モジュール名"` はコピペ後の所属を識別するために保持する。
依存先を持つ DkMath の Lake 環境で、各ブロックを別ファイルとして検査できる。

## 数学的な到達点

同じ Frey 曲線 E、同じ残余直線 L、同じ巡回段 T（|T|=p^(n+1)）を固定する。
元の点への包含を保ったまま T を E[p^(n+2)] に持ち上げ、

    Q = E[p^(n+2)] / T

を取る。標数0の実際の楕円曲線捩れの濃度から、

    |Q| = p^(2(n+2)) / p^(n+1) = p^(n+3)

が成り立つ。ここでは元の段を、単に同型な別の群へ置き換えない。

悪い住所 q≠p、同じ付値環 A とその慣性群 I_A に対し、既存の局所積零性から

    c_x(σ) = [σx − x] : I_A → Q

は通常の加法的群準同型であり、全ての値は同じ商作用の慣性固定部分群 Q^(I_A) に属する。
今回、その部分群と値域制限を実際に定義する。
`Multiplicative` はこの同じ加法群の型タグであり、単元値 Tate 指標 χ∞・d とは異なる。

Galois 群には既存の Krull 位相、I_A にはその部分群位相、Q には標準商位相を使う。
元の torsion 軌道写像の連続性を合成することで c_x の連続性が従い、
核は **I_A の中で** 開かつ閉になる。絶対 Galois 群の中で開くという主張へ拡張しない。

像は Q の部分群なので、その濃度は p^s（0≤s≤n+3）。第一同型定理から

    |im c_x| = |I_A / ker c_x| = [I_A : ker c_x] = p^s

を得る。I_A 自体の有限性を仮定する必要はない。
従来の正確な `hclass` と同じ Cofixed 候補から得た障害証明書の y を基点にすると、
同じ証人 τ で c_y(τ)≠0、かつその値の厳密位数は p。
したがって s≥1 となり、正の p 冪指数の開核が得られる。
**一点の値の位数 p から、像全体の位数が p と結論することはできない。**

## 模範解答との照合

ローカル `fermats-last-theorem` の
`Theorems/Thm_WeierstrassCurve_isOpen_torsionBy_fixingSubgroup.lean`、その実装と、
`P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean:1242` の `hopen` 使用箇所を読んだ。
模範解答は全捩れを固定する部分群の開性を別途供給し、`hInert` と組み合わせる。
今回の DkMath 実装は既存の実際の捩れ軌道の連続性から同じ有限商の連続性へ進む。
外部 proof/provider を import せず、P2M/P2MW の証明を依存に加えない。
参照 HEAD と SHA-256 は `evidence/note032-frey-finite-character-reference-audit.json` に記録した。

## 保持する証明境界

`c_x(σ)=σ[x]−[x]` を、同じ商作用に関する実際の恒等式として公開した。
これは Q を係数とする coboundary の形であり、非零 H¹ 類の構成ではない。
今回、群コホモロジー API による H¹ の零性定理は追加していない。
通常の準同型として非自明であることと、この境界を混同しない。

全ての差分値が慣性固定でも、Q 全体が慣性固定とは限らない。
有限 p 群への連続準同型であることだけでは、それは零にならない。
野生慣性への制限の消滅、tame/Frobenius 関係と固定基点の q 倍則は未証明である。
既存の共役輸送恒等式では基点が移動することにも注意する。

`hclass` は rootField ζ の実際の ClassModP の ω² 固有空間消滅であり、最終存在定理に残る。
新しい連続性・有限性・像濃度・核指数・配置・吸収を算術 provider にしていない。
今回の結論は障害候補の有限連続な構造を精密化するもの。
その排除と `hclass` の算術的供給は残り、**無条件の一般 hno は未完成**である。

## 1. p 冪値域への準同型の像と核商

一般の群準同型に対する第一同型定理と Lagrange の濃度整除を使う。非自明な値があれば指数 s は正になる。

ソース: `DkMath/Lib/Algebra/FinitePrimePowerCharacter.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.Prime.Basic

#print "file: DkMath.Lib.Algebra.FinitePrimePowerCharacter"

/-!
# p 冪濃度の群に値を持つ準同型の像と核商

非自明な値があれば像の指数は正。野生慣性や分岐の消滅は仮定しない。
-/
namespace DkMath.Lib.Algebra.FinitePrimePowerCharacter
variable {Γ A : Type*} [Group Γ] [Group A] (f : Γ →* A)

/-- 同じ準同型の核商と実際の像の濃度は一致する。 -/
theorem card_quotient_kernel : Nat.card (Γ ⧸ f.ker) = Nat.card f.range :=
  Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

/-- 値域の濃度 p^m から、像と核商の同じ濃度 p^s を内部計算する。 -/
theorem image_profile {p m : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ m) :
    ∃ s ≤ m, Nat.card f.range = p ^ s ∧ Nat.card (Γ ⧸ f.ker) = p ^ s ∧ f.ker.index = p ^ s := by
  have hd : Nat.card f.range ∣ p ^ m := hA ▸ Subgroup.card_subgroup_dvd_card f.range
  obtain ⟨s, hs, hc⟩ := (Nat.dvd_prime_pow hp).mp hd
  exact ⟨s, hs, hc, (card_quotient_kernel f).trans hc, (Subgroup.index_ker f).trans hc⟩

/-- 非自明な同じ準同型では s≥1。像と開核候補の指数を取り違えない。 -/
theorem nontrivial_image_profile {p m : ℕ} (hp : p.Prime) (hA : Nat.card A = p ^ m)
    (hf : ∃ g, f g ≠ 1) :
    ∃ s, 1 ≤ s ∧ s ≤ m ∧ Nat.card f.range = p ^ s ∧
      Nat.card (Γ ⧸ f.ker) = p ^ s ∧ f.ker.index = p ^ s := by
  obtain ⟨s, hs, hc, hq, hi⟩ := image_profile f hp hA
  have hne : Nat.card f.range ≠ 1 := by
    intro h
    have hsub := (Nat.card_eq_one_iff_unique.mp h).1
    obtain ⟨g, hg⟩ := hf
    exact hg (congrArg Subtype.val (hsub.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1))
  have hs0 : s ≠ 0 := by intro h; exact hne (by rw [hc, h, pow_zero])
  exact ⟨s, by omega, hs, hc, hq, hi⟩

end DkMath.Lib.Algebra.FinitePrimePowerCharacter
```

## 2. 元の段を保つ持ち上げと正確な商濃度

点を保つ加法同型で持ち上げ段の濃度を元の T へ戻し、実際の捩れ群の濃度から商濃度を計算する。

ソース: `DkMath/FLT/FreyStageUpperQuotientCard.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageUpperQuotient
import DkMath.Lib.NumberTheory.EllipticTorsionAllCard

#print "file: DkMath.FLT.FreyStageUpperQuotientCard"

/-!
# 元の同じ段による一段上の捩れ商の正確な濃度

E[p^(n+2)]/T の濃度は p^(n+3)。元の点と段を保つ加法同型で計算する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 上位捩れ内の段と元の同じ T は、同じ点を保つ加法同型。 -/
def ResidualCyclicStage.upperStageEquiv (T : S.ResidualCyclicStage L n) :
    T.upperStage ≃+ T.carrier where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, by
    change p ^ (n + 1 + 1) • x.val = 0
    rw [pow_succ, mul_nsmul, T.killed x.val x.property, nsmul_zero]⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- 元の段の濃度をそのまま保持する。 -/
theorem ResidualCyclicStage.upperStage_card (T : S.ResidualCyclicStage L n) :
    Nat.card T.upperStage = p ^ (n + 1) :=
  (Nat.card_congr T.upperStageEquiv.toEquiv).trans T.card

/-- 実際の一段上の有限捩れ商の濃度は正確に p^(n+3)。 -/
theorem ResidualCyclicStage.upperQuotient_card (T : S.ResidualCyclicStage L n) :
    Nat.card T.upperQuotient = p ^ (n + 3) := by
  let : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
  have hc := T.upperStage.card_eq_card_quotient_mul_card_addSubgroup
  rw [card_torsion_sq S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), T.upperStage_card] at hc
  apply mul_right_cancel₀ (pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero)
  calc
    Nat.card T.upperQuotient * p ^ (n + 1) = (p ^ (n + 1 + 1)) ^ 2 := hc.symm
    _ = p ^ (n + 3) * p ^ (n + 1) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

end
end DkMath.FLT.Frey.Source
```

## 3. 同じ作用と差分準同型の連続性

既存の軌道の連続性から標準商作用と差分を構成する。核の開閉性と、同じ商元の作用差という恒等式を証明する。

ソース: `DkMath/FLT/FreyStageUpperQuotientTopology.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyStageUpperQuotientCard
import DkMath.FLT.FreyInertiaDifferenceCharacter
import DkMath.Lib.NumberTheory.EllipticTorsionContinuity
import Mathlib.Topology.Algebra.Group.Quotient

#print "file: DkMath.FLT.FreyStageUpperQuotientTopology"

/-!
# 同じ有限商・Galois 作用・慣性差分の連続性

元の Krull 位相、慣性の部分群位相、標準商位相を保つ。
連続性や開核を新しい provider として要求しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}

/-- 離散な有限捩れ群の標準商位相は離散。別の位相へ取り替えない。 -/
instance ResidualCyclicStage.upperQuotientDiscreteTopology (T : S.ResidualCyclicStage L n) :
    DiscreteTopology T.upperQuotient := QuotientAddGroup.discreteTopology (isOpen_discrete _)

/-- 同じ実際の商作用の各軌道写像は Krull 位相から連続。 -/
theorem ResidualCyclicStage.upperQuotient_orbit_continuous (T : S.ResidualCyclicStage L n)
    (z : T.upperQuotient) : Continuous (fun σ : Field.absoluteGaloisGroup ℚ => T.upperQuotientAction σ z) := by
  refine QuotientAddGroup.induction_on z ?_
  intro x
  change Continuous (fun σ : Field.absoluteGaloisGroup ℚ =>
    (QuotientAddGroup.mk' T.upperStage) (representation S.rationalCurve (p ^ (n + 1 + 1)) σ x))
  exact (continuous_of_discreteTopology : Continuous (QuotientAddGroup.mk' T.upperStage)).comp
    (representation_orbit_continuous S.rationalCurve _ x)

/-- Galois 元と同じ商元の両変数について連続。 -/
theorem ResidualCyclicStage.upperQuotient_action_continuous (T : S.ResidualCyclicStage L n) :
    Continuous (fun z : Field.absoluteGaloisGroup ℚ × T.upperQuotient => T.upperQuotientAction z.1 z.2) := by
  rw [continuous_prod_of_discrete_right]
  intro z
  exact T.upperQuotient_orbit_continuous z

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)
    (n : ℕ) (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ有限点を基点とする実際の慣性差分準同型は連続。 -/
theorem inertiaDifferenceCharacter_continuous (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    Continuous (S.inertiaDifferenceCharacter n hp5 hq hqp haddr A hA x) := by
  change Continuous (fun σ : inertiaSubgroupIn A ℚ =>
    Multiplicative.ofAdd (representation S.rationalCurve (p ^ (n + 1)) σ.val x - x))
  exact continuous_ofAdd.comp
    (((representation_orbit_continuous S.rationalCurve _ x).comp (@continuous_subtype_val (Field.absoluteGaloisGroup ℚ) _ (fun σ => σ ∈ inertiaSubgroupIn A ℚ))).sub continuous_const)

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 元の同じ有限商への慣性差分準同型も連続。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_continuous
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    Continuous (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x) := by
  exact (continuous_of_discreteTopology : Continuous (QuotientAddGroup.mk' T.upperStage).toMultiplicative).comp
    (S.inertiaDifferenceCharacter_continuous (n + 1) hp5 hq hqp haddr A hA x)

/-- 同じ準同型の実際の核は開かつ閉。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_kernel_isClopen
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    IsClopen ((T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x).ker :
      Set (inertiaSubgroupIn A ℚ)) := by
  have hc := T.inertiaQuotientDifferenceCharacter_continuous hp5 hq hqp haddr A hA x
  change IsClopen ((T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x) ⁻¹' {1})
  exact ⟨isClosed_singleton.preimage hc, (isOpen_discrete {1}).preimage hc⟩

/-- この差分は同じ商元を基点とする作用差そのもの。非零 H¹ 類の主張ではない。 -/
theorem ResidualCyclicStage.inertiaQuotientDifferenceCharacter_coboundary
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) =
      T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
        (QuotientAddGroup.mk' T.upperStage) x := by
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 hq hqp haddr A hA x σ, map_sub]
  rfl

end
end DkMath.FLT.Frey.Source
```

## 4. 慣性固定部分群と障害証明書の有限像

値域を実際の固定部分群へ制限し、同じ hclass と Cofixed 候補から正の p 冪指数の開核を内部供給する。

ソース: `DkMath/FLT/FreyInertiaCharacterFiniteImage.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.FinitePrimePowerCharacter
import DkMath.FLT.FreyStageUpperQuotientTopology

#print "file: DkMath.FLT.FreyInertiaCharacterFiniteImage"

/-!
# 同じ慣性固定商への差分と有限像・開核の証明書

hclass と同じ Cofixed 候補から、正の p 冪指数の開核を内部構成する。
連続性・有限性・像の濃度を追加仮定にしない。非自明な coboundary の有限像であり、
非零 H¹ 類、野生慣性の消滅、Frobenius の q 倍則を主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.Algebra
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 元の同じ商作用について、全慣性群が固定する元の加法部分群。 -/
def ResidualCyclicStage.inertiaFixedUpperQuotient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    AddSubgroup T.upperQuotient where
  carrier := {z | ∀ σ ∈ inertiaSubgroupIn A ℚ, T.upperQuotientAction σ z = z}
  zero_mem' := by intro σ _; exact map_zero _
  add_mem' := by intro x y hx hy σ hσ; rw [map_add, hx σ hσ, hy σ hσ]
  neg_mem' := by intro x hx σ hσ; rw [map_neg, hx σ hσ]

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 既存の同じ差分準同型の値域を、実際の慣性固定部分群へ制限する。 -/
def ResidualCyclicStage.inertiaFixedDifferenceCharacter
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    inertiaSubgroupIn A ℚ →* Multiplicative (T.inertiaFixedUpperQuotient A) where
  toFun σ := Multiplicative.ofAdd ⟨Multiplicative.toAdd
    (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ), by
      intro τ hτ
      exact T.inertiaQuotientDifferenceCharacter_values_fixed hp5 hq hqp haddr A hA x ⟨τ, hτ⟩ σ⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_one (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x))
  map_mul' σ τ := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (map_mul (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x) σ τ)

/-- 値域制限後も、元の商の同じ値である。 -/
theorem ResidualCyclicStage.inertiaFixedDifferenceCharacter_apply
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) (σ : inertiaSubgroupIn A ℚ) :
    (Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ)).val =
      Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x σ) := rfl

/-- 同じ実際の商の濃度から、像・核商・核の指数を一つの p 冪に同定する。 -/
theorem ResidualCyclicStage.inertia_character_image_profile
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    let c := T.inertiaQuotientDifferenceCharacter hp5 hq hqp haddr A hA x
    ∃ s ≤ n + 3, Nat.card c.range = p ^ s ∧
      Nat.card ((inertiaSubgroupIn A ℚ) ⧸ c.ker) = p ^ s ∧ c.ker.index = p ^ s := by
  apply FinitePrimePowerCharacter.image_profile _ (Fact.out : p.Prime)
  exact T.upperQuotient_card

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害点を基点にすると、像と開核の指数は正の p 冪。 -/
theorem NarrowAbsorptionObstruction.inertia_character_finite_profile
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
    IsClopen (c.ker : Set (inertiaSubgroupIn A ℚ)) ∧
      ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card c.range = p ^ s ∧
        Nat.card ((inertiaSubgroupIn A ℚ) ⧸ c.ker) = p ^ s ∧ c.ker.index = p ^ s := by
  refine ⟨T.inertiaQuotientDifferenceCharacter_kernel_isClopen hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩, ?_⟩
  exact FinitePrimePowerCharacter.nontrivial_image_profile _ (Fact.out : p.Prime)
    T.upperQuotient_card ⟨⟨τ, h.inertia⟩, (h.inertia_character_nontrivial hp5).1⟩

end
end DkMath.FLT.Frey.Source

namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation CyclotomicKernelField CyclotomicKummerWeight ValuationInertia
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
/-- 同じ hclass と Cofixed 候補から、非自明な有限像と正の p 冪指数の開核を内部供給する。 -/
theorem residual_exists_finite_inertia_character
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      let c := T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x
      c ⟨τ, h.inertia⟩ ≠ 1 ∧ addOrderOf (Multiplicative.toAdd (c ⟨τ, h.inertia⟩)) = p ∧
      IsClopen (c.ker : Set (inertiaSubgroupIn A ℚ)) ∧
        ∃ s, 1 ≤ s ∧ s ≤ n + 3 ∧ Nat.card c.range = p ^ s ∧
          Nat.card ((inertiaSubgroupIn A ℚ) ⧸ c.ker) = p ^ s ∧ c.ker.index = p ^ s := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, (h.inertia_character_nontrivial hp5).1, (h.inertia_character_nontrivial hp5).2,
    h.inertia_character_finite_profile hp5⟩

end
end DkMath.FLT.Frey.Source
```

## 検証の入口

`DkMath.Lib` / `DkMath.FLT` / `DkMath` から4モジュールを公開し、
`DkMathTest.lean` に有限例の回帰検査と再帰依存監査を追加した。
ZMod25 の5倍写像で像濃度5・核指数5・正の指数1を確認し、
自明な準同型では指数0が許されることも確認する。
全19新規 production 宣言の checked type・constructor・opaque proof value を再帰走査し、
16件の公開入力監査で継続する算術入力を明示する。
実行結果は `evidence/validation-note032-frey-finite-character.txt` を参照。

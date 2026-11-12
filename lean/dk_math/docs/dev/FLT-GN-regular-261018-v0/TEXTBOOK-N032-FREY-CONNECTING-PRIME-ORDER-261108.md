# NOTE-032 教科書 — 実際の inflation・短完全列・連結像・類の厳密位数 p

日付: 2026-11-08。最新レビューの長完全系列の提案とローカル模範解答を照合し、5ステップを実装した。
この文書の5つの Lean ブロックは、対応する5 production ファイルの全文である。
各 import 群直後の正確な `#print "file: モジュール名"` を保持する。
同じ DkMath の Lake 環境で、それぞれ別ファイルへコピペして検査できる。

## 同じ対象を保つ

同じ Frey 曲線 E、巡回段 T、有限商 Q=E[p^(n+2)]/T、慣性群 I、固定部分群 F=Q^I、
野生合同部分群 W と実際の馴分岐商 J=I/W を使う。
前回の固定係数類を α_J∈H¹(J,F)、α_I∈H¹(I,F) とする。
係数 F の作用は実際の固定性に対応する自明作用、Q の作用は元の実際の慣性作用である。
この文書の H¹ と H⁰ は Mathlib の **通常の群コホモロジー** を意味する。

## 1. 代表の一致から実際の H¹ inflation へ

前回は代表 cocycle の引き戻し値の一致を証明していた。
今回は実際の群商 I→J と、同じ F の恒等線形写像による制限表現の射を明示し、
Mathlib の `groupCohomology.map` で通常の H¹ inflation を構成した。
次数1の自然性から

    inf(α_J) = α_I

を同じクラスについて証明した。一般の inflation の単射性定理は追加していない。

## 2. 元の実際の係数の短完全列

F の同じ部分群を Q の整数部分加群として読み、元の Q の作用を Q/F へ降ろす。
元の包含と商写像を使い、表現の圏で

    0 → F → Q → Q/F → 0

という実際の `ShortComplex` と `ShortExact` を構成した。
包含の単射性は同じ部分群の包含、商写像の全射性は同じ標準商、
像と核の一致は同じ F の所属条件から証明する。
短完全性を新しい provider として要求しない。

## 3. 同じ不変剰余類と不変持ち上げ障害

元の同じ捩れ点 x の Q での商元を u=[x] とし、Q/F への像を ū とする。
局所積零性から σu−u は F に入るので

    ū ∈ (Q/F)^I

が成り立つ。これを実際の商表現の不変元として定義した。
同じ障害証明書では元の差分値が非零なので、ū≠0 も証明できる。
もし ū が Q の不変元 z から持ち上がれば、Q^I=F より z の Q/F での像は零になる。
従って同じ ū は Q の不変元による持ち上げを持たない。

これは不変元としての持ち上げの障害である。
元の Q への単なる持ち上げは u 自身が与えており、単なる持ち上げの不存在とは区別する。

## 4. Mathlib の連結準同型で同じ類を回収する

上の実際の短完全列の連結準同型を

    δ : H⁰(I,Q/F) → H¹(I,F)

とする。標準 H⁰ 同型で ū を H⁰ の元へ写し、Mathlib の `δ₀_apply` を使う。
同じ持ち上げ u に対して同じ固定係数 cocycle c_F は

    ι∘c_F(σ) = σu−u = d₀₁(u)(σ)

を満たす。したがって Mathlib の符号規約のまま

    δ(ū) = α_I

が成り立つ。この δ は独自に定義した似た写像ではなく、
`groupCohomology.δ` と実際の短完全性の証明から構成する連結準同型である。
前回の係数写像での零性は、この同じ連結像の構造と整合する。

## 5. 一つの値から飛躍せず、類そのものの厳密位数を確定する

一つの値の厳密位数が p というだけでは、指標全体や H¹ 類の位数は決まらない。
今回は元の障害証明書に保持されていた **p•y∈T** と元の段の Galois 安定性を使う。
任意の慣性元 σ について

    p•(σy−y) = σ(p•y)−p•y ∈ T

なので、元の Q での全ての差分値は p で消える。
包含 F→Q の単射性から同じ F 値も p で消え、同じ馴分岐商上でも全値が p で消える。
従って cocycle 全体、さらに H¹ への射影後の類全体について

    p•α_I=0,   p•α_J=0

が成り立つ。前回の同じ非零性と p の素数性を合わせて

    addOrderOf α_I = p,   addOrderOf α_J = p

を証明した。新しい全値の零化証明があるために、前回は主張しなかった厳密位数を今回確定できる。
像全体の濃度が p とまでは結論しない。

## 同じ算術証明書での終点

最終定理 `residual_exists_connecting_prime_order_H1` は従来の正確な hclass と同じ Cofixed 候補から、
元の n,T,q,A,τ,y と同じ障害証明書 h を取得する。
同じ x=⟨y,h.killed⟩ について、二つの通常の H¹ 類の厳密位数 p、実際の inflation 等式、
実際の連結像等式、不変持ち上げの不存在、元の係数写像での零性を一緒に出力する。

新しい短完全性・inflation・連結像・全値の零化・厳密位数を算術 provider にしていない。
局所幾何から不変剰余類を作る部分と、同じ証明書から非零性・零化を得る部分を明示している。
この非零連結像は整合した数学的構造であり、それ自体は矛盾ではない。

**今回も通常の群コホモロジーである。**
連続 H¹ との比較、大域円分類群との同定、両共鳴分岐の Frey 固有の算術的排除、hclass の供給は未完成。
**無条件の一般 hno は引き続き未完成。**

## 模範解答と Mathlib の照合

ローカル模範解答の `S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero.lean` で、
実際の H¹ inflation と代表 cocycle の自然性を照合した。
`S_groupCohomology_deltaCochain0_mem_coboundaries1_iff.lean` と
`S_groupCohomology_comp_mem_coboundaries1_iff_exists_invariants_sub_deltaCochain0.lean` では、
不変元の持ち上げと coboundary の関係を確認した。
今回は外部の独自 cochain 定義や連続版の provider を移植せず、
Mathlib の通常の `LongExactSequence.δ₀_apply` を使って同じ短完全列へ接続した。
外部の theorem/provider、P2M/P2MW は import しない。
参照 HEAD と SHA-256 は `evidence/note032-frey-connecting-reference-audit.json` に保存した。

## 1. 同じ固定係数類の H¹ inflation

制限表現からの係数の射を明示し、Mathlib の次数1の自然性を適用する。

ソース: `DkMath/FLT/FreyFixedH1Inflation.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInertiaH1CoefficientBoundary

#print "file: DkMath.FLT.FreyFixedH1Inflation"

/-!
# 同じ馴分岐固定係数類の実際の H¹ inflation

代表の値の一致を、Mathlib の通常の H¹ 写像の等式へ上げる。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 同じ F の恒等線形写像を、群商に沿う制限表現からの射として明示する。 -/
def ResidualCyclicStage.fixedInflationCoefficient (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Rep.res (QuotientGroup.mk' (wildInertiaSubgroup A))
      (TrivialCharacterH1.coefficient (tameInertiaQuotient A) (T.inertiaFixedUpperQuotient A)) ⟶
      TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- 同じ群商 I→J と同じ自明係数 F による、実際の通常の H¹ inflation。 -/
def ResidualCyclicStage.fixedH1Inflation (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  groupCohomology.map
    (A := TrivialCharacterH1.coefficient (tameInertiaQuotient A) (T.inertiaFixedUpperQuotient A))
    (B := TrivialCharacterH1.coefficient (inertiaSubgroupIn A ℚ) (T.inertiaFixedUpperQuotient A))
    (QuotientGroup.mk' (wildInertiaSubgroup A)) (T.fixedInflationCoefficient A) 1

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

/-- 同じ馴分岐類の inflation は、元の同じ慣性類そのもの。 -/
theorem ResidualCyclicStage.fixedTameClass_inflation
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedH1Inflation A (T.fixedTameH1Class hp5 hq hqp haddr A hA x) =
      T.fixedInertiaH1Class hp5 hq hqp haddr A hA x := by
  unfold fixedH1Inflation fixedTameH1Class fixedInertiaH1Class TrivialCharacterH1.cohomologyClass
  rw [groupCohomology.H1π_comp_map_apply]
  congr 1

end
end DkMath.FLT.Frey.Source
```

## 2. 同じ係数による実際の短完全列

元の部分群・商・作用を保ち、表現の圏で短完全性を証明する。

ソース: `DkMath/FLT/FreyFixedCoefficientSequence.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1Inflation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

#print "file: DkMath.FLT.FreyFixedCoefficientSequence"

/-!
# 元の実際の係数による短完全列 0→F→Q→Q/F→0

F=Q^I の元の部分群を整数部分加群と読み、元の慣性作用を商へ降ろす。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))

/-- 元の同じ固定部分群を、元の Q の整数部分加群として読む。 -/
abbrev ResidualCyclicStage.fixedCoefficientSubmodule : Submodule ℤ (T.fullInertiaCoefficient A) :=
  (T.inertiaFixedUpperQuotient A).toIntSubmodule

/-- 同じ固定部分加群は元の実際の慣性作用で安定。 -/
theorem ResidualCyclicStage.fixedCoefficient_stable (σ : inertiaSubgroupIn A ℚ) :
    T.fixedCoefficientSubmodule A ≤ (T.fixedCoefficientSubmodule A).comap
      ((T.fullInertiaCoefficient A).ρ σ) := by
  intro z hz
  change T.upperQuotientAction σ.val z ∈ T.inertiaFixedUpperQuotient A
  rw [hz σ.val σ.property]
  exact hz

/-- 元の Q/F への実際の商表現。 -/
def ResidualCyclicStage.fixedQuotientCoefficient : Rep ℤ (inertiaSubgroupIn A ℚ) :=
  (T.fullInertiaCoefficient A).quotient (T.fixedCoefficientSubmodule A) (T.fixedCoefficient_stable A)

/-- 同じ点をその商類へ写す、元の実際の表現の射。 -/
def ResidualCyclicStage.fixedCoefficientProjection :
    T.fullInertiaCoefficient A ⟶ T.fixedQuotientCoefficient A :=
  (T.fullInertiaCoefficient A).mkQ (T.fixedCoefficientSubmodule A) (T.fixedCoefficient_stable A)

/-- 元の包含と商写像による実際の短複体。 -/
def ResidualCyclicStage.fixedCoefficientSequence : ShortComplex (Rep ℤ (inertiaSubgroupIn A ℚ)) :=
  ShortComplex.mk (T.fixedCoefficientInclusion A) (T.fixedCoefficientProjection A) (by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro z
    change (T.fixedCoefficientSubmodule A).mkQ z.val = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr z.property)

-- 任意の Rep オブジェクトでは、その記録済み整数加群構造を使う。
attribute [local instance 2000] Rep.hV2

/-- 元の包含は単射で、元の商写像は全射、像は同じ核。 -/
theorem ResidualCyclicStage.fixedCoefficientSequence_shortExact :
    (T.fixedCoefficientSequence A).ShortExact := by
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply ((T.fixedCoefficientSequence A).exact_map_iff_of_faithful
      (forget₂ (Rep ℤ (inertiaSubgroupIn A ℚ)) (ModuleCat ℤ))).mp
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro z hz
    have hz' : z ∈ T.fixedCoefficientSubmodule A := (Submodule.Quotient.mk_eq_zero _).mp hz
    exact ⟨⟨z, hz'⟩, rfl⟩
  · apply (Rep.mono_iff_injective _).mpr
    exact Subtype.val_injective
  · apply (Rep.epi_iff_surjective _).mpr
    exact Submodule.mkQ_surjective _

end
end DkMath.FLT.Frey.Source
```

## 3. 同じ不変剰余類と持ち上げ障害

同じ作用差の固定性から不変剰余類を構成し、元の非自明な値から不変持ち上げを排除する。

ソース: `DkMath/FLT/FreyInvariantCosetObstruction.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedCoefficientSequence

#print "file: DkMath.FLT.FreyInvariantCosetObstruction"

/-!
# 同じ Q/F の不変剰余類と不変な持ち上げの障害

作用差が F に入るため [x]+F は不変。障害点では非零で、不変な Q の元へ持ち上がらない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

include hp5 hq hqp haddr hA in
/-- 元の同じ [x] を Q/F へ写すと、同じ実際の商作用で不変になる。 -/
def ResidualCyclicStage.fixedCosetInvariant
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    (T.fixedQuotientCoefficient A).ρ.invariants :=
  ⟨T.fixedCoefficientProjection A ((QuotientAddGroup.mk' T.upperStage) x), by
    intro σ
    change (T.fixedCoefficientSubmodule A).mkQ
        (T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x)) =
      (T.fixedCoefficientSubmodule A).mkQ ((QuotientAddGroup.mk' T.upperStage) x)
    have hm : T.upperQuotientAction σ.val ((QuotientAddGroup.mk' T.upperStage) x) -
        (QuotientAddGroup.mk' T.upperStage) x ∈ T.fixedCoefficientSubmodule A := by
      have hf := (Multiplicative.toAdd
        (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x σ)).property
      exact (T.inertiaQuotientDifferenceCharacter_coboundary hp5 hq hqp haddr A hA x σ) ▸ hf
    apply sub_eq_zero.mp
    exact (map_sub (T.fixedCoefficientSubmodule A).mkQ _ _).symm.trans
      ((Submodule.Quotient.mk_eq_zero _).mpr hm)⟩

variable {T} {A} {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 同じ障害証明書の不変剰余類は非零。 -/
theorem NarrowAbsorptionObstruction.fixedCoset_ne_zero
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val ≠ 0 := by
  dsimp only
  intro hz
  have hx : (QuotientAddGroup.mk' T.upperStage) (⟨y, h.killed⟩ : Torsion S.rationalCurve (p ^ (n + 1 + 1))) ∈
      T.fixedCoefficientSubmodule A := (Submodule.Quotient.mk_eq_zero _).mp hz
  apply (h.inertia_character_nontrivial hp5).1
  change Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩) = 0
  rw [T.inertiaQuotientDifferenceCharacter_coboundary hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ ⟨τ, h.inertia⟩, hx τ h.inertia, sub_self]

/-- この同じ剰余類は、元の Q の不変元による持ち上げを持たない。 -/
theorem NarrowAbsorptionObstruction.no_invariant_lift
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    ¬ ∃ z : (T.fullInertiaCoefficient A).ρ.invariants,
      T.fixedCoefficientProjection A z.val =
        (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val := by
  dsimp only
  rintro ⟨z, hz⟩
  have hz0 : T.fixedCoefficientProjection A z.val = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    intro σ hσ
    exact z.property ⟨σ, hσ⟩
  exact h.fixedCoset_ne_zero hp5 (hz.symm.trans hz0)

end
end DkMath.FLT.Frey.Source
```

## 4. 連結準同型による同じ類の回収

同じ持ち上げと同じ cocycle を Mathlib の δ₀_apply へ渡す。

ソース: `DkMath/FLT/FreyFixedH1Connecting.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyInvariantCosetObstruction

#print "file: DkMath.FLT.FreyFixedH1Connecting"

/-!
# 実際の短完全列の連結準同型で同じ H¹ 類を回収する

Mathlib の δ₀_apply の符号規約を使い、同じ [x]+F の像が同じ差分類であることを証明する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory CategoryTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)

/-- 同じ実際の短完全列に対する、通常の H⁰→H¹ 連結準同型。 -/
noncomputable abbrev ResidualCyclicStage.fixedConnecting (A : ValuationSubring (AlgebraicClosure ℚ)) :=
  groupCohomology.δ (T.fixedCoefficientSequence_shortExact A) 0 1 rfl

variable (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)

include hp5 hq hqp haddr hA in
/-- 同じ不変剰余類を、標準 H⁰ 同型で通常の H⁰ の元にする。 -/
def ResidualCyclicStage.fixedCosetH0
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :=
  (groupCohomology.H0Iso (T.fixedQuotientCoefficient A)).inv
    (T.fixedCosetInvariant hp5 hq hqp haddr A hA x)

/-- 実際の連結準同型の像は、以前構成した同じ固定係数 H¹ 類そのもの。 -/
theorem ResidualCyclicStage.fixedCoset_connecting
    (x : Torsion S.rationalCurve (p ^ (n + 1 + 1))) :
    T.fixedConnecting A (T.fixedCosetH0 hp5 hq hqp haddr A hA x) =
      T.fixedInertiaH1Class hp5 hq hqp haddr A hA x := by
  let f : (inertiaSubgroupIn A ℚ) → T.inertiaFixedUpperQuotient A :=
    TrivialCharacterH1.cocycle (T.inertiaFixedDifferenceCharacter hp5 hq hqp haddr A hA x)
  have hf : (T.fixedCoefficientInclusion A).hom ∘ f =
      groupCohomology.d₀₁ (T.fullInertiaCoefficient A) ((QuotientAddGroup.mk' T.upperStage) x) := by
    funext σ
    exact T.fixedCocycle_include_value hp5 hq hqp haddr A hA x σ
  exact groupCohomology.δ₀_apply (T.fixedCoefficientSequence_shortExact A)
    (T.fixedCosetInvariant hp5 hq hqp haddr A hA x)
    ((QuotientAddGroup.mk' T.upperStage) x) rfl f hf

end
end DkMath.FLT.Frey.Source
```

## 5. 全値の p 倍零性と通常の H¹ 類の厳密位数

元の前像条件・安定性から全値を零化し、既存の非零性と合わせて類の位数を p と確定する。

ソース: `DkMath/FLT/FreyFixedH1PrimeOrder.lean`

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyFixedH1Connecting

#print "file: DkMath.FLT.FreyFixedH1PrimeOrder"

/-!
# 同じ前像条件から全ての差分値の p 倍零性と類の厳密位数 p へ

一点の値の位数だけでは足りない。p•y∈T と元の安定性から全ての値を p で消し、
既存の非零性と合わせて通常の H¹ 類そのものの厳密位数を確定する。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ}
    {T : S.ResidualCyclicStage L n} {q : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}
    {τ : Field.absoluteGaloisGroup ℚ} {y : Points S.rationalCurve}

/-- 元の前像条件と安定性により、同じ固定係数指標の全ての値は p で消える。 -/
theorem NarrowAbsorptionObstruction.fixed_character_values_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) (σ : inertiaSubgroupIn A ℚ) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • Multiplicative.toAdd (T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime
      (Or.inr h.support) A h.lies_over x σ) = 0 := by
  apply Subtype.ext
  change p • Multiplicative.toAdd (T.inertiaQuotientDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ σ) = 0
  rw [T.inertiaQuotientDifferenceCharacter_apply hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩ σ, ← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff (N := T.upperStage) _).mpr
  change p • (pointAction S.rationalCurve σ.val y - y) ∈ T.carrier
  rw [nsmul_sub, ← map_nsmul]
  exact T.carrier.sub_mem (T.stable σ.val _ h.preimage) h.preimage

/-- 同じ慣性固定係数類そのものは p で消える。 -/
theorem NarrowAbsorptionObstruction.fixed_inertia_class_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x = 0 := by
  let f := T.inertiaFixedDifferenceCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  have hc : p • TrivialCharacterH1.cocycle f = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro σ
    exact h.fixed_character_values_killed hp5 σ
  change p • groupCohomology.H1π _ (TrivialCharacterH1.cocycle f) = 0
  rw [← map_nsmul, hc, map_zero]

/-- 同じ馴分岐固定係数類も、全ての同じ値の p 倍零性から p で消える。 -/
theorem NarrowAbsorptionObstruction.fixed_tame_class_killed
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    p • T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x = 0 := by
  let f := T.fixedTameCharacter hp5 h.prime h.ne_torsion_prime
    (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩
  have hc : p • TrivialCharacterH1.cocycle f = 0 := by
    apply groupCohomology.cocycles₁_ext
    intro t
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective t
    exact h.fixed_character_values_killed hp5 σ
  change p • groupCohomology.H1π _ (TrivialCharacterH1.cocycle f) = 0
  rw [← map_nsmul, hc, map_zero]

/-- 同じ二つの通常の H¹ 類は、非零性と全値の零化から厳密位数 p を持つ。 -/
theorem NarrowAbsorptionObstruction.fixed_H1_order_eq_prime
    (h : S.NarrowAbsorptionObstruction L T q A τ y) (hp5 : 5 ≤ p) :
    let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
    addOrderOf (T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p := by
  exact ⟨addOrderOf_eq_prime_iff.mpr ⟨h.fixed_tame_class_killed hp5, (h.fixed_H1_nonzero hp5).1⟩,
    addOrderOf_eq_prime_iff.mpr ⟨h.fixed_inertia_class_killed hp5, (h.fixed_H1_nonzero hp5).2⟩⟩

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
/-- 同じ算術証明書から、実際の inflation・連結像・厳密位数 p と不変持ち上げ障害を出力する。 -/
theorem residual_exists_connecting_prime_order_H1
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n) (q : ℕ)
      (A : ValuationSubring (AlgebraicClosure ℚ)) (τ : Field.absoluteGaloisGroup ℚ)
      (y : Points S.rationalCurve), ∃ h : S.NarrowAbsorptionObstruction L T q A τ y,
      let x : Torsion S.rationalCurve (p ^ (n + 1 + 1)) := ⟨y, h.killed⟩
      addOrderOf (T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      addOrderOf (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = p ∧
      T.fixedH1Inflation A (T.fixedTameH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) =
        T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ∧
      T.fixedConnecting A (T.fixedCosetH0 hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) =
        T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x ∧
      (¬ ∃ z : (T.fullInertiaCoefficient A).ρ.invariants,
        T.fixedCoefficientProjection A z.val =
          (T.fixedCosetInvariant hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x).val) ∧
      groupCohomology.map (MonoidHom.id (inertiaSubgroupIn A ℚ)) (T.fixedCoefficientInclusion A) 1
        (T.fixedInertiaH1Class hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over x) = 0 := by
  obtain ⟨n, T, q, A, τ, y, h⟩ := S.residual_exists_narrow_geometric_obstruction L hline hζ hp5 hclass hcofixed
  exact ⟨n, T, q, A, τ, y, h, (h.fixed_H1_order_eq_prime hp5).1, (h.fixed_H1_order_eq_prime hp5).2,
    T.fixedTameClass_inflation hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    T.fixedCoset_connecting hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩,
    h.no_invariant_lift hp5,
    T.fixedInertiaClass_map_zero hp5 h.prime h.ne_torsion_prime (Or.inr h.support) A h.lies_over ⟨y, h.killed⟩⟩

end
end DkMath.FLT.Frey.Source
```

## 検証

新規20宣言の checked type・constructor・opaque proof value の再帰依存監査と、
17件の公開入力監査を通常テスト入口へ追加した。
ZMod5 の恒等指標の全値の零化から通常の H¹ 類の厳密位数5を確認する。
ZMod25 の恒等指標では値5の位数は5だが、H¹ 類全体は5で消えない例を検査し、
一点の位数だけから類全体の零化を推論できないことを確認する。
実行結果は `evidence/validation-note032-frey-connecting-prime-order.txt` を参照。

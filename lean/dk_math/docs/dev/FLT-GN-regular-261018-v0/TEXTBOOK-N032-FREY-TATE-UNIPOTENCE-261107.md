# NOTE-032 教科書: 局所慣性ユニポテンスから条件付き hno の閉鎖へ

更新日: 2026-11-07。前回の共鳴慣性証人を、同じ曲線・同じ作用の局所幾何で排除する４ステップ。
今回、従来の hclass と全段の狭い hbad のもとで Cofixed 排除を閉じる。
算術入力を除去した一般 hno の完成とは区別する。

## 模範解答との照合

ローカルの模範解答 checkout `/home/deskuma/develop/github/fermats-last-theorem` を確認した。
`P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean` の局所吸収部分は、
慣性差が零成分へ入る定理と、剰余標数と素な零成分捩れの慣性固定性を組み合わせる。
対応する公開定理は次の２つである。

- `WeierstrassCurve.inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn`
- `WeierstrassCurve.exists_torsion_zeroComponent_submodule_of_multiplicativeReduction`

DkMath では既存の `EllipticNodalInertia.inertia_difference_smooth` と
`EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction` が必要な幾何学を供給する。
今回はこれらを直接接続し、Tate 曲線や外部の慣性ユニポテンス定理を新しい provider にしない。
模範の大域分類・Mazur Step Three を移植したという意味ではない。
参照 checkout のコミットとファイル SHA-256 は
`evidence/note032-frey-unipotence-reference-audit.json` に保存した。
外部 theorem や P2M/P2MW を本番コードへ import していない。

## 1. 同じ節点モデルの有限捩れ上の二次冪零性

n が付値単元なら、実際の n 捩れ点 P の慣性差 Q=τP−P も n 捩れである。
同じ有理曲線の節点中心は分解群で固定され、既存の局所幾何から Q は滑らかに還元する。
したがって同じ慣性群の任意の σ は Q を固定する。
これは (ρ(σ)−1)(ρ(τ)−1)=0 という実際の線形作用の等式である。
特に σ=τ とすれば (ρ(τ)−1)²=0 を得る。

汎用入口には同じモデル、モデル一致、臨界中心 C、接方向 D、次数の付値単元性を保持する。
滑らかさや差分冪零性を仮定しない。中心の固定性も既存の実際の定理から内部供給する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticNodalDecomposition
import DkMath.Lib.NumberTheory.EllipticNodalInertia
import DkMath.Lib.NumberTheory.EllipticSmoothReductionInertia

#print "file: DkMath.Lib.NumberTheory.EllipticNodalUnipotence"

/-!
# 同じ節点モデルの有限捩れ上の慣性差分

慣性差は滑らかに還元し、単元次数の滑らかな捩れ点は慣性に固定される。
同じ作用の差分積が零になることを証明する。Tate 曲線や分類定理を入力しない。
-/
namespace DkMath.Lib.NumberTheory.EllipticNodalUnipotence
open EllipticTorsionRepresentation EllipticCriticalCentre EllipticTangentDirections
open EllipticNodalDecomposition ValuationInertia
noncomputable section
variable (E : WeierstrassCurve ℚ) (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : WeierstrassCurve A)
    (hmodel : M.map A.subtype = E.baseChange (AlgebraicClosure ℚ))
    (C : CriticalCentre A (E.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    (hn : A.valuation (n : AlgebraicClosure ℚ) = 1)

include hmodel D hn

/-- 同じ慣性群の二元について、実際の差分作用の積は零。 -/
theorem inertia_difference_product_zero
    (σ τ : Field.absoluteGaloisGroup ℚ) (hσ : σ ∈ inertiaSubgroupIn A ℚ)
    (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (representation E n σ - 1) * (representation E n τ - 1) = 0 := by
  classical
  apply LinearMap.ext
  intro P
  let Q : Torsion E n := (representation E n τ - 1) P
  have hdec := (ValuationTameCharacter.TameCharacter.mem_inertiaSubgroupIn_iff.mp hτ).1
  have hs : EllipticGoodReductionSeparation.HasSmoothReduction M Q.val :=
    EllipticNodalInertia.inertia_difference_smooth E A M hmodel C D τ hτ
      (centre_decomposition_fixed E A C τ hdec) P.val
  have hf := EllipticSmoothReductionInertia.fixed_of_inertia_of_smooth_reduction E n A M
    hmodel hn σ hσ Q hs
  change representation E n σ Q - Q = 0
  exact sub_eq_zero.mpr hf

/-- 同じ有限捩れ作用の慣性差分は二次冪零。 -/
theorem inertia_difference_square_zero
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (representation E n τ - 1) ^ 2 = 0 := by
  rw [pow_two]
  exact inertia_difference_product_zero E n A M hmodel C D hn τ τ hτ hτ

end
end DkMath.Lib.NumberTheory.EllipticNodalUnipotence
```

## 2. Frey の全正冪段と全 Tate 点列へ

q≠p の悪い住所で、同じ Source の臨界中心と接方向を内部構成する。
p^(n+1) が付値単元であることも既存の素数支持計算から供給する。
したがって全ての有限 E[p^(n+1)] の作用で差分二次冪零性が成立する。
全 Tate 点列について各成分を同じ有限作用へ評価し、点列の外延性で全作用の等式を得る。

ここまでの局所定理には Cofixed、基底、hclass、全段の狭い hbad は不要である。
住所の条件は q=2 または q|abc、q≠p、実際の LiesOverPrime と慣性所属である。
q=p へ条件を拡張していない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyNonresonantInertia
import DkMath.FLT.FreyCyclicTateVector
import DkMath.Lib.Algebra.PrimePowerTateModule
import DkMath.Lib.NumberTheory.EllipticNodalUnipotence
import DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll

#print "file: DkMath.FLT.FreyTateInertiaUnipotent"

/-!
# 同じ Frey 曲線の全 Tate 慣性作用の二次冪零性

節点幾何と滑らかな捩れ固定性から、全有限段を経て同じ全点列へ接続する。
hclass・hbad・Cofixed・基底の存在はこの局所定理の入力ではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory
open EllipticTorsionRepresentation PrimePowerTateSequence ValuationInertia
noncomputable section
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- q≠p の悪い住所の同じ有限捩れ作用で、慣性差分は二次冪零。 -/
theorem prime_power_inertia_difference_square_zero (hp5 : 5 ≤ p) (n : ℕ)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (representation S.rationalCurve (p ^ (n + 1)) τ - 1) ^ 2 = 0 := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨C, ⟨D⟩⟩ := S.exists_geometry_at_bad_address hp5 haddr A hA
  exact EllipticNodalUnipotence.inertia_difference_square_zero S.rationalCurve _ A
    (S.valuationModel A) (S.valuationModel_map A) C D
    (CyclotomicFrobenius.prime_power_valuation_eq_one hq hqp A hA n) τ hτ

/-- 全点列の各成分で上の実際の有限作用を比較する。 -/
theorem tate_inertia_difference_square_zero (hp5 : 5 ≤ p)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (actionLinear (p := p) S.residualPointActionHom τ - 1) ^ 2 = 0 := by
  apply LinearMap.ext
  intro x
  apply PrimePowerTateSequence.ext
  intro n
  have h := S.prime_power_inertia_difference_square_zero hp5 n hq hqp haddr A hA τ hτ
  have he := congrArg (fun f : Module.End (ZMod (p ^ (n + 1)))
      (Torsion S.rationalCurve (p ^ (n + 1))) => (f ⟨evaluation n x, killed x n⟩).val) h
  exact he

end
end DkMath.FLT.Frey.Source
```

## 3. 同じ第二指標を慣性上で1と同定する

従来の条件付き塔から得た同じ全 Tate 基底を用いる。
線形作用の等式を toMatrixAlgEquiv で移すと、同じ行列 M に対し (M−I)²=0 となる。
M は以前証明した同じ上三角行列なので、その (1,1) 成分は (d−1)²=0 を与える。
ここで初めて、整域 ℤp の零因子がないことを使って d=1 と結論する。

有限環 ZMod(p^n) ではこの最後の消去を行ってはいけない。
例えば法25で (6−1)²=0 でも 6≠1 である。
全 Tate 作用へ戻したことが、実際の第二指標の同定を可能にする。
この同定と前回の有限商の同値により、同じ塔の全有限段で高位慣性吸収も得る。

基底と指標を参照するこの段階では hclass と全段の狭い hbad を保持する。
新しいユニポテンス・高位吸収・慣性自明性 provider は追加しない。
上右成分の消滅や Galois 表現の分裂は結論しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateInertiaUnipotent
import DkMath.FLT.FreyTateInertiaQuotient

#print "file: DkMath.FLT.FreyTateInertiaCharacters"

/-!
# 同じ第二 Tate 指標の悪い住所での慣性自明性

有限環の冪零元を消去しない。全 Tate 作用の二次冪零性を同じ基底へ写し、
整域 ℤp で第二対角成分を1と同定してから有限剰余へ戻す。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)
local notation "basis" => S.residualTateBasis L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad

open ValuationInertia

/-- 同じ全 Tate 行列の慣性差分が二次冪零。 -/
theorem residualTateActionMatrix_inertia_square_zero {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) :
    (mat τ - 1) ^ 2 = 0 := by
  have h := congrArg (LinearMap.toMatrixAlgEquiv basis)
    (S.tate_inertia_difference_square_zero hp5 hq hqp haddr A hA τ hτ)
  simp only [map_pow, map_sub, map_one, map_zero] at h
  exact h

/-- 整域 ℤp の第二対角成分により、同じ第二指標は同じ慣性元で1。 -/
theorem residualTateSecondCharacter_inertia_eq_one {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ) : d τ = 1 := by
  have hm := S.residualTateActionMatrix_inertia_square_zero L hline hcofixed hζ hp5 hclass hbad
    hq hqp haddr A hA τ hτ
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ_[p] => M 1 1) hm
  have hz := (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad τ).2
  have hd : (mat τ 1 1 - 1) * (mat τ 1 1 - 1) = 0 := by
    simpa [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hz] using he
  apply Units.ext
  change mat τ 1 1 = 1
  exact sub_eq_zero.mp ((mul_eq_zero.mp hd).elim id id)

/-- 同じ指標の実際の自明性から、全有限段の高位吸収を内部供給する。 -/
theorem residualFinite_inertia_absorbs_at_bad (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (τ : Field.absoluteGaloisGroup ℚ) (hτ : τ ∈ inertiaSubgroupIn A ℚ)
    {y : Points S.rationalCurve} (hy : p ^ (n + 1) • y = 0) :
    pointAction S.rationalCurve τ y - y ∈ (tower n).carrier := by
  apply (S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad n τ).mpr
  · rw [S.residualTateSecondCharacter_inertia_eq_one L hline hcofixed hζ hp5 hclass hbad
      hq hqp haddr A hA τ hτ, Units.val_one, map_one]
  · exact hy

end
end DkMath.FLT.Frey.Source
```

## 4. 前回の非自明証人を排除し、条件付き hno を閉じる

前回、同じ hclass と全段の狭い hbad のもとで、共鳴悪素点の慣性元 τ に対し
同じ第二指標 d(τ)≠1 となる証人を取り出した。
その q は q≥5、q≠p、q|abc なので、ステップ3をそのまま同じ A と τ に適用できる。
これにより d(τ)=1 と d(τ)≠1 が衝突し、同じ直線の Cofixed 性を排除する。

さらに全ての対象直線・段に狭い吸収を供給すれば、既存の hno 入力と同じ形の
「一次元安定 Cofixed 直線は存在しない」という命題が従う。
この endpoint は hclass と hbadAll を明示入力とし、hno 自体を仮定しない。

もう一つ、算術境界を調べるための帰結も実装する。
hclass と同じ Cofixed 直線を固定すれば、従来の狭い吸収が失敗する実際の段 T が存在する。
定義を展開すると、共鳴悪素点 q、同じ A の慣性元 τ、実際の点 y が存在して、
p・y∈T.carrier だが τy−y∉T.carrier となる。
この２つの失敗定理は全段 hbad を入力に要求しない。
前回の高位証人は p・y∉K だったが、今回は狭い条件そのものの領域内にある点を出力する。
両者の仮定と結論を取り違えない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateInertiaCharacters
import DkMath.FLT.FreyTateResonantWitness

#print "file: DkMath.FLT.FreyConditionalCofixedExclusion"

/-!
# 実際の局所ユニポテンスで条件付き Cofixed 排除を閉じる

前回の高位失敗証人を排除し、hclass と全段の狭い hbad のもとで矛盾を得る。
同じ hclass と Cofixed のもとでは狭い hbad 自体の失敗段も存在する。
一般 hno に対する算術入力の無条件供給は別問題である。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.Algebra DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation PrimePowerTateSequence
noncomputable section

open CyclotomicKernelField CyclotomicKummerWeight
variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic
variable (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p) (hp5 : 5 ≤ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ
variable
    (hclass : ∀ a : CyclotomicClassVanishing.ClassModP (rootField ζ) p,
      (∀ γ : (rootField ζ) ≃ₐ[ℚ] (rootField ζ),
        CyclotomicClassVanishing.classModPAction p γ a =
          (baseCharacter hζ γ : ZMod p) ^ 2 • a) → a = 0)
    (hbad : ∀ (n : ℕ) (T : S.ResidualCyclicStage L n), S.ResonantAbsorptionAt T.carrier)

include hline hζ hp5 hclass hbad in
/-- 既存の類群消滅と全段の狭い吸収を保持した、同じ直線の Cofixed 排除。
新しいユニポテンス・高位吸収・慣性自明性 provider は要求しない。 -/
theorem residual_not_cofixed_of_class_vanishing_and_resonant_absorption :
    ¬ IsCofixedOn S.residualRepresentation L := by
  intro hcofixed
  obtain ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, hd⟩ :=
    S.residualSecond_nontrivial_resonant_inertia L hline hcofixed hζ hp5 hclass hbad
  exact hd (S.residualTateSecondCharacter_inertia_eq_one L hline hcofixed hζ hp5 hclass hbad
    hq hqp (Or.inr hs) A hA τ hτ)

include hline hζ hp5 hclass in
/-- Cofixed な同じ直線では、類群消滅を保持すると、従来の狭い hbad 自体が失敗する段がある。 -/
theorem residual_exists_narrow_absorption_failure
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n), ¬ S.ResonantAbsorptionAt T.carrier := by
  classical
  by_contra h
  push Not at h
  exact S.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
    L hline hζ hp5 hclass h hcofixed

include hline hζ hp5 hclass in
/-- 同じ hclass と Cofixed のもとでは、狭い条件の領域内に実際の失敗点が存在する。
全段 hbad をこの定理の入力には要求しない。 -/
theorem residual_exists_narrow_absorption_counterexample
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    ∃ (n : ℕ) (T : S.ResidualCyclicStage L n),
      ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
        ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), ValuationInertia.LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ ∧
      ∃ y : Points S.rationalCurve, p • y ∈ T.carrier ∧
        pointAction S.rationalCurve τ y - y ∉ T.carrier := by
  classical
  obtain ⟨n, T, hf⟩ := S.residual_exists_narrow_absorption_failure L hline hζ hp5 hclass hcofixed
  refine ⟨n, T, ?_⟩
  unfold ResonantAbsorptionAt at hf
  push Not at hf
  exact hf

include hζ hp5 hclass in
/-- 既存の hno 入口と同じ安定直線の不存在。残る入力は類群消滅と全直線・全段の狭い吸収。 -/
theorem residual_hno_of_class_vanishing_and_resonant_absorption
    (hbadAll : ∀ (L' : Submodule (ZMod p) S.ResidualSpace),
      Module.finrank (ZMod p) L' = 1 →
      ∀ (n : ℕ) (T : S.ResidualCyclicStage L' n), S.ResonantAbsorptionAt T.carrier) :
    ¬ ∃ L' : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L' = 1 ∧
      S.IsGaloisStable L' ∧ IsCofixedOn S.residualRepresentation L' := by
  rintro ⟨L', hline', _, hc⟩
  exact S.residual_not_cofixed_of_class_vanishing_and_resonant_absorption
    L' hline' hζ hp5 hclass (hbadAll L' hline') hc

end
end DkMath.FLT.Frey.Source
```

## 完成した部分と残る算術

実際の局所慣性ユニポテンス、同じ第二指標の慣性自明性、前回の証人との矛盾、
hclass・全直線全段の狭い吸収のもとでの hno は今回閉じた。

一般 hno の無条件閉鎖には、残された類群消滅や狭い吸収を必要な範囲で算術的に扱う工程が残る。
それらを仮定した条件付き定理を、算術入力の証明と同一視しない。
トレースと点数の同定、Galois 分裂、外部大域分類定理の移植も今回の結論に含めない。

## 検証とコピー

新しい４モジュールを Lib/FLT/root、２つの test モジュールを通常入口へ公開する。
新規11宣言を再帰的依存・公開入力・公理監査の対象とする。
回帰例では有限環の非零冪零元と、ℤ5 上の非対角成分が非零なユニポテント行列を検査する。

４つの Lean ブロックは本番ファイル全文と一致する。
各 import 直後の #print はコピー時にも元のモジュールを特定できるよう保持する。
実行結果は `evidence/validation-note032-frey-tate-unipotence.txt` に記録する。

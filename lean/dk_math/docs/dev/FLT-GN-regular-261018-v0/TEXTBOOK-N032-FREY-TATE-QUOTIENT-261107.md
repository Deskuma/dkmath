# NOTE-032 教科書: 有限商・第二指標・良還元点数・共鳴慣性の証人

更新日: 2026-11-07。今回は一般 hno に向け、固定捩れ点の還元を使う経路を４ステップ進める。
レビューの研究方針を参考にした。トレースと有限体点数の一致は今回の入力にも結論にも用いない。

最も重要な区別は、従来の ResonantAbsorptionAt が要求する条件が p・y∈K であること。
最終点数矛盾が要求する p^N・y=0 の全点についての吸収とは、同じ条件ではない。
今回、この差を実際の第二指標の有限剰余で測り、失敗する局所住所と点まで取り出す。

すべての Frey 入口で、同じ Source、残余直線、巡回塔、二点列、有限基底、Galois 作用を使う。
hclass と、全適格段での狭い hbad は従来の構成入力として保持する。

## 1. 同じ有限巡回段を核とする第二座標

E[p^(n+1)] の既存の有限基底を使い、第二座標 second を線形写像として定義する。
第二基底ベクトルの任意の係数倍を取れば、その座標が任意の値となるので全射である。
第一基底ベクトルが以前選んだ同じ生成元であることを確認し、
second(x)=0 と x が同じ K_n に属することを両方向に証明する。
したがって kernel(second) による商は ZMod(p^(n+1)) と線形同型になる。
核と元の K_n の一致は、単に同じ濃度というだけでなく、元の点の所属として証明する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCyclotomicDeterminant

#print "file: DkMath.FLT.FreyTateFiniteQuotient"

/-!
# 同じ有限巡回段の商を記述する第二座標

実際の有限基底の第二座標は全射で、その核は元の同じ巡回段。
hclass・全段 hbad を保持し、高位商作用の自明性を仮定しない。
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

/-- 同じ有限基底の第二座標。 -/
def residualFiniteSecond (n : ℕ) :
    Torsion S.rationalCurve (p ^ (n + 1)) →ₗ[ZMod (p ^ (n + 1))] ZMod (p ^ (n + 1)) where
  toFun x := (fb n).repr x 1
  map_add' x y := by simp
  map_smul' a x := by simp

local notation "second" => S.residualFiniteSecond L hline hcofixed hζ hp5 hclass hbad

/-- 第二座標は実際に全射。 -/
theorem residualFiniteSecond_surjective (n : ℕ) : Function.Surjective (second n) := by
  intro a
  refine ⟨a • fb n 1, ?_⟩
  simp [residualFiniteSecond]

/-- 有限第一基底ベクトルは以前の同じ段生成元。 -/
theorem residualFiniteBasis_first (n : ℕ) : (fb n 0).val = (gen n).val := by
  let : Fact (1 < p ^ (n + 1)) := ⟨one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)⟩
  rw [residualTateFiniteBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_zero]
  change (tatePairLevel S.rationalCurve
    (Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad))
    (S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad) n (1, 0)).val = _
  rw [tatePairLevel_val]
  simp only [ZMod.val_one, one_nsmul, ZMod.val_zero, zero_nsmul, add_zero]
  rfl

/-- 第二座標の核は、同型な別の部分群でなく元の同じ巡回段。 -/
theorem residualFiniteSecond_eq_zero_iff (n : ℕ) (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    second n x = 0 ↔ x.val ∈ (tower n).carrier := by
  constructor
  · intro hx
    have he := (fb n).sum_repr x
    rw [Fin.sum_univ_two] at he
    have hx' : (fb n).repr x 1 = 0 := hx
    rw [hx', zero_smul, add_zero] at he
    have hv := congrArg (fun z : Torsion S.rationalCurve (p ^ (n + 1)) => z.val) he
    rw [torsion_smul_val, S.residualFiniteBasis_first L hline hcofixed hζ hp5 hclass hbad] at hv
    rw [← hv]
    exact (tower n).carrier.nsmul_mem (gen n).property _
  · intro hx
    rw [← S.residualTateGenerators_generate L hline hcofixed hζ hp5 hclass hbad n] at hx
    obtain ⟨a, ha⟩ := hx
    have he : x = a • fb n 0 := by
      apply Subtype.ext
      change x.val = (torsionGroup S.rationalCurve _).subtype (a • fb n 0)
      rw [map_zsmul]
      change x.val = a • (fb n 0).val
      rw [S.residualFiniteBasis_first L hline hcofixed hζ hp5 hclass hbad]
      exact ha.symm
    rw [he, map_zsmul]
    have hz : second n (fb n 0) = 0 := by simp [residualFiniteSecond]
    rw [hz, zsmul_zero]

/-- 元の同じ段を核とする商は、標準有限環と線形同型。 -/
def residualFiniteQuotientEquiv (n : ℕ) :
    (Torsion S.rationalCurve (p ^ (n + 1)) ⧸ (second n).ker) ≃ₗ[ZMod (p ^ (n + 1))]
      ZMod (p ^ (n + 1)) :=
  (second n).quotKerEquivOfSurjective
    (S.residualFiniteSecond_surjective L hline hcofixed hζ hp5 hclass hbad n)

end
end DkMath.FLT.Frey.Source
```

## 2. 同じ商作用を第二指標で記述する

有限行列は同じ全 Tate 行列の標準剰余である。第一列の下成分は0なので、
任意の有限点 x について second(σx)=red(d(σ))・second(x) となる。
核の所属判定と全射性を使うと、次の正確な同値が得られる。

- 全 p^(n+1) 捩れ点 y に対する σy−y∈K_n。
- 同じ第二指標の標準剰余 red(d(σ))=1。

同じ慣性群の各元についても、この同値を適用できる。
任意の Galois 元への条件であり、Frobenius 性や良還元はこの代数的同値には不要である。
p・y∈K_n という狭い前提を全 p^(n+1) 捩れ条件へ拡張してはいない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateFiniteQuotient

#print "file: DkMath.FLT.FreyTateInertiaQuotient"

/-!
# 同じ有限商作用と第二指標の正確な同値

全 p^(n+1) 捩れ上の吸収と d mod p^(n+1)=1 を同値にする。
従来の p•y∈K という狭い hbad を高位吸収へ拡張しない。
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

local notation "second" => S.residualFiniteSecond L hline hcofixed hζ hp5 hclass hbad

/-- 同じ有限商への実際の作用は、同じ第二指標の標準剰余。 -/
theorem residualFiniteSecond_action (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ)
    (x : Torsion S.rationalCurve (p ^ (n + 1))) :
    second n (representation S.rationalCurve (p ^ (n + 1)) σ x) =
      PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) * second n x := by
  have h := congrArg (fun z => z 1)
    (LinearMap.toMatrix_mulVec_repr (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ) x)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h
  rw [← S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad,
    ← S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad] at h
  have hz := (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad σ).2
  rw [hz, map_zero, zero_mul, zero_add] at h
  exact h.symm

/-- 全有限捩れ点の作用差の吸収は、同じ第二指標の同じ剰余が1であることと同値。 -/
theorem residualFinite_absorption_iff (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    (∀ y : Points S.rationalCurve, p ^ (n + 1) • y = 0 →
      pointAction S.rationalCurve σ y - y ∈ (tower n).carrier) ↔
      PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) = 1 := by
  constructor
  · intro ha
    obtain ⟨x, hx⟩ := S.residualFiniteSecond_surjective L hline hcofixed hζ hp5 hclass hbad n 1
    have hy := ha x.val x.property
    have hz := (S.residualFiniteSecond_eq_zero_iff L hline hcofixed hζ hp5 hclass hbad n
      (representation S.rationalCurve (p ^ (n + 1)) σ x - x)).mpr hy
    rw [map_sub, S.residualFiniteSecond_action L hline hcofixed hζ hp5 hclass hbad, hx, mul_one] at hz
    exact sub_eq_zero.mp hz
  · intro hd y hy
    let x : Torsion S.rationalCurve (p ^ (n + 1)) := ⟨y, hy⟩
    apply (S.residualFiniteSecond_eq_zero_iff L hline hcofixed hζ hp5 hclass hbad n
      (representation S.rationalCurve (p ^ (n + 1)) σ x - x)).mp
    rw [map_sub, S.residualFiniteSecond_action L hline hcofixed hζ hp5 hclass hbad, hd, one_mul, sub_self]

/-- 同じ慣性群の各元についての高位吸収も、同じ指標の剰余条件に正確に置き換わる。 -/
theorem residualFinite_inertia_absorption_iff (n : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    (∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ, ∀ y : Points S.rationalCurve,
      p ^ (n + 1) • y = 0 → pointAction S.rationalCurve τ y - y ∈ (tower n).carrier) ↔
    (∀ τ ∈ ValuationInertia.inertiaSubgroupIn A ℚ,
      PadicInt.toZModPow (n + 1) (d τ : ℤ_[p]) = 1) := by
  exact forall₂_congr (fun τ _ => S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad n τ)

end
end DkMath.FLT.Frey.Source
```

## 3. 良還元点数で第二指標の高位非自明性を証明する

q≠p を良還元素数とし、同じ A と同じ Frobenius 元 σ を固定する。
もし red(d(σ))=1 なら、ステップ2により全作用差が同じ K_n に入る。
既存の固定点の核・像の個数計算と良還元の単射から、
p^(n+1)≤#E(Fq) が従う。ここでは実際の同じ有限曲線の点数を使う。

したがって p^(n+1)>#E(Fq) の段では red(d(σ))≠1。
N=#E(Fq)>0 と置き、n=N−1 とすれば、素数 p>1 に対する p^N>N が使える。
特に同じ第二指標は d(σ)≠1 である。これは従来の d mod p=1 と両立する高位の結論である。
点数が大きいだけで d=1 と結論する方向の議論ではない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateInertiaQuotient
import DkMath.FLT.FreyGoodReductionTowerObstruction

#print "file: DkMath.FLT.FreyTateGoodReductionCharacter"

/-!
# 良還元点数が第二指標の高位自明性を排除する

同じ有限商上で Frobenius が自明なら、実際の固定点還元により p^(n+1)≤#E(Fq)。
十分高い一段で第二指標は非自明。トレース・点数同定は用いない。
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

open EllipticFrobeniusFixedReduction ValuationInertia ValuationFrobenius

/-- 同じ良還元 Frobenius の第二指標が一段で1なら、その段の次数は実際の点数以下。 -/
theorem residualSecond_frobenius_bound (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgood : ¬ (q : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (hd : PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) = 1) :
    p ^ (n + 1) ≤ S.goodReductionPointCount q := by
  let T := tower n
  let := T.finite
  exact torsion_index_le_finite_point_count_of_absorbing S.rationalCurve S.curve S.curve_map
    hq (pow_pos (Fact.out : p.Prime).pos _) hgood
    (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp (hq.dvd_of_dvd_pow h)))
    A hA σ hσ T.carrier T.card
    ((S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad n σ).mpr hd)

/-- 一段の次数が点数を越えれば、その同じ有限剰余は1ではない。 -/
theorem residualSecond_frobenius_ne_one_at (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgood : ¬ (q : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (hbound : S.goodReductionPointCount q < p ^ (n + 1)) :
    PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) ≠ 1 := by
  intro hd
  exact (not_le_of_gt hbound)
    (S.residualSecond_frobenius_bound L hline hcofixed hζ hp5 hclass hbad n hq hqp hgood A hA hσ hd)

/-- 高さ N=#E(Fq) の段（添字 N-1）で、同じ第二指標は必ず非自明。 -/
theorem residualSecond_frobenius_ne_one {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgood : ¬ (q : ℤ) ∣ S.curve.Δ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) : d σ ≠ 1 := by
  intro hd
  have hN := S.goodReductionPointCount_pos hq hgood
  have he : S.goodReductionPointCount q - 1 + 1 = S.goodReductionPointCount q := by omega
  apply S.residualSecond_frobenius_ne_one_at L hline hcofixed hζ hp5 hclass hbad
    (S.goodReductionPointCount q - 1) hq hqp hgood A hA hσ
  · rw [he]
    exact Nat.lt_pow_self (Fact.out : p.Prime).one_lt
  · rw [hd, Units.val_one, map_one]

end
end DkMath.FLT.Frey.Source
```

## 4. 共鳴する悪い住所に実際の失敗点を取り出す

同じ良還元点数 N の高さで、K_(N−1) は実際に濃度 p^N の安定な巡回段である。
既存の局所吸収から大域吸収への定理と点数矛盾を使うと、すべての共鳴悪素点で
高位吸収が成立することは不可能である。
古い条件付き矛盾定理を単に入力として受け取らず、その証明済み定理へ実際の同じ段を渡す。

その否定から次の具体的なデータを得る。

- 素数 q≥5、q≠p、q|abc、q≡±1 mod p。
- 同じ q 上の付値環 A と、その慣性群内の実際の τ。
- p^N・y=0 である実際の幾何学的捩れ点 y。
- τy−y が同じ K_(N−1) に属さない。
- p・y も同じ K_(N−1) に属さない。
- 同じ τ における第二指標は法 p^N で1ではない。

p・y∉K は、保持した狭い hbad を同じ q,A,τ,y に適用すれば直ちに従う。
このため今回の失敗点は、狭い hbad の反例ではなく、その仮定領域の外にある。
最後の定理では良還元素数の存在も内部供給し、共鳴慣性上の d(τ)≠1 を公開する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateGoodReductionCharacter

#print "file: DkMath.FLT.FreyTateResonantWitness"

/-!
# 点数矛盾から実際の共鳴慣性の失敗点へ

条件付き塔を保持し、高位吸収の失敗を具体的な素点・慣性元・捩れ点として取り出す。
従来の狭い hbad と新しい失敗点は異なる領域の条件。一般 hno の矛盾ではない。
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
local notation "tower" => S.residualCyclicTower L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "gen" => S.residualTateGenerators L hline hcofixed hζ hp5 hclass hbad

open ValuationInertia

/-- 実際の良還元点数の高さでは、共鳴する悪い住所に高位吸収の失敗点が存在する。
狭い hbad は保持するが、高位吸収を入力にはしない。 -/
theorem residual_resonant_high_absorption_failure {ell : ℕ}
    (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ inertiaSubgroupIn A ℚ ∧
      ∃ y : Points S.rationalCurve, p ^ S.goodReductionPointCount ell • y = 0 ∧
        pointAction S.rationalCurve τ y - y ∉ (tower (S.goodReductionPointCount ell - 1)).carrier := by
  classical
  by_contra hf
  push Not at hf
  have hN := S.goodReductionPointCount_pos hell hgood
  have he : S.goodReductionPointCount ell - 1 + 1 = S.goodReductionPointCount ell := by omega
  let T := tower (S.goodReductionPointCount ell - 1)
  let := T.finite
  let := T.cyclic
  apply S.residual_cofixed_point_count_tower_resonant_inertia_impossible hp5 hell hellp hgood
    L hline hcofixed T.carrier T.stable (by simpa only [T, he] using T.card) T.base
  exact hf

/-- 同じ失敗点は、同じ第二指標の同じ有限剰余の非自明性を検出する。 -/
theorem residual_resonant_second_witness {ell : ℕ}
    (hell : ell.Prime) (hellp : ell ≠ p) (hgood : ¬ (ell : ℤ) ∣ S.curve.Δ) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ inertiaSubgroupIn A ℚ ∧
      ∃ y : Points S.rationalCurve, p ^ S.goodReductionPointCount ell • y = 0 ∧
        pointAction S.rationalCurve τ y - y ∉ (tower (S.goodReductionPointCount ell - 1)).carrier ∧
        p • y ∉ (tower (S.goodReductionPointCount ell - 1)).carrier ∧
        PadicInt.toZModPow (S.goodReductionPointCount ell) (d τ : ℤ_[p]) ≠ 1 := by
  obtain ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail⟩ :=
    S.residual_resonant_high_absorption_failure L hline hcofixed hζ hp5 hclass hbad hell hellp hgood
  refine ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail, ?_, ?_⟩
  · intro hpy
    exact hfail (hbad _ (tower (S.goodReductionPointCount ell - 1)) q hq hqp hq5 hs hr A hA τ hτ y hpy)
  intro hd
  have hN := S.goodReductionPointCount_pos hell hgood
  have he : S.goodReductionPointCount ell - 1 + 1 = S.goodReductionPointCount ell := by omega
  apply hfail
  apply (S.residualFinite_absorption_iff L hline hcofixed hζ hp5 hclass hbad
    (S.goodReductionPointCount ell - 1) τ).mpr
  · rwa [he]
  · rwa [he]

/-- 良還元素数の存在も内部供給し、実際の局所慣性上で第二指標が非自明となる。 -/
theorem residualSecond_nontrivial_resonant_inertia :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ 5 ≤ q ∧ (q : ℤ) ∣ S.a * S.b * S.c ∧
      ((q : ZMod p) = 1 ∨ (q : ZMod p) = -1) ∧
      ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A q ∧
      ∃ τ : Field.absoluteGaloisGroup ℚ, τ ∈ inertiaSubgroupIn A ℚ ∧ d τ ≠ 1 := by
  obtain ⟨ell, hell, hellp, hgood⟩ := S.exists_good_prime_ne
  obtain ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, y, hy, hfail, hpy, hd⟩ :=
    S.residual_resonant_second_witness L hline hcofixed hζ hp5 hclass hbad hell hellp hgood
  refine ⟨q, hq, hqp, hq5, hs, hr, A, hA, τ, hτ, ?_⟩
  intro h
  apply hd
  rw [h, Units.val_one, map_one]

end
end DkMath.FLT.Frey.Source
```

## ここまでの到達点と hno の境界

全 p 進第二指標の高位非自明性と、実際の共鳴慣性上の非自明性を、
同じ条件付き塔と既存の良還元点数上界から証明した。
この結論は hclass と全段の狭い hbad を算術的に供給したという意味ではない。
第２指標の自明性や一般 hno の矛盾を証明したとも扱わない。

一般 hno へ進むには、この具体的な共鳴慣性の非自明性を排除する追加の局所算術、
または hclass・狭い hbad 自体の供給／障害解析が必要である。
トレース=q+1−#E(Fq) の同定は未完成のままであり、今回の４ステップはそこに依存しない。
Galois 分裂も結論していない。

## 検証とコピー

通常入口 DkMath/FLT と DkMathTest から公開する。
主要14宣言の公理・再帰依存監査と12件の公開入力監査を用意した。
法25の diag(1,6) により、5・y が第一軸に入るときの狭い吸収と、
y=(0,1) における高位吸収の失敗を回帰確認する。

４つの Lean ブロックは production 各ファイル全文と同一である。
各 import 直後の #print は元のモジュール名を示し、コピー時にも保持する。
実行結果は evidence/validation-note032-frey-tate-quotient.txt に記録する。

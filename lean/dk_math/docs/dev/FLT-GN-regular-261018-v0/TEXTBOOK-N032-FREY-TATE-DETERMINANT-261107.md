# NOTE-032 教科書: 全 Tate 表現の円分行列式

更新日: 2026-11-07。今回は次の３ステップを実装した。

1. 可換環上の交代対から、非退化性による係数の単射性と行列式公式を証明する。
2. 実際の幾何学的 Weil 対を用い、任意の非零整数 n の捩れ表現の行列式を有限円分指標と同定する。
3. 同じ Frey 塔から得た有限基底と全 Tate 基底を比較し、全 p 進行列式と第２指標を同定する。

## 1. 体に依存しない係数の消去

法 p のベクトル空間で使える「非零だから係数を消去する」という議論は、
法 p 冪の加群にはそのまま使えない。例えば ZMod 25 の非零元 5 は 5 によって消える。
ここでは交代対 e の非退化性を用いる。a と c が基底対の値へ同じ作用を持つなら、
(a-c) 倍した第一基底ベクトルは全ベクトルと対を取って0になる。
非退化性からそのベクトルは0、第一座標から a=c となる。
これにより原始根を選んでその位数を別途証明することなく、必要な係数の忠実性が得られる。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.AlternatingDeterminant

#print "file: DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing"

/-!
# 可換環上の二次元交代対と係数の忠実性

法 p 冪は一般に体でない。非零ベクトルの scalar 消去を使わず、
非退化性から基底対の値に作用する係数の単射性を直接証明する。
-/
namespace DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing
open Module
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W]
    (e : V →ₗ[R] V →ₗ[R] W) (halt : ∀ x, e x x = 0) (b : Basis (Fin 2) R V)

include halt

/-- 可換環上でも交代性は反対称性を与える。 -/
theorem skew (x y : V) : e y x = - e x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- 環上の基底座標による交代対の実際の展開。 -/
theorem coordinates (x y : V) :
    e x y = (b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0) • e (b 0) (b 1) := by
  have hx : x = b.repr x 0 • b 0 + b.repr x 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  have hy : y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr y).symm
  conv_lhs => rw [hx, hy]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, halt,
    smul_zero, zero_add, add_zero, skew e halt (b 0) (b 1)]
  module

/-- 非退化性は基底対の値に対する scalar 作用を忠実にする。体の仮定は不要。 -/
theorem coefficient_injective (hnd : ∀ x, (∀ y, e x y = 0) → x = 0) :
    Function.Injective (fun a : R => a • e (b 0) (b 1)) := by
  intro a c h
  dsimp only at h
  have hz : (a - c) • e (b 0) (b 1) = 0 := by rw [sub_smul, h, sub_self]
  have hx : (a - c) • b 0 = 0 := by
    apply hnd
    intro y
    rw [map_smul, LinearMap.smul_apply]
    have hb : e (b 0) y = b.repr y 1 • e (b 0) (b 1) := by
      rw [coordinates e halt b]
      simp
    rw [hb, smul_comm, hz, smul_zero]
  have hc := congrArg (fun x : V => b.repr x 0) hx
  have hd : a - c = 0 := by simpa using hc
  exact sub_eq_zero.mp hd

/-- 同じ線形作用の前後で、対の値は実際の行列式倍になる。 -/
theorem map_eq_det_smul (f : V →ₗ[R] V) :
    e (f (b 0)) (f (b 1)) = LinearMap.det f • e (b 0) (b 1) := by
  rw [coordinates e halt b, ← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  congr 2
  ring

/-- 同変性と忠実性から行列式の係数を同定する。 -/
theorem det_eq_of_equivariant (hnd : ∀ x, (∀ y, e x y = 0) → x = 0)
    (f : V →ₗ[R] V) (c : R) (heq : e (f (b 0)) (f (b 1)) = c • e (b 0) (b 1)) :
    LinearMap.det f = c :=
  coefficient_injective e halt b hnd ((map_eq_det_smul e halt b f).symm.trans heq)

end DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing
```

## 2. 実際の全非零捩れ段

有限円分指標は同じ代数閉包の n 乗根への実際の Galois 作用で定義する。
既存の geometricWeilPairingData が実際の対・交代性・非退化性・同変性を供給する。
行列式の係数と有限円分指標の係数が基底対へ同じ作用を持つため、ステップ1で同定できる。
この定理は標数0、n≠0、および実際の E[n] の階数2基底 b を要求する。
任意の n に対する基底の存在をこのファイルで新たに証明したわけではない。
対やその非退化性を利用側の新しい provider 入力にしてはいない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.AlternatingDeterminantRing
import DkMath.Lib.NumberTheory.EllipticGeometricWeilPairing

#print "file: DkMath.Lib.NumberTheory.EllipticWeilDeterminantAll"

/-!
# 全ての非零捩れ段の幾何学的 Weil 対と円分行列式

法 n は体とは限らない。実際の幾何学的対の非退化性から係数の忠実性を使い、
同じ表現の行列式を全 n 乗根への作用で定まる指標と同定する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
open Module CyclotomicRootModule DkMath.Lib.RepresentationTheory
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- 同じ代数閉包の全 n 乗根への作用を表す、標準有限円分指標。 -/
def torsionCyclotomicCharacter (n : ℕ) (hn : n ≠ 0) : Field.absoluteGaloisGroup K →* (ZMod n)ˣ := by
  let : NeZero n := ⟨hn⟩
  exact (modularCyclotomicCharacter (AlgebraicClosure K)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) n)).comp
      { toFun := fun σ => σ.toRingEquiv
        map_one' := rfl
        map_mul' := fun _ _ => rfl }

/-- 有限円分指標の、同じ全 n 乗根への実際の作用公式。 -/
theorem torsionCyclotomicCharacter_spec (n : ℕ) (hn : n ≠ 0) (σ : Field.absoluteGaloisGroup K)
    (z : rootsOfUnity n (AlgebraicClosure K)) :
    σ.toAlgHom (z.val : AlgebraicClosure K) =
      (z.val : AlgebraicClosure K) ^ (torsionCyclotomicCharacter n hn σ : ZMod n).val := by
  let : NeZero n := ⟨hn⟩
  exact modularCyclotomicCharacter.spec (AlgebraicClosure K)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) n) σ.toRingEquiv z.property

variable (E : WeierstrassCurve K) [E.IsElliptic]

/-- 実際の全 n 捩れ基底に対して、同じ行列式は有限円分指標に一致する。
対の存在・非退化性・同変性を新しい provider として要求しない。 -/
theorem torsion_determinant_all (n : ℕ) (hn : n ≠ 0) (b : Basis (Fin 2) (ZMod n) (Torsion E n))
    (σ : Field.absoluteGaloisGroup K) :
    LinearMap.det (representation E n σ) = (torsionCyclotomicCharacter n hn σ : ZMod n) := by
  let : NeZero n := ⟨hn⟩
  let w := geometricWeilPairingData E n hn
  apply AlternatingDeterminantRing.det_eq_of_equivariant w.pairing.rootForm
    w.pairing.rootForm_alternating b w.pairing.rootForm_nondegenerate
  change w.pairing.rootValue _ _ = (torsionCyclotomicCharacter n hn σ : ZMod n) • w.pairing.rootValue _ _
  apply Additive.ext
  rw [smul_toMul]
  apply Subtype.ext
  apply Units.ext
  exact (w.equivariant σ (b 0) (b 1)).trans
    (torsionCyclotomicCharacter_spec n hn σ
      ⟨w.pairing.value (b 0) (b 1), (mem_rootsOfUnity n _).mpr (w.pairing.value_pow _ _)⟩)

end
end DkMath.Lib.NumberTheory.EllipticTorsionRepresentation
```

## 3. 同じ有限基底から全 p 進行列式へ

前回までに構成した同じ二点列 v,w を使い、各段の有限基底を定義する。
全点列の座標を法 p^(n+1) へ写すことと、その成分の有限基底座標を取ることが一致する。
したがって、同じ Galois 元の全行列の各成分を還元すると、同じ有限作用行列になる。
行列式と環準同型の可換性によりステップ2を各段へ適用できる。
Mathlib の p 進円分指標も同じ有限円分指標へ還元されるため、全正冪剰余の外延性で
全行列式 = p 進円分指標が従う。最後に既存の三角行列式 = χ∞・d と合わせ、
単元として d = cyclo∞・χ∞⁻¹ を得る。

hclass と「すべての対象巡回段についての hbad」は、同じ塔・同じ基底を構成する入力として保持する。
新しい行列式・Weil 対・比の同定を仮定として追加していない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCharactersModP
import DkMath.Lib.NumberTheory.EllipticWeilDeterminantAll

#print "file: DkMath.FLT.FreyTateCyclotomicDeterminant"

/-!
# 同じ全 Frey Tate 作用の p 進円分行列式

同じ有限基底と全 Tate 基底の座標を標準剰余で比較する。
全非零捩れ段の実際の幾何学的 Weil 行列式を供給し、全正冪剰余の外延性で閉じる。
hclass・全段 hbad は基底構成から保持する。Frobenius や一般 hno は別の課題。
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
local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad
local notation "v" => Subtype.val (S.residualCyclicTateVector L hline hcofixed hζ hp5 hclass hbad)
local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad
local notation "hb" => S.residualTatePair_base_span L hline hcofixed hζ hp5 hclass hbad
local notation "lev" => tatePairLevelEquiv S.rationalCurve v w hb
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad

/-- 同じ二点列の第 n 成分による実際の有限基底。 -/
def residualTateFiniteBasis (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (p ^ (n + 1))) (Torsion S.rationalCurve (p ^ (n + 1))) :=
  (Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))).map (lev n)

local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad

/-- 同じ全点列の座標を還元すると、同じ有限点の座標になる。 -/
theorem residualTate_coordinate_reduction (x : Tate p (Points S.rationalCurve)) (n : ℕ) (i : Fin 2) :
    (fb n).repr ⟨evaluation n x, killed x n⟩ i = PadicInt.toZModPow (n + 1) ((basis).repr x i) := by
  have h := tatePairParametrization_level S.rationalCurve v w ((eqv).symm x) n
  have ha : tatePairParametrization S.rationalCurve v w ((eqv).symm x) = x := (eqv).apply_symm_apply x
  rw [ha] at h
  have hc : (lev n).symm ⟨evaluation n x, killed x n⟩ =
      (PadicInt.toZModPow (n + 1) ((eqv).symm x).1, PadicInt.toZModPow (n + 1) ((eqv).symm x).2) := by
    apply (lev n).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact h
  rw [residualTateFiniteBasis, Module.Basis.map_repr, residualTateBasis, Module.Basis.map_repr]
  change (Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))).repr
    ((lev n).symm ⟨evaluation n x, killed x n⟩) i =
    PadicInt.toZModPow (n + 1) ((Module.Basis.finTwoProd ℤ_[p]).repr ((eqv).symm x) i)
  rw [hc]
  fin_cases i <;> rfl

/-- 全基底の成分は、同じ有限基底の同じ点である。 -/
theorem residualTate_basis_reduction (n : ℕ) (j : Fin 2) :
    evaluation n (basis j) = (fb n j).val := by
  rw [residualTateBasis, Module.Basis.map_apply, residualTateFiniteBasis, Module.Basis.map_apply]
  fin_cases j
  · change evaluation n (eqv ((Module.Basis.finTwoProd ℤ_[p]) 0)) =
      (lev n ((Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))) 0)).val
    simp only [Module.Basis.finTwoProd_zero]
    rw [S.residualTateEquiv_first L hline hcofixed hζ hp5 hclass hbad]
    change evaluation n v = ((1 : ZMod (p ^ (n + 1))) • (⟨evaluation n v, killed v n⟩ : Torsion S.rationalCurve _) +
      (0 : ZMod (p ^ (n + 1))) • (⟨evaluation n w, killed w n⟩ : Torsion S.rationalCurve _)).val
    rw [one_smul, zero_smul, add_zero]
  · change evaluation n (eqv ((Module.Basis.finTwoProd ℤ_[p]) 1)) =
      (lev n ((Module.Basis.finTwoProd (ZMod (p ^ (n + 1)))) 1)).val
    simp only [Module.Basis.finTwoProd_one]
    rw [S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad]
    change evaluation n w = ((0 : ZMod (p ^ (n + 1))) • (⟨evaluation n v, killed v n⟩ : Torsion S.rationalCurve _) +
      (1 : ZMod (p ^ (n + 1))) • (⟨evaluation n w, killed w n⟩ : Torsion S.rationalCurve _)).val
    rw [zero_smul, one_smul, zero_add]

/-- 実際の全 Galois 行列の各成分の剰余は、同じ有限表現の行列成分。 -/
theorem residualTate_matrix_reduction (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) (i j : Fin 2) :
    PadicInt.toZModPow (n + 1) (mat σ i j) =
      LinearMap.toMatrix (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ) i j := by
  rw [residualTateActionMatrix, LinearMap.toMatrix_apply,
    ← S.residualTate_coordinate_reduction L hline hcofixed hζ hp5 hclass hbad]
  rw [LinearMap.toMatrix_apply]
  congr 1
  apply congrArg (fb n).repr
  apply Subtype.ext
  change pointAction S.rationalCurve σ (evaluation n (basis j)) = pointAction S.rationalCurve σ (fb n j).val
  rw [S.residualTate_basis_reduction L hline hcofixed hζ hp5 hclass hbad]

/-- 各正冪精度で、実際の全行列式は同じ有限円分指標に一致する。 -/
theorem residualTate_determinant_finite (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    PadicInt.toZModPow (n + 1) (mat σ).det =
      (torsionCyclotomicCharacter (p ^ (n + 1)) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ : ZMod (p ^ (n + 1))) := by
  rw [RingHom.map_det]
  have he : (mat σ).map (PadicInt.toZModPow (n + 1)) =
      LinearMap.toMatrix (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ) := by
    ext i j
    exact S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad n σ i j
  change ((mat σ).map (PadicInt.toZModPow (n + 1))).det = _
  rw [he, LinearMap.det_toMatrix]
  exact torsion_determinant_all S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (fb n) σ

/-- 全 p 冪乗根への作用から定まる、Mathlib の実際の p 進円分指標。 -/
def tateCyclotomicCharacter : Field.absoluteGaloisGroup ℚ →* ℤ_[p]ˣ :=
  (_root_.cyclotomicCharacter (AlgebraicClosure ℚ) p).comp
    { toFun := fun σ => σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

local notation "cyc" => tateCyclotomicCharacter (p := p)

/-- p 進円分指標の同じ有限剰余。 -/
theorem tateCyclotomicCharacter_mod (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    PadicInt.toZModPow (n + 1) (cyc σ : ℤ_[p]) =
      (torsionCyclotomicCharacter (p ^ (n + 1)) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ : ZMod (p ^ (n + 1))) := by
  exact _root_.cyclotomicCharacter.toZModPow (L := AlgebraicClosure ℚ) p σ.toRingEquiv

/-- 同じ全 Tate 作用の実際の行列式は、全 p 進精度で円分指標に一致する。 -/
theorem residualTate_determinant_cyclotomic (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).det = (cyc σ : ℤ_[p]) := by
  apply PadicCharacterLimit.ext_positive
  intro n
  rw [S.residualTate_determinant_finite L hline hcofixed hζ hp5 hclass hbad, tateCyclotomicCharacter_mod]

/-- 同じ第二指標の高位の関係。mod p だけでなく、実際の単元として一致する。 -/
theorem residualTateSecondCharacter_eq_cyclotomic (σ : Field.absoluteGaloisGroup ℚ) :
    d σ = cyc σ * (chi σ)⁻¹ := by
  have hu : chi σ * d σ = cyc σ := Units.ext
    ((S.residualTate_determinant L hline hcofixed hζ hp5 hclass hbad σ).symm.trans
      (S.residualTate_determinant_cyclotomic L hline hcofixed hζ hp5 hclass hbad σ))
  calc
    d σ = (chi σ)⁻¹ * (chi σ * d σ) := by simp
    _ = (chi σ)⁻¹ * cyc σ := by rw [hu]
    _ = cyc σ * (chi σ)⁻¹ := mul_comm _ _

end
end DkMath.FLT.Frey.Source
```

## 到達点と残る境界

全 p 進円分行列式と第２指標の比の同定は、上記の同じ算術入力のもとで実装済みとなった。
これは mod p のみの行列式同定を越える結果である。
第２指標が全精度で1、第１指標が円分指標、表現が Galois 分裂する、とは結論していない。
Frobenius のトレース・特性多項式による算術的矛盾、hclass と全段 hbad の算術的供給、
一般 hno の閉鎖は引き続き未完成である。原始根の厳密位数を与える別定理も今回の実装対象には含まない。

検証入口は DkMath、DkMathTest、および今回の再帰的依存監査・入力監査である。
３つの Lean ブロックはそれぞれ本番ファイル全文と同一で、import 直後の #print にモジュール名を保持する。
実行結果は evidence/validation-note032-frey-tate-determinant.txt に記録する。

# NOTE-032 教科書：第二 Tate 指標・連続性・mod p の算術

日付：2026-11-06。前段：`TEXTBOOK-N032-FREY-TATE-BASIS-261106.md`。

今回の3ステップは、①実際の上三角行列準同型の二指標と積公式、
②同じ Frey 第二対角指標とその連続性、③元の Cofixed 条件による mod p 自明性である。
以下の3つの Lean ブロックは production ファイルの全文である。
順に配置し、import 直後の正確な `#print "file: …"` を保持する。

## ステップ1：実際の上三角作用から二つの単元値指標を構成する

Γ を群、R を可換環、ρ:Γ→*Matrix(Fin 2)(Fin 2)R を実際の準同型とする。
下左成分 ρ(g)₁₀=0 を仮定する。
これは汎用構成の入力であり、Frey 適用では前回の同じ基底・指標作用から供給する。

2×2 行列積を展開すると、第一・第二対角成分はそれぞれ乗法的になる。
Γ の逆元を写せば両対角成分が単元となり、実際の単元値指標を得る。
可逆性を新しい provider として要求しない。

上右成分を b(g)、二指標を a(g),d(g) とすれば、同じ行列積から

    b(gh)=a(g)b(h)+b(g)d(h)

を証明する。行列式も det(ρ(g))=a(g)d(g) となる。
これは環上の実際の作用の公式であり、b(g)=0 や Galois 加群としての分裂を結論するものではない。

同じファイルでは、p 進単元値指標 d の各標準有限剰余の核が開なら d が連続となることを公開する。
標準剰余の両立性と、以前の実際の指標極限の一意性・連続性を使う。
無限段の核が開とは主張しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.PadicCharacterLimit
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

#print "file: DkMath.Lib.RepresentationTheory.TriangularTwoCharacter"

/-!
# 実際の上三角2次作用の二つの指標と積公式

群からの実際の行列準同型を使う。対角成分の可逆性は群の逆元から導き、
非対角成分が零・完全列が分裂するとは主張しない。
-/
namespace DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
noncomputable section
variable {Γ R : Type*} [Group Γ] [CommRing R]
    (ρ : Γ →* Matrix (Fin 2) (Fin 2) R) (ht : ∀ g, ρ g 1 0 = 0)

/-- 第一対角成分の実際の乗法性。 -/
def firstHom : Γ →* R where
  toFun g := ρ g 0 0
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ht h, mul_zero, add_zero]

/-- 第二対角成分の実際の乗法性。 -/
def secondHom : Γ →* R where
  toFun g := ρ g 1 1
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two, ht g, zero_mul, zero_add]

/-- 対角成分の単元性は群の逆元を写して得る。 -/
def first : Γ →* Rˣ := (firstHom ρ ht).toHomUnits
def second : Γ →* Rˣ := (secondHom ρ ht).toHomUnits

/-- 非対角成分は二つの指標を伴う積公式を満たす。 -/
theorem offDiagonal_mul (g h : Γ) :
    ρ (g * h) 0 1 = (first ρ ht g : R) * ρ h 0 1 + ρ g 0 1 * (second ρ ht h : R) := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rfl

/-- 実際の行列式は二つの同じ対角指標の積。算術的な同定は別の課題。 -/
theorem determinant (g : Γ) :
    (ρ g).det = (first ρ ht g : R) * (second ρ ht g : R) := by
  rw [Matrix.det_fin_two, ht, mul_zero, sub_zero]
  rfl

end
end DkMath.Lib.RepresentationTheory.TriangularTwoCharacter

namespace DkMath.Lib.Algebra.PadicCharacterLimit
noncomputable section
variable {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ]

/-- p 進指標の全ての標準有限剰余。 -/
def reductions (d : Γ →* ℤ_[p]ˣ) (n : ℕ) : Γ →* (ZMod (p ^ (n + 1)))ˣ :=
  (Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom).comp d

/-- p 進指標から取った有限剰余は標準剰余写像で両立する。 -/
theorem reductions_compatible (d : Γ →* ℤ_[p]ˣ) (n : ℕ) (g : Γ) :
    Units.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1)))
      (ZMod (p ^ (n + 1)))).toMonoidHom (reductions d (n + 1) g) = reductions d n g := by
  apply Units.ext
  exact congrArg (fun f : ℤ_[p] →+* ZMod (p ^ (n + 1)) => f (d g : ℤ_[p]))
    (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 1 + 1) (Nat.le_succ _))

/-- 有限剰余の開核を実際に供給すれば、同じ p 進指標は連続。無限核の開性は不要。 -/
theorem continuous_of_reduction_kernels [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (d : Γ →* ℤ_[p]ˣ) (hopen : ∀ n, IsOpen ((reductions d n).ker : Set Γ)) : Continuous d := by
  have he := character_unique (reductions d) (reductions_compatible d) d (fun _ _ => rfl)
  rw [← he]
  exact character_continuous _ _ hopen

end
end DkMath.Lib.Algebra.PadicCharacterLimit
```

## ステップ2：同じ Frey 第二指標と連続性

同じ Source、残余直線 L、rootField、hclass、全段 hbad、前回の実際の全 Tate 基底を保持する。
`LinearMap.toMatrixAlgEquiv` と元の `actionLinear` を合成し、
同じ作用行列を実際の行列準同型として公開する。
前回の行列値と定義的に同じであり、別の三角行列を選んでいるのではない。

第一列の結果から、汎用構成の下左成分0を内部供給する。
第一対角指標は以前の同じ連続 p 進指標 χ∞ と一致する。
第二対角指標 `residualTateSecondCharacter` を d と書くと、

    (d(σ):ℤₚ)=M(σ)₁₁

である。この可逆性・乗法性は実際の群準同型から証明する。
上右成分の積公式と行列式の χ∞(σ)d(σ) 表示も同じ行列へ適用する。
高位の円分行列式との一致は、この積表示とは別の課題である。

### 有限捩れ開核から第二指標の連続性へ

同じ第二基底点列 w への作用を、以前の実際の二成分同型で読む。
その第二座標は同じ M(σ)₁₁、すなわち d(σ) である。

同じ E[p^(n+1)] 全体への作用が恒等である σ を取る。
w の第 n 点も固定されるので、有限段の同じ座標同型の単射性から、
σ(w) の二係数の剰余は (0,1) に等しい。
特に d(σ) mod p^(n+1)=1 である。

従って第二指標の各有限剰余の核は、実際の全捩れ表現の開核を含む。
この包含と以前の開核定理から、各有限剰余の核が開となる。
ステップ1の連続性補題を使い、実際の第二単元値指標 d の連続性を得る。
新しい hopen/hcont provider、全 Tate 群の位相的基底同型を仮定していない。
上右成分や全行列表示の連続性をこの定理で新たに証明したとは主張しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateBasis
import DkMath.Lib.RepresentationTheory.TriangularTwoCharacter

#print "file: DkMath.FLT.FreyTateCharacters"

/-!
# 同じ Frey Tate 作用の第二単元値指標と連続性

実際の行列準同型から第二対角指標を構成する。各有限剰余の核は
同じ全捩れ表現の開核を含むので連続となる。指標値1や分裂は仮定しない。
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
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad

/-- 同じ実際の全線形作用を同じ基底で行列化した群準同型。 -/
def residualTateMatrixRepresentation : Field.absoluteGaloisGroup ℚ →* Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  (LinearMap.toMatrixAlgEquiv basis).toMonoidHom.comp (actionLinear S.residualPointActionHom)

local notation "rho" => S.residualTateMatrixRepresentation L hline hcofixed hζ hp5 hclass hbad

theorem residualTateMatrixRepresentation_apply (σ : Field.absoluteGaloisGroup ℚ) : rho σ = mat σ := rfl

/-- 既存の第一列の零から得た、実際の上三角性。 -/
theorem residualTateMatrixRepresentation_lower_zero (σ : Field.absoluteGaloisGroup ℚ) : rho σ 1 0 = 0 :=
  (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad σ).2

local notation "tri" => S.residualTateMatrixRepresentation_lower_zero L hline hcofixed hζ hp5 hclass hbad

/-- 第一対角指標は、以前の同じ p 進指標そのもの。 -/
theorem residualTateMatrix_first_character : TriangularTwoCharacter.first rho tri = chi := by
  apply MonoidHom.ext; intro σ
  apply Units.ext
  exact (S.residualTateActionMatrix_first_column L hline hcofixed hζ hp5 hclass hbad σ).1

/-- 群の逆元から可逆性を証明した同じ第二対角指標。 -/
def residualTateSecondCharacter : Field.absoluteGaloisGroup ℚ →* ℤ_[p]ˣ :=
  TriangularTwoCharacter.second rho tri

local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad

theorem residualTateSecondCharacter_coe (σ : Field.absoluteGaloisGroup ℚ) : (d σ : ℤ_[p]) = mat σ 1 1 := rfl

/-- 第二点列を動かした時の第二座標は、同じ行列の第二対角成分。 -/
theorem residualTateSecond_coordinate (σ : Field.absoluteGaloisGroup ℚ) :
    ((eqv).symm (actionLinear S.residualPointActionHom σ w)).2 = (d σ : ℤ_[p]) := by
  have h1 : basis 1 = w := by
    rw [residualTateBasis, Module.Basis.map_apply, Module.Basis.finTwoProd_one]
    exact S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad
  rw [residualTateSecondCharacter_coe, residualTateActionMatrix, LinearMap.toMatrix_apply, h1,
    residualTateBasis, Module.Basis.map_repr]
  rfl

/-- 非対角成分の積公式。零や Galois 分裂は結論しない。 -/
theorem residualTate_offDiagonal_mul (σ τ : Field.absoluteGaloisGroup ℚ) :
    mat (σ * τ) 0 1 = (chi σ : ℤ_[p]) * mat τ 0 1 + mat σ 0 1 * (d τ : ℤ_[p]) := by
  have h := TriangularTwoCharacter.offDiagonal_mul rho tri σ τ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 実際の行列式の積表示。高位円分指標との一致ではない。 -/
theorem residualTate_determinant (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).det = (chi σ : ℤ_[p]) * (d σ : ℤ_[p]) := by
  have h := TriangularTwoCharacter.determinant rho tri σ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 同じ全捩れ作用の核の元は、第二指標の同じ有限剰余の核に入る。 -/
theorem residualTateSecondCharacter_finite_kernel (n : ℕ) :
    representationKernel S.rationalCurve (p ^ (n + 1)) ≤ (PadicCharacterLimit.reductions d n).ker := by
  intro σ hσ
  change Units.map (PadicInt.toZModPow (n + 1)).toMonoidHom (d σ) = 1
  apply Units.ext
  change PadicInt.toZModPow (n + 1) (d σ : ℤ_[p]) = 1
  let a := (eqv).symm (actionLinear S.residualPointActionHom σ w)
  have ha : tatePairParametrization S.rationalCurve v w a = actionLinear S.residualPointActionHom σ w :=
    (eqv).apply_symm_apply _
  have hpt : pointAction S.rationalCurve σ (evaluation n w) = evaluation n w := by
    change representation S.rationalCurve (p ^ (n + 1)) σ = 1 at hσ
    have he := congrArg (fun f : Module.End (ZMod (p ^ (n + 1))) (Torsion S.rationalCurve (p ^ (n + 1))) =>
      f ⟨evaluation n w, killed w n⟩) hσ
    exact congrArg Subtype.val he
  have he := congrArg (evaluation n) ha
  rw [tatePairParametrization_level] at he
  change _ = pointAction S.rationalCurve σ (evaluation n w) at he
  rw [hpt] at he
  have hi : (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2) = (0, 1) := by
    apply (tatePairLevelEquiv S.rationalCurve v w hb n).injective
    apply Subtype.ext
    change (tatePairLevel S.rationalCurve v w n
      (PadicInt.toZModPow (n + 1) a.1, PadicInt.toZModPow (n + 1) a.2)).val =
      (tatePairLevel S.rationalCurve v w n (0, 1)).val
    change _ = ((0 : ZMod (p ^ (n + 1))) • (⟨evaluation n v, killed v n⟩ : Torsion S.rationalCurve _) +
      (1 : ZMod (p ^ (n + 1))) • (⟨evaluation n w, killed w n⟩ : Torsion S.rationalCurve _)).val
    rw [zero_smul, one_smul, zero_add]
    exact he
  have hs := congrArg Prod.snd hi
  change PadicInt.toZModPow (n + 1) ((eqv).symm (actionLinear S.residualPointActionHom σ w)).2 = 1 at hs
  rw [S.residualTateSecond_coordinate L hline hcofixed hζ hp5 hclass hbad] at hs
  exact hs

/-- 第二指標の各有限剰余は、実際に開核を持つ。 -/
theorem residualTateSecondCharacter_finite_kernel_isOpen (n : ℕ) :
    IsOpen ((PadicCharacterLimit.reductions d n).ker : Set (Field.absoluteGaloisGroup ℚ)) :=
  Subgroup.isOpen_mono
    (S.residualTateSecondCharacter_finite_kernel L hline hcofixed hζ hp5 hclass hbad n)
    (representationKernel_isOpen_of_ne_zero S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

/-- 第二単元値指標は連続。新しい連続性・開核 provider は不要。 -/
theorem residualTateSecondCharacter_continuous : Continuous d :=
  PadicCharacterLimit.continuous_of_reduction_kernels d
    (S.residualTateSecondCharacter_finite_kernel_isOpen L hline hcofixed hζ hp5 hclass hbad)

end
end DkMath.FLT.Frey.Source
```

## ステップ3：元の Cofixed 条件から第二指標 mod p を計算する

法 p¹ から法 p への標準写像を明示した環準同型を π:ℤₚ→ZMod p とする。
同じ第二基底点列 w について、y=σ(w)−w と置く。

元の同じ残余表現の Cofixed 条件により、y の第0評価は同じ L に入る。
以前の同じ直線 C の還元全射性から、その同じ残余点を持つ c∈C を取る。
すると y−c の第0成分は零であり、以前の実際の一段シフトから

    y−c=p•z

となる全 Tate 点列 z が存在する。

同じ二成分座標で、c の第二係数は0、w の第二係数は1、σ(w) の第二係数は d(σ) である。
従って上の実際の点列等式の第二座標は

    d(σ)−1=p•z₂

となる。標準剰余写像 π を適用し、π(p)=0 を使って

    Units.map π (d(σ))=1

を証明する。

ここで使う Cofixed 条件は **元の mod p 残余条件** である。
y 自体が C に入る、全 Tate 商が自明に作用される、d(σ)=1 といった高位の結論へ飛躍しない。
実際に得たのは y が C と p 倍像の和に入ることと、第二指標の mod p 自明性である。

以前の同じ第一指標の mod p 円分一致と、今回の実際の行列式の積表示を合わせると、

    π(det M(σ))=χ_cyc,p(σ)

も従う。これは元の残余構造からの mod p の計算である。
高位 Weil pairing を新たに移植した結果や、全 p 進円分行列式を証明した結果ではない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCharacters

#print "file: DkMath.FLT.FreyTateCharactersModP"

/-!
# 同じ第二 Tate 指標の mod p 自明性

元の残余 Cofixed 条件を使い、第二基底点列の作用差を還元して同じ L へ戻す。
同じ直線への持ち上げとの差は実際に p 倍となるため、第二係数は mod p で1。
高位で指標が自明、完全列が分裂、一般 hno が閉じたとは主張しない。
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
local notation "eqv" => S.residualTateEquiv L hline hcofixed hζ hp5 hclass hbad
local notation "w" => S.residualTateSecond L hline hcofixed hζ hp5 hclass hbad
local notation "line" => S.residualCyclicTateLine L hline hcofixed hζ hp5 hclass hbad
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "mat" => S.residualTateActionMatrix L hline hcofixed hζ hp5 hclass hbad

/-- 法 p^1 から法 p への標準写像も明示した p 進剰余写像。 -/
def tateResidueModP : ℤ_[p] →+* ZMod p :=
  (ZMod.castHom (dvd_pow_self p (by decide : 0 + 1 ≠ 0)) (ZMod p)).comp (PadicInt.toZModPow 1)

local notation "piP" => tateResidueModP (p := p)

/-- 元の同じ Cofixed 条件により、第二指標の mod p は1。
有限段の商作用の結論であり、第二 p 進指標全体の自明性ではない。 -/
theorem residualTateSecondCharacter_mod_prime (σ : Field.absoluteGaloisGroup ℚ) :
    Units.map (piP).toMonoidHom (d σ) = 1 := by
  let y := actionLinear S.residualPointActionHom σ w - w
  have hy : tateReduction S.rationalCurve p y ∈ L := by
    change S.residualRepresentation σ (tateReduction S.rationalCurve p w) -
      tateReduction S.rationalCurve p w ∈ L
    exact hcofixed σ _
  let q : L := ⟨tateReduction S.rationalCurve p y, hy⟩
  obtain ⟨c, hc⟩ := S.residualTateLineReduction_surjective L hline hcofixed hζ hp5 hclass hbad q
  have hcpt := congrArg (fun z : L => z.val.val) hc
  change evaluation 0 c.val = evaluation 0 y at hcpt
  have hz0 : reduction (y - c.val) = 0 := by
    apply Subtype.ext
    change evaluation 0 y - evaluation 0 c.val = 0
    exact sub_eq_zero.mpr hcpt.symm
  let z := shiftOfZero (y - c.val) hz0
  have hpz : p • z = y - c.val := nsmul_shiftOfZero _ hz0
  have hcs : ((eqv).symm c.val).2 = 0 := by
    apply (S.residualTateEquiv_mem_line_iff L hline hcofixed hζ hp5 hclass hbad
      ((eqv).symm c.val).1 ((eqv).symm c.val).2).mp
    simpa only [Prod.mk.eta, LinearEquiv.apply_symm_apply] using c.property
  have hw : (eqv).symm w = (0, 1) :=
    (eqv).symm_apply_eq.mpr (S.residualTateEquiv_second L hline hcofixed hζ hp5 hclass hbad).symm
  have hys : ((eqv).symm y).2 = (d σ : ℤ_[p]) - 1 := by
    dsimp only [y]
    rw [map_sub]
    change ((eqv).symm (actionLinear S.residualPointActionHom σ w)).2 - ((eqv).symm w).2 = _
    rw [S.residualTateSecond_coordinate L hline hcofixed hζ hp5 hclass hbad, hw]
  have he := congrArg (eqv).symm hpz
  rw [map_nsmul, map_sub] at he
  have hs := congrArg Prod.snd he
  change p • ((eqv).symm z).2 = ((eqv).symm y).2 - ((eqv).symm c.val).2 at hs
  rw [hys, hcs, sub_zero] at hs
  have hr := congrArg piP hs
  have hz : (0 : ZMod p) = piP (d σ : ℤ_[p]) - 1 := by
    simpa only [map_nsmul, nsmul_eq_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul, map_sub, map_one] using hr
  apply Units.ext
  change piP (d σ : ℤ_[p]) = 1
  exact sub_eq_zero.mp hz.symm

/-- 実際の行列式を mod p に落とすと、以前の同じ円分指標となる。
これは高位 p 進行列式の円分同定を新たに証明した定理ではない。 -/
theorem residualTate_determinant_mod_prime (σ : Field.absoluteGaloisGroup ℚ) :
    piP (mat σ).det = (CyclotomicRootModule.cyclotomicCharacter p σ : ZMod p) := by
  rw [S.residualTate_determinant L hline hcofixed hζ hp5 hclass hbad, map_mul]
  have hd := congrArg Units.val (S.residualTateSecondCharacter_mod_prime L hline hcofixed hζ hp5 hclass hbad σ)
  change piP (d σ : ℤ_[p]) = 1 at hd
  rw [hd, mul_one]
  exact congrArg Units.val (S.residualPadicTowerCharacter_mod_prime L hline hcofixed hζ hp5 hclass hbad σ)

end
end DkMath.FLT.Frey.Source
```

## 回帰例と監査

`DkMathTest.FLT.FreyTateCharacters` は具体的な Γ=(ZMod 25)ˣ 上で

    ρ(u)=[[u,1−u],[0,1]]

という実際の群準同型を構成する。
汎用構成の二指標が実際に u と1になり、u=6（逆元21）では上右成分が非零となることを確認する。
第二指標が1でも上右成分が自動的に0とはならないことを検査する。
また単元6は mod 5 で1でも mod 25 では1でなく、有限精度の自明性と高位自明性を区別する。

同じ条件付き Frey Source では、第二指標の逆元公式と、上右成分の積公式を σ と σ⁻¹ に適用した零公式、
元の Cofixed 条件からの同じ第二指標の有限剰余を確認する。

主要15宣言の公理報告・型／構成子／不透明証明本体の再帰依存監査、12件の公開入力監査を追加する。
実際の行列準同型・同じ基底・有限段の座標単射性・全捩れ開核・同じ直線の還元全射性・シフト逆像を監査する。
汎用の三角性 ht・有限剰余開核 hopen は明示し、実際の Frey 適用では既存の証明から供給する。
同じ hclass と全段 hbad を保持し、hunit/hsecond/hcont/hcocycle/hsplit/htrivial/hmodp/hdet を新たな provider にしない。

3 production の Lib/FLT/root 公開、通常テスト入口、root smoke、教科書3ブロックの全文一致・個別コンパイルを確認する。
記録：`evidence/validation-note032-frey-tate-characters.txt`。

## 残る境界

- 同じ円分類群商の特定 ω² 成分の消滅 hclass。
- 全段の共鳴素点条件 hbad または反復に十分な保存性。
- 第二指標 d の高位の算術的制約、高位 Weil pairing と全 p 進円分行列式との一致。
- 良還元 Frobenius の特性多項式と最終矛盾の局所・大域算術。

今回、実際の第二連続単元値指標、非対角成分の積公式、行列式の二指標積、第二指標の mod p 自明性まで完成した。
完全列の Galois 分裂・上右成分の消滅・第二指標全体の自明性は証明していない。
**今回の3ステップは完成。一般 hno は引き続き未完成である。**
外部の深い分類定理を追加せず、既存の同じ点作用・基底・有限捩れ開核・残余 Cofixed 条件・
直線の還元・実際の p 倍逆像と Mathlib の行列積・単元 API を使う。

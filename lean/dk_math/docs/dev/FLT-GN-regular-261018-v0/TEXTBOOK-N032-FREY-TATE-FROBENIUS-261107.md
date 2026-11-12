# NOTE-032 教科書: 同じ Frobenius の円分値・特性多項式・有限捩れ二次関係

更新日: 2026-11-07。前回の全精度円分行列式を、同じ実際の Frobenius 作用へ接続する３ステップ。
レビューの今後の方針を参考に、今回実装できる部分と有限体点数との未接続部分を区別する。

## 1. 同じ Frobenius 元の円分値は全精度で q

同じ付値環 A の剰余体上で q 乗として作用する σ を使う。
次数 n が付値単元なら n 乗根は剰余合同から一意に復元できる。
既存 apply_root_eq_pow により σ(z)=z^q を体自身へ戻し、原始 n 乗根の位数で
有限円分指標の値を q mod n と同定する。n は素数でなくてよい。

q と p が異なる素数なら、同じ A において p とその全正冪は付値単元である。
Mathlib の p 進円分指標は各有限円分指標へ還元されるため、全正冪剰余の外延性から
cyclo∞(σ)=q を p 進整数そのものの等式として得る。
ここは円分体の計算なので、楕円曲線の良還元を要求しない。
q≠p、LiesOverPrime、同じ σ の IsFrobeniusAt を省略しない。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicFrobenius
import DkMath.Lib.NumberTheory.EllipticWeilDeterminantAll
import DkMath.Lib.Algebra.PadicCharacterLimit

#print "file: DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll"

/-!
# 同じ Frobenius の全有限・p 進円分値

剰余体上で q 乗として作用する同じ元を保つ。良還元はこの円分計算には不要。
捩れ次数が付値単元であることから冪根の作用を体へ戻し、全正冪剰余で比較する。
-/
namespace DkMath.Lib.NumberTheory.CyclotomicFrobenius
open ValuationInertia ValuationFrobenius EllipticTorsionRepresentation

/-- 任意の非零単元次数で、同じ Frobenius の有限円分値は q。 -/
theorem torsionCyclotomicCharacter_eq_natCast (n : ℕ) (hn : n ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ}
    (hunit : A.valuation (n : AlgebraicClosure ℚ) = 1)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (torsionCyclotomicCharacter n hn σ : ZMod n) = (q : ZMod n) := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n
  have hpow := apply_root_eq_pow A hσ hn hunit hz.pow_eq_one
  have hc := torsionCyclotomicCharacter_spec n hn σ hz.toRootsOfUnity
  have he : z ^ (torsionCyclotomicCharacter n hn σ : ZMod n).val = z ^ q := hc.symm.trans hpow
  have hmod : Nat.ModEq n (torsionCyclotomicCharacter n hn σ : ZMod n).val q := by
    have heU : hz.toRootsOfUnity.val ^ (torsionCyclotomicCharacter n hn σ : ZMod n).val =
        hz.toRootsOfUnity.val ^ q := Units.ext he
    have h := pow_eq_pow_iff_modEq.mp heU
    rw [← orderOf_units] at h
    change Nat.ModEq (orderOf z) (torsionCyclotomicCharacter n hn σ : ZMod n).val q at h
    rwa [← hz.eq_orderOf] at h
  simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

/-- q≠p の同じ素点では p の全冪も付値単元。 -/
theorem prime_power_valuation_eq_one {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (n : ℕ) :
    A.valuation ((p ^ (n + 1) : ℕ) : AlgebraicClosure ℚ) = 1 := by
  have hu : A.valuation (p : AlgebraicClosure ℚ) = 1 :=
    ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff A).mp hA) (by
        intro h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp (by exact_mod_cast h)))
  rw [Nat.cast_pow, map_pow, hu, one_pow]

/-- 標準 p 進円分指標の同じ実際の Frobenius 値は、整数 q 自身。 -/
theorem padicCyclotomicCharacter_eq_natCast {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (_root_.cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]) = q := by
  apply DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive
  intro n
  rw [_root_.cyclotomicCharacter.toZModPow]
  change (torsionCyclotomicCharacter (p ^ (n + 1))
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ : ZMod (p ^ (n + 1))) = _
  rw [torsionCyclotomicCharacter_eq_natCast _ _ A (prime_power_valuation_eq_one hq hqp A hA n) hσ]
  exact (map_natCast (PadicInt.toZModPow (n + 1)) q).symm

end DkMath.Lib.NumberTheory.CyclotomicFrobenius
```

## 2. 行列・線形作用としての二次関係

上三角2次作用の trace は第一指標と第二指標の和、特性多項式は
(X−a)(X−d) となる。上右成分 b は一般に零ではない。
多項式が因数分解されることを、Galois 表現の分裂と取り違えない。

可換環上の任意の2次行列 M について M²+det(M)I=trace(M)M を成分ごとに証明する。
体の仮定も三角性も要らない。実際の基底の toMatrixAlgEquiv の単射性を使うと、
その式は同じ線形作用 f に対する f(f(x))+c・x=a・f(x) に戻る。
汎用入口では実際の行列の trace=a、det=c を明示入力とし、次の Frey 入口で内部供給する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

#print "file: DkMath.Lib.RepresentationTheory.TriangularTwoCharacteristic"

/-!
# 上三角作用の特性多項式と実際の二次関係

係数環は可換環。非対角成分を零と仮定せず、全行列について証明する。
-/
namespace DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
open Polynomial
variable {Γ R : Type*} [Group Γ] [CommRing R]
    (ρ : Γ →* Matrix (Fin 2) (Fin 2) R) (ht : ∀ g, ρ g 1 0 = 0)

/-- 実際の trace は同じ二つの対角指標の和。 -/
theorem trace (g : Γ) :
    (ρ g).trace = (first ρ ht g : R) + (second ρ ht g : R) := Matrix.trace_fin_two _

/-- 二つの対角指標が特性多項式を因数分解する。分裂するのは多項式であり表現ではない。 -/
theorem charpoly_factor [Nontrivial R] (g : Γ) :
    (ρ g).charpoly = (X - C (first ρ ht g : R)) * (X - C (second ρ ht g : R)) := by
  rw [Matrix.charpoly_fin_two, trace ρ ht, determinant ρ ht, map_add, map_mul]
  ring

/-- 同じ行列自体の二次関係。上右成分を含めて直接確認する。 -/
theorem quadratic (g : Γ) :
    ρ g * ρ g + ((first ρ ht g : R) * (second ρ ht g : R)) • (1 : Matrix (Fin 2) (Fin 2) R) =
      ((first ρ ht g : R) + (second ρ ht g : R)) • ρ g := by
  change ρ g * ρ g + (ρ g 0 0 * ρ g 1 1) • (1 : Matrix (Fin 2) (Fin 2) R) =
    (ρ g 0 0 + ρ g 1 1) • ρ g
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht] <;> ring

/-- 任意の二次行列の二次関係。三角性さえ必要ない。 -/
theorem matrix_quadratic (M : Matrix (Fin 2) (Fin 2) R) :
    M * M + M.det • (1 : Matrix (Fin 2) (Fin 2) R) = M.trace • M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- 実際の基底での行列の二次関係を、同じ線形作用そのものへ戻す。 -/
theorem linear_quadratic {V : Type*} [AddCommGroup V] [Module R V]
    (b : Module.Basis (Fin 2) R V) (f : V →ₗ[R] V) (a c : R)
    (htrace : (LinearMap.toMatrix b b f).trace = a)
    (hdet : (LinearMap.toMatrix b b f).det = c) (x : V) :
    f (f x) + c • x = a • f x := by
  have hm := matrix_quadratic (LinearMap.toMatrix b b f)
  rw [htrace, hdet] at hm
  have hf : f * f + c • (1 : V →ₗ[R] V) = a • f := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    simp only [map_add, map_mul, map_smul, map_one]
    change (LinearMap.toMatrix b b f) * (LinearMap.toMatrix b b f) + c • 1 = a • (LinearMap.toMatrix b b f)
    exact hm
  exact congrArg (fun g : V →ₗ[R] V => g x) hf

end DkMath.Lib.RepresentationTheory.TriangularTwoCharacter
```

## 3. 同じ Frey Tate 表現と有限捩れ点へ

前回までと同じ Source、L、巡回塔、二点列、有限・全 Tate 基底を使う。
同じ全行列の各成分の剰余比較から、有限 trace も全 trace の標準剰余に一致する。
前回の det=cyclo∞ とステップ1を合わせ、同じ σ について det=q を得る。
また d=cyclo∞・χ∞⁻¹ より、実際の trace は χ∞+qχ∞⁻¹ と同定される。
したがって実際の特性多項式は X²−(χ∞+qχ∞⁻¹)X+q となる。

ステップ2の基底による復元で、同じ全 Tate 点列に対する二次関係が従う。
各有限段でも、同じ有限基底と実際の幾何学的 Weil 行列式を使い、
同じ E[p^(n+1)] の点そのものについて二次関係を証明する。
有限段の trace 係数は全 trace の標準剰余である。
新しい htrace、hdet、hCH を最終利用者へ要求しない。
既存の hclass とすべての適格巡回段についての hbad は基底・指標構成の入力として保持する。

```lean
/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyTateCyclotomicDeterminant
import DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll
import DkMath.Lib.RepresentationTheory.TriangularTwoCharacteristic

#print "file: DkMath.FLT.FreyTateFrobenius"

/-!
# 同じ Frey Tate 作用の Frobenius 特性多項式と有限段二次関係

実際の同じ Frobenius 元の円分値は q。トレース係数は実際の χ∞+qχ∞⁻¹。
有限体点数 q+1-#E(Fq) との一致は本章では証明しない。
hclass・全段 hbad を保持し、一般 hno の閉鎖とも区別する。
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
local notation "chi" => S.residualPadicTowerCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "d" => S.residualTateSecondCharacter L hline hcofixed hζ hp5 hclass hbad
local notation "fb" => S.residualTateFiniteBasis L hline hcofixed hζ hp5 hclass hbad
local notation "rho" => S.residualTateMatrixRepresentation L hline hcofixed hζ hp5 hclass hbad
local notation "tri" => S.residualTateMatrixRepresentation_lower_zero L hline hcofixed hζ hp5 hclass hbad
local notation "cyc" => tateCyclotomicCharacter (p := p)
open Polynomial ValuationInertia ValuationFrobenius

/-- 実際の同じ trace。 -/
theorem residualTate_trace (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).trace = (chi σ : ℤ_[p]) + (d σ : ℤ_[p]) := by
  have h := TriangularTwoCharacter.trace rho tri σ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 実際の特性多項式の因数分解。Galois 分裂を主張しない。 -/
theorem residualTate_charpoly (σ : Field.absoluteGaloisGroup ℚ) :
    (mat σ).charpoly = (X - C (chi σ : ℤ_[p])) * (X - C (d σ : ℤ_[p])) := by
  have h := TriangularTwoCharacter.charpoly_factor rho tri σ
  rw [S.residualTateMatrix_first_character L hline hcofixed hζ hp5 hclass hbad] at h
  exact h

/-- 同じ有限基底の実際のトレースは、全トレースの同じ剰余。 -/
theorem residualTate_trace_reduction (n : ℕ) (σ : Field.absoluteGaloisGroup ℚ) :
    (LinearMap.toMatrix (fb n) (fb n) (representation S.rationalCurve (p ^ (n + 1)) σ)).trace =
      PadicInt.toZModPow (n + 1) (mat σ).trace := by
  simp only [Matrix.trace_fin_two, map_add]
  rw [S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad,
    S.residualTate_matrix_reduction L hline hcofixed hζ hp5 hclass hbad]

/-- 同じ実際の Frobenius の p 進円分値。良還元を要求しない。 -/
theorem tateCyclotomicCharacter_frobenius {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (cyc σ : ℤ_[p]) = q :=
  CyclotomicFrobenius.padicCyclotomicCharacter_eq_natCast hq hqp A hA hσ

/-- Frobenius の実際の行列式は q。 -/
theorem residualTate_frobenius_det {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (mat σ).det = (q : ℤ_[p]) := by
  rw [S.residualTate_determinant_cyclotomic L hline hcofixed hζ hp5 hclass hbad]
  exact tateCyclotomicCharacter_frobenius hq hqp A hA hσ

/-- Frobenius の実際のトレース係数。有限体点数とはまだ同定していない。 -/
theorem residualTate_frobenius_trace {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (mat σ).trace = (chi σ : ℤ_[p]) + (q : ℤ_[p]) * ((chi σ)⁻¹ : ℤ_[p]ˣ) := by
  rw [S.residualTate_trace L hline hcofixed hζ hp5 hclass hbad,
    S.residualTateSecondCharacter_eq_cyclotomic L hline hcofixed hζ hp5 hclass hbad,
    Units.val_mul, tateCyclotomicCharacter_frobenius hq hqp A hA hσ]

/-- 同じ Frobenius の特性多項式の定数項を実際に q と同定する。 -/
theorem residualTate_frobenius_charpoly {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (mat σ).charpoly = X ^ 2 - C ((chi σ : ℤ_[p]) +
      (q : ℤ_[p]) * ((chi σ)⁻¹ : ℤ_[p]ˣ)) * X + C (q : ℤ_[p]) := by
  rw [Matrix.charpoly_fin_two,
    S.residualTate_frobenius_trace L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ,
    S.residualTate_frobenius_det L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ]

/-- 同じ全 Tate 点列そのものが満たす、実際の Frobenius 二次関係。 -/
theorem residualTate_frobenius_relation {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (x : Tate p (Points S.rationalCurve)) :
    actionLinear S.residualPointActionHom σ (actionLinear S.residualPointActionHom σ x) +
      (q : ℤ_[p]) • x = (mat σ).trace • actionLinear S.residualPointActionHom σ x := by
  exact TriangularTwoCharacter.linear_quadratic basis (actionLinear S.residualPointActionHom σ)
    (mat σ).trace (q : ℤ_[p]) rfl
    (S.residualTate_frobenius_det L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ) x

/-- 同じ有限捩れ点への二次関係。新たな Cayley–Hamilton provider は不要。 -/
theorem residualTate_finite_frobenius_relation (n : ℕ) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q)
    (P : Torsion S.rationalCurve (p ^ (n + 1))) :
    representation S.rationalCurve (p ^ (n + 1)) σ (representation S.rationalCurve (p ^ (n + 1)) σ P) +
      (q : ZMod (p ^ (n + 1))) • P =
      PadicInt.toZModPow (n + 1) (mat σ).trace • representation S.rationalCurve (p ^ (n + 1)) σ P := by
  apply TriangularTwoCharacter.linear_quadratic (fb n)
  · exact S.residualTate_trace_reduction L hline hcofixed hζ hp5 hclass hbad n σ
  · rw [LinearMap.det_toMatrix,
      torsion_determinant_all S.rationalCurve _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) (fb n) σ,
      ← S.residualTate_determinant_finite L hline hcofixed hζ hp5 hclass hbad n σ]
    rw [S.residualTate_frobenius_det L hline hcofixed hζ hp5 hclass hbad hq hqp A hA hσ, map_natCast]

end
end DkMath.FLT.Frey.Source
```

## 算術的な境界

今回の特性多項式の係数は、実際の Galois 作用から計算した χ∞+qχ∞⁻¹ である。
良還元時にこれが整数 a_q=q+1−#E(F_q) に一致することは、まだ証明していない。
したがって有限体点数を係数とする算術的 Frobenius 関係や、既存の最終捩れ塔矛盾への
全接続が完成したとは扱わない。記号だけを a_q と名付けて点数同定を隠すこともしない。

第二指標全体の自明性、商上の高位固定性、Galois 分裂、hclass と全段 hbad の算術的供給、
最終矛盾は残っており、一般 hno は未完成である。

## 検証とコードのコピー

通常入口 DkMath と DkMathTest から公開する。
主要15宣言の公理・再帰依存監査と12件の公開入力監査を用意した。
法25の重根特性多項式と非スカラー行列、非三角行列の二次関係を回帰例とする。
この３つの Lean ブロックは production 各ファイル全文と同一である。
各 import 直後の #print は元のモジュール名を示し、コピー時にも保持する。
実行結果は evidence/validation-note032-frey-tate-frobenius.txt に記録する。

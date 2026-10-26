/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Polynomial formulas adapted from Definitions/Def_WeierstrassCurve_Velu.lean,
blob 35bd154a52a4e83267a2930da2438ece8cc64a54.
Modified: finite indexed families, arbitrary subring integrality and no quotient assertion.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula

#print "file: DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial"

/-!
# 分母を持たないVélu係数の多項式算術

[DkMath.Lib] 非零反転対から一つずつ選んだ点では、t=6x²+b₂x+b₄、
w=(2y+a₁x+a₃)²+xtを使う。これらは反転不変であり、割り算を含まない。
係数候補a₄'=a₄−5Σt、a₆'=a₆−b₂Σt−7Σwは任意の部分環で構成できる。

本所有者は多項式の係数構成と環写像・整性を証明する。
この候補が既存kernelModelと一致することや、同じ座標の方程式、楕円性は主張しない。
-/
namespace DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial
open WeierstrassCurve
open scoped BigOperators
variable {R : Type*} [CommRing R]

/-- [DkMath.Lib] 非零反転対のt寄与。yに依存せず、分母を持たない。 -/
def momentT (W : WeierstrassCurve R) (x : R) : R := 6 * x ^ 2 + W.b₂ * x + W.b₄

/-- [DkMath.Lib] 非零反転対のw寄与。反転で符号が変わる線形式を平方して使う。 -/
def momentW (W : WeierstrassCurve R) (x y : R) : R :=
  (2 * y + W.a₁ * x + W.a₃) ^ 2 + x * momentT W x

/-- [DkMath.Lib] 同じx上の反対点を選んでもwは変わらない。 -/
theorem momentW_negY (W : WeierstrassCurve R) (x y : R) :
    momentW W x (W.toAffine.negY x y) = momentW W x y := by
  simp only [momentW, Affine.negY]
  ring

/-- [DkMath.Lib] 有限添字集合から構成するVélu型の多項式係数モデル候補。 -/
def polynomialModel {ι : Type*} (W : WeierstrassCurve R) (s : Finset ι) (x y : ι → R) :
    WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * ∑ i ∈ s, momentT W (x i)
  a₆ := W.a₆ - W.b₂ * (∑ i ∈ s, momentT W (x i)) - 7 * ∑ i ∈ s, momentW W (x i) (y i)

/-- [DkMath.Lib] 多項式係数の構成は任意の環準同型と可換。剰余環への写像にも使える。 -/
theorem polynomialModel_map {S : Type*} [CommRing S] (f : R →+* S)
    {ι : Type*} (W : WeierstrassCurve R) (s : Finset ι) (x y : ι → R) :
    (polynomialModel W s x y).map f = polynomialModel (W.map f) s (f ∘ x) (f ∘ y) := by
  ext <;> simp [polynomialModel, momentT, momentW, b₂, b₄, map_sum, map_ofNat]

/-- [DkMath.Lib] モデルの五つの係数が同じ部分環に入るという条件。 -/
def CoefficientsIn (A : Subring R) (W : WeierstrassCurve R) : Prop :=
  W.a₁ ∈ A ∧ W.a₂ ∈ A ∧ W.a₃ ∈ A ∧ W.a₄ ∈ A ∧ W.a₆ ∈ A

/-- [DkMath.Lib] 部分環に入る源の係数と有限点座標から、同じ多項式係数候補の整性を得る。
部分環の閉性だけで成立し、2や核の位数の逆数を使用しない。 -/
theorem polynomialModel_coefficientsIn {ι : Type*} (A : Subring R) (W : WeierstrassCurve R)
    (s : Finset ι) (x y : ι → R) (hW : CoefficientsIn A W)
    (hxy : ∀ i ∈ s, x i ∈ A ∧ y i ∈ A) : CoefficientsIn A (polynomialModel W s x y) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := hW
  have hb₂ : W.b₂ ∈ A := A.add_mem (A.pow_mem h₁ 2) (A.mul_mem (natCast_mem A 4) h₂)
  have hb₄ : W.b₄ ∈ A := A.add_mem (A.mul_mem (natCast_mem A 2) h₄) (A.mul_mem h₁ h₃)
  have ht (i : ι) (hi : i ∈ s) : momentT W (x i) ∈ A :=
    A.add_mem (A.add_mem (A.mul_mem (natCast_mem A 6) (A.pow_mem (hxy i hi).1 2))
      (A.mul_mem hb₂ (hxy i hi).1)) hb₄
  have hw (i : ι) (hi : i ∈ s) : momentW W (x i) (y i) ∈ A :=
    A.add_mem (A.pow_mem (A.add_mem (A.add_mem (A.mul_mem (natCast_mem A 2) (hxy i hi).2)
      (A.mul_mem h₁ (hxy i hi).1)) h₃) 2) (A.mul_mem (hxy i hi).1 (ht i hi))
  exact ⟨h₁, h₂, h₃, A.sub_mem h₄ (A.mul_mem (natCast_mem A 5) (A.sum_mem ht)),
    A.sub_mem (A.sub_mem h₆ (A.mul_mem hb₂ (A.sum_mem ht)))
      (A.mul_mem (natCast_mem A 7) (A.sum_mem hw))⟩

/-- [DkMath.Lib] 二つのモーメントは任意の環写像と可換。 -/
theorem moments_map {S : Type*} [CommRing S] (f : R →+* S)
    (W : WeierstrassCurve R) (x y : R) :
    momentT (W.map f) (f x) = f (momentT W x) ∧
      momentW (W.map f) (f x) (f y) = f (momentW W x y) := by
  constructor <;> simp [momentT, momentW, b₂, b₄, map_ofNat]

/-- [DkMath.Lib] 候補の平方完成三次式の係数。二つのモーメント和を明示して保つ。 -/
theorem polynomialModel_b_invariants {ι : Type*} (W : WeierstrassCurve R)
    (s : Finset ι) (x y : ι → R) :
    (polynomialModel W s x y).b₂ = W.b₂ ∧
      (polynomialModel W s x y).b₄ = W.b₄ - 10 * ∑ i ∈ s, momentT W (x i) ∧
      (polynomialModel W s x y).b₆ = W.b₆ - 4 * W.b₂ * (∑ i ∈ s, momentT W (x i)) -
        28 * ∑ i ∈ s, momentW W (x i) (y i) := by
  simp only [polynomialModel, b₂, b₄, b₆]
  constructor
  · trivial
  constructor <;> ring

end DkMath.Lib.NumberTheory.WeierstrassVeluPolynomial

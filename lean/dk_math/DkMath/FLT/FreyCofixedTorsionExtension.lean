/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedCyclotomic
import DkMath.Lib.NumberTheory.EllipticTorsionPreimageExtension

#print "file: DkMath.FLT.FreyCofixedTorsionExtension"

/-!
# Cofixed 直線から、実際の二次元 extension の第一段へ

元の残余直線 `L` の実点群内の像を `K` とし、`V=(p⁻¹K)/K` を構成する。
`C` は元の `E[p]` の同じ商への像である。これらは形式的な代替空間ではない。

既存の幾何学・Cofixed 性・円分指標公式を合成し、次を全て内部供給する。
`#V=p²`, `dim V=2`, `dim C=1`, `C` の点ごとの固定性、商上の円分作用、開核。
この段階で安定な補直線が存在すると仮定したり、主張したりしない。
安定な補直線を作る局所分裂・大域 extension 消滅が次の算術課題である。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory EllipticTorsionRepresentation CyclotomicRootModule
open DkMath.Lib.Algebra
open DkMath.Lib.RepresentationTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] (S : Source p)
local instance : S.rationalCurve.IsElliptic := S.rationalCurve_isElliptic

/-- 同じ実点群から作った次段商。 -/
abbrev ResidualPreimageQuotient (L : Submodule (ZMod p) S.ResidualSpace) :=
  TorsionPreimageQuotient.Quotient p (pointSubgroup S.rationalCurve p L)

/-- 構成した商における、実際の元の `p` 捩れの像。 -/
def residualPreimageFixedLine (L : Submodule (ZMod p) S.ResidualSpace) :
    Submodule (ZMod p) (S.ResidualPreimageQuotient L) :=
  TorsionPreimageQuotient.torsionImage p (pointSubgroup S.rationalCurve p L)

/-- Cofixed 性が供給する安定性で、同じ商への Galois 表現を定義する。 -/
def residualPreimageRepresentation (L : Submodule (ZMod p) S.ResidualSpace)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    Representation (ZMod p) (Field.absoluteGaloisGroup ℚ) (S.ResidualPreimageQuotient L) :=
  preimageRepresentation S.rationalCurve p (pointSubgroup S.rationalCurve p L)
    (pointSubgroup_stable S.rationalCurve p L hcofixed.isStable)

/-- 実際の extension の濃度・次元・固定直線・開核を合流する。
Cofixed と一次元性以外の arithmetic provider を仮定しない。 -/
theorem residual_cofixed_preimage_extension_profile
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) :
    Nat.card (S.ResidualPreimageQuotient L) = p ^ 2 ∧
      Module.finrank (ZMod p) (S.ResidualPreimageQuotient L) = 2 ∧
      Module.finrank (ZMod p) (S.residualPreimageFixedLine L) = 1 ∧
      IsFixedOn (S.residualPreimageRepresentation L hcofixed) (S.residualPreimageFixedLine L) ∧
      IsOpen ((S.residualPreimageRepresentation L hcofixed).ker :
        Set (Field.absoluteGaloisGroup ℚ)) := by
  let K := pointSubgroup S.rationalCurve p L
  have hKcard : Nat.card K = p ^ 1 := by
    rw [pow_one]
    exact card_pointSubgroup S.rationalCurve p L hline
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : IsAddCyclic K := isAddCyclic_pointSubgroup S.rationalCurve p L hline
  exact ⟨card_preimageQuotient S.rationalCurve K,
    finrank_preimageQuotient S.rationalCurve K,
    finrank_torsionImage_of_cyclic S.rationalCurve K (by decide : 1 ≤ 1) hKcard,
    preimageRepresentation_fixed_torsionImage_of_cofixed S.rationalCurve K _ L hcofixed le_rfl,
    preimageRepresentation_kernel_isOpen S.rationalCurve K _ 1 (by
      intro x hx
      simpa only [pow_one] using pointSubgroup_killed S.rationalCurve p L x hx)⟩

/-- 同じ extension の商 `V/C` 上の作用は円分指標。
位数 `p` の元の核への既存の円分作用を、具体的な倍写像 `V → K` を通じて輸送する。 -/
theorem residual_cofixed_preimage_quotient_cyclotomic
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (σ : Field.absoluteGaloisGroup ℚ) (v : S.ResidualPreimageQuotient L) :
    S.residualPreimageRepresentation L hcofixed σ v -
        (cyclotomicCharacter p σ : ZMod p).val • v ∈ S.residualPreimageFixedLine L := by
  exact TorsionPreimageQuotient.representation_sub_nsmul_mem_torsionImage p
    (pointSubgroup S.rationalCurve p L) (pointActionEndHom S.rationalCurve) _
    (fun x hx => pointSubgroup_killed S.rationalCurve p L x hx)
    (fun τ => (cyclotomicCharacter p τ : ZMod p).val)
    (fun τ x hx => S.residual_cofixed_pointSubgroup_action_eq_cyclotomic_nsmul
      L hline hcofixed τ hx) σ v

/-- 最初の extension に安定な補直線を供給できれば、同じ点群の中に次の
位数 `p²` の安定部分群を具体的に持ち上げられる。補直線の存在は別の算術入力。
次段の濃度・巡回性・捩れ次数・底への包含を provider として要求しない。 -/
theorem residual_preimage_stable_complement_lifts
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L)
    (C' : Submodule (ZMod p) (S.ResidualPreimageQuotient L))
    (hcompl : IsCompl (S.residualPreimageFixedLine L) C')
    (hstable : ∀ σ : Field.absoluteGaloisGroup ℚ, ∀ v ∈ C',
      S.residualPreimageRepresentation L hcofixed σ v ∈ C') :
    ∃ K' : AddSubgroup (Points S.rationalCurve), pointSubgroup S.rationalCurve p L ≤ K' ∧
      Nat.card K' = p ^ 2 ∧ IsAddCyclic K' ∧ (∀ x ∈ K', p ^ 2 • x = 0) ∧
      (∀ σ : Field.absoluteGaloisGroup ℚ, ∀ x ∈ K', pointAction S.rationalCurve σ x ∈ K') ∧
      (∀ x ∈ K', p • x = 0 → x ∈ pointSubgroup S.rationalCurve p L) := by
  let K := pointSubgroup S.rationalCurve p L
  have hKcard : Nat.card K = p ^ 1 := by
    rw [pow_one]
    exact card_pointSubgroup S.rationalCurve p L hline
  let : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let : IsAddCyclic K := isAddCyclic_pointSubgroup S.rationalCurve p L hline
  exact exists_tower_step_of_stable_complement S.rationalCurve K
    (pointSubgroup_stable S.rationalCurve p L hcofixed.isStable)
    (by decide : 1 ≤ 1) hKcard (by
      intro x hx
      simpa only [pow_one] using pointSubgroup_killed S.rationalCurve p L x hx)
    C' hcompl hstable

end
end DkMath.FLT.Frey.Source

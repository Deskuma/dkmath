/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyIntegralTorsionWitness
import DkMath.Lib.NumberTheory.EllipticGoodReductionKernel
import DkMath.Lib.RepresentationTheory.AbsorbingSubspace
import DkMath.Lib.NumberTheory.AbsoluteInertiaConjugacy

#print "file: DkMath.FLT.FreyPrimeGoodFiltration"

/-!
# NOTE-031-004B/C: p∤abcの場合の真の吸収空間と局所二択

同じ実際のE[p]と、無限遠に還元する点の加法部分群との交わりをFₚ部分加群にする。
良還元なら全慣性変化量がこの部分加群へ入る。安定直線から既に構成した整な有限捩れ点は
還元核の外にあるので、この部分加群は真である。
剰余標数と位数が等しいp上の議論であり、031-002の単元位数の整性を誤用しない。
この章の終点はp∤abcの場合であり、乗法的還元の場合を追加仮定で隠さない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory EllipticDyadicSeparation EllipticReductionKernel
open EllipticTorsionRepresentation ValuationInertia
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
noncomputable local instance instDecidableEqFreyPrimeGoodFiltration : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _
variable {p : ℕ} [Fact p.Prime] (S : Source p)

omit [Fact p.Prime] in
/-- 同じFrey曲線は任意の付値環において既存の整数モデルから整である。 -/
theorem integral_at_valuation (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Integral A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) := by
  rw [← S.valuationModel_map A]
  exact ⟨(S.valuationModel A).a₁.2, (S.valuationModel A).a₂.2,
    (S.valuationModel A).a₃.2, (S.valuationModel A).a₄.2, (S.valuationModel A).a₆.2⟩

/-- 実際の残余点を元の幾何学的点群へ戻す加法準同型。 -/
noncomputable def residualUnderlyingHom : S.ResidualSpace →+
    (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).toAffine.Point where
  toFun P := P.val
  map_zero' := rfl
  map_add' _ _ := rfl

/-- 実際のE[p]のうち、無限遠へ還元する点からなるFₚ部分加群。 -/
noncomputable def residualReductionKernel (A : ValuationSubring (AlgebraicClosure ℚ)) :
    Submodule (ZMod p) S.ResidualSpace :=
  AddSubgroup.toZModSubmodule p
    ((ofIntegral A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) (S.integral_at_valuation A)).comap
      S.residualUnderlyingHom)

/-- 部分加群への所属は、同じ実点が無限遠または極であることと同値である。 -/
theorem mem_residualReductionKernel_iff (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : S.ResidualSpace) : P ∈ S.residualReductionKernel A ↔
      PoleOrZero A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) P.val := by
  change P.val ∈ ofIntegral A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)) _ ↔ _
  exact mem_ofIntegral_iff A _ _ P.val

/-- 全ガロア安定直線があるなら、還元核との交わりは真の部分加群である。
整な有限p捩れ点の存在を数論から供給する。 -/
theorem residualReductionKernel_ne_top (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) : S.residualReductionKernel A ≠ ⊤ := by
  obtain ⟨t, x, y, h, ht, hx⟩ := S.exists_integral_torsion_of_stable_line hp5 A hA N hN hbot htop
  intro heq
  have hm : t ∈ S.residualReductionKernel A := heq ▸ Submodule.mem_top
  rw [S.mem_residualReductionKernel_iff A t, ht, poleOrZero_some_iff] at hm
  exact hm.not_ge ((A.valuation_le_one_iff _).mpr hx)

/-- p∤abcで、慣性による全残余変化量を同じ還元核部分加群が吸収する。 -/
theorem residualReductionKernel_absorbs_at_good_prime (hp2 : p ≠ 2)
    (hgood : ¬ (p : ℤ) ∣ S.a * S.b * S.c)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    CofixedOn S.residualRepresentation (S.residualReductionKernel A) (inertiaSubgroupIn A ℚ) := by
  have hE := S.valuation_reduction_isElliptic (Nat.Prime.pos Fact.out) hp2 hgood A hA
  have hg : (((S.integral_at_valuation A).model).map (IsLocalRing.residue A)).Δ ≠ 0 := by
    have he : (S.integral_at_valuation A).model = S.valuationModel A := by
      apply WeierstrassCurve.map_injective (f := A.subtype) Subtype.val_injective
      change (S.integral_at_valuation A).model.map A.subtype = (S.valuationModel A).map A.subtype
      rw [Integral.model_map, S.valuationModel_map A]
    rw [he]
    exact isUnit_iff_ne_zero.mp ((WeierstrassCurve.isElliptic_iff _).mp hE)
  intro σ hσ P
  rw [S.mem_residualReductionKernel_iff]
  have hm := EllipticGoodReductionKernel.inertia_difference_mem S.rationalCurve A
    (S.integral_at_valuation A) hg σ hσ P.val
  change PoleOrZero A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))
    (pointAction S.rationalCurve σ P.val - P.val) at hm
  exact hm

/-- p∤abcの場合、同じ安定直線または同じ商がp上の慣性群全体で固定される。 -/
theorem residual_fixed_or_cofixed_at_p_of_good (hp5 : 5 ≤ p)
    (hgood : ¬ (p : ℤ) ∣ S.a * S.b * S.c)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A p) :
    FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) ∨
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) := by
  have := S.rationalCurve_isElliptic
  exact AbsorbingSubspace.fixed_or_cofixed S.residualRepresentation S.residual_finrank_eq_two
    (inertiaSubgroupIn A ℚ) N (fun g _ => hN g) hbot htop (S.residualReductionKernel A)
    (S.residualReductionKernel_ne_top hp5 A hA N hN hbot htop)
    (S.residualReductionKernel_absorbs_at_good_prime (by omega) hgood A hA)

/-- p∤abcの場合、一つのp上の局所二択から、全てのp上の付値環で同じ側の二択を得る。
慣性元ごとも付値環ごとも側を選び直さず、同じ安定直線と商を保つ。 -/
theorem residual_common_side_at_p_of_good (hp5 : 5 ≤ p)
    (hgood : ¬ (p : ℤ) ∣ S.a * S.b * S.c)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤) :
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p →
      FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) ∨
    (∀ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p →
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ)) := by
  by_cases hex : ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A p
  · obtain ⟨A, hA⟩ := hex
    exact AbsoluteInertiaConjugacy.common_side_on_places S.residualRepresentation N hN Fact.out A hA
      (S.residual_fixed_or_cofixed_at_p_of_good hp5 hgood N hN hbot htop A hA)
  · left
    intro A hA
    exact (hex ⟨A, hA⟩).elim

end DkMath.FLT.Frey.Source

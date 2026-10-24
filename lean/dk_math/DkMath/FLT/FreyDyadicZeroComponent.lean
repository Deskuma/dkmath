/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDyadicGeometry
import DkMath.Lib.NumberTheory.EllipticNodalTorsionBound

#print "file: DkMath.FLT.FreyDyadicZeroComponent"

/-!
# NOTE-032-003B: 2上の零成分外の点と非自明慣性を供給する

同じSourceの実際のE₀[p]を、その点を変えずに滑らかなp捩れの集合へ単射に写す。
単元位数の捩れ還元の単射性と剰余節点曲線の上界から|E₀[p]|≤pを得る。
同じE[p]の位数p²と比較して零成分の真性を証明し、外側の実点を取る。
003A・002へこの点を渡すと、2上の実際の残余慣性作用が非自明となる。

零成分への慣性変化量の吸収も内部で供給し、非自明な変化量からE₀[p]の非零性を得る。
従って同じE₀[p]は一次元で、位数は正確にpとなる。
E₀と無限遠へ還元するE₁は区別し、hno入口には枝交換だけを残す。
a≡3 mod8からの枝交換の存在は003Cの課題であり、無条件hnoはまだ結論しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じ実際のE₀[p]の位数は高々pである。
中心・方向・還元の単射性・剰余上界を実証明から供給し、位数上界をproviderにしない。 -/
theorem residualZeroComponent_card_le_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    Nat.card (S.residualZeroComponent A) ≤ p := by
  classical
  have := S.rationalCurve_isElliptic
  obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
  apply EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion
    (S.valuationModel A) _ (S.valuationModel_map A) C D
    (Fact.out : p.Prime).pos (residual_order_unit_at_two (by omega) A hA)
    (fun P : S.residualZeroComponent A => P.val.val)
  · intro P Q h
    exact Subtype.ext (Subtype.ext h)
  · intro P
    exact (S.mem_residualZeroComponent_iff A P.val).mp P.property
  · intro P
    exact P.val.property

/-- E[p]の実際の位数p²と比較し、E₀[p]が真部分空間であることを証明する。 -/
theorem residualZeroComponent_ne_top_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    S.residualZeroComponent A ≠ ⊤ := by
  have hc := S.residualZeroComponent_card_le_at_two hp5 A hA
  intro heq
  rw [heq, Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule (ZMod p) S.ResidualSpace) ≃ₗ[ZMod p]
    S.ResidualSpace).toEquiv, S.residual_card_prime_sq] at hc
  nlinarith

/-- 同じSource・同じモデルの実際のp捩れに、零成分外の点が存在する。 -/
theorem residual_exists_not_smooth_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val :=
  (S.residualZeroComponent_ne_top_iff A).mp (S.residualZeroComponent_ne_top_at_two hp5 A hA)

/-- 中心幾何から、2上の全慣性変化量が同じE₀[p]へ入ることを供給する。 -/
theorem residualZeroComponent_absorbs_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    CofixedOn S.residualRepresentation (S.residualZeroComponent A) (inertiaSubgroupIn A ℚ) := by
  obtain ⟨C, D, hfix, -⟩ := S.exists_dyadic_geometry hp5 A hA
  exact S.residualZeroComponent_absorbs_of_fixed_centre A C D hfix

/-- 032-002の終点。p≥5の同じSourceでは、任意の2上の住所の残余慣性作用が非自明である。
中心・方向・中心固定・零成分外の点の存在を追加入力に要求しない。 -/
theorem residual_exists_dyadic_inertia_ne (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P :=
  S.residual_exists_dyadic_inertia_ne_of_zeroComponent_ne_top hp5 A hA
    (S.residualZeroComponent_ne_top_at_two hp5 A hA)

/-- 非自明慣性の実際の変化量が吸収されるので、E₀[p]は非零である。 -/
theorem residualZeroComponent_ne_bot_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    S.residualZeroComponent A ≠ ⊥ := by
  obtain ⟨τ, hτ, P, hne⟩ := S.residual_exists_dyadic_inertia_ne hp5 A hA
  have hmem := S.residualZeroComponent_absorbs_at_two hp5 A hA τ hτ P
  intro heq
  rw [heq, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hne hmem

/-- 位数上界と非零性を合わせると、同じE₀[p]は正確に一次元となる。
零成分の一次元性を初めから仮定せず、還元算術と非自明慣性から導く。 -/
theorem residualZeroComponent_finrank_eq_one_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    Module.finrank (ZMod p) (S.residualZeroComponent A) = 1 := by
  have := S.rationalCurve_isElliptic
  have : Nontrivial (S.residualZeroComponent A) :=
    Submodule.nontrivial_iff_ne_bot.mpr (S.residualZeroComponent_ne_bot_at_two hp5 A hA)
  have hpos := Module.finrank_pos (R := ZMod p) (M := S.residualZeroComponent A)
  have hc := S.residualZeroComponent_card_le_at_two hp5 A hA
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := S.residualZeroComponent A), Nat.card_zmod] at hc
  have hd : Module.finrank (ZMod p) (S.residualZeroComponent A) ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    simpa using hc
  omega

/-- 同じ2上の零成分のp捩れの位数は正確にpである。 -/
theorem residualZeroComponent_card_eq_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    Nat.card (S.residualZeroComponent A) = p := by
  have := S.rationalCurve_isElliptic
  rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := S.residualZeroComponent A), Nat.card_zmod, S.residualZeroComponent_finrank_eq_one_at_two hp5 A hA,
    pow_one]

/-- hnoの残る局所幾何入力は枝交換だけである。
零成分外の点・中心固定・非自明慣性を同じSourceの証明済み定理から供給する。 -/
theorem residual_no_cofixed_line_of_branch_swap_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_dyadic_branch_swap hp5 A hA
    (S.residual_exists_not_smooth_at_two hp5 A hA) hswap

/-- 同じ枝交換だけを残したhnoから、b偶数の同じSourceの既約性へ接続する。 -/
theorem residual_isIrreducible_of_branch_swap_at_two (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction hp5 hbe
    (S.residual_no_cofixed_line_of_branch_swap_at_two hp5 A hA hswap)

end DkMath.FLT.Frey.Source

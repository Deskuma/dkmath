/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyValuationArithmetic
import DkMath.FLT.FreyRationalTorsionValuation
import DkMath.FLT.FreyResidualRankTwo
import DkMath.Lib.NumberTheory.EllipticDyadicWildInertia
import DkMath.Lib.NumberTheory.ValuationTameCharacter
import DkMath.Lib.RepresentationTheory.ConjugateSquare

#print "file: DkMath.FLT.FreyDyadicInertia"

/-!
# NOTE-031-003: 同じFrey残余表現の2上の安定直線と商は慣性固定

Sourceの整数モデルをそのまま使い、a₁=1,a₃=a₆=0,a₄≠0を供給する。
奇素数pは2上の単元なので、野生合同を満たす元は実際のE[p]を固定する。
次に任意の2上の付値環にFrobenius元φを構成し、φτφ⁻¹とτ²の差が
野生合同を満たすことから、表現上の共役二乗関係を得る。

同じ全ガロア安定な真の非零部分加群Nへ線形代数を適用すると、N上の固定と
商E[p]/N上の固定が同時に従う。Frobeniusの存在・野生作用の消滅・二次元性を
追加providerに置かず、既存の同じSourceから供給する。
p上の局所二択(031-004)、大域の反例排除、FLTの終点はこの章の結論ではない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- 同じSourceの奇素数位数は、任意の2上の付値環で単元となる。 -/
theorem residual_order_unit_at_two (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    A.valuation (p : AlgebraicClosure ℚ) = 1 := by
  apply valuation_intCast_eq_one_of_not_dvd A Nat.prime_two
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (z := (p : ℤ))
  intro h
  have hd : 2 ∣ p := by exact_mod_cast h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp hd).symm

/-- 全非零元の乗法的野生合同を満たす自己同型は、同じ実際のE[p]を固定する。 -/
theorem residual_fixed_of_dyadic_wild (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits)
    (P : S.ResidualSpace) : S.residualRepresentation σ P = P := by
  classical
  have := S.rationalCurve_isElliptic
  let E := S.rationalCurve.baseChange (AlgebraicClosure ℚ)
  have hm := S.valuationModel_map A
  have hW : EllipticDyadicSeparation.Integral A E := by
    dsimp [E]
    rw [← hm]
    exact ⟨(S.valuationModel A).a₁.2, (S.valuationModel A).a₂.2,
      (S.valuationModel A).a₃.2, (S.valuationModel A).a₄.2, (S.valuationModel A).a₆.2⟩
  have h₁ : E.a₁ = 1 := by simp [E, WeierstrassCurve.baseChange, S.rationalCurve_a₁]
  have h₃ : E.a₃ = 0 := by simp [E, WeierstrassCurve.baseChange, S.rationalCurve_a₃]
  have h₆ : E.a₆ = 0 := by simp [E, WeierstrassCurve.baseChange, S.rationalCurve_a₆]
  have h₄ : E.a₄ ≠ 0 := by
    simp only [E, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₄,
      S.rationalCurve_a₄, ne_eq, map_eq_zero]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero
      (pow_ne_zero _ (by exact_mod_cast S.a_ne))
      (pow_ne_zero _ (by exact_mod_cast S.b_ne)))) (by norm_num)
  exact EllipticDyadicWildInertia.fixed_of_wild S.rationalCurve p A hW h₁ h₃ h₆ h₄
    ((ValuationSubring.mem_nonunits_iff _).mp hA) (Nat.Prime.odd_of_ne_two Fact.out hp2)
    (by rw [ValuationSubring.mem_nonunits_iff, residual_order_unit_at_two hp2 A hA]; exact lt_irrefl _)
    σ hwild P

/-- 任意の2上の付値環で、実際の残余作用に共役二乗関係を与えるFrobenius元が存在する。 -/
theorem residual_exists_dyadic_conjugate_square (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
      ∀ τ ∈ inertiaSubgroupIn A ℚ, ∀ P : S.ResidualSpace,
        S.residualRepresentation φ (S.residualRepresentation τ
          (S.residualRepresentation φ⁻¹ P)) =
        S.residualRepresentation τ (S.residualRepresentation τ P) := by
  let ρ : Representation (ZMod p) ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
      S.ResidualSpace := S.residualRepresentation
  obtain ⟨φ, hφ⟩ := ValuationTameCharacter.exists_conjugate_pow_wild Nat.prime_two A hA
  refine ⟨φ, fun τ hτ P => ?_⟩
  obtain ⟨_, hwild⟩ := hφ τ hτ
  let ω := φ * τ * φ⁻¹ * (τ ^ 2)⁻¹
  have hω := S.residual_fixed_of_dyadic_wild hp2 A hA ω hwild
    (ρ (τ ^ 2) P)
  change ρ ω (ρ (τ ^ 2) P) = ρ (τ ^ 2) P at hω
  change ρ φ (ρ τ (ρ φ⁻¹ P)) = ρ τ (ρ τ P)
  have he : ω * τ ^ 2 = φ * τ * φ⁻¹ := by simp [ω]
  have hmul := congrArg (fun g => ρ g P) he
  have hmul_apply (a b : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (x : S.ResidualSpace) :
      ρ (a * b) x =
        ρ a (ρ b x) :=
    congrArg (fun T : Module.End (ZMod p) S.ResidualSpace => T x)
      (ρ.map_mul a b)
  rw [hmul_apply, hω] at hmul
  rw [hmul_apply, hmul_apply] at hmul
  rw [← hmul, pow_two, hmul_apply]

/-- 031-003の終点。同じ全ガロア安定な真の非零部分加群とその商で、2上の慣性が同時に自明となる。 -/
theorem residual_fixed_and_cofixed_at_two (hp2 : p ≠ 2)
    (N : Submodule (ZMod p) S.ResidualSpace) (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥) (htop : N ≠ ⊤)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    FixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) ∧
      CofixedOn S.residualRepresentation N (inertiaSubgroupIn A ℚ) := by
  have := S.rationalCurve_isElliptic
  obtain ⟨φ, hφ⟩ := S.residual_exists_dyadic_conjugate_square hp2 A hA
  have hpoint : ∀ τ ∈ inertiaSubgroupIn A ℚ,
      (∀ x ∈ N, S.residualRepresentation τ x = x) ∧
        (∀ x, S.residualRepresentation τ x - x ∈ N) := by
    intro τ hτ
    apply ConjugateSquare.eq_id_on_line_of_conj_eq_sq S.residual_finrank_eq_two N hbot htop
      (S.residualRepresentation τ) (S.residualRepresentation φ) (S.residualRepresentation φ⁻¹)
    · exact (S.residualRepresentation.apply_bijective τ).injective
    · exact fun x => S.residualRepresentation.self_inv_apply φ x
    · exact hN τ
    · exact hN φ
    · exact hN φ⁻¹
    · exact hφ τ hτ
  exact ⟨fun τ hτ => (hpoint τ hτ).1, fun τ hτ => (hpoint τ hτ).2⟩

end DkMath.FLT.Frey.Source

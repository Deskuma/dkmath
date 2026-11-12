/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyDyadicNontrivial
import DkMath.Lib.NumberTheory.EllipticDyadicGeometry

#print "file: DkMath.FLT.FreyDyadicGeometry"

/-!
# NOTE-032-003A: 同じFrey Sourceの2上の中心と方向を供給する

整数モデルのc₄が奇数であることと、p≥5での正の判別式深さを既存算術から取る。
これを任意の2上の付値環Aへ写して、同じ曲線の臨界中心Cを構成する。
二次式の整根の一意性から中心は分解群固定、モニック二次式から方向Dは整となる。
方向は全慣性に個別に固定されるが、分解群全体での個別固定は結論しない。

032-002へC,Dと中心固定を内部で渡す。その結果、零成分外の実際のp捩れ点があれば、
その同じ点を動かす慣性元を得る。hno入口の入力は零成分の真性と枝交換まで減る。
零成分外の点の存在(003B)とa≡3 mod8からの枝交換(003C)は次の工程に残す。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
open WeierstrassCurve
variable {p : ℕ} (S : Source p)

/-- 正規化条件から、同じ整数モデルのc₄は任意の2上の付値環で単元となる。
指数の素数性やp≥5はこの係数の算術には不要である。 -/
theorem valuation_c4_eq_one_at_two
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    A.valuation (S.curve.c₄ : AlgebraicClosure ℚ) = 1 :=
  valuation_intCast_eq_one_of_not_dvd A Nat.prime_two ((ValuationSubring.mem_nonunits_iff _).mp hA)
    (FreyGapCubic.not_two_dvd_integral_c4 _ _ S.normalization)

/-- p≥5では、同じ整数モデルの判別式は2で割れる。
有理モデルの−8補正を保った付値公式から正性を取り、整数モデルの台帳へ戻す。 -/
theorem two_dvd_curve_discriminant (hp5 : 5 ≤ p) : (2 : ℤ) ∣ S.curve.Δ := by
  have hv : 0 < padicValRat 2 S.rationalCurve.Δ := by
    rw [S.minimal_discriminant_valuation_two.2]
    have hpZ : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    have hprod : (1 : ℤ) ≤ padicValInt 2 (S.a * S.b * S.c) := by
      exact_mod_cast S.one_le_product_two_valuation
    push_cast
    nlinarith
  by_contra hn
  rw [← S.curve_two_valuation_natCast_eq, padicValInt.eq_zero_of_not_dvd hn] at hv
  norm_num at hv

/-- 同じ有理曲線の臨界中心が、任意の2上の付値環で存在する。
整数モデルの係数を直接写し、奇素数用の中心固定定理は使用しない。 -/
theorem exists_criticalCentre_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    Nonempty (CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) := by
  let W := S.rationalCurve.baseChange (AlgebraicClosure ℚ)
  have hW : W = S.curve.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
    dsimp only [W]
    rw [← S.curve_map, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
    congr 1
  have hΔ : W.Δ = (S.curve.Δ : AlgebraicClosure ℚ) := by simp [hW, eq_intCast]
  have hc : W.c₄ = (S.curve.c₄ : AlgebraicClosure ℚ) := by simp [hW, eq_intCast]
  apply EllipticCriticalCentre.exists_criticalCentre A W
    (by rw [hW, map_a₁]; exact intCast_mem A _)
    (by rw [hW, map_a₂]; exact intCast_mem A _)
    (by rw [hW, map_a₃]; exact intCast_mem A _)
    (by rw [hW, map_a₄]; exact intCast_mem A _)
    (by rw [hW, map_a₆]; exact intCast_mem A _)
  · rw [hΔ]
    exact Int.cast_ne_zero.mpr S.curve_discriminant_ne_zero
  · rw [hΔ]
    exact valuation_intCast_lt_one_of_dvd A ((ValuationSubring.mem_nonunits_iff _).mp hA)
      (S.two_dvd_curve_discriminant hp5)
  · rw [hc]
    exact S.valuation_c4_eq_one_at_two A hA

/-- 同じ曲線の任意の2上の中心は、分解群全体に固定される。
中心を標準候補へ選び直す必要はなく、既存のCを保持したまま適用できる。 -/
theorem criticalCentre_decomposition_fixed_at_two
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ C.x = C.x ∧ σ C.y = C.y :=
  EllipticDyadicGeometry.decomposition_fixed S.rationalCurve A C
    ((ValuationSubring.mem_nonunits_iff _).mp hA) σ hσ

/-- 2上の中心の慣性固定。032-002が明示入力として要求していた条件を供給する。 -/
theorem criticalCentre_inertia_fixed_at_two
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    σ C.x = C.x ∧ σ C.y = C.y :=
  EllipticDyadicGeometry.inertia_fixed S.rationalCurve A C
    ((ValuationSubring.mem_nonunits_iff _).mp hA) σ hσ

/-- 同じ既存の中心と方向の二つの接線は、2上の全慣性元で個別に固定される。
分解群の残る剰余作用による枝交換とは区別する。 -/
theorem tangentDirections_inertia_fixed_at_two
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    {C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))}
    (D : TangentDirections C)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ inertiaSubgroupIn A ℚ) :
    σ D.α = D.α ∧ σ D.β = D.β :=
  EllipticDyadicGeometry.tangentDirections_inertia_fixed S.rationalCurve A D σ hσ
    (S.criticalCentre_inertia_fixed_at_two A hA C σ hσ).1

/-- 任意の2上の住所で、同じ中心・方向と中心および各方向の慣性固定を一緒に供給する。
存在をproviderに置かず、整数係数・判別式深さ・節点の単元性から構成する。 -/
theorem exists_dyadic_geometry (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      ∃ D : TangentDirections C,
        (∀ σ ∈ inertiaSubgroupIn A ℚ, σ C.x = C.x ∧ σ C.y = C.y) ∧
        (∀ σ ∈ inertiaSubgroupIn A ℚ, σ D.α = D.α ∧ σ D.β = D.β) := by
  obtain ⟨C⟩ := S.exists_criticalCentre_at_two hp5 A hA
  obtain ⟨D⟩ := EllipticDyadicGeometry.exists_tangentDirections A _ C
    (by rw [← S.valuationModel_map A, map_a₁]; exact (S.valuationModel A).a₁.property)
    (by rw [← S.valuationModel_map A, map_a₂]; exact (S.valuationModel A).a₂.property)
  exact ⟨C, D, S.criticalCentre_inertia_fixed_at_two A hA C,
    S.tangentDirections_inertia_fixed_at_two A hA D⟩

variable [Fact p.Prime]

/-- 零成分外の同じp捩れ点を動かす慣性元を、中心・方向・中心固定の追加入力なしで得る。
零成分外の点の存在はこの定理の前提に残す。 -/
theorem residual_exists_inertia_ne_of_not_smooth_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (P : S.ResidualSpace) (hP : ¬ HasSmoothReduction (S.valuationModel A) P.val) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, S.residualRepresentation τ P ≠ P := by
  obtain ⟨C, D, hfix, -⟩ := S.exists_dyadic_geometry hp5 A hA
  exact S.residual_exists_inertia_ne_of_not_smooth hp5 A hA C D (fun τ hτ => (hfix τ hτ).1) P hP

/-- 実際のE₀[p]が真部分空間なら、同じ表現の2上の慣性作用は非自明である。
E₁[p]の真性で代用せず、実際の滑らかな零成分の所属条件から外側の点を取る。 -/
theorem residual_exists_dyadic_inertia_ne_of_zeroComponent_ne_top (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hproper : S.residualZeroComponent A ≠ ⊤) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P := by
  obtain ⟨P, hP⟩ := (S.residualZeroComponent_ne_top_iff A).mp hproper
  obtain ⟨τ, hτ, hne⟩ := S.residual_exists_inertia_ne_of_not_smooth_at_two hp5 A hA P hP
  exact ⟨τ, hτ, P, hne⟩

/-- 中心・方向・中心固定・非自明慣性を内部で供給したhno入口。
零成分の真性と枝交換の二つが残る幾何入力である。 -/
theorem residual_no_cofixed_line_of_dyadic_branch_swap (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L := by
  obtain ⟨C, D, hfix, -⟩ := S.exists_dyadic_geometry hp5 A hA
  exact S.residual_no_cofixed_line_of_dyadic_geometry hp5 A hA C D hfix hout hswap

/-- 031-005の既約性へ同じSourceのまま接続する。
今回供給した中心幾何のほかに、b偶数、零成分外の点、枝交換を必要とする。 -/
theorem residual_isIrreducible_of_dyadic_branch_swap (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction hp5 hbe
    (S.residual_no_cofixed_line_of_dyadic_branch_swap hp5 A hA hout hswap)

end DkMath.FLT.Frey.Source

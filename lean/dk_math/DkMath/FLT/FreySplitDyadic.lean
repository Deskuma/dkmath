/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyModEightIrreducibility
import DkMath.Lib.NumberTheory.FreySplitModEight
import DkMath.Lib.NumberTheory.EllipticSplitDyadic

#print "file: DkMath.FLT.FreySplitDyadic"

/-!
# NOTE-032-005A: 7側の分解群作用と一般hnoの残る橋

a≡7 mod8なら同じ整数モデルのa₂は偶数で、剰余接錐はz²+zとなる。
中心・方向は既存の同じSourceから構成し、分解群全体が方向を個別に固定することを証明する。
全ての実際の残余点Pでρ(σ)P−P∈E₀[p]となり、分解群は商で+1として作用する。
従って3側で使った「分解群元による商上の−1作用」は7側では存在しない。

一方、一般の大域Cofixed直線Lがあれば、2上の非自明慣性とE₀[p]の一次元性から
同じ住所のL=E₀[p]が強制される。これにより一般hnoは、
E₀[p]から外へ出る実際のガロア変化量の存在へ言い換えられる。
7側でその元が存在すれば分解群の外にある。存在そのものは今回証明しない。
分解群でのCofixed性を大域Cofixed性へ延長したとも、一般hnoを閉じたとも主張しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed WeierstrassCurve IsLocalRing
variable {p : ℕ} (S : Source p)

/-- 7側でもaは奇数なので、整数モデルの分母条件からb偶数を得る。 -/
theorem b_even_of_a_mod_eight_seven (ha8 : S.a % 8 = 7) : Even S.b := by
  have hpow : (2 : ℤ) ∣ (S.a * S.b) ^ p := by
    rw [mul_pow]
    exact dvd_trans (by norm_num : (2 : ℤ) ∣ 16) S.normalization.sixteen
  rcases Int.prime_two.dvd_mul.mp (Int.prime_two.dvd_of_dvd_pow hpow) with ha | hb
  · obtain ⟨k, hk⟩ := ha
    omega
  · exact even_iff_two_dvd.mpr hb

variable [Fact p.Prime]

/-- 7側の同じ整数a₂は偶数である。正則性の仮定は使用しない。 -/
theorem curve_a2_even_of_a_mod_eight_seven (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7) : Even S.curve.a₂ :=
  FreySplitModEight.integral_a2_even ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega)
    ha8 (S.b_even_of_a_mod_eight_seven ha8)

/-- 同じ既存の中心に分裂接錐の係数を供給する。中心の剰余X座標はY偏微分から零となる。 -/
theorem dyadic_split_residue_profile (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) :
    ((S.valuationModel A).map (residue A)).a₁ = 1 ∧
      ((S.valuationModel A).map (residue A)).a₂ = 0 ∧ residue A (⟨C.x, C.x_mem⟩ : A) = 0 := by
  have : CharP (ResidueField A) 2 := charP_residueField A Nat.prime_two hA
  refine ⟨by simp [valuationModel, curve, FreyGapCubic.integral], ?_, ?_⟩
  · change residue A (S.curve.a₂ : A) = 0
    obtain ⟨k, hk⟩ := S.curve_a2_even_of_a_mod_eight_seven hp5 ha8
    have htwo : (2 : ResidueField A) = 0 := CharP.cast_eq_zero (ResidueField A) 2
    rw [hk]
    simp only [Int.cast_add, map_add]
    rw [← two_mul, htwo, zero_mul]
  · apply (ValuationResidue.coe_mem_nonunits_iff_residue_eq_zero A _).mp
    rw [ValuationSubring.mem_nonunits_iff]
    exact EllipticFrobeniusBranchSwap.centre_x_small_of_normalized C
      (by simp [WeierstrassCurve.baseChange, S.rationalCurve_a₁])
      (by simp [WeierstrassCurve.baseChange, S.rationalCurve_a₃])
      ((ValuationSubring.mem_nonunits_iff _).mp hA)

/-- 7側の同じ方向は全分解群で個別固定される。中心・方向の存在は003Aで供給済み。 -/
theorem dyadic_directions_decomposition_fixed_of_seven (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) (D : TangentDirections C)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    σ D.α = D.α ∧ σ D.β = D.β := by
  obtain ⟨ha₁, ha₂, hx₀⟩ := S.dyadic_split_residue_profile hp5 ha8 A hA C
  exact EllipticSplitDyadic.directions_decomposition_fixed S.rationalCurve A hA
    (S.valuationModel A) (S.valuationModel_map A) C D ha₁ ha₂ hx₀ hσ

/-- 7側の全残余点の分解群変化量は、同じE₀[p]へ入る。
零成分外だけに制限せず、全点で証明された一般幾何を適用する。 -/
theorem residual_decomposition_difference_smooth_of_seven (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : σ ∈ A.decompositionSubgroup ℚ)
    (P : S.ResidualSpace) :
    HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P - P).val := by
  classical
  obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
  obtain ⟨ha₁, ha₂, hx₀⟩ := S.dyadic_split_residue_profile hp5 ha8 A hA C
  exact EllipticSplitDyadic.decomposition_difference_smooth S.rationalCurve A hA
    (S.valuationModel A) (S.valuationModel_map A) C D ha₁ ha₂ hx₀ hσ P.val

/-- 7側では、慣性より大きい分解群全体で商E[p]/E₀[p]が固定される。
全ガロア群でのCofixed性とは区別する。 -/
theorem residualZeroComponent_cofixed_decomposition_of_seven (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    CofixedOn S.residualRepresentation (S.residualZeroComponent A) (A.decompositionSubgroup ℚ) := by
  intro σ hσ P
  exact (S.mem_residualZeroComponent_iff A _).mpr
    (S.residual_decomposition_difference_smooth_of_seven hp5 ha8 A hA hσ P)

/-- 7側には分解群内の商上の符号反転元が存在しない。
外側の点の存在と2≠0を使い、同じ点の和と差の両方がE₀[p]に入ることを禁じる。 -/
theorem residual_no_decomposition_branch_swap_of_seven (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ¬ ∃ σ ∈ A.decompositionSubgroup ℚ, ∀ P : S.ResidualSpace,
      ¬ HasSmoothReduction (S.valuationModel A) P.val →
        HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val := by
  rintro ⟨σ, hσ, hswap⟩
  obtain ⟨P, hP⟩ := S.residual_exists_not_smooth_at_two hp5 A hA
  have hminus := S.residualZeroComponent_cofixed_decomposition_of_seven hp5 ha8 A hA σ hσ P
  have hplus := (S.mem_residualZeroComponent_iff A _).mpr (hswap P hP)
  have htwice := (S.residualZeroComponent A).sub_mem hplus hminus
  have he : (S.residualRepresentation σ P + P) - (S.residualRepresentation σ P - P) =
      (2 : ZMod p) • P := by rw [two_smul]; abel
  rw [he] at htwice
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hh : ((2 : ℕ) : ZMod p) ≠ 0 := fun h => (by omega : p ≠ 2)
      ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
    exact_mod_cast hh
  exact hP ((S.mem_residualZeroComponent_iff A P).mp
    (((S.residualZeroComponent A).smul_mem_iff h2).mp htwice))

/-- 大域Cofixed直線があれば、それは任意の2上の住所で同じE₀[p]に一致する。
非自明慣性からの包含と、両方の次元1を使う。合同条件は不要である。 -/
theorem residual_cofixed_line_eq_zeroComponent_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (L : Submodule (ZMod p) S.ResidualSpace) (hline : Module.finrank (ZMod p) L = 1)
    (hcofixed : IsCofixedOn S.residualRepresentation L) : L = S.residualZeroComponent A := by
  have := S.rationalCurve_isElliptic
  have hle := CofixedBranchSwap.line_le_of_cofixed_and_nontrivial S.residualRepresentation
    (inertiaSubgroupIn A ℚ) hline hcofixed (S.residualZeroComponent_absorbs_at_two hp5 A hA)
    (S.residual_exists_dyadic_inertia_ne hp5 A hA)
  exact Submodule.eq_of_le_of_finrank_le hle (by
    rw [S.residualZeroComponent_finrank_eq_one_at_two hp5 A hA, hline])

/-- 任意のCofixed直線を探す問題を、同じ2上のE₀[p]の大域Cofixed性へ絞る。
右辺の大域性を左辺の局所幾何だけから供給したとはしない。 -/
theorem residual_exists_cofixed_line_iff_zeroComponent_cofixed (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) ↔
      IsCofixedOn S.residualRepresentation (S.residualZeroComponent A) := by
  constructor
  · rintro ⟨L, hline, -, hcofixed⟩
    simpa only [S.residual_cofixed_line_eq_zeroComponent_at_two hp5 A hA L hline hcofixed] using hcofixed
  · intro hcofixed
    exact ⟨S.residualZeroComponent A, S.residualZeroComponent_finrank_eq_one_at_two hp5 A hA,
      hcofixed.isStable, hcofixed⟩

/-- 一般hnoの残る橋は、同じE₀[p]を外れる実際のガロア変化量の存在である。
この同値は存在証明ではなく、未解決の算術入力を同じSource上で固定する。 -/
theorem residual_hno_iff_exists_zeroComponent_escape (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) ↔
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), ∃ P : S.ResidualSpace,
        S.residualRepresentation σ P - P ∉ S.residualZeroComponent A := by
  classical
  rw [S.residual_exists_cofixed_line_iff_zeroComponent_cofixed hp5 A hA]
  simp only [IsCofixedOn, not_forall]
  rfl

/-- 7側で上の脱出元が存在するなら、必ず2上の分解群の外にある。
その元の存在は入力に残し、局所Cofixed性を大域へ延長しない。 -/
theorem residual_zeroComponent_escape_not_decomposition_of_seven (hp5 : 5 ≤ p)
    (ha8 : S.a % 8 = 7) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} {P : S.ResidualSpace}
    (hescape : S.residualRepresentation σ P - P ∉ S.residualZeroComponent A) :
    σ ∉ A.decompositionSubgroup ℚ := by
  intro hσ
  exact hescape (S.residualZeroComponent_cofixed_decomposition_of_seven hp5 ha8 A hA σ hσ P)

end DkMath.FLT.Frey.Source

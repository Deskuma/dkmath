/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from S_FreyPackage_frey_exists_decomposition_branch_swap_of_a_mod_eight.lean,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Modified: same DkMath Source, actual residual representation and zero component;
reuse centre/odd-torsion depth APIs and separate mod-eight arithmetic from local geometry.
-/

import DkMath.FLT.FreyDyadicZeroComponent
import DkMath.Lib.NumberTheory.FreyModEight
import DkMath.Lib.NumberTheory.EllipticFrobeniusBranchSwap

#print "file: DkMath.FLT.FreyDyadicBranchSwap"

/-!
# NOTE-032-003C: a≡3 mod8から同じFrey Sourceの枝交換を供給する

a≡3 mod8と整数モデルの分母条件からbが偶数となる。
奇数指数p≥5では整数a₂が奇数になり、2上の剰余接錐はz²+z+1となる。
中心の剰余X座標はY偏微分から零となる。実際のFrobenius元を既存の存在定理で取り、
同じ中心・方向についての交換と、同じ残余点についてのσP+P∈E₀[p]を供給する。

外側のp捩れ点の浅さは、既存の実際の倍点軌道の定理から供給する。
一般FLTやMazur理論を使ったSourceの空虚な排除を証明経路にしない。
a≡7 mod8にはこの剰余接錐の計算を適用しない。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport ValuationFrobenius
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
open WeierstrassCurve IsLocalRing
variable {p : ℕ} (S : Source p)

/-- a≡3 mod8ならaは奇数で、分母16の条件からbは偶数となる。
この向き付けの帰結に、素数性や冪和の方程式は使用しない。 -/
theorem b_even_of_a_mod_eight (ha8 : S.a % 8 = 3) : Even S.b := by
  have hpow : (2 : ℤ) ∣ (S.a * S.b) ^ p := by
    rw [mul_pow]
    exact dvd_trans (by norm_num : (2 : ℤ) ∣ 16) S.normalization.sixteen
  rcases Int.prime_two.dvd_mul.mp (Int.prime_two.dvd_of_dvd_pow hpow) with ha | hb
  · obtain ⟨k, hk⟩ := ha
    omega
  · exact even_iff_two_dvd.mpr hb

variable [Fact p.Prime]

/-- a≡3 mod8での整数モデルのa₂の奇数性。正則素数の仮定は不要。 -/
theorem curve_a2_odd_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3) : Odd S.curve.a₂ :=
  FreyModEight.integral_a2_odd ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega)
    ha8 (S.b_even_of_a_mod_eight ha8)

/-- 同じ2上の接錐がz²+z+1となる係数を、任意の既存の中心に供給する。
中心の剰余X座標の零性は、a₁=1,a₃=0と中心のY偏微分から直接証明する。 -/
theorem dyadic_tangent_residue_profile_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ))) :
    ((S.valuationModel A).map (residue A)).a₁ = 1 ∧
      ((S.valuationModel A).map (residue A)).a₂ = 1 ∧ residue A (⟨C.x, C.x_mem⟩ : A) = 0 := by
  have : CharP (ResidueField A) 2 := charP_residueField A Nat.prime_two hA
  refine ⟨by simp [valuationModel, curve, FreyGapCubic.integral], ?_, ?_⟩
  · change residue A (S.curve.a₂ : A) = 1
    obtain ⟨k, hk⟩ := S.curve_a2_odd_of_a_mod_eight hp5 ha8
    rw [hk]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
      map_add, map_mul, map_ofNat, map_one]
    have htwo : (2 : ResidueField A) = 0 := CharP.cast_eq_zero (ResidueField A) 2
    rw [htwo, zero_mul, zero_add]
  · apply (ValuationResidue.coe_mem_nonunits_iff_residue_eq_zero A (⟨C.x, C.x_mem⟩ : A)).mp
    rw [ValuationSubring.mem_nonunits_iff]
    exact EllipticFrobeniusBranchSwap.centre_x_small_of_normalized C
      (by simp [WeierstrassCurve.baseChange, S.rationalCurve_a₁])
      (by simp [WeierstrassCurve.baseChange, S.rationalCurve_a₃])
      ((ValuationSubring.mem_nonunits_iff _).mp hA)

/-- 任意の2上の住所で、同じ中心の二方向を交換する実際のFrobenius元が存在する。
剰余上の交換を体内の方向の等号まで持ち上げ、中心・方向・自己同型を一緒に保持する。 -/
theorem exists_dyadic_direction_swap_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)),
      ∃ D : TangentDirections C, ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        IsFrobeniusAt A σ 2 ∧ σ D.α = D.β ∧ σ D.β = D.α := by
  obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  obtain ⟨ha₁, ha₂, hx₀⟩ := S.dyadic_tangent_residue_profile_of_a_mod_eight hp5 ha8 A hA C
  exact ⟨C, D, σ, hσ, EllipticFrobeniusBranchSwap.directions_swap_of_frobenius
    S.rationalCurve A hA (S.valuationModel A) (S.valuationModel_map A) C D ha₁ ha₂ hx₀ hσ⟩

/-- 同じ残余点に対し、任意の2乗Frobenius元は零成分の商で符号を反転する。
外側の点の浅さ・中心固定・深さ保存・異なる枝の和を全て内部で供給する。 -/
theorem residual_frobenius_branch_swap_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    {σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hσ : IsFrobeniusAt A σ 2)
    (P : S.ResidualSpace) (hout : ¬ HasSmoothReduction (S.valuationModel A) P.val) :
    HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val := by
  classical
  obtain ⟨C, D, -, -⟩ := S.exists_dyadic_geometry hp5 A hA
  obtain ⟨ha₁, ha₂, hx₀⟩ := S.dyadic_tangent_residue_profile_of_a_mod_eight hp5 ha8 A hA C
  obtain ⟨pt, hkill⟩ := P
  cases pt with
  | zero => exact (hout (hasSmoothReduction_zero _ _)).elim
  | some x y h =>
    have ht : p • Affine.Point.some x y h = 0 := hkill
    have hX := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
      (S.valuationModel A) _ (S.valuationModel_map A) C h).mp hout
    have hsh := (EllipticTorsionDepth.odd_torsion_depth_of_model (S.valuationModel A) _
      (S.valuationModel_map A) C D ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega)
      (residual_order_unit_at_two (by omega) A hA) h ht hX).1
    exact EllipticFrobeniusBranchSwap.add_smooth_of_frobenius S.rationalCurve A hA
      (S.valuationModel A) (S.valuationModel_map A) C D ha₁ ha₂ hx₀ hσ h hX hsh

/-- a≡3 mod8から、同じE₀[p]の外側でσP+PがE₀[p]へ入る分解群元を構成する。
これが032-003Cの点群上の枝交換であり、方向の交換だけで止めない。 -/
theorem residual_exists_decomposition_branch_swap_of_a_mod_eight (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ∃ σ ∈ A.decompositionSubgroup ℚ,
      ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
        HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val := by
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  exact ⟨σ, hσ.mem_decompositionSubgroup,
    S.residual_frobenius_branch_swap_of_a_mod_eight hp5 ha8 A hA hσ⟩

/-- 同じ2上の住所での3側の直接hno。残っていた枝交換を実際に供給する。 -/
theorem residual_no_cofixed_line_of_a_mod_eight_at_two (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L := by
  obtain ⟨σ, -, hswap⟩ := S.residual_exists_decomposition_branch_swap_of_a_mod_eight hp5 ha8 A hA
  exact S.residual_no_cofixed_line_of_branch_swap_at_two hp5 A hA ⟨σ, hswap⟩

/-- a≡3 mod8ではb偶数も内部で供給し、同じSourceの既約性へ接続する。 -/
theorem residual_isIrreducible_of_a_mod_eight_at_two (hp5 : 5 ≤ p) (ha8 : S.a % 8 = 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) : S.ResidualIsIrreducible :=
  S.residual_isIrreducible_of_oriented_cofixed_obstruction hp5 (S.b_even_of_a_mod_eight ha8)
    (S.residual_no_cofixed_line_of_a_mod_eight_at_two hp5 ha8 A hA)

end DkMath.FLT.Frey.Source

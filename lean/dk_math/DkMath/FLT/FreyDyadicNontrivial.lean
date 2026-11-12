/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCofixedBranchSwap
import DkMath.Lib.NumberTheory.KummerInertia

#print "file: DkMath.FLT.FreyDyadicNontrivial"

/-!
# NOTE-032-002B: 判別式の深さ障害から同じE[p]の非自明慣性へ

整数モデルの判別式と有理モデルの判別式の付値を同一視する橋を明示し、
p∤v₂(Δ)をKummerInertiaへ接続する。零成分外のp捩れ点Pについては、
031-002の実際の倍点軌道の定理から
v(x(P)−x₀)ᵖ=v(Δ)ʲ、1≤j、2j<pを供給する。
この点を全慣性が固定すると、慣性固定の中心との差も固定され、深さ障害に反する。

中心C、方向D、中心の慣性固定、および零成分外の点の存在は明示入力である。
今回、非自明慣性を独立のproviderから除去するが、この幾何入力の存在を証明したとはしない。
同じSource・整数モデル・E[p]を保ち、a≡3 mod8から枝交換元を供給する工程も残す。
-/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open EllipticCriticalCentre EllipticCriticalCentreAlgebra EllipticTangentDirections
open EllipticGoodReductionSeparation
open WeierstrassCurve Affine Affine.Point
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
variable {p : ℕ} [Fact p.Prime] (S : Source p)

omit [Fact p.Prime] in
/-- 同じ整数モデルの自然数値v₂(Δ)と、有理モデルの整数値v₂(Δ)は一致する。
非零判別式はSourceから保持し、別の最小モデルへの交換は行わない。 -/
theorem curve_two_valuation_natCast_eq :
    (padicValInt 2 S.curve.Δ : ℤ) = padicValRat 2 S.rationalCurve.Δ := by
  have hΔ := congrArg WeierstrassCurve.Δ S.curve_map
  rw [WeierstrassCurve.map_Δ] at hΔ
  change (S.curve.Δ : ℚ) = S.rationalCurve.Δ at hΔ
  rw [← hΔ, padicValRat.of_int]

/-- Kummer深さの台帳に使う、自然数値v₂(Δ)のp非可除性。 -/
theorem not_exponent_dvd_curve_two_valuation (hp5 : 5 ≤ p) :
    ¬ p ∣ padicValInt 2 S.curve.Δ := by
  intro hd
  apply S.not_exponent_dvd_two_valuation hp5
  rw [← S.curve_two_valuation_natCast_eq]
  exact_mod_cast hd

/-- 捩れ軌道の深さを持つ任意の元tは、2上の慣性によって動かされる。
jの範囲と素数性からp∤v₂(Δ)jを得て、正則性に依存しないKummer核を適用する。 -/
theorem exists_inertia_ne_of_two_depth (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    {t : AlgebraicClosure ℚ} {j : ℕ} (hj : 1 ≤ j) (hjp : j < p)
    (hdepth : A.valuation t ^ p = A.valuation (S.curve.Δ : AlgebraicClosure ℚ) ^ j) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, τ t ≠ t := by
  have hpm : ¬ p ∣ padicValInt 2 S.curve.Δ * j := by
    intro hd
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp hd with hd | hd
    · exact S.not_exponent_dvd_curve_two_valuation hp5 hd
    · exact (not_le.mpr hjp) (Nat.le_of_dvd (by omega) hd)
  rw [valuation_intCast_eq_pow_padicValInt A Nat.prime_two
    ((ValuationSubring.mem_nonunits_iff _).mp hA) S.curve_discriminant_ne_zero,
    ← pow_mul] at hdepth
  exact KummerInertia.exists_inertia_ne_of_valuation_pow_eq A hA Nat.prime_two Fact.out
    (by omega) hpm hdepth

/-- 同じ実際のp捩れ点が零成分外なら、その点を動かす2上の慣性元が存在する。
中心と方向を固定し、深さの冪等式を実際の倍点軌道から供給する。
中心の慣性固定はX座標だけで十分であり、点のY座標の固定は要求しない。 -/
theorem residual_exists_inertia_ne_of_not_smooth (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x)
    (P : S.ResidualSpace) (hP : ¬ HasSmoothReduction (S.valuationModel A) P.val) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, S.residualRepresentation τ P ≠ P := by
  classical
  obtain ⟨pt, hkill⟩ := P
  cases pt with
  | zero => exact (hP (hasSmoothReduction_zero _ _)).elim
  | some x y hxy =>
    have ht : p • Point.some x y hxy = 0 := hkill
    have hX := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model
      (S.valuationModel A) _ (S.valuationModel_map A) C hxy).mp hP
    obtain ⟨-, j, hj, hjp, hdepth⟩ := EllipticTorsionDepth.odd_torsion_depth_of_model
      (S.valuationModel A) _ (S.valuationModel_map A) C D
      ((Fact.out : p.Prime).odd_of_ne_two (by omega)) (by omega)
      (residual_order_unit_at_two (by omega) A hA) hxy ht hX
    have hΔ : (S.rationalCurve.baseChange (AlgebraicClosure ℚ)).Δ =
        (S.curve.Δ : AlgebraicClosure ℚ) := by
      rw [← S.curve_map, WeierstrassCurve.baseChange, WeierstrassCurve.map_map, WeierstrassCurve.map_Δ]
      rfl
    rw [C.defect_valuation, hΔ] at hdepth
    obtain ⟨τ, hτ, hne⟩ := S.exists_inertia_ne_of_two_depth hp5 A hA hj (by omega) hdepth
    refine ⟨τ, hτ, fun heq => hne ?_⟩
    have hx : τ x = x := congrArg (fun Q : S.ResidualSpace =>
      match Q.val with
      | .zero => 0
      | .some x _ _ => x) heq
    rw [map_sub, hx, hfix τ hτ]

/-- 零成分の真性から非自明慣性を供給する。同じ点Pが実際に動くことを上の定理で示す。 -/
theorem residual_exists_dyadic_inertia_ne_of_geometry (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, ∃ P, S.residualRepresentation τ P ≠ P := by
  obtain ⟨P, hP⟩ := hout
  obtain ⟨τ, hτ, hne⟩ := S.residual_exists_inertia_ne_of_not_smooth hp5 A hA C D hfix P hP
  exact ⟨τ, hτ, P, hne⟩

/-- 032-001から非自明慣性providerを取り除いたhno接続。
中心・方向・中心固定、零成分外の点、枝交換の算術的供給は次の幾何工程に残る。 -/
theorem residual_no_cofixed_line_of_dyadic_geometry (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2)
    (C : CriticalCentre A (S.rationalCurve.baseChange (AlgebraicClosure ℚ)))
    (D : TangentDirections C)
    (hfix : ∀ τ ∈ inertiaSubgroupIn A ℚ, τ C.x = C.x ∧ τ C.y = C.y)
    (hout : ∃ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val)
    (hswap : ∃ σ, ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
      HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val) :
    ¬ ∃ L : Submodule (ZMod p) S.ResidualSpace, Module.finrank (ZMod p) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L :=
  S.residual_no_cofixed_line_of_zeroComponent_branch_swap (by omega) A C D hfix hout
    (S.residual_exists_dyadic_inertia_ne_of_geometry hp5 A hA C D (fun τ hτ => (hfix τ hτ).1) hout)
    hswap

end DkMath.FLT.Frey.Source

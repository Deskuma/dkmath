import DkMath.Lib.NumberTheory.EllipticFrobeniusBranchSwap
import DkMath.Lib.NumberTheory.FreyModEight
import DkMath.Lib.NumberTheory.EllipticNodalTorsionBound
import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber
import DkMath.Lib.NumberTheory.EllipticTorsionDepth

#print "file: Note032FrobeniusBranchSwapBoundary"

/-!
NOTE-032-003Cの境界と実例。mod4の向き付けだけでは接錐の非分裂性は得られない。
Frey Sourceを仮定しない曲線でも、実際のFrobeniusが方向を交換し、
零成分外の実際の3捩れ点とその像の和が零成分へ入ることを確認する。
-/
namespace EllipticFrobeniusBranchSwapTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport ValuationFrobenius
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open EllipticTorsionRepresentation WeierstrassCurve IsLocalRing
local notation "ℚ̄" => AlgebraicClosure ℚ
noncomputable local instance : DecidableEq ℚ̄ := Classical.decEq _

/-- 指数37・負整数aでも、一般の剰余算術と整数除算の定理を使用できる。 -/
theorem exponent37_negative_input :
    ((2 : ℤ) ^ 37 - (-5) ^ 37 - 1) % 8 = 4 ∧
      Odd (FreyGapCubic.integral ((-5) ^ 37) ((2 : ℤ) ^ 37)).a₂ :=
  ⟨FreyModEight.power_difference_mod_eight (by decide) (by decide) (by norm_num) (by decide),
    FreyModEight.integral_a2_odd (by decide) (by decide) (by norm_num) (by decide)⟩

/-- a≡7 mod8もa≡3 mod4だが、a₂は偶数となり、3側の係数条件を満たさない。 -/
theorem seven_side_boundary :
    (7 : ℤ) % 4 = 3 ∧ ((2 : ℤ) ^ 3 - 7 ^ 3 - 1) % 8 = 0 ∧
      Even (FreyGapCubic.integral ((7 : ℤ) ^ 3) ((2 : ℤ) ^ 3)).a₂ := by
  norm_num [FreyGapCubic.integral, even_iff_two_dvd]

/-- 奇数でも指数1では偶数の冪がmod8で消えない。指数下界を省けない。 -/
theorem exponent_one_boundary : ((2 : ℤ) ^ 1 - 3 ^ 1 - 1) % 8 = 6 := by norm_num

/-- 定数項が零の分裂二次式では、根0は2乗作用に固定される。
z²+z=1の条件を落として非固定性を主張できない。 -/
theorem split_quadratic_boundary {k : Type*} [Field k] [CharP k 2] :
    (0 : k) ^ 2 + 0 = 0 ∧ (0 : k) ^ 2 = 0 := by simp

/-- Frey Sourceとは独立の実際の整数曲線。 -/
def nodalCurve : WeierstrassCurve ℤ := ⟨1, 1, 0, 2, 0⟩

/-- 判別式の2可除性とc₄の単元性を具体的な整数等式で検証する。 -/
theorem nodalCurve_invariants : nodalCurve.Δ = -412 ∧ nodalCurve.c₄ = -71 := by
  norm_num [nodalCurve, WeierstrassCurve.Δ, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 同じ具体曲線で、中心・方向・Frobenius・零成分外の点を全て構成する。
|E[3]|=9と|E₀[3]|≤3を比較して点を得て、奇数捩れの浅さから和の滑らかな還元を導く。
単に「方向が交換されるなら」と仮定した確認ではない。 -/
theorem nodalCurve_frobenius_three (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    let W := nodalCurve.map (Int.castRingHom A)
    let E := nodalCurve.map (Int.castRingHom ℚ)
    ∃ C : CriticalCentre A (E.baseChange ℚ̄), ∃ D : TangentDirections C,
      ∃ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, IsFrobeniusAt A σ 2 ∧ σ D.α = D.β ∧ σ D.β = D.α ∧
        ∃ P : Torsion E 3, ¬ HasSmoothReduction W P.val ∧
          HasSmoothReduction W (pointAction E σ P.val + P.val) := by
  classical
  let W := nodalCurve.map (Int.castRingHom A)
  let E := nodalCurve.map (Int.castRingHom ℚ)
  let V := E.baseChange ℚ̄
  have hm : W.map A.subtype = V := by
    ext <;> simp [W, V, E, WeierstrassCurve.baseChange, nodalCurve, map_ofNat]
  have hΔ : V.Δ = (-412 : ℚ̄) := by
    simp [V, E, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, nodalCurve_invariants.1]
  have hc : V.c₄ = (-71 : ℚ̄) := by
    simp [V, E, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, nodalCurve_invariants.2]
  have : E.IsElliptic := ⟨by
    rw [isUnit_iff_ne_zero]
    simp [E, WeierstrassCurve.map_Δ, nodalCurve_invariants.1]⟩
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hΔsmall : A.valuation V.Δ < 1 := by
    rw [hΔ]
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := -412) (by norm_num)
  have hcunit : A.valuation V.c₄ = 1 := by
    rw [hc]
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2 (z := -71) (by norm_num)
  obtain ⟨C⟩ := EllipticCriticalCentre.exists_criticalCentre A V
    (by rw [← hm, WeierstrassCurve.map_a₁]; exact W.a₁.property)
    (by rw [← hm, WeierstrassCurve.map_a₂]; exact W.a₂.property)
    (by rw [← hm, WeierstrassCurve.map_a₃]; exact W.a₃.property)
    (by rw [← hm, WeierstrassCurve.map_a₄]; exact W.a₄.property)
    (by rw [← hm, WeierstrassCurve.map_a₆]; exact W.a₆.property)
    (by rw [hΔ]; norm_num) hΔsmall hcunit
  obtain ⟨D⟩ := EllipticDyadicGeometry.exists_tangentDirections A V C
    (by rw [← hm, WeierstrassCurve.map_a₁]; exact W.a₁.property)
    (by rw [← hm, WeierstrassCurve.map_a₂]; exact W.a₂.property)
  have h3 : A.valuation (3 : ℚ̄) = 1 := by
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2 (z := 3) (by norm_num)
  have hout : ∃ P : Torsion E 3, ¬ HasSmoothReduction W P.val := by
    by_contra! hall
    have hbound : Nat.card (Torsion E 3) ≤ 3 :=
      EllipticNodalTorsionBound.card_le_of_injective_smooth_torsion W V hm C D (by decide) h3
        (fun P : Torsion E 3 => P.val) Subtype.val_injective hall (fun P => P.property)
    rw [card_torsion_prime_sq E 3] at hbound
    norm_num at hbound
  have hx₀ : residue A (⟨C.x, C.x_mem⟩ : A) = 0 := by
    apply (ValuationResidue.coe_mem_nonunits_iff_residue_eq_zero A _).mp
    rw [ValuationSubring.mem_nonunits_iff]
    exact EllipticFrobeniusBranchSwap.centre_x_small_of_normalized C
      (by simp [V, E, WeierstrassCurve.baseChange, nodalCurve])
      (by simp [V, E, WeierstrassCurve.baseChange, nodalCurve]) h2
  have ha₁ : (W.map (residue A)).a₁ = 1 := by simp [W, nodalCurve]
  have ha₂ : (W.map (residue A)).a₂ = 1 := by simp [W, nodalCurve]
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  obtain ⟨hα, hβ⟩ := EllipticFrobeniusBranchSwap.directions_swap_of_frobenius E A hA W hm C D
    ha₁ ha₂ hx₀ hσ
  refine ⟨C, D, σ, hσ, hα, hβ, ?_⟩
  obtain ⟨P, hP⟩ := hout
  refine ⟨P, hP, ?_⟩
  obtain ⟨pt, hkill⟩ := P
  cases pt with
  | zero => exact (hP (hasSmoothReduction_zero W _)).elim
  | some x y h =>
    have hX := (EllipticNodalReduction.not_hasSmoothReduction_some_iff_of_model W V hm C h).mp hP
    have hsh := (EllipticTorsionDepth.odd_torsion_depth_of_model W V hm C D
      (by decide : Odd 3) (by decide) h3 h hkill hX).1
    exact EllipticFrobeniusBranchSwap.add_smooth_of_frobenius E A hA W hm C D ha₁ ha₂ hx₀ hσ h hX hsh

end EllipticFrobeniusBranchSwapTest

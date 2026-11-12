import DkMath.Lib.NumberTheory.FreySplitModEight
import DkMath.Lib.NumberTheory.EllipticSplitDyadic
import DkMath.Lib.NumberTheory.EllipticNodalTorsionBound
import DkMath.Lib.NumberTheory.EllipticTorsionRegularFiber

#print "file: Note032SplitDyadicBoundary"

/-!
032-005Aの実例。分裂接錐の方向保存・差の滑らかな還元と、和の失敗を
Frey Sourceの存在を仮定しない実際の曲線と3捩れ点で確認する。
-/
namespace EllipticSplitDyadicTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport ValuationFrobenius
open EllipticCriticalCentre EllipticTangentDirections EllipticGoodReductionSeparation
open EllipticTorsionRepresentation WeierstrassCurve IsLocalRing
local notation "ℚ̄" => AlgebraicClosure ℚ
noncomputable local instance : DecidableEq ℚ̄ := Classical.decEq _

/-- 指数37、a=−1≡7 mod8でも分子は0 mod8で整数a₂は偶数となる。 -/
theorem exponent37_split_arithmetic :
    ((2 : ℤ) ^ 37 - (-1) ^ 37 - 1) % 8 = 0 ∧
      Even (FreyGapCubic.integral ((-1) ^ 37) ((2 : ℤ) ^ 37)).a₂ :=
  ⟨FreySplitModEight.power_difference_mod_eight (by decide) (by decide) (by norm_num) (by decide),
    FreySplitModEight.integral_a2_even (by decide) (by decide) (by norm_num) (by decide)⟩

/-- 標数0ではもう一つの根は−1であり、0,1への分類は成立しない。標数2が必要。 -/
theorem characteristic_boundary : (-1 : ℚ) ^ 2 + (-1) = 0 ∧ (-1 : ℚ) ≠ 0 ∧ (-1 : ℚ) ≠ 1 := by
  norm_num

/-- a₂=0で2上の接錐が分裂する整数曲線。 -/
def splitCurve : WeierstrassCurve ℤ := ⟨1, 0, 0, 2, 0⟩

/-- 判別式は2で割れ、c₄は奇数である。 -/
theorem splitCurve_invariants : splitCurve.Δ = -508 ∧ splitCurve.c₄ = -95 := by
  norm_num [splitCurve, WeierstrassCurve.Δ, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- 実際のFrobeniusが二方向を個別固定する具体例。
外側の3捩れ点Pを位数比較で構成し、σP−Pは零成分、σP+Pは零成分外と証明する。
和と差を取り違えると偽になることを、同じ曲線・住所・自己同型・実点で確認する。 -/
theorem splitCurve_frobenius_boundary (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    let W := splitCurve.map (Int.castRingHom A)
    let E := splitCurve.map (Int.castRingHom ℚ)
    ∃ C : CriticalCentre A (E.baseChange ℚ̄), ∃ D : TangentDirections C,
      ∃ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, IsFrobeniusAt A σ 2 ∧ σ D.α = D.α ∧ σ D.β = D.β ∧
        ∃ P : Torsion E 3, ¬ HasSmoothReduction W P.val ∧
          HasSmoothReduction W (pointAction E σ P.val - P.val) ∧
          ¬ HasSmoothReduction W (pointAction E σ P.val + P.val) := by
  classical
  let W := splitCurve.map (Int.castRingHom A)
  let E := splitCurve.map (Int.castRingHom ℚ)
  let V := E.baseChange ℚ̄
  have hm : W.map A.subtype = V := by
    ext <;> simp [W, V, E, WeierstrassCurve.baseChange, splitCurve, map_ofNat]
  have hΔ : V.Δ = (-508 : ℚ̄) := by
    simp [V, E, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, splitCurve_invariants.1]
  have hc : V.c₄ = (-95 : ℚ̄) := by
    simp [V, E, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, splitCurve_invariants.2]
  have : E.IsElliptic := ⟨by
    rw [isUnit_iff_ne_zero]
    simp [E, WeierstrassCurve.map_Δ, splitCurve_invariants.1]⟩
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hΔsmall : A.valuation V.Δ < 1 := by
    rw [hΔ]
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := -508) (by norm_num)
  have hcunit : A.valuation V.c₄ = 1 := by
    rw [hc]
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2 (z := -95) (by norm_num)
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
      (by simp [V, E, WeierstrassCurve.baseChange, splitCurve])
      (by simp [V, E, WeierstrassCurve.baseChange, splitCurve]) h2
  have ha₁ : (W.map (residue A)).a₁ = 1 := by simp [W, splitCurve]
  have ha₂ : (W.map (residue A)).a₂ = 0 := by simp [W, splitCurve]
  obtain ⟨σ, hσ⟩ := exists_isFrobeniusAt_of_liesOverPrime Nat.prime_two A hA
  obtain ⟨hα, hβ⟩ := EllipticSplitDyadic.directions_decomposition_fixed E A hA W hm C D
    ha₁ ha₂ hx₀ hσ.mem_decompositionSubgroup
  refine ⟨C, D, σ, hσ, hα, hβ, ?_⟩
  obtain ⟨P, hP⟩ := hout
  have hminus : HasSmoothReduction W (pointAction E σ P.val - P.val) :=
    EllipticSplitDyadic.decomposition_difference_smooth E A hA W hm C D
      ha₁ ha₂ hx₀ hσ.mem_decompositionSubgroup P.val
  refine ⟨P, hP, hminus, ?_⟩
  intro hplus
  change HasSmoothReduction W (pointAction E σ P.val + P.val) at hplus
  have htwice := EllipticNodalInertia.smooth_sub_of_model W V hm hplus hminus
  change HasSmoothReduction W ((pointAction E σ P.val + P.val) -
    (pointAction E σ P.val - P.val)) at htwice
  have he : (pointAction E σ P.val + P.val) - (pointAction E σ P.val - P.val) = P.val + P.val := by abel
  have hkill : (2 + 1) • P.val = 0 := P.property
  rw [add_nsmul, two_nsmul, one_nsmul] at hkill
  have hneg : P.val + P.val = -P.val := eq_neg_of_add_eq_zero_left hkill
  rw [he, hneg] at htwice
  have hp := EllipticNodalInertia.smooth_sub_of_model W V hm (hasSmoothReduction_zero W V) htwice
  change HasSmoothReduction W ((0 : Points E) - -P.val) at hp
  exact hP (by simpa only [zero_sub, neg_neg] using hp)

end EllipticSplitDyadicTest

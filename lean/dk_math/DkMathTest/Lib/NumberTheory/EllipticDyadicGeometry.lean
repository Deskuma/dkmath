import DkMath.Lib.NumberTheory.EllipticDyadicGeometry

#print "file: DkMathTest.Lib.NumberTheory.EllipticDyadicGeometry"

/-!
NOTE-032-003Aの境界と具体例。整根の一意性は係数の二条件を両方必要とする。
Sourceを仮定しない具体的曲線y²+xy=x³+x²+2xにも中心・方向の存在定理を適用する。
-/
namespace EllipticDyadicGeometryTest
open DkMath.Lib.NumberTheory ValuationInertia ValuationPrimeSupport
open DkMath.Lib.Algebra.ValuationQuadraticRoot
open EllipticCriticalCentre EllipticTangentDirections
open WeierstrassCurve
local notation "ℚ̄" => AlgebraicClosure ℚ

/-- 一次係数が単元でも、最高次係数の小ささを落とすと0,1の二つの整根がある。 -/
theorem leading_coefficient_boundary {K : Type*} [Field K] (A : ValuationSubring K) :
    (0 : K) ∈ A ∧ (1 : K) ∈ A ∧ (0 : K) ≠ 1 ∧
      (0 : K) ^ 2 - 0 = 0 ∧ (1 : K) ^ 2 - 1 = 0 ∧ A.valuation (-1 : K) = 1 := by
  exact ⟨zero_mem A, one_mem A, zero_ne_one, by ring, by ring, by simp⟩

/-- 最高次係数が非単元でも、一次係数の単元性を落とすと二つの整根が残る。 -/
theorem linear_coefficient_boundary (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    A.valuation (2 : ℚ̄) < 1 ∧ A.valuation (-2 : ℚ̄) < 1 ∧
      (2 : ℚ̄) * 0 ^ 2 - 2 * 0 = 0 ∧ (2 : ℚ̄) * 1 ^ 2 - 2 * 1 = 0 ∧
      (0 : ℚ̄) ≠ 1 := by
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp hA
  exact ⟨h2, by rwa [Valuation.map_neg], by ring, by ring, zero_ne_one⟩

/-- FLT Sourceを仮定せず、2で節点還元する具体的な有理曲線。 -/
def exampleCurve : WeierstrassCurve ℚ := ⟨1, 1, 0, 2, 0⟩

/-- 具体的曲線の判別式とc₄。Δは2で割れ、c₄は奇数である。 -/
theorem example_invariants : exampleCurve.Δ = -412 ∧ exampleCurve.c₄ = -71 := by
  norm_num [exampleCurve, WeierstrassCurve.Δ, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- 実際の曲線上で、2が非単元の住所に中心と分離した整な方向が存在し、慣性が全て固定する。
これは中心・方向の存在を仮定しただけのスモークではない。 -/
theorem example_geometry (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    ∃ C : CriticalCentre A (exampleCurve.baseChange ℚ̄), ∃ D : TangentDirections C,
      (∀ σ ∈ inertiaSubgroupIn A ℚ, σ C.x = C.x ∧ σ C.y = C.y) ∧
      (∀ σ ∈ inertiaSubgroupIn A ℚ, σ D.α = D.α ∧ σ D.β = D.β) := by
  let W := exampleCurve.baseChange ℚ̄
  have hΔ : W.Δ = (-412 : ℚ̄) := by
    dsimp only [W, WeierstrassCurve.baseChange]
    rw [WeierstrassCurve.map_Δ, example_invariants.1]
    norm_num
  have hc : W.c₄ = (-71 : ℚ̄) := by
    dsimp only [W, WeierstrassCurve.baseChange]
    rw [WeierstrassCurve.map_c₄, example_invariants.2]
    norm_num
  have h2 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hcunit : A.valuation W.c₄ = 1 := by
    rw [hc]
    simpa using valuation_intCast_eq_one_of_not_dvd A Nat.prime_two h2 (z := -71) (by norm_num)
  have hΔsmall : A.valuation W.Δ < 1 := by
    rw [hΔ]
    simpa using valuation_intCast_lt_one_of_dvd A h2 (z := -412) (by norm_num)
  have h₁ : W.a₁ ∈ A := by change (1 : ℚ̄) ∈ A; exact one_mem A
  have h₂ : W.a₂ ∈ A := by change (1 : ℚ̄) ∈ A; exact one_mem A
  obtain ⟨C⟩ := EllipticCriticalCentre.exists_criticalCentre A W h₁ h₂
    (by simp [W, WeierstrassCurve.baseChange, exampleCurve])
    (by change (2 : ℚ̄) ∈ A; exact ofNat_mem A 2)
    (by simp [W, WeierstrassCurve.baseChange, exampleCurve])
    (by rw [hΔ]; norm_num) hΔsmall hcunit
  obtain ⟨D⟩ := EllipticDyadicGeometry.exists_tangentDirections A W C h₁ h₂
  have hfix := EllipticDyadicGeometry.inertia_fixed exampleCurve A C h2
  exact ⟨C, D, hfix, fun σ hσ =>
    EllipticDyadicGeometry.tangentDirections_inertia_fixed exampleCurve A D σ hσ (hfix σ hσ).1⟩

end EllipticDyadicGeometryTest

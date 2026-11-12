import DkMath.Lib.NumberTheory.KummerInertia

#print "file: DkMathTest.Lib.NumberTheory.KummerInertia"

/-!
NOTE-032-002の境界例。指数37に正則性を仮定せず、実際のKummer根が動くことを確認する。
同時に、単元wとp∤mの仮定を取り去ると何が起こるかを示す。
-/
namespace KummerInertiaTest
open DkMath.Lib.NumberTheory ValuationInertia
local notation "ℚ̄" => AlgebraicClosure ℚ

/-- 指数37でも、2の37乗根を動かす慣性元は正則性なしで存在する。
その根の37乗は固定されるので、単元の仮定なしには冪の剛性を使えない。 -/
theorem nonunit_power_boundary (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    ∃ s : ℚ̄, s ^ 37 = 2 ∧ A.valuation s ≠ 1 ∧
      ∃ τ ∈ inertiaSubgroupIn A ℚ, τ (s ^ 37) = s ^ 37 ∧ τ s ≠ s := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℚ̄) (by decide : 0 < 37)
  have hroot : s ^ 37 = (2 : ℚ̄) ^ 1 := by simpa using hs
  obtain ⟨τ, hτ, hne⟩ := KummerInertia.exists_inertia_ne_of_pow_eq A hA
    Nat.prime_two (by decide : Nat.Prime 37) (by decide) (by decide : ¬ 37 ∣ 1) hroot
  refine ⟨s, hs, ?_, τ, hτ, ?_, hne⟩
  · intro hv
    have hsmall := (ValuationSubring.mem_nonunits_iff A).mp hA
    have hv2 : A.valuation (2 : ℚ̄) = 1 := by rw [← hs, map_pow, hv, one_pow]
    exact hsmall.ne hv2
  · rw [hs, map_ofNat]

/-- q=3,p=5,m=2も同じ一般核を使える。2に固有の偶奇計算を仮定しない。 -/
theorem odd_residue_prime (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 3)
    {s : ℚ̄} (hs : s ^ 5 = (3 : ℚ̄) ^ 2) :
    ∃ τ ∈ inertiaSubgroupIn A ℚ, τ s ≠ s :=
  KummerInertia.exists_inertia_ne_of_pow_eq A hA (by decide) (by decide)
    (by decide) (by decide : ¬ 5 ∣ 2) hs

/-- p∣mの場合には有理数q自身を取れて、全慣性に固定される。p∤mは本質的。 -/
theorem divisible_depth_boundary (A : ValuationSubring ℚ̄) :
    (2 : ℚ̄) ^ 37 = 2 ^ 37 ∧
      ¬ ∃ τ ∈ inertiaSubgroupIn A ℚ, τ (2 : ℚ̄) ≠ 2 := by
  refine ⟨rfl, ?_⟩
  rintro ⟨τ, -, hne⟩
  exact hne (map_ofNat τ 2)

/-- 剰余標数2でζ=−1は1と区別できない。指数の単元条件を落とせない。 -/
theorem residue_characteristic_boundary (A : ValuationSubring ℚ̄) (hA : LiesOverPrime A 2) :
    (-1 : ℚ̄) ^ 2 = 1 ∧ (-1 : ℚ̄) ≠ 1 ∧ A.valuation ((-1 : ℚ̄) - 1) < 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hsmall := (ValuationSubring.mem_nonunits_iff A).mp hA
  rw [show (-1 : ℚ̄) - 1 = -2 by ring, Valuation.map_neg]
  exact hsmall

end KummerInertiaTest

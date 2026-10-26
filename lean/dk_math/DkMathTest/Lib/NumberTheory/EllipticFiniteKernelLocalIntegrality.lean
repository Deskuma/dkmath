/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality
import DkMath.Lib.NumberTheory.WeierstrassDenominatorSupport
import DkMathTest.Lib.NumberTheory.WeierstrassIntegralModel

#print "file: DkMathTest.Lib.NumberTheory.EllipticFiniteKernelLocalIntegrality"

/-!
非巡回E[3]の9点核で半核が4点になること、有理分母の例外素数、
分母2を導入しない候補係数の標数2への還元を検査する。
候補を既存kernelModelに同一視する証明はここでも仮定しない。
-/
namespace EllipticFiniteKernelLocalIntegralityTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory EllipticFiniteKernel EllipticTorsionRepresentation
open WeierstrassVeluPolynomial WeierstrassRationalIntegralModel RationalPrimeDenominator
open EllipticFiniteKernelTest EllipticFiniteKernelPolesTest EllipticFiniteKernelNonsingularTest
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
local instance : Fintype fullThreeKernel := by
  let := finite_torsion_of_ne_zero curve 3 (by decide)
  exact Fintype.ofFinite (Torsion curve 3)

/-- 巡回性を仮定せず、実際の9点核から4つの反転対代表を得る。 -/
theorem actual_nine_point_half : (halfKernel curve fullThreeKernel).card = 4 := by
  have h := card_halfKernel curve fullThreeKernel fullThree_card.2
  rw [fullThree_card.1] at h
  omega

/-- 同じ4点の半核と反転半核は非零核を尽くし、交わらない。 -/
theorem actual_half_partition :
    halfKernel curve fullThreeKernel ∪ (halfKernel curve fullThreeKernel).image Neg.neg =
      Finset.univ.erase 0 ∧
    Disjoint (halfKernel curve fullThreeKernel) ((halfKernel curve fullThreeKernel).image Neg.neg) :=
  halfKernel_partition curve fullThreeKernel fullThree_card.2

/-- 37を除いた場所では1/37は整だが、37進では整でない。 -/
theorem rational_single_exception :
    (∀ q : ℕ, q.Prime → q ≠ 37 → 0 ≤ padicValRat q (1 / 37 : ℚ)) ∧
      ¬ 0 ≤ padicValRat 37 (1 / 37 : ℚ) := by
  constructor
  · apply (exists_den_eq_pow_iff (1 / 37 : ℚ) (by decide : Nat.Prime 37)).mp
    exact ⟨1, by norm_num⟩
  · rw [padicValRat_nonneg_iff _ (by decide : Nat.Prime 37)]
    norm_num

/-- 例外を37だけに縮めることはできない分母74の境界例。 -/
theorem rational_two_exceptions :
    (1 / 74 : ℚ).den.primeFactors ⊆ ({2, 37} : Finset ℕ) ∧
      ¬ ∃ e : ℕ, (1 / 74 : ℚ).den = 37 ^ e := by
  constructor
  · rw [show (1 / 74 : ℚ).den = 74 by norm_num]
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    have hd : q ∣ 2 * 37 := Nat.dvd_of_mem_primeFactors hq
    rcases hp.dvd_mul.mp hd with h | h
    · exact Finset.mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)))
  · intro h
    have hh := (exists_den_eq_pow_iff (1 / 74 : ℚ) (by decide : Nat.Prime 37)).mp h
    have he := (padicValRat_nonneg_iff (1 / 74 : ℚ) (by decide : Nat.Prime 2)).mp
      (hh 2 (by decide) (by decide))
    norm_num at he

/-- 分母16の既存曲線では、整性の例外は正確に2。 -/
theorem actual_sample_places :
    (∀ q : ℕ, q.Prime → q ≠ 2 → CoeffIntegralAt WeierstrassIntegralModelTest.sample q) ∧
      ¬ CoeffIntegralAt WeierstrassIntegralModelTest.sample 2 := by
  constructor
  · apply (exists_commonDenominator_pow_iff _ (by decide : Nat.Prime 2)).mp
    exact ⟨4, by rw [WeierstrassIntegralModelTest.sample_denominator]; norm_num⟩
  · rw [coeffIntegralAt_iff_not_dvd _ (by decide : Nat.Prime 2),
      WeierstrassIntegralModelTest.sample_denominator]
    norm_num

/-- y²+y=x³の(0,0)代表から作る整数係数候補。商との一致は主張しない。 -/
def toy : WeierstrassCurve ℤ := ⟨0, 0, 1, 0, 0⟩

/-- 半核一代表の公式は、整数のままy²+y=x³−7を与える。 -/
theorem toy_candidate : polynomialModel toy ({()} : Finset Unit) (fun _ => 0) (fun _ => 0) =
    (⟨0, 0, 1, 0, -7⟩ : WeierstrassCurve ℤ) := by
  ext <;> norm_num [polynomialModel, momentT, momentW, toy, b₂, b₄]

/-- 整数構成を先に標数2へ移しても同じ候補になる。2の逆数は必要ない。 -/
theorem toy_reduction_at_two :
    polynomialModel (toy.map (Int.castRingHom (ZMod 2))) ({()} : Finset Unit)
      (fun _ => 0) (fun _ => 0) = (⟨0, 0, 1, 0, 1⟩ : WeierstrassCurve (ZMod 2)) := by
  have he := polynomialModel_map (Int.castRingHom (ZMod 2)) toy ({()} : Finset Unit)
    (fun _ => 0) (fun _ => 0)
  rw [toy_candidate] at he
  have hm : (⟨0, 0, 1, 0, -7⟩ : WeierstrassCurve ℤ).map (Int.castRingHom (ZMod 2)) =
      (⟨0, 0, 1, 0, 1⟩ : WeierstrassCurve (ZMod 2)) := by
    ext <;> norm_num [WeierstrassCurve.map]
    decide
  rw [hm] at he
  simpa [Function.comp_def] using he.symm

end
end EllipticFiniteKernelLocalIntegralityTest

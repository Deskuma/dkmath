/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: actual residue roots/torsion/fixed lifts supplied internally for original overfield.
-/

import DkMath.Lib.NumberTheory.InertiaResidueRootLifts
import Mathlib.Data.Nat.Factorization.Basic

#print "file: DkMath.Lib.NumberTheory.InertiaResidueUnitRoots"

/-!
# 慣性固定体を含む実際の中間体での単元 p 冪根近似

剰余冪根・有限位数・根の1の固定体内持ち上げを、全て証明済みの定理から供給する。
得られるのは極大イデアルを法とする近似であり、体内の正確な p 乗根ではない。
-/
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open ValuationInertia

/-- 同じ固定体を含む中間体の単元は、同じ付値環で p 乗根近似を持つ。 -/
theorem approximate_unit_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime P q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : fixedField P ≤ E)
    (u : P.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : P.comap (algebraMap E (AlgebraicClosure ℚ)),
      z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
  have hroots (c : IsLocalRing.ResidueField P) : ∃ y, y ^ p = c :=
    AlgebraicResidue.power_surjective P p hp.ne_zero c
  have htor (c : IsLocalRing.ResidueField P) (hc : c ≠ 0) : ∃ N : ℕ, 0 < N ∧ c ^ N = 1 :=
    AlgebraicResidue.nonzero_finite_order P q hq hA c hc
  have hμ (i : ℕ) (y : IsLocalRing.ResidueField P) (hy : y ^ (p ^ i) = 1) :
      ∃ k : E, ∃ hk : algebraMap E (AlgebraicClosure ℚ) k ∈ P,
        IsLocalRing.residue P ⟨algebraMap E (AlgebraicClosure ℚ) k, hk⟩ = y := by
    obtain ⟨ζ, hζE, _, hζA, hres⟩ := primePower_root_lift hp hq hpq P hA i y hy
    exact ⟨⟨ζ, hE hζE⟩, hζA, hres⟩
  classical
  let ψ : P.comap (algebraMap E (AlgebraicClosure ℚ)) →+* P :=
    { toFun := fun k => ⟨algebraMap E (AlgebraicClosure ℚ) k, k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  let r : P.comap (algebraMap E (AlgebraicClosure ℚ)) →+* IsLocalRing.ResidueField P := (IsLocalRing.residue P).comp ψ
  have hr : ∀ (k : E) (hk : algebraMap E (AlgebraicClosure ℚ) k ∈ P),
      r ⟨k, hk⟩ = IsLocalRing.residue P ⟨algebraMap E (AlgebraicClosure ℚ) k, hk⟩ := fun _ _ => rfl
  have hrefl : ∀ t, r t = 0 → t ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
    intro t ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro htu
    have h1 : IsUnit (ψ t) := htu.map ψ
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit] at h1
    exact h1 ht
  have hū : r u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hu.map ψ)
  obtain ⟨y, hy⟩ := hroots (r u)
  obtain ⟨N, hN, hN1⟩ := htor (r u) hū
  obtain ⟨a, m, hnd, hNam⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.one_lt.ne'
  have hyM : y ^ (p ^ (a + 1) * m) = 1 := by
    rw [pow_succ', mul_assoc, pow_mul, hy, ← hNam, hN1]
  have tail : ∀ (e : ℕ) (w : IsLocalRing.ResidueField P), w ^ (p ^ (a + 1)) = 1 → y = r u ^ e * w →
      ∃ z : P.comap (algebraMap E (AlgebraicClosure ℚ)), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
    intro e w hw hyw
    obtain ⟨k, hk, hkw⟩ := hμ (a + 1) w hw
    refine ⟨⟨k, hk⟩ * u ^ e, hrefl _ ?_⟩
    rw [map_sub, map_pow, map_mul, map_pow, sub_eq_zero, hr k hk, hkw, mul_comm, ← hyw, hy]
  by_cases hm1 : m = 1
  · refine tail 0 y ?_ (by rw [pow_zero, one_mul])
    rw [← hyM, hm1, mul_one]
  · have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hNam
      exact hN.ne' hNam
    have hm : 1 < m := Nat.lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hm0) (Ne.symm hm1)
    have hcop : Nat.Coprime (p ^ (a + 1)) m :=
      (Nat.coprime_pow_left_iff (Nat.succ_pos a) _ _).mpr (hp.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨A, -, hA⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hm
    set j := p ^ (a + 1) * A / m with hj
    have hMA : p ^ (a + 1) * A = m * j + 1 := by
      have := Nat.div_add_mod (p ^ (a + 1) * A) m
      rw [hA] at this
      exact this.symm
    have hyjM : (y ^ (m * j)) ^ (p ^ (a + 1)) = 1 := by
      rw [← pow_mul, show m * j * p ^ (a + 1) = (p ^ (a + 1) * m) * j by ring, pow_mul, hyM, one_pow]
    refine tail (p ^ a * A) ((y ^ (m * j)) ^ (p ^ (a + 1) - 1)) ?_ ?_
    · rw [← pow_mul, mul_comm (p ^ (a + 1) - 1) (p ^ (a + 1)), pow_mul, hyjM, one_pow]
    · symm
      calc r u ^ (p ^ a * A) * (y ^ (m * j)) ^ (p ^ (a + 1) - 1)
          = y ^ (m * j) * y * (y ^ (m * j)) ^ (p ^ (a + 1) - 1) := by
            rw [← hy, ← pow_mul, show p * (p ^ a * A) = p ^ (a + 1) * A by ring, hMA, pow_succ]
        _ = y * ((y ^ (m * j)) ^ (p ^ (a + 1) - 1) * y ^ (m * j)) := by ring
        _ = y * (y ^ (m * j)) ^ (p ^ (a + 1)) := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)]
        _ = y := by rw [hyjM, mul_one]

/-- 同じ近似根は単元でもある。後の単根持ち上げに使うガードを保持する。 -/
theorem approximate_unit_pRoot_isUnit {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime P q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : fixedField P ≤ E)
    (u : P.comap (algebraMap E (AlgebraicClosure ℚ))) (hu : IsUnit u) :
    ∃ z : P.comap (algebraMap E (AlgebraicClosure ℚ)), IsUnit z ∧
      z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap E (AlgebraicClosure ℚ))) := by
  obtain ⟨z, hz⟩ := approximate_unit_pRoot hp hq hpq P hA E hE u hu
  have hzn : IsUnit (z ^ p) := by
    by_contra hn
    have hm := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hum := Ideal.sub_mem _ hm hz
    rw [sub_sub_cancel] at hum
    exact (IsLocalRing.mem_maximalIdeal _).mp hum hu
  exact ⟨z, (isUnit_pow_iff hp.ne_zero).mp hzn, hz⟩

end
end DkMath.Lib.NumberTheory.InertiaResidue

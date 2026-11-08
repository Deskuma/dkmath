/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from P2M/Sol/S_ValuationSubring_exists_pow_eq_of_kummer_descent.lean,
commit 115356cbc627159d0d16add0da6e9a2bb3655ed8.
Modified: valuation stability and exact radical descent in the reusable DkMath library.
-/

import DkMath.Lib.NumberTheory.ValuationRadicalDivisibility

#print "file: DkMath.Lib.NumberTheory.InertiaRadicalExactRoots"

/-! # 実際の tail 上位体における正確な p 乗根
一般降下補題の入力を、同じ付値環・同じ tail 体から全て内部供給する。
これは体の乗法群の p 可除性であり、慣性群や Frey 共通商の巡回性は別の命題である。 -/
namespace DkMath.Lib.NumberTheory.RadicalDescent
noncomputable section
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem exists_pow_eq [IsAlgClosed L] [IsGalois K L] [CharZero L] (P : ValuationSubring L)
    (hstab : ∀ (σ : L ≃ₐ[K] L) (x : L), x ∈ P → σ x ∈ P)
    (p q : ℕ) (hp : p.Prime) (hqp : q.Prime) (hpq : p ≠ q)
    (hq : ((q : ℕ) : P) ∈ IsLocalRing.maximalIdeal P)
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    (hroot : ∀ k : ℕ, ∃ r : K, r ^ (p ^ k) = (q : K))
    (hres : ∀ u : P.comap (algebraMap K L), IsUnit u →
      ∃ z : P.comap (algebraMap K L), z ^ p - u ∈ IsLocalRing.maximalIdeal (P.comap (algebraMap K L)))
    (a : K) (ha : a ≠ 0) : ∃ b : K, b ^ p = a := by
  have : CharZero K := (algebraMap K L).charZero
  set R : ValuationSubring K := P.comap (algebraMap K L) with hR
  have hmemR : ∀ k : K, k ∈ R ↔ algebraMap K L k ∈ P := fun _ => Iff.rfl
  set v := P.valuation with hv
  let vK : Valuation K P.ValueGroup := v.comap (algebraMap K L)
  have hvK : ∀ k : K, vK k = v (algebraMap K L k) := fun _ => rfl
  have hmem_of_le : ∀ k : K, vK k ≤ 1 → k ∈ R := fun k hk => (hmemR k).mpr ((P.valuation_le_one_iff _).mp hk)
  have hunit_of_eq : ∀ (k : K) (hk : vK k = 1), IsUnit (⟨k, hmem_of_le k hk.le⟩ : R) := by
    intro k hk
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, map_zero] at hk; exact zero_ne_one hk
    have hinv : vK k⁻¹ ≤ 1 := by rw [map_inv₀, hk, inv_one]
    exact IsUnit.of_mul_eq_one ⟨k⁻¹, hmem_of_le _ hinv⟩ (Subtype.ext (mul_inv_cancel₀ hk0))
  have hq0L : (q : L) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hq0K : (q : K) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr hpq
  have hvp : vK (p : K) = 1 := by rw [hvK, map_natCast]; exact RationalValue.valuation_natCast_eq_one P q hq p hcop
  have hpunit : IsUnit ((p : ℕ) : R) := by
    have h := hunit_of_eq (p : K) hvp
    have e : (⟨(p : K), hmem_of_le _ hvp.le⟩ : R) = ((p : ℕ) : R) := Subtype.ext (by simp)
    rwa [e] at h
  have hx0 : algebraMap K L a ≠ 0 := (_root_.map_ne_zero (algebraMap K L)).mpr ha
  obtain ⟨n, hn, m, hnm⟩ := RationalValue.exists_valuation_pow_eq P q hqp hq (algebraMap K L a) hx0 (halg _)
  have hrat : ∃ n : ℕ, 0 < n ∧ ∃ m : ℤ, vK a ^ n = vK (q : K) ^ m := by
    refine ⟨n, hn, m, ?_⟩
    rw [hvK, hvK, map_natCast]; exact hnm
  obtain ⟨b₀, hb₀, hvb⟩ := RadicalValue.exists_valuation_eq_pow vK p hp (q : K) hq0K hroot a ha hrat
  set u : K := a / b₀ ^ p with hu
  have hbp0 : b₀ ^ p ≠ 0 := pow_ne_zero _ hb₀
  have hvu : vK u = 1 := by rw [hu, map_div₀, map_pow, hvb, div_self (pow_ne_zero _ ((Valuation.ne_zero_iff vK).mpr hb₀))]
  have hau : a = b₀ ^ p * u := by rw [hu, mul_div_cancel₀ _ hbp0]
  have : HenselianLocalRing R := StableValuation.henselianLocalRing_comap P hstab
  set uR : R := ⟨u, hmem_of_le u hvu.le⟩ with huR
  obtain ⟨z, hz⟩ := hres uR (hunit_of_eq u hvu)
  obtain ⟨w, hw, -⟩ := InertiaResidue.exists_pow_eq_of_pow_sub_mem p hpunit uR z (hunit_of_eq u hvu) hz
  refine ⟨b₀ * (w : K), ?_⟩
  have hwK : (w : K) ^ p = u := by
    have := congrArg ((↑) : R → K) hw
    simpa using this
  rw [mul_pow, hwK, ← hau]


end
end DkMath.Lib.NumberTheory.RadicalDescent
namespace DkMath.Lib.NumberTheory.InertiaResidue
noncomputable section
open ValuationInertia
/-- tail 体の任意の実際の上位体で、非零元は正確な p 乗根を持つ。 -/
theorem tailOverfield_exact_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (a : E) (ha : a ≠ 0) : ∃ b : E, b ^ p = a := by
  have hfixed := (fixedField_le_tailField A p q).trans hE
  have hqmax : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hA.2 (((A.valuation_eq_one_iff _).mp hu).ge)
  have hroot (k : ℕ) : ∃ r : E, r ^ (p ^ k) = (q : E) := by
    refine ⟨⟨InertiaRadical.radical p q hp k, hE (tower_mem_tailField A hp k)⟩, ?_⟩
    apply Subtype.ext
    exact PrimeRadicalTower.tower_pow p hp.pos (q : AlgebraicClosure ℚ) k
  exact RadicalDescent.exists_pow_eq A (InertiaStability.overfield_stable A E hfixed)
    p q hp hq hpq hqmax (fun x => Algebra.IsAlgebraic.isAlgebraic x) hroot
    (fun u hu => approximate_unit_pRoot hp hq hpq A hA E hfixed u hu) a ha

/-- 元の tail 体そのものの正確な非零 p 乗根。 -/
theorem tailField_exact_pRoot {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (a : tailField A p q) (ha : a ≠ 0) : ∃ b : tailField A p q, b ^ p = a :=
  tailOverfield_exact_pRoot hp hq hpq A hA _ le_rfl a ha
/-- 零を含む冪写像の全射性。実際の tail 上位体だけを入力する。 -/
theorem tailOverfield_power_surjective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (a : E) : ∃ b : E, b ^ p = a := by
  by_cases ha : a = 0
  · exact ⟨0, by rw [ha, zero_pow hp.ne_zero]⟩
  · exact tailOverfield_exact_pRoot hp hq hpq A hA E hE a ha

/-- 同じ上位体内で任意の有限深さの p 冪根を構成する。 -/
theorem tailOverfield_primePower_surjective {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    (E : IntermediateField ℚ (AlgebraicClosure ℚ)) (hE : tailField A p q ≤ E)
    (n : ℕ) (a : E) : ∃ b : E, b ^ (p ^ n) = a := by
  induction n generalizing a with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := tailOverfield_power_surjective hp hq hpq A hA E hE a
    obtain ⟨b, hb⟩ := ih c
    exact ⟨b, by rw [pow_succ, pow_mul, hb, hc]⟩
end
end DkMath.Lib.NumberTheory.InertiaResidue


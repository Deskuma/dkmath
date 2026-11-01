/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicRootModule
import DkMath.Lib.NumberTheory.ValuationInertiaPower
import DkMath.Lib.NumberTheory.ValuationFrobenius

#print "file: DkMath.Lib.NumberTheory.CyclotomicFrobenius"

/-!
# 実際の Frobenius の円分指標は `q mod p`

単元次数の冪根は剰余合同から同一と判定できる。従って剰余上で `q` 乗として作用する
分解群元は、prime-to-`q` な冪根自体にも `q` 乗として作用する。
指定された同じ付値環・同じ自己同型を保ち、剰余合同を指標値へ接続する。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicFrobenius

open ValuationInertia ValuationFrobenius CyclotomicRootModule

/-- 単元次数の二つの冪根が同じ剰余なら、元の体でも一致する。 -/
theorem roots_eq_of_congruent {K : Type*} [Field K] (A : ValuationSubring K)
    {n : ℕ} (hn : n ≠ 0) (hunit : A.valuation (n : K) = 1)
    {z w : K} (hz : z ^ n = 1) (hw : w ^ n = 1) (hd : z - w ∈ A.nonunits) : z = w := by
  have hv (a : K) (ha : a ^ n = 1) : A.valuation a = 1 := by
    apply pow_left_injective (M := A.ValueGroup) hn
    change A.valuation a ^ n = 1 ^ n
    rw [← map_pow, ha, map_one, one_pow]
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_pow hn] at hw; exact zero_ne_one hw
  by_contra hne
  have hr : (z / w) ^ n = 1 := by rw [div_pow, hz, hw, div_self one_ne_zero]
  have hrne : z / w ≠ 1 := fun h => hne ((div_eq_one_iff_eq hw0).mp h)
  have hvr := ValuationInertiaPower.valuation_sub_one_eq_one hn hunit hr hrne
  have hsmall := (ValuationSubring.mem_nonunits_iff A).mp hd
  have he : z - w = (z / w - 1) * w := by field_simp
  rw [he, map_mul, hvr, hv w hw, mul_one] at hsmall
  exact (lt_irrefl 1) hsmall

/-- 実際の Frobenius は、単元次数の冪根を `q` 乗へ送る。 -/
theorem apply_root_eq_pow {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {σ : L ≃ₐ[K] L} {q n : ℕ} (hσ : IsFrobeniusAt A σ q)
    (hn : n ≠ 0) (hunit : A.valuation (n : L) = 1) {z : L} (hz : z ^ n = 1) :
    σ z = z ^ q := by
  have hvz : A.valuation z = 1 := by
    apply pow_left_injective (M := A.ValueGroup) hn
    change A.valuation z ^ n = 1 ^ n
    rw [← map_pow, hz, map_one, one_pow]
  let zA : A := ⟨z, (A.valuation_le_one_iff _).mp hvz.le⟩
  have hres := hσ.smul_residue_eq (IsLocalRing.residue A zA)
  rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow] at hres
  have hd := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr (Ideal.Quotient.eq.mp hres)
  apply roots_eq_of_congruent A hn hunit (z := σ z) (w := z ^ q) ?_ ?_ hd
  · rw [← map_pow, hz, map_one]
  · rw [← pow_mul, Nat.mul_comm q n, pow_mul, hz, one_pow]

/-- `q≠p` の同じ素点で、円分指標の値は実際の `q mod p`。 -/
theorem cyclotomicCharacter_eq_natCast {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (cyclotomicCharacter p σ : ZMod p) = (q : ZMod p) := by
  have hp : p.Prime := Fact.out
  have hunit : A.valuation (p : AlgebraicClosure ℚ) = 1 :=
    ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff A).mp hA) (by
        intro h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast h)))
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p
  have hpow := apply_root_eq_pow A hσ hp.ne_zero hunit hz.pow_eq_one
  have hc := cyclotomicCharacter_spec (K := ℚ) p σ hz.toRootsOfUnity
  have he : z ^ (cyclotomicCharacter p σ : ZMod p).val = z ^ q := hc.symm.trans hpow
  have hmod : Nat.ModEq p (cyclotomicCharacter p σ : ZMod p).val q := by
    have heU : hz.toRootsOfUnity.val ^ (cyclotomicCharacter p σ : ZMod p).val =
        hz.toRootsOfUnity.val ^ q := Units.ext he
    have h := pow_eq_pow_iff_modEq.mp heU
    rw [← orderOf_units] at h
    change Nat.ModEq (orderOf z) (cyclotomicCharacter p σ : ZMod p).val q at h
    rwa [← hz.eq_orderOf] at h
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simpa only [ZMod.natCast_zmod_val] using hcast

end DkMath.Lib.NumberTheory.CyclotomicFrobenius

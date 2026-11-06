/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CyclotomicFrobenius
import DkMath.Lib.NumberTheory.EllipticWeilDeterminantAll
import DkMath.Lib.Algebra.PadicCharacterLimit

#print "file: DkMath.Lib.NumberTheory.CyclotomicFrobeniusAll"

/-!
# 同じ Frobenius の全有限・p 進円分値

剰余体上で q 乗として作用する同じ元を保つ。良還元はこの円分計算には不要。
捩れ次数が付値単元であることから冪根の作用を体へ戻し、全正冪剰余で比較する。
-/
namespace DkMath.Lib.NumberTheory.CyclotomicFrobenius
open ValuationInertia ValuationFrobenius EllipticTorsionRepresentation

/-- 任意の非零単元次数で、同じ Frobenius の有限円分値は q。 -/
theorem torsionCyclotomicCharacter_eq_natCast (n : ℕ) (hn : n ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ}
    (hunit : A.valuation (n : AlgebraicClosure ℚ) = 1)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (torsionCyclotomicCharacter n hn σ : ZMod n) = (q : ZMod n) := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) n
  have hpow := apply_root_eq_pow A hσ hn hunit hz.pow_eq_one
  have hc := torsionCyclotomicCharacter_spec n hn σ hz.toRootsOfUnity
  have he : z ^ (torsionCyclotomicCharacter n hn σ : ZMod n).val = z ^ q := hc.symm.trans hpow
  have hmod : Nat.ModEq n (torsionCyclotomicCharacter n hn σ : ZMod n).val q := by
    have heU : hz.toRootsOfUnity.val ^ (torsionCyclotomicCharacter n hn σ : ZMod n).val =
        hz.toRootsOfUnity.val ^ q := Units.ext he
    have h := pow_eq_pow_iff_modEq.mp heU
    rw [← orderOf_units] at h
    change Nat.ModEq (orderOf z) (torsionCyclotomicCharacter n hn σ : ZMod n).val q at h
    rwa [← hz.eq_orderOf] at h
  simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

/-- q≠p の同じ素点では p の全冪も付値単元。 -/
theorem prime_power_valuation_eq_one {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q) (n : ℕ) :
    A.valuation ((p ^ (n + 1) : ℕ) : AlgebraicClosure ℚ) = 1 := by
  have hu : A.valuation (p : AlgebraicClosure ℚ) = 1 :=
    ValuationPrimeSupport.valuation_intCast_eq_one_of_not_dvd A hq
      ((ValuationSubring.mem_nonunits_iff A).mp hA) (by
        intro h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp (by exact_mod_cast h)))
  rw [Nat.cast_pow, map_pow, hu, one_pow]

/-- 標準 p 進円分指標の同じ実際の Frobenius 値は、整数 q 自身。 -/
theorem padicCyclotomicCharacter_eq_natCast {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A q)
    {σ : Field.absoluteGaloisGroup ℚ} (hσ : IsFrobeniusAt A σ q) :
    (_root_.cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]) = q := by
  apply DkMath.Lib.Algebra.PadicCharacterLimit.ext_positive
  intro n
  rw [_root_.cyclotomicCharacter.toZModPow]
  change (torsionCyclotomicCharacter (p ^ (n + 1))
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) σ : ZMod (p ^ (n + 1))) = _
  rw [torsionCyclotomicCharacter_eq_natCast _ _ A (prime_power_valuation_eq_one hq hqp A hA n) hσ]
  exact (map_natCast (PadicInt.toZModPow (n + 1)) q).symm

end DkMath.Lib.NumberTheory.CyclotomicFrobenius

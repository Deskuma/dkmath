import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia

open scoped NumberField Pointwise

namespace DkMath.FLT.Seven
open SevenRealCubicInt
namespace SevenRealCubic
noncomputable section

example
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    multiplicity P (Ideal.span {modelEquivRingOfIntegers
      (t.powerSplit.gapSplit.a : SevenRealCubicInt)}) =
        t.powerSplit.gapSplit.a.factorization q := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hqZ : Prime (q : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hbase : base.IsPrime := by
    dsimp [base]
    exact (Ideal.span_singleton_prime (by
      exact Int.ofNat_ne_zero.mpr (Nat.Prime.ne_zero hq))).mpr hqZ
  have hbase0 : base ≠ ⊥ := by
    simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  let : P.IsPrime := hPprime
  have hP0 : P ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  let : P.LiesOver base := by simpa [base] using hPover
  have hmap : Ideal.map (algebraMap ℤ O)
      (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) =
      Ideal.span {modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} := by
    simp [Ideal.map_span]
  have hscalar0 : Ideal.span {(t.powerSplit.gapSplit.a : ℤ)} ≠ ⊥ := by
    simpa using (Int.ofNat_ne_zero.mpr t.powerSplit.gapSplit.a_pos.ne')
  have hmult :
      emultiplicity P (Ideal.map (algebraMap ℤ O)
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)})) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
    rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
      hscalar0 (Ideal.prime_of_isPrime hbase0 hbase).irreducible
      (Ideal.prime_of_isPrime hP0 hPprime).irreducible hP0]
    have hram : (Ideal.span {(q : ℤ)}).ramificationIdx' P = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hbase0]
      have hcomplete := common_norm_prime_complete_split t hq hqR hqS
      have hri := Ideal.ramificationIdxIn_eq_ramificationIdx
        (Ideal.span {(q : ℤ)}) P (Gal(Field / ℚ))
      rw [← hri, hcomplete.2.2.1]
    rw [hram]
    simp only [Nat.cast_one, one_mul]
    change emultiplicity base
      (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) = _
    have hfin : FiniteMultiplicity base
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) :=
      FiniteMultiplicity.of_prime_left
        (Ideal.prime_of_isPrime hbase0 hbase) hscalar0
    rw [hfin.emultiplicity_eq_multiplicity]
    rw [Ideal.multiplicity_span_eq_multiplicity]
    rw [← Int.multiplicity_natAbs q (t.powerSplit.gapSplit.a : ℤ)]
    simp only [Int.natAbs_natCast, Nat.cast_inj]
    rw [Nat.multiplicity_eq_factorization hq]
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← hmap]
  exact hmult

end
end SevenRealCubic
end DkMath.FLT.Seven

#check Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
#check emultiplicity_mul
#check multiplicity_mul
#check emultiplicity_eq_zero
#check emultiplicity_eq_zero_of_irreducible_ne
#check Ideal.dvd_iff_le
#check multiplicity_eq_of_emultiplicity_eq_some
#check FiniteMultiplicity.emultiplicity_eq_multiplicity
#check FiniteMultiplicity.of_prime_left
#check Ideal.multiplicity_span_eq_multiplicity
#check Nat.multiplicity_eq_factorization
#check Int.multiplicity_natAbs
#check Nat.cast_ne_zero
#check Nat.cast_injective
#check Xor
#check Or.inl
#check Ideal.ramificationIdx'_eq_ramificationIdx
#check Ideal.ramificationIdxIn_eq_ramificationIdx
#check Ideal.natAbs_pow_inertiaDeg
#check IsDedekindDomain.HeightOneSpectrum.factorization_eq_multiplicity
#check Ideal.map_span
#check Ideal.span_singleton_prime
#check Nat.factorization_gcd
#check Nat.factorization_mul
#check Nat.prod_primeFactors_pow_factorization

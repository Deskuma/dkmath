/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicPrimeAllocation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.RamificationInertia.Ramification

#print "file: DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor"

namespace DkMath.FLT.Seven

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

set_option linter.style.longLine false
set_option linter.style.setOption false

namespace SevenRealCubic

private theorem canonicalCommonFactor_scalar_ideal_map
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p) :
    Ideal.map (algebraMap ℤ O)
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)}) =
      Ideal.span {modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} := by
  simp [Ideal.map_span]

private theorem canonicalCommonFactor_span_model_ne_bot
    {s : SevenRealCubicInt} (hs : s ≠ 0) :
    Ideal.span ({modelEquivRingOfIntegers s} : Set O) ≠ ⊥ := by
  intro h
  have hm : modelEquivRingOfIntegers s ∈ (⊥ : Ideal O) := by
    rw [← h]
    exact Ideal.mem_span_singleton_self _
  have hm0 : modelEquivRingOfIntegers s = 0 := by
    simpa using hm
  apply hs
  apply modelEquivRingOfIntegers.injective
  simpa using hm0

theorem directOrbitCanonicalCommonFactor_scalar_ideal_multiplicity
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
  have hscalar0 : Ideal.span {(t.powerSplit.gapSplit.a : ℤ)} ≠ ⊥ := by
    simpa using (Int.ofNat_ne_zero.mpr t.powerSplit.gapSplit.a_pos.ne')
  have hram : (Ideal.span {(q : ℤ)}).ramificationIdx' P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hbase0]
    have hcomplete := common_norm_prime_complete_split t hq hqR hqS
    have hri := Ideal.ramificationIdxIn_eq_ramificationIdx
      (Ideal.span {(q : ℤ)}) P (Gal(Field / ℚ))
    rw [← hri, hcomplete.2.2.1]
  have hmult :
      emultiplicity P (Ideal.map (algebraMap ℤ O)
        (Ideal.span {(t.powerSplit.gapSplit.a : ℤ)})) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
    rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
      hscalar0 (Ideal.prime_of_isPrime hbase0 hbase).irreducible
      (Ideal.prime_of_isPrime hP0 hPprime).irreducible hP0]
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
  rw [← canonicalCommonFactor_scalar_ideal_map t]
  exact hmult

theorem directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot))
    (P : Ideal O) (hPprime : P.IsPrime)
    (hPover : P.LiesOver (Ideal.span {(q : ℤ)})) :
    Xor
      (gapSquareIdeal t ≤ P ∧
        multiplicity P (gapSquareIdeal t) =
          t.powerSplit.gapSplit.a.factorization q ∧
        multiplicity P (quotientSquareIdeal t) = 0)
      (quotientSquareIdeal t ≤ P ∧
        multiplicity P (gapSquareIdeal t) = 0 ∧
        multiplicity P (quotientSquareIdeal t) =
          t.powerSplit.gapSplit.a.factorization q) := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hqZ : Prime (q : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hbase0 : base ≠ ⊥ := by
    simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  have hx := directOrbitSquareRefinement_prime_ideal_allocation_xor
    t hq hqR hqS P hPprime hPover
  have hgap0 : gapSquareIdeal t ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    apply directOrbit_squareTwist_squareRoot_ne_zero t
  have hquotRoot0 : t.quotientSquareRoot ≠ 0 := by
    intro hz
    have hpos := directOrbitSquareRefinement_quotient_square_norm_pos t
    rw [hz] at hpos
    norm_num [SevenRealCubicInt.norm] at hpos
  have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    intro hz
    apply hquotRoot0
    apply modelEquivRingOfIntegers.injective
    simpa using congrArg modelEquivRingOfIntegers hz
  have hscalar0 : Ideal.span
      ({modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} : Set O) ≠ ⊥ := by
    apply canonicalCommonFactor_span_model_ne_bot
    intro hz
    have hzO := congrArg modelEquivRingOfIntegers hz
    have hzONat : (t.powerSplit.gapSplit.a : O) = 0 := by
      simpa using hzO
    exact t.powerSplit.gapSplit.a_pos.ne' (by exact_mod_cast hzONat)
  have hPprime' : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  have hscalar_mult := directOrbitCanonicalCommonFactor_scalar_ideal_multiplicity
    t hq hqR hqS P hPprime hPover
  have hscalar_emult : emultiplicity P
      (Ideal.span ({modelEquivRingOfIntegers
        (t.powerSplit.gapSplit.a : SevenRealCubicInt)} : Set O)) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
    rw [(FiniteMultiplicity.of_prime_left hPprime' hscalar0).emultiplicity_eq_multiplicity,
      hscalar_mult]
  rcases hx with ⟨hgap, hnotquot⟩ | ⟨hquot, hnotgap⟩
  · left
    have hquot_zero : emultiplicity (P : Ideal O) (quotientSquareIdeal t) = 0 := by
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      exact hnotquot (Ideal.dvd_iff_le.mp hdiv)
    have hprod_emult : emultiplicity (P : Ideal O)
        (gapSquareIdeal t * quotientSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      change emultiplicity P
        (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
          Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O)) = _
      rw [directOrbitSquareRefinement_principal_ideal_scalar_split t]
      exact hscalar_emult
    have hgap_emult : emultiplicity (P : Ideal O) (gapSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      rw [emultiplicity_mul hPprime', hquot_zero] at hprod_emult
      simpa using hprod_emult
    exact
      ⟨⟨hgap, multiplicity_eq_of_emultiplicity_eq_some hgap_emult,
          multiplicity_eq_of_emultiplicity_eq_some hquot_zero⟩,
        by intro h; exact hnotquot h.1⟩
  · right
    have hgap_zero : emultiplicity (P : Ideal O) (gapSquareIdeal t) = 0 := by
      apply emultiplicity_eq_zero.mpr
      intro hdiv
      exact hnotgap (Ideal.dvd_iff_le.mp hdiv)
    have hprod_emult : emultiplicity (P : Ideal O)
        (gapSquareIdeal t * quotientSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      change emultiplicity P
        (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O) *
          Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O)) = _
      rw [directOrbitSquareRefinement_principal_ideal_scalar_split t]
      exact hscalar_emult
    have hquot_emult : emultiplicity (P : Ideal O) (quotientSquareIdeal t) =
        (t.powerSplit.gapSplit.a.factorization q : ℕ∞) := by
      rw [emultiplicity_mul hPprime', hgap_zero] at hprod_emult
      simpa using hprod_emult
    exact
      ⟨⟨hquot, multiplicity_eq_of_emultiplicity_eq_some hgap_zero,
          multiplicity_eq_of_emultiplicity_eq_some hquot_emult⟩,
        by intro h; exact hnotgap h.1⟩

end SevenRealCubic
end
end DkMath.FLT.Seven

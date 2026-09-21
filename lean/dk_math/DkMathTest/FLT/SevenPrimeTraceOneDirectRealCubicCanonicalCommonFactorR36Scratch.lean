import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCanonicalCommonFactor
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Factorization

namespace DkMath.FLT.Seven.SevenRealCubic

noncomputable section

open SevenRealCubicInt
open scoped NumberField Pointwise

#check Ideal.natAbs_pow_inertiaDeg
#check Ideal.absNorm_eq_one_iff
#check Ideal.exists_isMaximal_dvd_of_dvd_absNorm'
#check Ideal.absNorm_dvd_absNorm_of_le
#check IsDedekindDomain.HeightOneSpectrum.factorization_eq_multiplicity
#check Ideal.finprod_heightOneSpectrum_factorization
#check map_mul
#check FiniteMultiplicity.exists_eq_pow_mul_and_not_dvd
#check FiniteMultiplicity.pow
#check multiplicity_pos_of_dvd
#check Nat.factorization_pow
#check Nat.factorization_eq_zero_of_not_dvd
#check Nat.Prime.factorization_self
#check IsCoprime.pow_left
#check IsCoprime.pow_right

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
    Ideal.absNorm P = q := by
  let : P.IsPrime := hPprime
  let : P.LiesOver (Ideal.span {(q : ℤ)}) := hPover
  have hqZ : Prime (q : ℤ) :=
    Int.prime_iff_natAbs_prime.mpr (by simpa using hq)
  have hbase0 : Ideal.span {(q : ℤ)} ≠ (⊥ : Ideal ℤ) := by
    simpa using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hP0 : P ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  have hinertia : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg
      (Ideal.span {(q : ℤ)}) P Gal(Field / ℚ)]
    exact (common_norm_prime_complete_split t hq hqR hqS).2.2.2
  have hpow := Ideal.natAbs_pow_inertiaDeg (q : ℤ) P
  rw [hinertia, pow_one] at hpow
  exact hpow.symm

example
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    ∃ P J : Ideal O,
      P.IsMaximal ∧
      P.LiesOver (Ideal.span {(q : ℤ)}) ∧
      gapSquareIdeal t = P ^ t.powerSplit.gapSplit.a.factorization q * J ∧
      ¬q ∣ Ideal.absNorm J := by
  have hqR' : q ∣ Ideal.absNorm (gapSquareIdeal t) := by
    change q ∣ Ideal.absNorm
      (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O))
    rw [directOrbitSquareRefinement_absNorm_span_model]
    exact hqR
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq (gapSquareIdeal t) hqR'
  have hPover : P.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hPunder.symm⟩
  have hbase0 : Ideal.span {(q : ℤ)} ≠ (⊥ : Ideal ℤ) := by
    simpa using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hP0 : P ≠ ⊥ := by
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 P
  have hgap0 : gapSquareIdeal t ≠ ⊥ := by
    intro h
    have hm : modelEquivRingOfIntegers t.gapSquareRoot ∈ (⊥ : Ideal O) := by
      rw [← h]
      exact Ideal.mem_span_singleton_self _
    have hm0 : modelEquivRingOfIntegers t.gapSquareRoot = 0 := by
      simpa using hm
    have : t.gapSquareRoot = 0 := by
      apply modelEquivRingOfIntegers.injective
      simpa using hm0
    exact directOrbit_squareTwist_squareRoot_ne_zero t this
  have hPprime : P.IsPrime := hPmax.isPrime
  have hPprime' : Prime P := Ideal.prime_of_isPrime hP0 hPprime
  have hfin : FiniteMultiplicity P (gapSquareIdeal t) :=
    FiniteMultiplicity.of_prime_left hPprime' hgap0
  obtain ⟨J, hJ, hJnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hPmem : P ∈
      {Q | Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O ∧
        gapSquareIdeal t ≤ Q} := by
    exact ⟨⟨hPprime, hPover⟩, Ideal.dvd_iff_le.mp hPdiv⟩
  have hPalloc := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
    t hq hqR hqS P hPprime hPover
  have hPmult : multiplicity P (gapSquareIdeal t) =
      t.powerSplit.gapSplit.a.factorization q := by
    rcases hPalloc with ⟨⟨_, hmult, _⟩, _⟩ | ⟨⟨_, hzero, _⟩, _⟩
    · exact hmult
    · have hpos := multiplicity_pos_of_dvd hPdiv hfin
      rw [hzero] at hpos
      exact (Nat.not_lt_zero _ hpos).elim
  have hPcenter : ∀ {Q : Ideal O},
      Q ∈ {Q | Q ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) O ∧
        gapSquareIdeal t ≤ Q} → Q = P := by
    intro Q hQmem
    obtain ⟨P0, hset⟩ := Set.ncard_eq_one.mp
      (directOrbitSquareRefinement_common_prime_gap_ncard t hq hqR hqS)
    have hP0eq : P0 = P := by
      have : P ∈ ({P0} : Set (Ideal O)) := by
        rw [← hset]
        exact hPmem
      simpa using this.symm
    have hQ0eq : Q ∈ ({P0} : Set (Ideal O)) := by
      rw [← hset]
      exact hQmem
    have hQP0 : Q = P0 := by simpa using hQ0eq
    exact hQP0.trans hP0eq
  have hqfree : ¬q ∣ Ideal.absNorm J := by
    intro hqJ
    obtain ⟨Q, hQmax, hQunder, hQdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq J hqJ
    have hQover : Q.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hQunder.symm⟩
    have hQprime : Q.IsPrime := hQmax.isPrime
    have hQdivI : Q ∣ gapSquareIdeal t := by
      rw [hJ]
      exact dvd_mul_of_dvd_right hQdiv _
    have hx := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
      t hq hqR hqS Q hQprime hQover
    rcases hx with ⟨⟨hQgap, _, _⟩, _⟩ | ⟨⟨_, hQzero, _⟩, _⟩
    · have hQP : Q = P := hPcenter
        ⟨⟨hQprime, hQover⟩, hQgap⟩
      exact hJnot (by simpa [hQP] using hQdiv)
    · have hQ0 : Q ≠ ⊥ :=
        Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 Q
      have hQprime' : Prime Q := Ideal.prime_of_isPrime hQ0 hQprime
      have hQfin : FiniteMultiplicity Q (gapSquareIdeal t) :=
        FiniteMultiplicity.of_prime_left hQprime' hgap0
      have hQpos := multiplicity_pos_of_dvd hQdivI hQfin
      rw [hQzero] at hQpos
      exact (Nat.not_lt_zero _ hQpos).elim
  exact ⟨P, J, hPmax, hPover, by simpa [hPmult] using hJ, hqfree⟩

example
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    (Int.natAbs (norm t.gapSquareRoot)).factorization q =
      t.powerSplit.gapSplit.a.factorization q := by
  obtain ⟨P, J, hPmax, hPover, hEq, hqfree⟩ :=
    directOrbitCanonicalCommonFactor_gap_qPrimary_residual
      t hq hqR hqS
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have hgap0 : gapSquareIdeal t ≠ ⊥ := by
      intro h
      have hm : modelEquivRingOfIntegers t.gapSquareRoot ∈ (⊥ : Ideal O) := by
        rw [← h]
        exact Ideal.mem_span_singleton_self _
      have hm0 : modelEquivRingOfIntegers t.gapSquareRoot = 0 := by
        simpa using hm
      have hz : t.gapSquareRoot = 0 := by
        apply modelEquivRingOfIntegers.injective
        simpa using hm0
      exact directOrbit_squareTwist_squareRoot_ne_zero t hz
    apply hgap0
    have hzero : gapSquareIdeal t = ⊥ := by
      simpa [hJ] using hEq
    exact hzero
  have hnormJ0 : Ideal.absNorm J ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr hJ0
  have hnormP := directOrbitCanonicalCommonFactor_prime_absNorm
    t hq hqR hqS P hPmax.isPrime hPover
  have hnormI : Ideal.absNorm (gapSquareIdeal t) =
      q ^ t.powerSplit.gapSplit.a.factorization q * Ideal.absNorm J := by
    have h := congrArg Ideal.absNorm hEq
    rw [map_mul, map_pow, hnormP] at h
    exact h
  have hfac : (Ideal.absNorm (gapSquareIdeal t)).factorization q =
      (q ^ t.powerSplit.gapSplit.a.factorization q).factorization q +
        (Ideal.absNorm J).factorization q := by
    rw [hnormI, Nat.factorization_mul
      (pow_ne_zero _ hq.ne_zero) hnormJ0]
    rfl
  have hfacJ : (Ideal.absNorm J).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqfree
  have hfacPow :
      (q ^ t.powerSplit.gapSplit.a.factorization q).factorization q =
        t.powerSplit.gapSplit.a.factorization q := by
    exact Nat.factorization_pow_self hq
  change (Ideal.absNorm
    (Ideal.span ({modelEquivRingOfIntegers t.gapSquareRoot} : Set O))).factorization q = _
    at hfac
  rw [directOrbitSquareRefinement_absNorm_span_model] at hfac
  rw [hfacJ, hfacPow, add_zero] at hfac
  exact hfac

example
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    ∃ A B J : Ideal O,
      A.IsPrime ∧ B.IsPrime ∧
      A.LiesOver (Ideal.span {(q : ℤ)}) ∧
      B.LiesOver (Ideal.span {(q : ℤ)}) ∧
      A ≠ B ∧
      quotientSquareIdeal t =
        (A ^ t.powerSplit.gapSplit.a.factorization q) *
          (B ^ t.powerSplit.gapSplit.a.factorization q) * J ∧
      ¬q ∣ Ideal.absNorm J := by
  let base : Ideal ℤ := Ideal.span {(q : ℤ)}
  have hbase0 : base ≠ (⊥ : Ideal ℤ) := by
    simpa [base] using (Int.ofNat_ne_zero.mpr hq.ne_zero)
  have hHcard : ({Q | Q ∈ Ideal.primesOver base O ∧
      quotientSquareIdeal t ≤ Q} : Set (Ideal O)).ncard = 2 := by
    simpa [base] using
      directOrbitSquareRefinement_common_prime_quotient_ncard t hq hqR hqS
  obtain ⟨A, B, hAB, hHset⟩ := Set.ncard_eq_two.mp hHcard
  have hAmem' : A ∈ ({Q | Q ∈ Ideal.primesOver base O ∧
      quotientSquareIdeal t ≤ Q} : Set (Ideal O)) := by
    rw [hHset]
    simp
  have hBmem' : B ∈ ({Q | Q ∈ Ideal.primesOver base O ∧
      quotientSquareIdeal t ≤ Q} : Set (Ideal O)) := by
    rw [hHset]
    simp
  have hAmem : A ∈ Ideal.primesOver base O ∧ quotientSquareIdeal t ≤ A := hAmem'
  have hBmem : B ∈ Ideal.primesOver base O ∧ quotientSquareIdeal t ≤ B := hBmem'
  have hAprime : A.IsPrime := hAmem.1.1
  have hBprime : B.IsPrime := hBmem.1.1
  have hAover : A.LiesOver base := hAmem.1.2
  have hBover : B.LiesOver base := hBmem.1.2
  have hA0 : A ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 A
  have hB0 : B ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hbase0 B
  have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
    intro h
    have hm : modelEquivRingOfIntegers t.quotientSquareRoot ∈ (⊥ : Ideal O) := by
      rw [← h]
      exact Ideal.mem_span_singleton_self _
    have hm0 : modelEquivRingOfIntegers t.quotientSquareRoot = 0 := by
      simpa using hm
    have hz : t.quotientSquareRoot = 0 := by
      apply modelEquivRingOfIntegers.injective
      simpa using hm0
    exact directOrbitSquareRefinement_quotient_square_norm_pos t |>.ne'
      (by simp [hz, SevenRealCubicInt.norm])
  have hAfin : FiniteMultiplicity A (quotientSquareIdeal t) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime hA0 hAprime) hquot0
  have hBfin : FiniteMultiplicity B (quotientSquareIdeal t) :=
    FiniteMultiplicity.of_prime_left
      (Ideal.prime_of_isPrime hB0 hBprime) hquot0
  have hAmult : multiplicity A (quotientSquareIdeal t) =
      t.powerSplit.gapSplit.a.factorization q := by
    have hx := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
      t hq hqR hqS A hAprime hAover
    rcases hx with ⟨⟨_, _, hzero⟩, _⟩ | ⟨⟨_, _, hmult⟩, _⟩
    · have hpos := multiplicity_pos_of_dvd
        (Ideal.dvd_iff_le.mpr hAmem.2) hAfin
      rw [hzero] at hpos
      exact (Nat.not_lt_zero _ hpos).elim
    · exact hmult
  have hBmult : multiplicity B (quotientSquareIdeal t) =
      t.powerSplit.gapSplit.a.factorization q := by
    have hx := directOrbitCanonicalCommonFactor_allocated_ideal_multiplicities
      t hq hqR hqS B hBprime hBover
    rcases hx with ⟨⟨_, _, hzero⟩, _⟩ | ⟨⟨_, _, hmult⟩, _⟩
    · have hpos := multiplicity_pos_of_dvd
        (Ideal.dvd_iff_le.mpr hBmem.2) hBfin
      rw [hzero] at hpos
      exact (Nat.not_lt_zero _ hpos).elim
    · exact hmult
  have hAdiv : A ^ t.powerSplit.gapSplit.a.factorization q ∣
      quotientSquareIdeal t := by
    exact pow_dvd_of_le_multiplicity (hAmult ▸ le_rfl)
  have hBdiv : B ^ t.powerSplit.gapSplit.a.factorization q ∣
      quotientSquareIdeal t := by
    exact pow_dvd_of_le_multiplicity (hBmult ▸ le_rfl)
  let : A.IsMaximal := hAprime.isMaximal hA0
  let : B.IsMaximal := hBprime.isMaximal hB0
  have hcop : IsCoprime A B := Ideal.isCoprime_of_isMaximal hAB
  have hcopPow : IsCoprime
      (A ^ t.powerSplit.gapSplit.a.factorization q) B := hcop.pow_left
  have hcopPow' : IsCoprime
      (A ^ t.powerSplit.gapSplit.a.factorization q)
      (B ^ t.powerSplit.gapSplit.a.factorization q) := hcopPow.pow_right
  obtain ⟨J, hJ⟩ := hcopPow'.mul_dvd hAdiv hBdiv
  have hJ0 : J ≠ ⊥ := by
    intro hJ0
    have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
      intro h
      have hm : modelEquivRingOfIntegers t.quotientSquareRoot ∈ (⊥ : Ideal O) := by
        rw [← h]
        exact Ideal.mem_span_singleton_self _
      have hm0 : modelEquivRingOfIntegers t.quotientSquareRoot = 0 := by
        simpa using hm
      have hz : t.quotientSquareRoot = 0 := by
        apply modelEquivRingOfIntegers.injective
        simpa using hm0
      exact directOrbitSquareRefinement_quotient_square_norm_pos t |>.ne'
        (by simp [hz, SevenRealCubicInt.norm])
    apply hquot0
    simpa [hJ0] using hJ
  have hAnot : ¬A ^ (t.powerSplit.gapSplit.a.factorization q + 1) ∣
      quotientSquareIdeal t := by
    apply hAfin.not_pow_dvd_of_multiplicity_lt
    rw [hAmult]
    exact Nat.lt_succ_self _
  have hBnot : ¬B ^ (t.powerSplit.gapSplit.a.factorization q + 1) ∣
      quotientSquareIdeal t := by
    apply hBfin.not_pow_dvd_of_multiplicity_lt
    rw [hBmult]
    exact Nat.lt_succ_self _
  have hAres : ¬A ∣ J := by
    intro hAJ
    obtain ⟨K, hK⟩ := hAJ
    apply hAnot
    rw [hJ, hK, pow_succ]
    exact ⟨B ^ t.powerSplit.gapSplit.a.factorization q * K, by ac_rfl⟩
  have hBres : ¬B ∣ J := by
    intro hBJ
    obtain ⟨K, hK⟩ := hBJ
    apply hBnot
    rw [hJ, hK, pow_succ]
    exact ⟨A ^ t.powerSplit.gapSplit.a.factorization q * K, by
      simp [mul_assoc, mul_comm, mul_left_comm]⟩
  have hqfree : ¬q ∣ Ideal.absNorm J := by
    intro hqJ
    obtain ⟨Q, hQmax, hQunder, hQdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hq J hqJ
    have hQover : Q.LiesOver base := ⟨hQunder.symm⟩
    have hQdivI : Q ∣ quotientSquareIdeal t := by
      rw [hJ]
      exact dvd_mul_of_dvd_right hQdiv _
    have hQmem : Q ∈ ({A, B} : Set (Ideal O)) := by
      have : Q ∈ ({Q | Q ∈ Ideal.primesOver base O ∧
          quotientSquareIdeal t ≤ Q} : Set (Ideal O)) :=
        ⟨⟨hQmax.isPrime, hQover⟩, Ideal.dvd_iff_le.mp hQdivI⟩
      rw [hHset] at this
      simpa using this
    rcases hQmem with hQA | hQB
    · subst Q
      exact hAres hQdiv
    · subst Q
      exact hBres hQdiv
  exact ⟨A, B, J, hAprime, hBprime, hAover, hBover, hAB, hJ, hqfree⟩

example
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    (Int.natAbs (norm t.quotientSquareRoot)).factorization q =
      2 * t.powerSplit.gapSplit.a.factorization q := by
  obtain ⟨A, B, J, hAprime, hBprime, hAover, hBover, hAB, hEq, hqfree⟩ :=
    directOrbitCanonicalCommonFactor_quotient_qPrimary_residual
      t hq hqR hqS
  have hJ0 : J ≠ ⊥ := by
    intro hJ
    have hquot0 : quotientSquareIdeal t ≠ ⊥ := by
      intro h
      have hm : modelEquivRingOfIntegers t.quotientSquareRoot ∈ (⊥ : Ideal O) := by
        rw [← h]
        exact Ideal.mem_span_singleton_self _
      have hm0 : modelEquivRingOfIntegers t.quotientSquareRoot = 0 := by
        simpa using hm
      have hz : t.quotientSquareRoot = 0 := by
        apply modelEquivRingOfIntegers.injective
        simpa using hm0
      exact directOrbitSquareRefinement_quotient_square_norm_pos t |>.ne'
        (by simp [hz, SevenRealCubicInt.norm])
    apply hquot0
    simpa [hJ] using hEq
  have hnormJ0 : Ideal.absNorm J ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr hJ0
  have hnormA := directOrbitCanonicalCommonFactor_prime_absNorm
    t hq hqR hqS A hAprime hAover
  have hnormB := directOrbitCanonicalCommonFactor_prime_absNorm
    t hq hqR hqS B hBprime hBover
  let m := t.powerSplit.gapSplit.a.factorization q
  have hnormI : Ideal.absNorm (quotientSquareIdeal t) =
      q ^ (2 * m) * Ideal.absNorm J := by
    have h := congrArg Ideal.absNorm hEq
    rw [map_mul, map_mul, map_pow, map_pow, hnormA, hnormB] at h
    calc
      Ideal.absNorm (quotientSquareIdeal t) = q ^ m * q ^ m * Ideal.absNorm J := h
      _ = q ^ (2 * m) * Ideal.absNorm J := by
        rw [← pow_add]
        have hm : m + m = 2 * m := by omega
        rw [hm]
  have hfac : (Ideal.absNorm (quotientSquareIdeal t)).factorization q =
      (q ^ (2 * m)).factorization q + (Ideal.absNorm J).factorization q := by
    rw [hnormI, Nat.factorization_mul
      (pow_ne_zero _ hq.ne_zero) hnormJ0]
    rfl
  have hfacJ : (Ideal.absNorm J).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hqfree
  have hfacPow : (q ^ (2 * m)).factorization q = 2 * m := by
    exact Nat.factorization_pow_self hq
  change (Ideal.absNorm
    (Ideal.span ({modelEquivRingOfIntegers t.quotientSquareRoot} : Set O))).factorization q = _
    at hfac
  rw [directOrbitSquareRefinement_absNorm_span_model] at hfac
  rw [hfacJ, hfacPow, add_zero] at hfac
  exact hfac

end
end DkMath.FLT.Seven.SevenRealCubic

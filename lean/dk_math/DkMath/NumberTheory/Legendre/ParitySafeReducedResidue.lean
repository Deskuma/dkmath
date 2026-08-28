/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.ParitySafeIncidenceBalance
import DkMath.NumberTheory.Legendre.Quotient

#print "file: DkMath.NumberTheory.Legendre.ParitySafeReducedResidue"

/-!
## ParitySafeReducedResidue

This module normalizes the parity-safe square-offset world by the modulus
`2 * n`.  Candidate seats become reduced residues of their complete points,
and an active prime wave is transported to complementary quotient factors in
a short interval.  The statements are finite arithmetic identities and
factorization frontiers; they do not provide a prime-counting estimate or a
proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive
open DkMath.NumberTheory.StructuralArithmetic
open scoped BigOperators

/-! ### PRIM-L037.1: reduced-residue candidate normalization -/

/-- Coprimality with `2 * n` is anchor coprimality plus oddness. -/
theorem coprime_two_mul_iff_coprime_and_odd
    {n x : ℕ} :
    Nat.Coprime (2 * n) x ↔ Nat.Coprime n x ∧ Odd x := by
  rw [Nat.coprime_comm, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hcop, htwo⟩
    exact ⟨htwo.symm, Nat.coprime_two_right.mp hcop⟩
  · rintro ⟨hcop, hodd⟩
    exact ⟨Nat.coprime_two_right.mpr hodd, hcop.symm⟩

/-- A parity-safe candidate is exactly a reduced residue of its complete point. -/
@[simp] theorem mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue
    {n r : ℕ} :
    r ∈ squareAnchorOddPointCoprimeOffsets n ↔
      SquareOffset n r ∧ Nat.Coprime (2 * n) (n ^ 2 + r) := by
  constructor
  · intro hr
    rcases mem_squareAnchorOddPointCoprimeOffsets.mp hr with ⟨hrc, hodd⟩
    rcases mem_squareAnchorCoprimeOffsets.mp hrc with ⟨hsq, hcop⟩
    have hpointcop : Nat.Coprime n (n ^ 2 + r) := by
      simpa [pow_two] using (Nat.coprime_mul_left_add_right n r n).mpr hcop
    exact ⟨hsq, coprime_two_mul_iff_coprime_and_odd.mpr ⟨
      hpointcop, hodd⟩⟩
  · rintro ⟨hsq, hred⟩
    have hparts := coprime_two_mul_iff_coprime_and_odd.mp hred
    apply mem_squareAnchorOddPointCoprimeOffsets.mpr
    exact ⟨mem_squareAnchorCoprimeOffsets.mpr ⟨hsq,
      (Nat.coprime_mul_left_add_right n r n).mp (by simpa [pow_two] using hparts.1)⟩,
      hparts.2⟩

/-! ### PRIM-L037.2: exact candidate cardinality -/

/-- The parity-safe candidate window has the reduced-residue cardinality
`Nat.totient (2 * n)`. -/
theorem card_squareAnchorOddPointCoprimeOffsets_eq_totient_two_mul
    {n : ℕ} (_hn : 0 < n) :
    (squareAnchorOddPointCoprimeOffsets n).card = Nat.totient (2 * n) := by
  classical
  let t : Finset ℕ :=
    (Finset.Ico (n ^ 2 + 1) (n ^ 2 + 1 + 2 * n)).filter
      (fun x => Nat.Coprime (2 * n) x)
  have hcard : (squareAnchorOddPointCoprimeOffsets n).card = t.card := by
    apply Finset.card_bij (fun r _ => n ^ 2 + r)
    · intro r hr
      have hr' := (mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp hr)
      change n ^ 2 + r ∈ t
      dsimp [t]
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨?_, hr'.2⟩
      dsimp [SquareOffset] at hr'
      omega
    · intro r₁ hr₁ r₂ hr₂ heq
      omega
    · intro x hx
      have hx' := Finset.mem_filter.mp (show x ∈ t from hx)
      have hxIco : n ^ 2 + 1 ≤ x ∧ x < n ^ 2 + 1 + 2 * n :=
        Finset.mem_Ico.mp hx'.1
      refine ⟨x - n ^ 2, ?_, ?_⟩
      · apply mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mpr
        refine ⟨?_, ?_⟩
        · dsimp [SquareOffset]
          constructor <;> omega
        · have hsum : n ^ 2 + (x - n ^ 2) = x := by
            rw [Nat.add_sub_of_le]
            omega
          rw [hsum]
          exact hx'.2
      · omega
  calc
    (squareAnchorOddPointCoprimeOffsets n).card = t.card := hcard
    _ = Nat.totient (2 * n) := by
      dsimp [t]
      exact Nat.filter_coprime_Ico_eq_totient (2 * n) (n ^ 2 + 1)

/-! ### PRIM-L037.3: active primes as reduced residues -/

/- A small packet of facts carried by an active-prime membership proof. -/
theorem activePrime_reducedResidue_packet
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    Nat.Prime q ∧ q ≤ n ∧ ¬ q ∣ n ∧ q ≠ 2 ∧ Nat.Coprime (2 * n) q := by
  have hq' := mem_squareAnchorOddActivePrimes.mp hq
  refine ⟨hq'.1, hq'.2.1, hq'.2.2.1, hq'.2.2.2, ?_⟩
  rw [Nat.coprime_comm, Nat.coprime_mul_iff_right]
  exact ⟨Nat.coprime_two_right.mpr (hq'.1.odd_of_ne_two hq'.2.2.2),
    hq'.1.coprime_iff_not_dvd.mpr hq'.2.2.1⟩

/-! ### PRIM-L037.4: quotient transfer -/

/-- An active parity-safe wave hit has a reduced-residue complementary factor. -/
theorem paritySafeActiveWaveOffsets_quotient_properties
    {n q r : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n)
    (hr : r ∈ paritySafeActiveWaveOffsets n q) :
    n < squareOffsetSupportQuotient n q r ∧
      Nat.Coprime (2 * n) (squareOffsetSupportQuotient n q r) ∧
      Odd (squareOffsetSupportQuotient n q r) ∧
      q * squareOffsetSupportQuotient n q r = n ^ 2 + r := by
  have hr' := mem_paritySafeActiveWaveOffsets.mp hr
  have hq' := activePrime_reducedResidue_packet hq
  have hqdiv : q ∣ n ^ 2 + r := hr'.2
  have hquot := coprime_anchor_squareOffsetSupportQuotient_iff
    hq'.1 hq'.2.2.1 hqdiv
  have hnr : Nat.Coprime n r :=
    coprime_of_mem_squareAnchorOddPointCoprimeOffsets hr'.1
  have hnk : Nat.Coprime n (squareOffsetSupportQuotient n q r) := hquot.mpr hnr
  have hoddPoint := (mem_squareAnchorOddPointCoprimeOffsets.mp hr'.1).2
  have hfactor := mul_squareOffsetSupportQuotient_eq hqdiv
  have hoddK : Odd (squareOffsetSupportQuotient n q r) := by
    apply Nat.Odd.of_mul_right
    rw [hfactor]
    exact hoddPoint
  refine ⟨anchor_lt_squareOffsetSupportQuotient
      (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr'.1)
      hq'.2.1 hqdiv, ?_, hoddK, ?_⟩
  · exact (coprime_two_mul_iff_coprime_and_odd).mpr ⟨hnk, hoddK⟩
  · exact mul_squareOffsetSupportQuotient_eq hqdiv

/-! ### PRIM-L037.5: the reduced quotient interval -/

/-- Reduced residues in the quotient interval corresponding to one wave. -/
noncomputable def paritySafeReducedQuotientInterval
    (n q : ℕ) : Finset ℕ :=
  (Finset.Ioc ((n ^ 2) / q) ((n ^ 2 + 2 * n) / q)).filter
    (fun k => Nat.Coprime (2 * n) k)

/-- Membership in the quotient interval is the intended product window plus
the reduced-residue condition. -/
theorem mem_paritySafeReducedQuotientInterval_iff
    {n q k : ℕ} (hqpos : 0 < q) :
    k ∈ paritySafeReducedQuotientInterval n q ↔
      n ^ 2 < q * k ∧ q * k ≤ n ^ 2 + 2 * n ∧
        Nat.Coprime (2 * n) k := by
  rw [paritySafeReducedQuotientInterval]
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  rw [Nat.div_lt_iff_lt_mul hqpos, Nat.le_div_iff_mul_le hqpos]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, hcop⟩
    exact ⟨by simpa [Nat.mul_comm] using h₁,
      by simpa [Nat.mul_comm] using h₂, hcop⟩
  · rintro ⟨h₁, h₂, hcop⟩
    exact ⟨⟨by simpa [Nat.mul_comm] using h₁,
      by simpa [Nat.mul_comm] using h₂⟩, hcop⟩

/-- Every parity-safe active-wave hit maps into its reduced quotient interval. -/
theorem paritySafeActiveWaveOffsets_quotient_mem_interval
    {n q r : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n)
    (hr : r ∈ paritySafeActiveWaveOffsets n q) :
    squareOffsetSupportQuotient n q r ∈
      paritySafeReducedQuotientInterval n q := by
  have hq' := activePrime_reducedResidue_packet hq
  have hprops := paritySafeActiveWaveOffsets_quotient_properties hq hr
  have hsq := (mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp
    (mem_paritySafeActiveWaveOffsets.mp hr).1).1
  dsimp [SquareOffset] at hsq
  apply (mem_paritySafeReducedQuotientInterval_iff hq'.1.pos).mpr
  refine ⟨?_, ?_, hprops.2.1⟩
  · rw [hprops.2.2.2]
    omega
  · rw [hprops.2.2.2]
    omega

/-! ### PRIM-L037.6: quotient interval inverse -/

/-- An interval quotient reconstructs a parity-safe wave seat. -/
theorem paritySafeReducedQuotientInterval_mem_wave
    {n q k : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n)
    (hk : k ∈ paritySafeReducedQuotientInterval n q) :
    q * k - n ^ 2 ∈ paritySafeActiveWaveOffsets n q ∧
      squareOffsetSupportQuotient n q (q * k - n ^ 2) = k := by
  have hq' := activePrime_reducedResidue_packet hq
  have hk' := mem_paritySafeReducedQuotientInterval_iff hq'.1.pos |>.mp hk
  let r := q * k - n ^ 2
  have hlow : n ^ 2 ≤ q * k := le_of_lt hk'.1
  have hsum : n ^ 2 + r = q * k := by
    dsimp [r]
    rw [Nat.add_sub_of_le hlow]
  have hdiv : q ∣ n ^ 2 + r := by
    refine ⟨k, ?_⟩
    rw [hsum]
  have hquot : squareOffsetSupportQuotient n q r = k := by
    unfold squareOffsetSupportQuotient
    apply Nat.div_eq_of_eq_mul_left hq'.1.pos
    simpa [Nat.mul_comm] using hsum
  have hcopK : Nat.Coprime n k :=
    (coprime_two_mul_iff_coprime_and_odd.mp hk'.2.2).1
  have hcopR : Nat.Coprime n r := by
    have htransfer := coprime_anchor_squareOffsetSupportQuotient_iff
      hq'.1 hq'.2.2.1 hdiv
    rw [hquot] at htransfer
    exact htransfer.mp hcopK
  have hoddK : Odd k :=
    (coprime_two_mul_iff_coprime_and_odd.mp hk'.2.2).2
  have hoddQ : Odd q := hq'.1.odd_of_ne_two hq'.2.2.2.1
  have hoddPoint : Odd (n ^ 2 + r) := by
    rw [hsum]
    exact hoddQ.mul hoddK
  have hsq : SquareOffset n r := by
    dsimp [SquareOffset]
    constructor <;> omega
  have hwave : r ∈ paritySafeActiveWaveOffsets n q := by
    apply mem_paritySafeActiveWaveOffsets.mpr
    exact ⟨mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mpr
      ⟨hsq, coprime_two_mul_iff_coprime_and_odd.mpr
        ⟨by simpa [pow_two] using
          (Nat.coprime_mul_left_add_right n r n).mpr hcopR, hoddPoint⟩⟩,
      hdiv⟩
  exact ⟨hwave, hquot⟩

/-- The support quotient gives a bijective cardinality correspondence between
an active wave and its reduced quotient interval. -/
theorem card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval
    {n q : ℕ} (hq : q ∈ squareAnchorOddActivePrimes n) :
    (paritySafeActiveWaveOffsets n q).card =
      (paritySafeReducedQuotientInterval n q).card := by
  classical
  apply Finset.card_bij (fun r _ => squareOffsetSupportQuotient n q r)
  · intro r hr
    exact paritySafeActiveWaveOffsets_quotient_mem_interval hq hr
  · intro r₁ hr₁ r₂ hr₂ heq
    have h₁ := paritySafeActiveWaveOffsets_quotient_properties hq hr₁
    have h₂ := paritySafeActiveWaveOffsets_quotient_properties hq hr₂
    have hpoint : n ^ 2 + r₁ = n ^ 2 + r₂ := by
      calc
        n ^ 2 + r₁ = q * squareOffsetSupportQuotient n q r₁ := h₁.2.2.2.symm
        _ = q * squareOffsetSupportQuotient n q r₂ := by rw [heq]
        _ = n ^ 2 + r₂ := h₂.2.2.2
    omega
  · intro k hk
    let r := q * k - n ^ 2
    have hback := paritySafeReducedQuotientInterval_mem_wave hq hk
    refine ⟨r, ?_, ?_⟩
    · simpa [r] using hback.1
    · simpa [r] using hback.2

/-! ### PRIM-L037.7: quotient rigidity and incidence rewrite -/

/-- Distinct seats in one active wave form an even-separated quotient
progression.  The theorem records divisibility, not false exact adjacency. -/
theorem paritySafeActiveWave_same_wave_quotient_rigidity
    {n q r s : ℕ}
    (hq : q ∈ squareAnchorOddActivePrimes n)
    (hr : r ∈ paritySafeActiveWaveOffsets n q)
    (hs : s ∈ paritySafeActiveWaveOffsets n q)
    (hrs : r < s) :
    q ∣ s - r ∧
      2 * q ∣ s - r ∧
      squareOffsetSupportQuotient n q r <
        squareOffsetSupportQuotient n q s ∧
      2 ≤ squareOffsetSupportQuotient n q s -
        squareOffsetSupportQuotient n q r ∧
      Even (squareOffsetSupportQuotient n q s -
        squareOffsetSupportQuotient n q r) ∧
      q * (squareOffsetSupportQuotient n q s -
        squareOffsetSupportQuotient n q r) = s - r := by
  have h₁ := paritySafeActiveWaveOffsets_quotient_properties hq hr
  have h₂ := paritySafeActiveWaveOffsets_quotient_properties hq hs
  have hqpos := (activePrime_reducedResidue_packet hq).1.pos
  have hlt : squareOffsetSupportQuotient n q r <
      squareOffsetSupportQuotient n q s := by
    apply (Nat.mul_lt_mul_left hqpos).mp
    omega
  have hodd₁ := h₁.2.2.1
  have hodd₂ := h₂.2.2.1
  have heven : Even (squareOffsetSupportQuotient n q s -
      squareOffsetSupportQuotient n q r) :=
    Nat.Odd.sub_odd hodd₂ hodd₁
  have hformula : q * (squareOffsetSupportQuotient n q s -
      squareOffsetSupportQuotient n q r) = s - r := by
    rw [Nat.mul_sub_left_distrib, h₁.2.2.2, h₂.2.2.2]
    omega
  have hqdiv : q ∣ s - r := by
    exact ⟨squareOffsetSupportQuotient n q s -
      squareOffsetSupportQuotient n q r, hformula.symm⟩
  have htwodiv : 2 * q ∣ s - r := by
    rcases (even_iff_two_dvd.mp heven) with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hformula, ht]
    ring
  have htwo : 2 ≤ squareOffsetSupportQuotient n q s -
      squareOffsetSupportQuotient n q r := by
    rcases (even_iff_two_dvd.mp heven) with ⟨t, ht⟩
    omega
  exact ⟨hqdiv, htwodiv, hlt, htwo, heven, hformula⟩

/-- The L036 incidence count is exactly the sum of reduced quotient-interval
cardinalities. -/
theorem paritySafeIncidenceCount_eq_reducedQuotientInterval_sum
    (n : ℕ) :
    paritySafeIncidenceCount n =
      ∑ q ∈ squareAnchorOddActivePrimes n,
        (paritySafeReducedQuotientInterval n q).card := by
  unfold paritySafeIncidenceCount
  apply Finset.sum_congr rfl
  intro q hq
  exact card_paritySafeActiveWaveOffsets_eq_reducedQuotientInterval hq

/-! ### PRIM-L037.8: full-cover factorization frontier -/

/-- Full cover of a parity-safe candidate supplies an active prime and a
reduced-residue complementary factor above the anchor. -/
theorem exists_activePrime_reducedQuotient_factorization_of_fullyCovered
    {n r : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n)
    (hfull : SquareOffsetsFullyCovered n) :
    ∃ q k, q ∈ squareAnchorOddActivePrimes n ∧
      Nat.Coprime (2 * n) q ∧ Nat.Coprime (2 * n) k ∧
      q ≤ n ∧ n < k ∧ q * k = n ^ 2 + r := by
  have hmem := mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mp hr
  have hn : 0 < n := by
    dsimp [SquareOffset] at hmem
    omega
  obtain ⟨q, hqprime, hql, hqdiv⟩ :=
    squareOffsetCovered_iff_exists_prime_dvd.mp (hfull r hmem.1)
  have hqne : ¬ q ∣ n := by
    intro hqn
    have hcopr : Nat.Coprime n r :=
      coprime_of_mem_squareAnchorOddPointCoprimeOffsets hr
    have hdivisor : SquareOffsetCoveredByAnchorDivisorPrime n r :=
      ⟨q, mem_squareAnchorDivisorPrimes.mpr ⟨hqprime, hql, hqn⟩, hqdiv⟩
    exact (squareOffsetCoveredByAnchorDivisorPrime_iff_not_coprime hn).mp
      hdivisor hcopr
  have hqactive : q ∈ squareAnchorOddActivePrimes n := by
    have hq2 : q ≠ 2 := by
      intro hqeq
      subst q
      exact (Nat.not_even_iff_odd.mpr
        (mem_squareAnchorOddPointCoprimeOffsets.mp hr).2)
        (even_iff_two_dvd.mpr hqdiv)
    exact mem_squareAnchorOddActivePrimes.mpr ⟨hqprime, hql, hqne, hq2⟩
  have hrwave : r ∈ paritySafeActiveWaveOffsets n q :=
    mem_paritySafeActiveWaveOffsets.mpr ⟨hr, hqdiv⟩
  have hprops := paritySafeActiveWaveOffsets_quotient_properties hqactive hrwave
  exact ⟨q, squareOffsetSupportQuotient n q r, hqactive,
    (activePrime_reducedResidue_packet hqactive).2.2.2.2,
    hprops.2.1, (activePrime_reducedResidue_packet hqactive).2.1,
    hprops.1, hprops.2.2.2⟩

end DkMath.NumberTheory.Legendre

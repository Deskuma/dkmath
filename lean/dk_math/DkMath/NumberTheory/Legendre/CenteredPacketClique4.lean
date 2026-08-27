/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredPacketDiamond

#print "file: DkMath.NumberTheory.Legendre.CenteredPacketClique4"

/-!
## CenteredPacketClique4

The shifted fourth seat `6 * k + 3` repairs the L026 parity collision for
the arithmetic four-point configuration.  The shell membership requires
`2 ≤ k`; the tempting weaker condition `0 < k` fails at `k = 1`.  Under
that corrected finite-shell condition and `Coprime (4 * k + 3) 15`, the
four complete points are pairwise coprime and full cover supplies four
distinct old-prime witnesses.  This remains a bounded structural result,
not a proof of Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive

/-! ### PRIM-L027.1: repaired fourth-seat shell membership -/

/-- The proposed positive-anchor shell claim fails at `k = 1`. -/
theorem not_squareOffset_centeredPacketClique4_at_one :
    ¬ SquareOffset 4 9 := by
  norm_num [SquareOffset]

/-- The repaired fourth seat lies in the shell once `2 ≤ k`. -/
theorem squareOffset_centeredPacketClique4_D
    {k : ℕ} (hk : 2 ≤ k) :
    SquareOffset (4 * k) (6 * k + 3) := by
  dsimp [SquareOffset]
  omega

/-! ### PRIM-L027.2: unconditional A/C coprimality -/

/-- The centered A/C complete points are coprime without a prime hypothesis. -/
theorem coprime_centeredPacketClique4_AC
    (k : ℕ) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
      ((4 * k) ^ 2 + (6 * k + 1)) := by
  by_contra hnot
  rcases (Nat.Prime.not_coprime_iff_dvd.mp hnot) with
    ⟨q, hq, hA, hC⟩
  have hpoint :
      (4 * k) ^ 2 + (6 * k + 1) =
        ((4 * k) ^ 2 + 2 * k) + (4 * k + 1) := by
    ring
  rw [hpoint] at hC
  have hg : q ∣ 4 * k + 1 :=
    (Nat.dvd_add_iff_right hA).mpr hC
  have hsum : q ∣
      2 * ((4 * k) ^ 2 + 2 * k) + (4 * k + 1) := by
    exact dvd_add (dvd_mul_of_dvd_right hA 2) hg
  have hidentity :
      2 * ((4 * k) ^ 2 + 2 * k) + (4 * k + 1) =
        (4 * k + 1) * (8 * k) + 1 := by
    ring
  rw [hidentity] at hsum
  have hprod : q ∣ (4 * k + 1) * (8 * k) :=
    dvd_mul_of_dvd_left hg (8 * k)
  have hone : q ∣ 1 := (Nat.dvd_add_iff_right hprod).mpr hsum
  exact hq.not_dvd_one hone

/-! ### PRIM-L027.3: C/D' coprimality -/

/-- The C/D' complete points are odd and differ by `2`, hence coprime. -/
theorem coprime_centeredPacketClique4_CD
    (k : ℕ) :
    Nat.Coprime ((4 * k) ^ 2 + (6 * k + 1))
      ((4 * k) ^ 2 + (6 * k + 3)) := by
  have hodd : Odd ((4 * k) ^ 2 + (6 * k + 1)) := by
    refine ⟨8 * k ^ 2 + 3 * k, ?_⟩
    ring
  have hcop2 : Nat.Coprime ((4 * k) ^ 2 + (6 * k + 1)) 2 :=
    Nat.coprime_two_right.mpr hodd
  have hpoint :
      (4 * k) ^ 2 + (6 * k + 3) =
        ((4 * k) ^ 2 + (6 * k + 1)) + 2 := by
    ring
  rw [hpoint]
  exact Nat.coprime_self_add_right.mpr hcop2

/-! ### PRIM-L027.4: B/D' coprimality -/

/-- The B/D' complete points are coprime for every `k`. -/
theorem coprime_centeredPacketClique4_BD
    {k : ℕ} :
    Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
      ((4 * k) ^ 2 + (6 * k + 3)) := by
  by_contra hnot
  rcases (Nat.Prime.not_coprime_iff_dvd.mp hnot) with
    ⟨q, hq, hB, hD⟩
  have hgap : q ∣ 4 * k + 2 := by
    have hpoint :
        (4 * k) ^ 2 + (6 * k + 3) =
          ((4 * k) ^ 2 + (2 * k + 1)) + (4 * k + 2) := by
      ring
    rw [hpoint] at hD
    exact (Nat.dvd_add_iff_right hB).mpr hD
  have hgap' : q ∣ 2 * (2 * k + 1) := by
    have heq : 4 * k + 2 = 2 * (2 * k + 1) := by ring
    rw [heq] at hgap
    exact hgap
  have hnot2 : ¬ 2 ∣ ((4 * k) ^ 2 + (2 * k + 1)) := by
    have hBodd : Odd ((4 * k) ^ 2 + (2 * k + 1)) := by
      refine ⟨8 * k ^ 2 + k, ?_⟩
      ring
    have hcopB2 : Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1)) 2 :=
      Nat.coprime_two_right.mpr hBodd
    intro h2
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨2, Nat.prime_two, h2, dvd_refl 2⟩) hcopB2
  rcases (Nat.Prime.dvd_mul hq).mp hgap' with hq2 | hqodd
  · have hqeq : q = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hq2).resolve_left hq.ne_one
    exact hnot2 (hqeq ▸ hB)
  · have hsum : q ∣
        ((4 * k) ^ 2 + (2 * k + 1)) + 3 * (2 * k + 1) := by
      exact dvd_add hB (dvd_mul_of_dvd_right hqodd 3)
    have hidentity :
        ((4 * k) ^ 2 + (2 * k + 1)) + 3 * (2 * k + 1) =
          (2 * k + 1) * (8 * k) + 4 := by
      ring
    rw [hidentity] at hsum
    have hprod : q ∣ (2 * k + 1) * (8 * k) :=
      dvd_mul_of_dvd_left hqodd (8 * k)
    have hfour : q ∣ 4 := (Nat.dvd_add_iff_right hprod).mpr hsum
    have hfour' : q ∣ 2 * 2 := by simpa using hfour
    rcases (Nat.Prime.dvd_mul hq).mp hfour' with hq2 | hq2
    · have hqeq : q = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp hq2).resolve_left hq.ne_one
      exact hnot2 (hqeq ▸ hB)
    · have hqeq : q = 2 :=
        ((Nat.dvd_prime Nat.prime_two).mp hq2).resolve_left hq.ne_one
      exact hnot2 (hqeq ▸ hB)

/-! ### PRIM-L027.5: A/D' constant-15 reduction -/

/-- A common prime divisor of A and D' divides the fixed constant `15`. -/
theorem common_centeredPacketClique4_AD_dvd_fifteen
    {k q : ℕ}
    (_hprime : Nat.Prime q)
    (hA : q ∣ (4 * k) ^ 2 + 2 * k)
    (hD : q ∣ (4 * k) ^ 2 + (6 * k + 3)) :
    q ∣ 4 * k + 3 ∧ q ∣ 15 := by
  have hpoint :
      (4 * k) ^ 2 + (6 * k + 3) =
        ((4 * k) ^ 2 + 2 * k) + (4 * k + 3) := by
    ring
  rw [hpoint] at hD
  have hg : q ∣ 4 * k + 3 := (Nat.dvd_add_iff_right hA).mpr hD
  have hsum : q ∣
      2 * ((4 * k) ^ 2 + 2 * k) + 5 * (4 * k + 3) := by
    exact dvd_add (dvd_mul_of_dvd_right hA 2)
      (dvd_mul_of_dvd_right hg 5)
  have hidentity :
      2 * ((4 * k) ^ 2 + 2 * k) + 5 * (4 * k + 3) =
        (4 * k + 3) * (8 * k) + 15 := by
    ring
  rw [hidentity] at hsum
  have hprod : q ∣ (4 * k + 3) * (8 * k) :=
    dvd_mul_of_dvd_left hg (8 * k)
  exact ⟨hg, (Nat.dvd_add_iff_right hprod).mpr hsum⟩

/-- The repaired A/D' complete points are coprime under the 15 condition. -/
theorem coprime_centeredPacketClique4_AD
    {k : ℕ}
    (hcop15 : Nat.Coprime (4 * k + 3) 15) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
      ((4 * k) ^ 2 + (6 * k + 3)) := by
  by_contra hnot
  rcases (Nat.Prime.not_coprime_iff_dvd.mp hnot) with
    ⟨q, hq, hA, hD⟩
  have hqg15 := common_centeredPacketClique4_AD_dvd_fifteen hq hA hD
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨q, hq, hqg15.1, hqg15.2⟩) hcop15

/-! ### PRIM-L027.6: pairwise coprimality and support separation -/

/-- The repaired four complete points are pairwise coprime. -/
theorem centeredPacketClique4_points_pairwise_coprime
    {k : ℕ}
    (hcop15 : Nat.Coprime (4 * k + 3) 15) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (2 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (6 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (6 * k + 3)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 3)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (6 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 3)) := by
  exact ⟨coprime_centeredPacketTriangle_AB k,
    coprime_centeredPacketClique4_AC k,
    coprime_centeredPacketClique4_AD hcop15,
    coprime_centeredPacketTriangle_BC k,
    coprime_centeredPacketClique4_BD,
    coprime_centeredPacketClique4_CD k⟩

/-- The four repaired-seat old-prime supports are pairwise disjoint. -/
theorem centeredPacketClique4_supports_pairwise_disjoint
    {k : ℕ}
    (hcop15 : Nat.Coprime (4 * k + 3) 15) :
    Disjoint (squareOffsetPrimeSupport (4 * k) (2 * k))
        (squareOffsetPrimeSupport (4 * k) (2 * k + 1)) ∧
      Disjoint (squareOffsetPrimeSupport (4 * k) (2 * k))
        (squareOffsetPrimeSupport (4 * k) (6 * k + 1)) ∧
      Disjoint (squareOffsetPrimeSupport (4 * k) (2 * k))
        (squareOffsetPrimeSupport (4 * k) (6 * k + 3)) ∧
      Disjoint (squareOffsetPrimeSupport (4 * k) (2 * k + 1))
        (squareOffsetPrimeSupport (4 * k) (6 * k + 1)) ∧
      Disjoint (squareOffsetPrimeSupport (4 * k) (2 * k + 1))
        (squareOffsetPrimeSupport (4 * k) (6 * k + 3)) ∧
      Disjoint (squareOffsetPrimeSupport (4 * k) (6 * k + 1))
        (squareOffsetPrimeSupport (4 * k) (6 * k + 3)) := by
  have h := centeredPacketClique4_points_pairwise_coprime hcop15
  exact ⟨
    disjoint_squareOffsetPrimeSupport_of_coprime_points h.1,
    disjoint_squareOffsetPrimeSupport_of_coprime_points h.2.1,
    disjoint_squareOffsetPrimeSupport_of_coprime_points h.2.2.1,
    disjoint_squareOffsetPrimeSupport_of_coprime_points h.2.2.2.1,
    disjoint_squareOffsetPrimeSupport_of_coprime_points h.2.2.2.2.1,
    disjoint_squareOffsetPrimeSupport_of_coprime_points h.2.2.2.2.2⟩

/-! ### PRIM-L027.7: full-cover four-distinct-witness consumer -/

/-- Full cover gives four pairwise-distinct old-prime witnesses for the repaired seats. -/
theorem exists_four_distinct_centeredPacketClique4_witnesses_of_fullyCovered
    {k : ℕ}
    (hk : 2 ≤ k)
    (hcop15 : Nat.Coprime (4 * k + 3) 15)
    (hfull : SquareOffsetsFullyCovered (4 * k)) :
    ∃ pA pB pC pD,
      pA ≠ pB ∧ pA ≠ pC ∧ pA ≠ pD ∧
      pB ≠ pC ∧ pB ≠ pD ∧ pC ≠ pD ∧
      pA ∈ squareOffsetPrimeSupport (4 * k) (2 * k) ∧
      pB ∈ squareOffsetPrimeSupport (4 * k) (2 * k + 1) ∧
      pC ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 1) ∧
      pD ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 3) := by
  have hA := squareOffset_centeredPacketTriangle_A (by omega : 0 < k)
  have hB := squareOffset_centeredPacketTriangle_B (by omega : 0 < k)
  have hC := squareOffset_centeredPacketTriangle_C (by omega : 0 < k)
  have hD := squareOffset_centeredPacketClique4_D hk
  obtain ⟨pA, hpA⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hA)
  obtain ⟨pB, hpB⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hB)
  obtain ⟨pC, hpC⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hC)
  obtain ⟨pD, hpD⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hD)
  have hdisj := centeredPacketClique4_supports_pairwise_disjoint hcop15
  refine ⟨pA, pB, pC, pD, ?_, ?_, ?_, ?_, ?_, ?_, hpA, hpB, hpC, hpD⟩
  · intro h; subst pB
    exact (Finset.disjoint_left.mp hdisj.1) hpA hpB
  · intro h; subst pC
    exact (Finset.disjoint_left.mp hdisj.2.1) hpA hpC
  · intro h; subst pD
    exact (Finset.disjoint_left.mp hdisj.2.2.1) hpA hpD
  · intro h; subst pC
    exact (Finset.disjoint_left.mp hdisj.2.2.2.1) hpB hpC
  · intro h; subst pD
    exact (Finset.disjoint_left.mp hdisj.2.2.2.2.1) hpB hpD
  · intro h; subst pD
    exact (Finset.disjoint_left.mp hdisj.2.2.2.2.2) hpC hpD

/-! ### PRIM-L027.8: an elementary periodic subfamily -/

/-- The repaired coprimality condition holds on the unbounded family `k = 15*t + 16`. -/
theorem coprime_four_mul_periodicClique4_family (t : ℕ) :
    Nat.Coprime (4 * (15 * t + 16) + 3) 15 := by
  have hbase : Nat.Coprime 67 15 := by norm_num
  have hperiod : Nat.Coprime (67 + (4 * t) * 15) 15 :=
    (Nat.coprime_add_mul_right_left 67 15 (4 * t)).mpr hbase
  have heq : 4 * (15 * t + 16) + 3 = 67 + (4 * t) * 15 := by
    ring
  rw [heq]
  exact hperiod

end DkMath.NumberTheory.Legendre

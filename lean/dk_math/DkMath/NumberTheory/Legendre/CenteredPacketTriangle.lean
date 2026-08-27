/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.CenteredPair

#print "file: DkMath.NumberTheory.Legendre.CenteredPacketTriangle"

/-!
## CenteredPacketTriangle

The three shell seats at anchor `4 * k` are `2 * k`, `2 * k + 1`, and
`6 * k + 1`.  Consecutive-point coprimality, packet coprimality, and the
centered odd-gap theorem meet on this triple.  The resulting API is a
finite three-seat structural refinement: it does not claim a contradiction
or prove Legendre's conjecture.
-/

namespace DkMath.NumberTheory.Legendre

open DkMath.NumberTheory.Primitive

/-! ### PRIM-L025.1: shell membership -/

/-- The first triangle seat is in the shell anchored at `4 * k`. -/
theorem squareOffset_centeredPacketTriangle_A
    {k : ℕ} (hk : 0 < k) :
    SquareOffset (4 * k) (2 * k) := by
  dsimp [SquareOffset]
  omega

/-- The second triangle seat is in the shell anchored at `4 * k`. -/
theorem squareOffset_centeredPacketTriangle_B
    {k : ℕ} (hk : 0 < k) :
    SquareOffset (4 * k) (2 * k + 1) := by
  dsimp [SquareOffset]
  omega

/-- The third triangle seat is in the shell anchored at `4 * k`. -/
theorem squareOffset_centeredPacketTriangle_C
    {k : ℕ} (hk : 0 < k) :
    SquareOffset (4 * k) (6 * k + 1) := by
  dsimp [SquareOffset]
  omega

/-! ### PRIM-L025.2: consecutive pair A/B -/

/-- The complete points at the consecutive seats A and B are coprime. -/
theorem coprime_centeredPacketTriangle_AB
    (k : ℕ) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
      ((4 * k) ^ 2 + (2 * k + 1)) := by
  have hcop : Nat.Coprime ((4 * k) ^ 2 + 2 * k)
      (((4 * k) ^ 2 + 2 * k) + 1) := by
    exact Nat.coprime_self_add_right.mpr (by simp)
  have hpoint :
      (4 * k) ^ 2 + (2 * k + 1) =
        ((4 * k) ^ 2 + 2 * k) + 1 := by
    omega
  rw [hpoint]
  exact hcop

/-! ### PRIM-L025.3: packet pair B/C -/

/-- The packet base `2 * k + 1` is coprime to the anchor `4 * k`. -/
theorem coprime_four_mul_k_two_mul_k_add_one
    (k : ℕ) :
    Nat.Coprime (4 * k) (2 * k + 1) := by
  have htwo : Nat.Coprime (2 * k + 1) 2 := by
    simp [Nat.mul_comm, Nat.add_comm]
  have htwoK : Nat.Coprime (2 * k + 1) (2 * k) := by
    simp [Nat.add_comm]
  have hprod : Nat.Coprime (2 * k + 1) ((2 * k) * 2) :=
    (Nat.coprime_mul_iff_right).mpr ⟨htwoK, htwo⟩
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprod.symm

/-- The complete points at the packet seats B and C are coprime. -/
theorem coprime_centeredPacketTriangle_BC
    (k : ℕ) :
    Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
      ((4 * k) ^ 2 + (6 * k + 1)) := by
  have h := coprime_squarePacketPoints_of_coprime_offset
    (n := 4 * k) (r := 2 * k + 1)
    (coprime_four_mul_k_two_mul_k_add_one k)
  have hsum : 4 * k + (2 * k + 1) = 6 * k + 1 := by
    ring
  rw [hsum] at h
  exact h

/-! ### PRIM-L025.4: centered pair A/C -/

/-- The centered prime gap cannot divide the left triangle point. -/
theorem not_four_mul_k_add_one_dvd_centeredPacketTriangle_A
    {k : ℕ} (hprime : Nat.Prime (4 * k + 1)) :
    ¬ (4 * k + 1) ∣ ((4 * k) ^ 2 + 2 * k) := by
  intro hdiv
  have hdouble : 4 * k + 1 ∣ 2 * ((4 * k) ^ 2 + 2 * k) := by
    exact dvd_mul_of_dvd_right hdiv 2
  have hsum : 4 * k + 1 ∣
      2 * ((4 * k) ^ 2 + 2 * k) + (4 * k + 1) := by
    exact dvd_add hdouble (dvd_refl _)
  have hidentity :
      2 * ((4 * k) ^ 2 + 2 * k) + (4 * k + 1) =
        (4 * k + 1) * (8 * k) + 1 := by
    ring
  rw [hidentity] at hsum
  have hone : 4 * k + 1 ∣ 1 :=
    (Nat.dvd_add_iff_right (dvd_mul_right (4 * k + 1) (8 * k))).mpr hsum
  exact hprime.not_dvd_one hone

/-- The complete points at the centered seats A and C are coprime. -/
theorem coprime_centeredPacketTriangle_AC
    {k : ℕ} (hprime : Nat.Prime (4 * k + 1)) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
      ((4 * k) ^ 2 + (6 * k + 1)) := by
  have hnot : ¬ (4 * k + 1) ∣ ((4 * k) ^ 2 + 2 * k) :=
    not_four_mul_k_add_one_dvd_centeredPacketTriangle_A hprime
  have hcopGap : Nat.Coprime (4 * k + 1)
      ((4 * k) ^ 2 + 2 * k) :=
    hprime.coprime_iff_not_dvd.mpr hnot
  have hcopLeft : Nat.Coprime ((4 * k) ^ 2 + 2 * k) (4 * k + 1) :=
    hcopGap.symm
  have hpoint :
      (4 * k) ^ 2 + (6 * k + 1) =
        ((4 * k) ^ 2 + 2 * k) + (4 * k + 1) := by
    ring
  rw [hpoint]
  exact Nat.coprime_self_add_right.mpr hcopLeft

/-! ### PRIM-L025.5: pairwise support disjointness -/

/-- Coprime complete points have disjoint old-prime support Finsets. -/
theorem disjoint_squareOffsetPrimeSupport_of_coprime_points
    {n r s : ℕ}
    (hcop : Nat.Coprime (n ^ 2 + r) (n ^ 2 + s)) :
    Disjoint (squareOffsetPrimeSupport n r)
      (squareOffsetPrimeSupport n s) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  have hp' := mem_squareOffsetPrimeSupport.mp hp
  have hq' := mem_squareOffsetPrimeSupport.mp hq
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp'.1, hp'.2.2, hq'.2.2⟩) hcop

/-- The three complete triangle points are pairwise coprime. -/
theorem centeredPacketTriangle_points_pairwise_coprime
    {k : ℕ} (hprime : Nat.Prime (4 * k + 1)) :
    Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (2 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + (2 * k + 1))
        ((4 * k) ^ 2 + (6 * k + 1)) ∧
      Nat.Coprime ((4 * k) ^ 2 + 2 * k)
        ((4 * k) ^ 2 + (6 * k + 1)) := by
  exact ⟨coprime_centeredPacketTriangle_AB k,
    coprime_centeredPacketTriangle_BC k,
    coprime_centeredPacketTriangle_AC hprime⟩

/-- The A/B support Finsets are disjoint. -/
theorem disjoint_centeredPacketTriangle_support_AB
    (k : ℕ) :
    Disjoint
      (squareOffsetPrimeSupport (4 * k) (2 * k))
      (squareOffsetPrimeSupport (4 * k) (2 * k + 1)) :=
  disjoint_squareOffsetPrimeSupport_of_coprime_points
    (coprime_centeredPacketTriangle_AB k)

/-- The B/C support Finsets are disjoint. -/
theorem disjoint_centeredPacketTriangle_support_BC
    (k : ℕ) :
    Disjoint
      (squareOffsetPrimeSupport (4 * k) (2 * k + 1))
      (squareOffsetPrimeSupport (4 * k) (6 * k + 1)) :=
  disjoint_squareOffsetPrimeSupport_of_coprime_points
    (coprime_centeredPacketTriangle_BC k)

/-- The A/C support Finsets are disjoint under the prime-gap hypothesis. -/
theorem disjoint_centeredPacketTriangle_support_AC
    {k : ℕ} (hprime : Nat.Prime (4 * k + 1)) :
    Disjoint
      (squareOffsetPrimeSupport (4 * k) (2 * k))
      (squareOffsetPrimeSupport (4 * k) (6 * k + 1)) :=
  disjoint_squareOffsetPrimeSupport_of_coprime_points
    (coprime_centeredPacketTriangle_AC hprime)

/-! ### PRIM-L025.6: full-cover three-witness consumer -/

/-- Full cover at `4 * k` supplies three pairwise-distinct old-prime witnesses. -/
theorem exists_three_distinct_centeredPacketTriangle_witnesses_of_fullyCovered
    {k : ℕ}
    (hk : 0 < k)
    (hprime : Nat.Prime (4 * k + 1))
    (hfull : SquareOffsetsFullyCovered (4 * k)) :
    ∃ p q ℓ,
      p ≠ q ∧
      p ≠ ℓ ∧
      q ≠ ℓ ∧
      p ∈ squareOffsetPrimeSupport (4 * k) (2 * k) ∧
      q ∈ squareOffsetPrimeSupport (4 * k) (2 * k + 1) ∧
      ℓ ∈ squareOffsetPrimeSupport (4 * k) (6 * k + 1) := by
  have hA := squareOffset_centeredPacketTriangle_A hk
  have hB := squareOffset_centeredPacketTriangle_B hk
  have hC := squareOffset_centeredPacketTriangle_C hk
  obtain ⟨p, hp⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hA)
  obtain ⟨q, hq⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hB)
  obtain ⟨ℓ, hℓ⟩ := squareOffsetCovered_iff_primeSupport_nonempty.mp
    (hfull _ hC)
  refine ⟨p, q, ℓ, ?_, ?_, ?_, hp, hq, hℓ⟩
  · intro hpq
    subst q
    exact (Finset.disjoint_left.mp
      (disjoint_centeredPacketTriangle_support_AB k)) hp hq
  · intro hpℓ
    subst ℓ
    exact (Finset.disjoint_left.mp
      (disjoint_centeredPacketTriangle_support_AC hprime)) hp hℓ
  · intro hqℓ
    subst ℓ
    exact (Finset.disjoint_left.mp
      (disjoint_centeredPacketTriangle_support_BC k)) hq hℓ

/-! ### PRIM-L025.7: finite-world cardinality consequence -/

/-- The three witnesses force at least three old prime directions. -/
theorem three_le_primeScalesUpTo_card_of_centeredPacketTriangle_fullyCovered
    {k : ℕ}
    (hk : 0 < k)
    (hprime : Nat.Prime (4 * k + 1))
    (hfull : SquareOffsetsFullyCovered (4 * k)) :
    3 ≤ (primeScalesUpTo (4 * k)).card := by
  obtain ⟨p, q, ℓ, hpq, hpℓ, hqℓ, hp, hq, hℓ⟩ :=
    exists_three_distinct_centeredPacketTriangle_witnesses_of_fullyCovered
      hk hprime hfull
  have hpS : p ∈ primeScalesUpTo (4 * k) := by
    exact mem_primeScalesUpTo.mpr
      ⟨(mem_squareOffsetPrimeSupport.mp hp).1,
        (mem_squareOffsetPrimeSupport.mp hp).2.1⟩
  have hqS : q ∈ primeScalesUpTo (4 * k) := by
    exact mem_primeScalesUpTo.mpr
      ⟨(mem_squareOffsetPrimeSupport.mp hq).1,
        (mem_squareOffsetPrimeSupport.mp hq).2.1⟩
  have hℓS : ℓ ∈ primeScalesUpTo (4 * k) := by
    exact mem_primeScalesUpTo.mpr
      ⟨(mem_squareOffsetPrimeSupport.mp hℓ).1,
        (mem_squareOffsetPrimeSupport.mp hℓ).2.1⟩
  have hsubset : ({p, q, ℓ} : Finset ℕ) ⊆ primeScalesUpTo (4 * k) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hpS
    · exact hqS
    · exact hℓS
  have hcard := Finset.card_le_card hsubset
  have htriple : ({p, q, ℓ} : Finset ℕ).card = 3 := by
    simp [hpq, hpℓ, hqℓ]
  rw [htriple] at hcard
  exact hcard

end DkMath.NumberTheory.Legendre

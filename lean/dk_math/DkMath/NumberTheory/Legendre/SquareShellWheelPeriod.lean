/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonResidueCover

#print "file: DkMath.NumberTheory.Legendre.SquareShellWheelPeriod"

/-! The exact collision criterion and an elementary eventual no-wrap bound. -/
namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- Anchor translation does not change modular collisions. -/
theorem squareShellWheelProjection_eq_iff_modEq (n r s : ℕ) :
    squareShellWheelProjection (primeScalesUpTo n) n r =
      squareShellWheelProjection (primeScalesUpTo n) n s ↔
    Nat.ModEq (finitePrimeBasisProduct (primeScalesUpTo n)) r s := by
  change Nat.ModEq _ (n ^ 2 + r) (n ^ 2 + s) ↔ _
  exact ⟨Nat.ModEq.add_left_cancel' _, fun h => Nat.ModEq.rfl.add h⟩

/-- A width equal to the period is still injective. -/
theorem squareShellWheelProjection_injOn_iff (n : ℕ) :
    Set.InjOn (squareShellWheelProjection (primeScalesUpTo n) n) (squareOffsets n) ↔
      2 * n ≤ finitePrimeBasisProduct (primeScalesUpTo n) := by
  have hM : 0 < finitePrimeBasisProduct (primeScalesUpTo n) :=
    Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero (primeScalesUpTo_isFinitePrimeBasis n))
  constructor
  · intro hi
    by_contra h
    have hlt : finitePrimeBasisProduct (primeScalesUpTo n) < 2 * n := by omega
    have h1 : 1 ∈ squareOffsets n := mem_squareOffsets.mpr (by dsimp [SquareOffset]; omega)
    have h2 : finitePrimeBasisProduct (primeScalesUpTo n) + 1 ∈ squareOffsets n :=
      mem_squareOffsets.mpr (by dsimp [SquareOffset]; omega)
    have he : squareShellWheelProjection (primeScalesUpTo n) n 1 =
        squareShellWheelProjection (primeScalesUpTo n) n
          (finitePrimeBasisProduct (primeScalesUpTo n) + 1) := by
      apply (squareShellWheelProjection_eq_iff_modEq _ _ _).mpr
      change 1 % _ = (_ + 1) % _
      simp
    have := hi h1 h2 he
    omega
  · intro hw r hr s hs he
    have hr := mem_squareOffsets.mp hr
    have hs := mem_squareOffsets.mp hs
    have hm := (squareShellWheelProjection_eq_iff_modEq _ _ _).mp he
    rcases le_total r s with hrs | hsr
    · have hd := (Nat.modEq_iff_dvd' hrs).mp hm
      have hz := Nat.eq_zero_of_dvd_of_lt hd (by dsimp [SquareOffset] at hr hs; omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' hsr).mp hm.symm
      have hz := Nat.eq_zero_of_dvd_of_lt hd (by dsimp [SquareOffset] at hr hs; omega)
      omega

/-- The odd part K of the primorial has K-2 unreserved by every prime ≤ n.
Its least prime factor therefore forces K-2 > n. This is a period bound,
not an escape witness in the square shell. -/
theorem squareShell_period_exceeds_width {n : ℕ} (hn : 5 ≤ n) :
    2 * n + 4 < finitePrimeBasisProduct (primeScalesUpTo n) := by
  let S := (primeScalesUpTo n).erase 2
  let K := finitePrimeBasisProduct S
  have hS : IsFinitePrimeBasis S := by
    intro p hp
    exact (mem_primeScalesUpTo.mp (Finset.mem_erase.mp hp).2).1
  have h2 : 2 ∈ primeScalesUpTo n := mem_primeScalesUpTo.mpr ⟨Nat.prime_two, by omega⟩
  have hM : finitePrimeBasisProduct (primeScalesUpTo n) = 2 * K := by
    dsimp [K, S, finitePrimeBasisProduct]
    exact (Finset.mul_prod_erase (primeScalesUpTo n) (fun p : ℕ => p) h2).symm
  have h15 : 15 ≤ K := by
    have hsub : ({3, 5} : Finset ℕ) ⊆ S := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨by decide, mem_primeScalesUpTo.mpr ⟨by decide, by omega⟩⟩
      · exact Finset.mem_erase.mpr ⟨by decide, mem_primeScalesUpTo.mpr ⟨by decide, hn⟩⟩
    have hd : finitePrimeBasisProduct {3, 5} ∣ K :=
      finitePrimeBasisProduct_dvd_of_commonMultiple (by
        intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> decide)
        (by intro p hp; exact mem_dvd_finitePrimeBasisProduct (hsub hp))
    have hk : 0 < K := Nat.pos_of_ne_zero (finitePrimeBasisProduct_ne_zero hS)
    norm_num [finitePrimeBasisProduct] at hd
    exact Nat.le_of_dvd hk hd
  have hodd : Odd K := by
    apply Nat.coprime_two_left.mp
    change Nat.Coprime 2 (∏ p ∈ S, p)
    rw [Nat.coprime_prod_right_iff]
    intro p hp
    exact (Nat.coprime_primes Nat.prime_two (hS p hp)).mpr
      (by intro he; exact (Finset.mem_erase.mp hp).1 he.symm)
  have hnot (p : ℕ) (hp : p ∈ primeScalesUpTo n) : ¬p ∣ K - 2 := by
    intro hd
    by_cases he : p = 2
    · subst p
      have hcp : Nat.Coprime 2 (K - 2) := by
        apply Nat.coprime_two_left.mpr
        obtain ⟨k, hk⟩ := hodd
        refine ⟨k - 1, ?_⟩
        omega
      have := hcp.eq_one_of_dvd hd
      omega
    · have hdK : p ∣ K := mem_dvd_finitePrimeBasisProduct (Finset.mem_erase.mpr ⟨he, hp⟩)
      have hdSum : p ∣ (K - 2) + 2 := by simpa [Nat.sub_add_cancel (by omega : 2 ≤ K)] using hdK
      have hd2 : p ∣ 2 := (Nat.dvd_add_iff_right hd).mpr hdSum
      exact he ((Nat.prime_dvd_prime_iff_eq (mem_primeScalesUpTo.mp hp).1 Nat.prime_two).mp hd2)
  have hx : n < K - 2 := by
    by_contra h
    have hle : K - 2 ≤ n := by omega
    have hp := Nat.minFac_prime (by omega : K - 2 ≠ 1)
    have hple := Nat.minFac_le (by omega : 0 < K - 2)
    exact hnot (K - 2).minFac (mem_primeScalesUpTo.mpr ⟨hp, hple.trans hle⟩) (Nat.minFac_dvd _)
  rw [hM]
  omega

/-- The complete natural-anchor classification, including the vacuous n=0 shell. -/
theorem squareShellWheelProjection_injOn_classification (n : ℕ) :
    Set.InjOn (squareShellWheelProjection (primeScalesUpTo n) n) (squareOffsets n) ↔
      n = 0 ∨ n = 3 ∨ 5 ≤ n := by
  rw [squareShellWheelProjection_injOn_iff]
  by_cases hn : 5 ≤ n
  · exact ⟨fun _ => Or.inr (Or.inr hn), fun _ => by have := squareShell_period_exceeds_width hn; omega⟩
  · interval_cases n <;> norm_num [finitePrimeBasisProduct, primeScalesUpTo] <;> decide

theorem squareShellWheelImage_card_of_injective {n : ℕ}
    (hn : n = 0 ∨ n = 3 ∨ 5 ≤ n) : (squareShellWheelImage n).card = 2 * n := by
  rw [squareShellWheelImage, Finset.card_image_of_injOn
    ((squareShellWheelProjection_injOn_classification n).mpr hn), card_squareOffsets]

end DkMath.NumberTheory.Legendre

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonResidueCover
import DkMath.NumberTheory.Legendre.CyclotomicPersistence
import Mathlib.Data.Nat.Sqrt

#print "file: DkMath.NumberTheory.Legendre.GnomonPrimorialTransition"

/-! Exact owner persistence restrictions. They do not assert propagation of full cover. -/
namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive DkMath.NumberTheory.PrimorialUniverse

/-- The old basis is fixed on both sides of this equation. -/
theorem squareAnchor_old_basis_succ (n : ℕ) :
    squareAnchorWheelProjection (primeScalesUpTo n) (n + 1) =
    (squareAnchorWheelProjection (primeScalesUpTo n) n + DkMath.Gnomon.oddGnomon n) %
      finitePrimeBasisProduct (primeScalesUpTo n) :=
  squareAnchorWheelProjection_succ (primeScalesUpTo_isFinitePrimeBasis n) n

/-- At a prime threshold the enlarged state projects to exactly the old state. -/
theorem squareAnchor_prime_threshold_projects_old {n : ℕ} (hp : (n + 1).Prime) :
    primeBasisWheelProjection (primeScalesUpTo n)
      (squareAnchorWheelProjection (primeScalesUpTo (n + 1)) (n + 1)) =
    squareAnchorWheelProjection (primeScalesUpTo n) (n + 1) := by
  have hnot : n + 1 ∉ primeScalesUpTo n := by
    intro h; have := (mem_primeScalesUpTo.mp h).2; omega
  rw [primeScalesUpTo_succ_eq, ite_eq_left hp]
  exact primeBasisWheelProjection_insert_fresh_then_old
    (primeScalesUpTo_isFinitePrimeBasis n) hp hnot _

theorem successorThresholdInsert_squareOffset {n r : ℕ} (hr : SquareOffset n r) :
    SquareOffset (n + 1) (successorThresholdInsert n r) :=
  mem_squareOffsets.mp (Finset.mem_sdiff.mp (successorThresholdInsert_mem_sdiff hr)).1

/-- Equal least owners are a common old prime, even if the new basis enlarges. -/
theorem residue_owner_persistence_mem_inter {n r : ℕ} (hr : SquareOffset n r)
    (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r))
    (he : squareResidueCoverOwner n r =
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r)) :
    squareResidueCoverOwner n r ∈ squareOffsetPrimeSupport n r ∩
      squareOffsetPrimeSupport (n + 1) (successorThresholdInsert n r) := by
  have h := squareResidueCoverOwner_packet hr hc
  have k := squareResidueCoverOwner_packet (successorThresholdInsert_squareOffset hr) hs
  refine Finset.mem_inter.mpr ⟨mem_squareOffsetPrimeSupport.mpr ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
  rw [he]
  exact mem_squareOffsetPrimeSupport.mpr ⟨k.1, k.2.1, k.2.2.1⟩

theorem residue_owner_persistence_lower {n r : ℕ} (hr : SquareOffset n r)
    (hl : r < n + 1) (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r))
    (he : squareResidueCoverOwner n r =
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r)) :
    squareResidueCoverOwner n r ∣ DkMath.Gnomon.oddGnomon n :=
  ((mem_reindexed_primeSupport_inter_lower_iff hr hl).mp
    (residue_owner_persistence_mem_inter hr hc hs he)).2

/-- A lower transition flips point parity, so two covered seats always change
least owner. Common nonleast support primes can still persist. -/
theorem residue_owner_changes_lower {n r : ℕ} (hr : SquareOffset n r)
    (hl : r < n + 1) (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r)) :
    squareResidueCoverOwner n r ≠
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r) := by
  intro he
  have hd := residue_owner_persistence_lower hr hl hc hs he
  have hp2 : squareResidueCoverOwner n r ≠ 2 := by
    intro htwo
    rw [htwo] at hd
    exact (DkMath.Gnomon.oddGnomon_odd n).not_two_dvd_nat hd
  have ho0 : Odd (n ^ 2 + r) := Nat.not_even_iff_odd.mp (by
    intro hev
    exact hp2 ((squareResidueCoverOwner_eq_two_iff hr).mpr hev.two_dvd))
  have hr1 := successorThresholdInsert_squareOffset hr
  have ho1 : Odd ((n + 1) ^ 2 + successorThresholdInsert n r) := Nat.not_even_iff_odd.mp (by
    intro hev
    exact hp2 (he.trans ((squareResidueCoverOwner_eq_two_iff hr1).mpr hev.two_dvd)))
  have hev : Even ((n + 1) ^ 2 + successorThresholdInsert n r) := by
    rw [successorThresholdInsert_lower_additive_displacement hl]
    exact ho0.add_odd (DkMath.Gnomon.oddGnomon_odd n)
  exact ho1.not_two_dvd_nat hev.two_dvd

theorem residue_owner_persistence_upper {n r : ℕ} (hr : SquareOffset n r)
    (hu : n + 1 ≤ r) (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r))
    (he : squareResidueCoverOwner n r =
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r)) :
    squareResidueCoverOwner n r ∣ 2 * (n + 1) :=
  ((mem_reindexed_primeSupport_inter_upper_iff hr hu).mp
    (residue_owner_persistence_mem_inter hr hc hs he)).2

theorem residue_owner_persistence_prime_upper {n r : ℕ} (hr : SquareOffset n r)
    (hu : n + 1 ≤ r) (hp : (n + 1).Prime) (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r))
    (he : squareResidueCoverOwner n r =
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r)) :
    squareResidueCoverOwner n r = 2 :=
  mem_reindexed_primeSupport_inter_upper_imp_eq_two hr hu hp
    (residue_owner_persistence_mem_inter hr hc hs he)

/-- A covered odd upper seat must change its least owner at a prime threshold. -/
theorem residue_owner_changes_prime_upper_odd {n r : ℕ} (hr : SquareOffset n r)
    (hu : n + 1 ≤ r) (hp : (n + 1).Prime) (hc : SquareOffsetCovered n r)
    (hs : SquareOffsetCovered (n + 1) (successorThresholdInsert n r))
    (ho : Odd (n ^ 2 + r)) :
    squareResidueCoverOwner n r ≠
      squareResidueCoverOwner (n + 1) (successorThresholdInsert n r) := by
  intro he
  have h2 := residue_owner_persistence_prime_upper hr hu hp hc hs he
  have hd := (squareResidueCoverOwner_packet hr hc).2.2.1
  rw [h2] at hd
  have hbad := (Nat.coprime_two_left.mpr ho).eq_one_of_dvd hd
  omega

/-- A single least owner cannot cover the same lower offset in three consecutive shells.
The covers themselves may coexist: this theorem only forces an owner change. -/
theorem residue_owner_no_three_lower {n r : ℕ} (hr : SquareOffset n r) (hl : r < n + 1)
    (h0 : SquareOffsetCovered n r) (h1 : SquareOffsetCovered (n + 1) r)
    (h2 : SquareOffsetCovered (n + 2) r) :
    ¬(squareResidueCoverOwner n r = squareResidueCoverOwner (n + 1) r ∧
      squareResidueCoverOwner (n + 1) r = squareResidueCoverOwner (n + 2) r) := by
  rintro ⟨he01, he12⟩
  have hi0 : successorThresholdInsert n r = r := by simp [successorThresholdInsert, hl]
  have hl1 : r < (n + 1) + 1 := by omega
  have hi1 : successorThresholdInsert (n + 1) r = r := by simp [successorThresholdInsert, hl1]
  have hr1 : SquareOffset (n + 1) r := by simpa [hi0] using successorThresholdInsert_squareOffset hr
  have hd0 : squareResidueCoverOwner n r ∣ DkMath.Gnomon.oddGnomon n :=
    residue_owner_persistence_lower hr hl h0 (by simpa [hi0] using h1) (by simpa [hi0] using he01)
  have hd1 : squareResidueCoverOwner n r ∣ DkMath.Gnomon.oddGnomon (n + 1) := by
    rw [he01]
    exact residue_owner_persistence_lower hr1 hl1 h1 (by simpa [hi1, Nat.add_assoc] using h2)
      (by simpa [hi1, Nat.add_assoc] using he12)
  have hp := (squareResidueCoverOwner_packet hr h0).1
  have hp2 : squareResidueCoverOwner n r ≠ 2 := by
    intro he
    rw [he] at hd0
    have ho : Odd (DkMath.Gnomon.oddGnomon n) := ⟨n, by simp [DkMath.Gnomon.oddGnomon]⟩
    have hbad := (Nat.coprime_two_left.mpr ho).eq_one_of_dvd hd0
    omega
  exact not_dvd_oddGnomon_succ hp hp2 hd0 hd1

/-- Apply the local obstruction to hypothetical full states without assuming propagation. -/
theorem fullyCovered_three_lower_owner_change {n r : ℕ} (hr : SquareOffset n r)
    (hl : r < n + 1) (h0 : SquareOffsetsFullyCovered n)
    (h1 : SquareOffsetsFullyCovered (n + 1)) (h2 : SquareOffsetsFullyCovered (n + 2)) :
    ¬(squareResidueCoverOwner n r = squareResidueCoverOwner (n + 1) r ∧
      squareResidueCoverOwner (n + 1) r = squareResidueCoverOwner (n + 2) r) := by
  have hr1 : SquareOffset (n + 1) r := by dsimp [SquareOffset] at hr ⊢; omega
  have hr2 : SquareOffset (n + 2) r := by dsimp [SquareOffset] at hr ⊢; omega
  exact residue_owner_no_three_lower hr hl (h0 r hr) (h1 r hr1) (h2 r hr2)

/-- The primorial's sqrt address is elementary and valid even at a square period. -/
theorem primorial_sqrt_address (n : ℕ) :
    let M := finitePrimeBasisProduct (primeScalesUpTo n)
    let a := Nat.sqrt M
    a ^ 2 ≤ M ∧ M < (a + 1) ^ 2 ∧
      (M - a ^ 2) + ((a + 1) ^ 2 - M) = 2 * a + 1 := by
  dsimp only
  have hl := Nat.sqrt_le' (finitePrimeBasisProduct (primeScalesUpTo n))
  have hu := Nat.lt_succ_sqrt' (finitePrimeBasisProduct (primeScalesUpTo n))
  simp only [Nat.succ_eq_add_one] at hu
  refine ⟨hl, hu, ?_⟩
  have he : (Nat.sqrt (finitePrimeBasisProduct (primeScalesUpTo n)) + 1) ^ 2 =
      Nat.sqrt (finitePrimeBasisProduct (primeScalesUpTo n)) ^ 2 +
        2 * Nat.sqrt (finitePrimeBasisProduct (primeScalesUpTo n)) + 1 := by ring
  omega

end DkMath.NumberTheory.Legendre

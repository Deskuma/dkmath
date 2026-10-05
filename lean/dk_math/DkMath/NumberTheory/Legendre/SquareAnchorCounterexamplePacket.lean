/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.SquareShellWheelPeriod
import DkMath.NumberTheory.Legendre.ParitySafeSqrtQuotientConservation
import DkMath.NumberTheory.Legendre.ParitySafeFullCoverCapacityFrontier

#print "file: DkMath.NumberTheory.Legendre.SquareAnchorCounterexamplePacket"

/-! Exact consequences and converses of a hypothetical fully covered square shell. -/
namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- On the reduced carrier all old prime divisors are active. -/
theorem squareOffsetPrimeSupport_eq_activeSupport {n r : ℕ}
    (hr : r ∈ squareAnchorOddPointCoprimeOffsets n) :
    squareOffsetPrimeSupport n r = paritySafeActiveSupport n r := by
  ext p
  rw [mem_squareOffsetPrimeSupport, mem_paritySafeActiveSupport_iff_dvd]
  constructor
  · rintro ⟨hp, hpn, hd⟩
    exact ⟨prime_dvd_candidate_mem_active hr hp hpn hd, hd⟩
  · rintro ⟨hp, hd⟩
    exact ⟨(mem_squareAnchorOddActivePrimes.mp hp).1,
      (mem_squareAnchorOddActivePrimes.mp hp).2.1, hd⟩

/-- The restriction loses no escape point for n≥2; n=1 has the extra prime 2. -/
theorem escapingSquareOffsets_eq_paritySafeUncovered {n : ℕ} (hn : 2 ≤ n) :
    escapingSquareOffsets n = paritySafeUncoveredCandidates n := by
  ext r
  rw [mem_escapingSquareOffsets, mem_paritySafeUncoveredCandidates_iff (by omega : 0 < n)]
  constructor
  · rintro ⟨hr, hc⟩
    have hp := (squareOffset_prime_iff_not_covered (by omega : 0 < n) hr).mpr hc
    have hgt : n < n ^ 2 + r := by
      dsimp [SquareOffset] at hr
      nlinarith
    have hcop : Nat.Coprime n (n ^ 2 + r) := by
      apply Nat.Coprime.symm
      apply hp.coprime_iff_not_dvd.mpr
      intro hd
      have := Nat.le_of_dvd (by omega : 0 < n) hd
      omega
    have ho : Odd (n ^ 2 + r) := hp.odd_of_ne_two (by omega)
    exact ⟨mem_squareAnchorOddPointCoprimeOffsets_iff_reducedResidue.mpr
      ⟨hr, coprime_two_mul_iff_coprime_and_odd.mpr ⟨hcop, ho⟩⟩, hc⟩
  · rintro ⟨hr, hc⟩
    exact ⟨squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hr, hc⟩

/-- Distinct survivor coordinates in the whole-shell image. -/
noncomputable def squareShellWheelSurvivorImage (n : ℕ) : Finset ℕ := by
  classical
  exact (squareShellWheelImage n).filter (IsPrimeBasisWheelSurvivor (primeScalesUpTo n))

/-- Projected survivors are exactly the images of escaping seats, with collisions retained. -/
theorem squareShell_survivor_filter_eq_image_escaping {n : ℕ} (hn : 2 ≤ n) :
    squareShellWheelSurvivorImage n =
      (escapingSquareOffsets n).image (squareShellWheelProjection (primeScalesUpTo n) n) := by
  classical
  ext x
  rw [squareShellWheelSurvivorImage, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hx, hs⟩
    obtain ⟨r, hr, he⟩ := mem_squareShellWheelImage.mp hx
    refine ⟨r, mem_escapingSquareOffsets.mpr ⟨mem_squareOffsets.mp hr, ?_⟩, he⟩
    exact (not_squareOffsetCovered_iff_projection_survivor hn).mpr (he.symm ▸ hs)
  · rintro ⟨r, hr, rfl⟩
    have hm := mem_escapingSquareOffsets.mp hr
    exact ⟨mem_squareShellWheelImage.mpr ⟨r, mem_squareOffsets.mpr hm.1, rfl⟩,
      (not_squareOffsetCovered_iff_projection_survivor hn).mp hm.2⟩

/-- From n=5, distinct projected survivors count exactly the uncovered seats. -/
theorem squareShell_survivor_card_eq_uncovered {n : ℕ} (hn : 5 ≤ n) :
    (squareShellWheelSurvivorImage n).card =
      (paritySafeUncoveredCandidates n).card := by
  classical
  rw [squareShell_survivor_filter_eq_image_escaping (by omega : 2 ≤ n)]
  have hi := (squareShellWheelProjection_injOn_classification n).mpr (Or.inr (Or.inr hn))
  rw [Finset.card_image_of_injOn (by
    intro r hr s hs he
    exact hi (mem_squareOffsets.mpr (mem_escapingSquareOffsets.mp hr).1)
      (mem_squareOffsets.mpr (mem_escapingSquareOffsets.mp hs).1) he),
    escapingSquareOffsets_eq_paritySafeUncovered (by omega : 2 ≤ n)]

theorem fullyCovered_iff_uncovered_empty {n : ℕ} (hn : 2 ≤ n) :
    SquareOffsetsFullyCovered n ↔ paritySafeUncoveredCandidates n = ∅ := by
  rw [← escapingSquareOffsets_eq_paritySafeUncovered hn]
  constructor
  · intro hf
    exact Finset.eq_empty_iff_forall_notMem.mpr
      (fun r hr => (mem_escapingSquareOffsets.mp hr).2 (hf r (mem_escapingSquareOffsets.mp hr).1))
  · intro he r hr
    by_contra hc
    have hm := mem_escapingSquareOffsets.mpr ⟨hr, hc⟩
    rw [he] at hm
    exact Finset.notMem_empty r hm

theorem fullyCovered_iff_rough_zero_card {n : ℕ} (hn : 2 ≤ n) :
    SquareOffsetsFullyCovered n ↔ (roughZeroSeats n).card = 0 := by
  rw [roughZeroSeats_eq_uncovered, Finset.card_eq_zero, fullyCovered_iff_uncovered_empty hn]

theorem fullyCovered_iff_no_wheel_image_survivor {n : ℕ} (hn : 2 ≤ n) :
    SquareOffsetsFullyCovered n ↔ ¬∃ x ∈ squareShellWheelImage n,
      IsPrimeBasisWheelSurvivor (primeScalesUpTo n) x := by
  exact ((not_congr (not_fullyCovered_iff_wheel_image_survivor hn)).symm.trans not_not).symm

theorem fullyCovered_iff_all_support_nonempty (n : ℕ) :
    SquareOffsetsFullyCovered n ↔ ∀ r, SquareOffset n r → (squareOffsetPrimeSupport n r).Nonempty := by
  simp only [SquareOffsetsFullyCovered, squareOffsetCovered_iff_primeSupport_nonempty]

theorem fullyCovered_iff_collapsed_census {n : ℕ} (hn : 2 ≤ n) :
    SquareOffsetsFullyCovered n ↔
      (canonicalRoughCandidates n (Nat.sqrt n)).card = (sqrtRoughCubeKeys n).card +
        (sqrtRoughCrossKeys n).card + (sqrtRoughRepeatedKeys n).card +
        (sqrtRoughTripleProductsInShell n).card := by
  rw [fullyCovered_iff_uncovered_empty hn, ← Finset.card_eq_zero]
  have h := sqrt_rough_factorization_census n
  omega

/-- Unconditional Nat-safe balance; its missing mass is exactly U. -/
theorem sqrt_counterexample_balance_with_uncovered (n : ℕ) :
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) +
      (paritySafeUncoveredCandidates n).card =
    (canonicalRoughCandidates n (Nat.sqrt n)).card + (sqrtRoughRepeatedKeys n).card +
      2 * (sqrtRoughTripleProductsInShell n).card +
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card := by
  have hc := sqrt_rough_factorization_census n
  have hq := sqrt_quotient_conservation n
  omega

/-- The complete corrected balance alone is equivalent to full cover on n≥2. -/
theorem fullyCovered_iff_corrected_balance {n : ℕ} (hn : 2 ≤ n) :
    SquareOffsetsFullyCovered n ↔
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) =
    (canonicalRoughCandidates n (Nat.sqrt n)).card + (sqrtRoughRepeatedKeys n).card +
      2 * (sqrtRoughTripleProductsInShell n).card +
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card := by
  rw [fullyCovered_iff_uncovered_empty hn, ← Finset.card_eq_zero]
  have h := sqrt_counterexample_balance_with_uncovered n
  omega

/-- A strict gap in the corrected counterexample balance is an exact finite provider. -/
theorem prime_squareCell_of_corrected_counterexample_gap {n : ℕ} (hn : 0 < n)
    (hgap : (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) <
      (canonicalRoughCandidates n (Nat.sqrt n)).card + (sqrtRoughRepeatedKeys n).card +
        2 * (sqrtRoughTripleProductsInShell n).card +
        ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card) :
    ∃ p, p.Prime ∧ SquareCell n p := by
  have h := sqrt_counterexample_balance_with_uncovered n
  apply exists_prime_squareCell_of_paritySafeUncoveredCandidates_nonempty hn
  apply Finset.card_pos.mp
  omega

/-- One simultaneous necessary-condition bundle. The hypothesis asserts no existence. -/
theorem squareAnchor_counterexample_packet {n : ℕ} (hn : 0 < n)
    (hfull : SquareOffsetsFullyCovered n) :
    (∀ r, SquareOffset n r → (squareOffsetPrimeSupport n r).Nonempty) ∧
    (¬∃ x ∈ squareShellWheelImage n, IsPrimeBasisWheelSurvivor (primeScalesUpTo n) x) ∧
    paritySafeUncoveredCandidates n = ∅ ∧ (roughZeroSeats n).card = 0 ∧
    (canonicalRoughCandidates n (Nat.sqrt n)).card = (sqrtRoughCubeKeys n).card +
      (sqrtRoughCrossKeys n).card + (sqrtRoughRepeatedKeys n).card +
      (sqrtRoughTripleProductsInShell n).card ∧
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) =
      (sqrtRoughCrossKeys n).card + (sqrtRoughCubeKeys n).card +
      2 * (sqrtRoughRepeatedKeys n).card + 3 * (sqrtRoughTripleProductsInShell n).card +
      (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card) ∧
    (∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughQuotientFiber n p).card) =
      (canonicalRoughCandidates n (Nat.sqrt n)).card + (sqrtRoughRepeatedKeys n).card +
      2 * (sqrtRoughTripleProductsInShell n).card +
      ∑ p ∈ roughActiveLabels n (Nat.sqrt n), (sqrtRoughRejectedFiber n p).card := by
  have he := paritySafeUncoveredCandidates_eq_empty_of_fullyCovered hn hfull
  have hzero : (paritySafeUncoveredCandidates n).card = 0 := by rw [he]; rfl
  refine ⟨fun r hr => squareOffsetCovered_iff_primeSupport_nonempty.mp (hfull r hr),
    ?_, he, by rw [roughZeroSeats_eq_uncovered, hzero], ?_, sqrt_quotient_conservation n, ?_⟩
  · rintro ⟨x, hx, hs⟩
    exact hs.2.2 ((fullyCovered_iff_wheel_image_reserved n).mp hfull x hx)
  · have := sqrt_rough_factorization_census n
    omega
  · have := sqrt_counterexample_balance_with_uncovered n
    omega

/-- Agreement with the existing least active owner; no second rough ledger is created. -/
theorem squareResidueCoverOwner_eq_paritySafeCanonical {n r : ℕ}
    (hr : r ∈ paritySafeCoveredCandidates n) :
    squareResidueCoverOwner n r = paritySafeCanonicalSupportPrime n r := by
  classical
  have hrc := (mem_paritySafeCoveredCandidates.mp hr).1
  have hne := (mem_paritySafeCoveredCandidates.mp hr).2
  have hS := squareOffsetPrimeSupport_eq_activeSupport hrc
  have hc : SquareOffsetCovered n r := squareOffsetCovered_iff_primeSupport_nonempty.mpr (hS ▸ hne)
  have hp := squareResidueCoverOwner_packet (squareOffset_of_mem_squareAnchorOddPointCoprimeOffsets hrc) hc
  have hm : squareResidueCoverOwner n r ∈ paritySafeActiveSupport n r := by
    rw [← hS]
    exact mem_squareOffsetPrimeSupport.mpr ⟨hp.1, hp.2.1, hp.2.2.1⟩
  rw [paritySafeCanonicalSupportPrime, dite_eq_left hne]
  apply le_antisymm
  · apply hp.2.2.2.2
    rw [hS]
    exact Finset.min'_mem _ hne
  · exact Finset.min'_le _ _ hm

/-- An exact support set determines the owner by its least element. -/
theorem squareResidueCoverOwner_eq_of_least_active {n r p : ℕ}
    (hr : r ∈ canonicalRoughCandidates n (Nat.sqrt n))
    (hp : p ∈ paritySafeActiveSupport n r)
    (hmin : ∀ q ∈ paritySafeActiveSupport n r, p ≤ q) : squareResidueCoverOwner n r = p := by
  classical
  have hc : r ∈ paritySafeCoveredCandidates n :=
    mem_paritySafeCoveredCandidates.mpr ⟨(Finset.mem_filter.mp hr).1, ⟨p, hp⟩⟩
  rw [squareResidueCoverOwner_eq_paritySafeCanonical hc, paritySafeCanonicalSupportPrime,
    dite_eq_left (show (paritySafeActiveSupport n r).Nonempty from ⟨p, hp⟩)]
  exact le_antisymm (Finset.min'_le _ _ hp) (hmin _ (Finset.min'_mem _ _))

theorem sqrt_cube_residue_owner {n p : ℕ} (hp : p ∈ sqrtRoughCubeKeys n) :
    squareResidueCoverOwner n (p ^ 3 - n ^ 2) = p := by
  have h := sqrt_cube_offset_packet hp
  apply squareResidueCoverOwner_eq_of_least_active (Finset.mem_filter.mp h.1).1
  · rw [h.2]; simp
  · intro q hq; have he : q = p := by simpa [h.2] using hq
    omega

theorem sqrt_cross_residue_owner {n p q : ℕ} (hp : (p, q) ∈ sqrtRoughCrossKeys n) :
    squareResidueCoverOwner n (p * q - n ^ 2) = p := by
  have h := sqrt_cross_offset_packet hp
  apply squareResidueCoverOwner_eq_of_least_active (Finset.mem_filter.mp h.1).1
  · rw [h.2]; simp
  · intro s hs; have he : s = p := by simpa [h.2] using hs
    omega

theorem sqrt_repeated_residue_owner {n : ℕ} {a : (ℕ × ℕ) × Bool}
    (ha : a ∈ sqrtRoughRepeatedKeys n) :
    squareResidueCoverOwner n (sqrtRepeatedProduct a - n ^ 2) = a.1.1 := by
  have h := sqrt_repeated_offset_packet ha
  have hpq := (mem_roughPairs.mp (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).1).2.2
  apply squareResidueCoverOwner_eq_of_least_active (Finset.mem_filter.mp h.1).1
  · rw [h.2]; simp
  · intro s hs; simp only [h.2, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with he | he
    · rw [he]
    · rw [he]; exact hpq.le

theorem sqrt_triple_residue_owner {n : ℕ} {a : ℕ × ℕ × ℕ}
    (ha : a ∈ sqrtRoughTripleProductsInShell n) :
    squareResidueCoverOwner n (a.1 * a.2.1 * a.2.2 - n ^ 2) = a.1 := by
  have h := sqrt_triple_offset_packet ha
  have hpq := mem_roughTriples.mp (Finset.mem_filter.mp ha).1
  apply squareResidueCoverOwner_eq_of_least_active (Finset.mem_filter.mp h.1).1
  · rw [h.2]; simp
  · intro s hs; simp only [h.2, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with he | he | he
    · rw [he]
    · rw [he]; exact hpq.2.2.2.1.le
    · rw [he]; exact (hpq.2.2.2.1.trans hpq.2.2.2.2).le

/-- Rough owners are coprime to every prime on the smaller quotient wheel. -/
theorem sqrt_small_prime_dvd_product_iff_quotient {n p q u : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hu : u.Prime) (hus : u ≤ Nat.sqrt n) :
    u ∣ p * q ↔ u ∣ q := by
  have hpP := (mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1).1
  have hgt := (Finset.mem_filter.mp hp).2
  rw [hu.dvd_mul]
  have hn : ¬u ∣ p := by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hu hpP).mp hd
    omega
  tauto

theorem sqrt_small_basis_reservation_product_iff {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) :
    ReservedByPrimeBasis (primeScalesUpTo (Nat.sqrt n)) (p * q) ↔
      ReservedByPrimeBasis (primeScalesUpTo (Nat.sqrt n)) q := by
  constructor <;> rintro ⟨u, hu, hd⟩ <;> refine ⟨u, hu, ?_⟩
  · exact (sqrt_small_prime_dvd_product_iff_quotient hp (mem_primeScalesUpTo.mp hu).1
      (mem_primeScalesUpTo.mp hu).2).mp hd
  · exact (sqrt_small_prime_dvd_product_iff_quotient hp (mem_primeScalesUpTo.mp hu).1
      (mem_primeScalesUpTo.mp hu).2).mpr hd

/-- Rejection is reservation on the quotient wheel, not the whole shell wheel. -/
theorem sqrt_rejected_iff_quotient_wheel_reserved {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughQuotientFiber n p) :
    q ∈ sqrtRoughRejectedFiber n p ↔
      ReservedByPrimeBasis (primeScalesUpTo (Nat.sqrt n))
        (primeBasisWheelProjection (primeScalesUpTo (Nat.sqrt n)) q) := by
  rw [reservedByPrimeBasis_projection_iff (primeScalesUpTo_isFinitePrimeBasis _),
    sqrt_quotient_rejected_iff_small_prime hp hq]
  constructor
  · rintro ⟨u, hu, hd, hle⟩; exact ⟨u, mem_primeScalesUpTo.mpr ⟨hu, hle⟩, hd⟩
  · rintro ⟨u, hu, hd⟩; exact ⟨u, (mem_primeScalesUpTo.mp hu).1, hd, (mem_primeScalesUpTo.mp hu).2⟩

/-- Every raw quotient is shell-covered; its small-wheel reservation is exactly rejection. -/
theorem sqrt_two_level_reservation_packet {n p q : ℕ}
    (hp : p ∈ roughActiveLabels n (Nat.sqrt n)) (hq : q ∈ sqrtRoughQuotientFiber n p) :
    SquareOffsetCovered n (p * q - n ^ 2) ∧
    (ReservedByPrimeBasis (primeScalesUpTo (Nat.sqrt n))
      (n ^ 2 + (p * q - n ^ 2)) ↔ q ∈ sqrtRoughRejectedFiber n p) := by
  have hs := sqrt_quotient_seat_packet hp hq
  have ha := mem_squareAnchorOddActivePrimes.mp (Finset.mem_filter.mp hp).1
  refine ⟨⟨p, mem_primeScalesUpTo.mpr ⟨ha.1, ha.2.1⟩, ?_⟩, ?_⟩
  · change p ∣ n ^ 2 + (p * q - n ^ 2)
    rw [hs.2.2.1]; exact dvd_mul_right p q
  · rw [hs.2.2.1, sqrt_small_basis_reservation_product_iff hp,
      sqrt_rejected_iff_quotient_wheel_reserved hp hq,
      reservedByPrimeBasis_projection_iff (primeScalesUpTo_isFinitePrimeBasis _)]

end DkMath.NumberTheory.Legendre

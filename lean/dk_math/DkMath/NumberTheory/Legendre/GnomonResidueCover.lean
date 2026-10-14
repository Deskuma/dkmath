/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.GnomonSuccessor

#print "file: DkMath.NumberTheory.Legendre.GnomonResidueCover"

/-! Exact residue-cover, whole-shell wheel image, and least whole-shell owner. -/

namespace DkMath.NumberTheory.Legendre
open DkMath.NumberTheory.Primitive DkMath.NumberTheory.PrimorialUniverse
open scoped BigOperators

/-- The square boundary is the one extra gnomon seat beyond the open shell. -/
theorem open_shell_card_add_one_eq_oddGnomon (n : ℕ) :
    (squareOffsets n).card + 1 = DkMath.Gnomon.oddGnomon n := by
  rw [card_squareOffsets, DkMath.Gnomon.oddGnomon]

theorem three_consecutive_odd_gnomons {n : ℕ} (hn : 0 < n) :
    DkMath.Gnomon.oddGnomon (n - 1) = 2 * n - 1 ∧
    DkMath.Gnomon.oddGnomon n = 2 * n + 1 ∧
    DkMath.Gnomon.oddGnomon (n + 1) = 2 * n + 3 := by
  unfold DkMath.Gnomon.oddGnomon
  omega

/-- Overlay one forbidden residue class on the existing open-shell offsets. -/
def squareResidueCoverFiber (n q : ℕ) : Finset ℕ :=
  (squareOffsets n).filter (fun r => r % q = squareAnchorForbiddenResidue n q)

theorem mem_squareResidueCoverFiber {n q r : ℕ} (hq : 0 < q) :
    r ∈ squareResidueCoverFiber n q ↔ SquareOffset n r ∧ q ∣ n ^ 2 + r := by
  rw [squareResidueCoverFiber, Finset.mem_filter, mem_squareOffsets,
    ← squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue hq]
  rfl

theorem coveredSquareOffsets_eq_residue_union (n : ℕ) :
    coveredSquareOffsets n = (primeScalesUpTo n).biUnion (squareResidueCoverFiber n) := by
  classical
  ext r
  rw [mem_coveredSquareOffsets, Finset.mem_biUnion]
  constructor
  · rintro ⟨hr, q, hq, hd⟩
    exact ⟨q, hq, (mem_squareResidueCoverFiber (mem_primeScalesUpTo.mp hq).1.pos).mpr ⟨hr, hd⟩⟩
  · rintro ⟨q, hq, hr⟩
    have h := (mem_squareResidueCoverFiber (mem_primeScalesUpTo.mp hq).1.pos).mp hr
    exact ⟨h.1, q, hq, h.2⟩

theorem fullyCovered_iff_residue_union (n : ℕ) :
    SquareOffsetsFullyCovered n ↔
      squareOffsets n = (primeScalesUpTo n).biUnion (squareResidueCoverFiber n) := by
  rw [← coveredSquareOffsets_eq_residue_union]
  constructor
  · intro hfull
    ext r
    rw [mem_squareOffsets, mem_coveredSquareOffsets]
    exact ⟨fun h => ⟨h, hfull r h⟩, And.left⟩
  · intro he r hr
    have hm : r ∈ coveredSquareOffsets n := by rw [← he]; exact mem_squareOffsets.mpr hr
    exact (mem_coveredSquareOffsets.mp hm).2

theorem fullyCovered_iff_pointwise_forbidden_residue (n : ℕ) :
    SquareOffsetsFullyCovered n ↔ ∀ r ∈ squareOffsets n,
      ∃ q ∈ primeScalesUpTo n, r % q = squareAnchorForbiddenResidue n q := by
  constructor
  · intro h r hr
    obtain ⟨q, hq, hd⟩ := h r (mem_squareOffsets.mp hr)
    exact ⟨q, hq, (squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
      (mem_primeScalesUpTo.mp hq).1.pos).mp hd⟩
  · intro h r hr
    obtain ⟨q, hq, hm⟩ := h r (mem_squareOffsets.mpr hr)
    exact ⟨q, hq, (squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue
      (mem_primeScalesUpTo.mp hq).1.pos).mpr hm⟩

def squareShellWheelImage (n : ℕ) : Finset ℕ :=
  (squareOffsets n).image (squareShellWheelProjection (primeScalesUpTo n) n)

theorem mem_squareShellWheelImage {n x : ℕ} : x ∈ squareShellWheelImage n ↔
    ∃ r ∈ squareOffsets n, squareShellWheelProjection (primeScalesUpTo n) n r = x := by
  rw [squareShellWheelImage, Finset.mem_image]

theorem fullyCovered_iff_wheel_image_reserved (n : ℕ) :
    SquareOffsetsFullyCovered n ↔ ∀ x ∈ squareShellWheelImage n,
      ReservedByPrimeBasis (primeScalesUpTo n) x := by
  constructor
  · intro hfull x hx
    obtain ⟨r, hr, rfl⟩ := mem_squareShellWheelImage.mp hx
    exact (reservedByPrimeBasis_projection_iff (primeScalesUpTo_isFinitePrimeBasis n) _).mpr
      (hfull r (mem_squareOffsets.mp hr))
  · intro h r hr
    exact (reservedByPrimeBasis_projection_iff (primeScalesUpTo_isFinitePrimeBasis n) _).mp
      (h _ (mem_squareShellWheelImage.mpr ⟨r, mem_squareOffsets.mpr hr, rfl⟩))

theorem not_fullyCovered_iff_wheel_image_survivor {n : ℕ} (hn : 2 ≤ n) :
    ¬SquareOffsetsFullyCovered n ↔ ∃ x ∈ squareShellWheelImage n,
      IsPrimeBasisWheelSurvivor (primeScalesUpTo n) x := by
  classical
  constructor
  · intro h
    have he : ∃ r, SquareOffset n r ∧ ¬SquareOffsetCovered n r := by
      simpa only [SquareOffsetsFullyCovered, not_forall, not_imp, exists_prop] using h
    obtain ⟨r, hr, hnot⟩ := he
    exact ⟨_, mem_squareShellWheelImage.mpr ⟨r, mem_squareOffsets.mpr hr, rfl⟩,
      (not_squareOffsetCovered_iff_projection_survivor hn).mp hnot⟩
  · rintro ⟨x, hx, hs⟩ hfull
    obtain ⟨r, hr, rfl⟩ := mem_squareShellWheelImage.mp hx
    exact (not_squareOffsetCovered_iff_projection_survivor hn).mpr hs
      (hfull r (mem_squareOffsets.mp hr))

/-- The specific run starting at n², not an arbitrary reserved wheel interval. -/
def SquareAnchorWheelFullyReserved (n : ℕ) : Prop :=
  ∀ r ∈ squareOffsets n, ReservedByPrimeBasis (primeScalesUpTo n)
    ((squareAnchorWheelProjection (primeScalesUpTo n) n + r) %
      finitePrimeBasisProduct (primeScalesUpTo n))

theorem squareAnchorWheelFullyReserved_iff_full (n : ℕ) :
    SquareAnchorWheelFullyReserved n ↔ SquareOffsetsFullyCovered n := by
  unfold SquareAnchorWheelFullyReserved
  simp_rw [← squareShellWheelProjection_eq_anchor_add (primeScalesUpTo_isFinitePrimeBasis n)]
  constructor
  · intro h r hr
    exact (reservedByPrimeBasis_projection_iff (primeScalesUpTo_isFinitePrimeBasis n) _).mp
      (h r (mem_squareOffsets.mpr hr))
  · intro h r hr
    exact (reservedByPrimeBasis_projection_iff (primeScalesUpTo_isFinitePrimeBasis n) _).mpr
      (h r (mem_squareOffsets.mp hr))

/-- On covered seats this is the least actual support prime; elsewhere it is simply minFac. -/
def squareResidueCoverOwner (n r : ℕ) : ℕ := (n ^ 2 + r).minFac

/-- Parity completely determines whether the least whole-point factor is two. -/
theorem squareResidueCoverOwner_eq_two_iff {n r : ℕ} (hr : SquareOffset n r) :
    squareResidueCoverOwner n r = 2 ↔ 2 ∣ n ^ 2 + r := by
  have hx : 1 < n ^ 2 + r := by
    dsimp [SquareOffset] at hr
    have hn : 0 < n := by omega
    nlinarith
  have hp := Nat.minFac_prime (ne_of_gt hx)
  constructor
  · intro he
    have hd := Nat.minFac_dvd (n ^ 2 + r)
    change (n ^ 2 + r).minFac = 2 at he
    rwa [he] at hd
  · intro hd
    have hle := Nat.minFac_le_of_dvd (by decide : 2 ≤ 2) hd
    have hge := hp.two_le
    change (n ^ 2 + r).minFac = 2
    omega

theorem squareResidueCoverOwner_packet {n r : ℕ} (hr : SquareOffset n r)
    (hc : SquareOffsetCovered n r) :
    (squareResidueCoverOwner n r).Prime ∧ squareResidueCoverOwner n r ≤ n ∧
    squareResidueCoverOwner n r ∣ n ^ 2 + r ∧
    r % squareResidueCoverOwner n r = squareAnchorForbiddenResidue n (squareResidueCoverOwner n r) ∧
    ∀ q ∈ squareOffsetPrimeSupport n r, squareResidueCoverOwner n r ≤ q := by
  obtain ⟨q, hq, hd⟩ := hc
  have hx : 1 < n ^ 2 + r := by
    dsimp only [SquareOffset] at hr
    have hn : 0 < n := by omega
    nlinarith
  have hp := Nat.minFac_prime (ne_of_gt hx)
  have hple := Nat.minFac_le_of_dvd (mem_primeScalesUpTo.mp hq).1.two_le hd
  refine ⟨hp, hple.trans (mem_primeScalesUpTo.mp hq).2, Nat.minFac_dvd _, ?_, ?_⟩
  · exact (squareOffsetForbiddenBy_iff_mod_eq_forbiddenResidue hp.pos).mp (Nat.minFac_dvd _)
  · intro p hp
    exact Nat.minFac_le_of_dvd (mem_squareOffsetPrimeSupport.mp hp).1.two_le
      (mem_squareOffsetPrimeSupport.mp hp).2.2

noncomputable def squareResidueOwnerFiber (n p : ℕ) : Finset ℕ :=
  (coveredSquareOffsets n).filter (fun r => squareResidueCoverOwner n r = p)

theorem residue_owner_fibers_disjoint {n p q : ℕ} (hpq : p ≠ q) :
    Disjoint (squareResidueOwnerFiber n p) (squareResidueOwnerFiber n q) := by
  classical
  exact Finset.disjoint_left.mpr (fun r hp hq => hpq
    ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2))

theorem coveredSquareOffsets_eq_owner_union (n : ℕ) :
    coveredSquareOffsets n = (primeScalesUpTo n).biUnion (squareResidueOwnerFiber n) := by
  classical
  ext r
  constructor
  · intro hr
    have hs := mem_coveredSquareOffsets.mp hr
    have hp := squareResidueCoverOwner_packet hs.1 hs.2
    exact Finset.mem_biUnion.mpr ⟨squareResidueCoverOwner n r,
      mem_primeScalesUpTo.mpr ⟨hp.1, hp.2.1⟩, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩
  · intro hr
    obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp hr
    exact (Finset.mem_filter.mp hp).1

theorem residue_owner_fiber_sum (n : ℕ) :
    (∑ p ∈ primeScalesUpTo n, (squareResidueOwnerFiber n p).card) = (coveredSquareOffsets n).card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise (f := squareResidueCoverOwner n) (t := primeScalesUpTo n)
    (by intro r hr
        have hs := mem_coveredSquareOffsets.mp hr
        have hp := squareResidueCoverOwner_packet hs.1 hs.2
        exact mem_primeScalesUpTo.mpr ⟨hp.1, hp.2.1⟩)

end DkMath.NumberTheory.Legendre

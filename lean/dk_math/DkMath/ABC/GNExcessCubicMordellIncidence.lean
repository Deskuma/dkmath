/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicMordellTransport

#print "file: DkMath.ABC.GNExcessCubicMordellIncidence"

/-!
# Fixed-parameter Mordell incidence ledger for the cubic shell

This module records the exact finite partition of shell witnesses by the
positive Mordell parameters `(S,u)`, together with the resulting coordinate
image and its polynomial equation.  It contains no integral-point estimate,
rank statement, asymptotic bound, or ABC assertion.
-/

namespace DkMath.ABC

/-! ## Canonical Mordell parameter and its fibers -/

/-- The fixed Mordell parameter carried by a shell witness. -/
noncomputable def GNExcessCubicMordellParameter (a : ℕ) : ℕ × ℕ :=
  (GNExcessCubicComplement a,
    GNExcessCubicSquarefulQuotient (GNExcessCubicFullRepeatedModulus a))

/-- The finite set of Mordell parameters represented in one shell. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellMordellParameterSpace
    (X D : ℕ) : Finset (ℕ × ℕ) :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).image
    GNExcessCubicMordellParameter

theorem mem_GNExcessCubicRealizedLargeModulusShellMordellParameterSpace_iff
    {X D S u : ℕ} :
    (S, u) ∈
        GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D ↔
      ∃ a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D,
        GNExcessCubicComplement a = S ∧
          GNExcessCubicSquarefulQuotient
              (GNExcessCubicFullRepeatedModulus a) = u := by
  simp [GNExcessCubicRealizedLargeModulusShellMordellParameterSpace,
    GNExcessCubicMordellParameter]

/-- The shell fiber at a fixed Mordell parameter `(S,u)`. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellMordellParameterFiber
    (X D S u : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a =>
      GNExcessCubicComplement a = S ∧
        GNExcessCubicSquarefulQuotient
            (GNExcessCubicFullRepeatedModulus a) = u)

theorem mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff
    {X D S u a : ℕ} :
    a ∈ GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D S u ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        GNExcessCubicComplement a = S ∧
          GNExcessCubicSquarefulQuotient
              (GNExcessCubicFullRepeatedModulus a) = u := by
  simp [GNExcessCubicRealizedLargeModulusShellMordellParameterFiber]

theorem GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_nonempty
    {X D S u : ℕ}
    (hSU : (S, u) ∈
      GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D) :
    (GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D S u).Nonempty := by
  obtain ⟨a, ha, hS, hu⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellMordellParameterSpace_iff.mp hSU
  exact ⟨a, mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mpr
    ⟨ha, hS, hu⟩⟩

/-! ## Positivity of represented parameters -/

private theorem mordell_complement_pos_of_shell_witness
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    0 < GNExcessCubicComplement a := by
  rcases GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha with
    ⟨ha1, _, _, _, hlarge, hEq, _, _, _⟩
  have hMpos : 0 < GNExcessCubicFullRepeatedModulus a := by omega
  have hquadpos : 0 < a ^ 2 + 3 * a + 3 := by nlinarith
  have hprodne :
      GNExcessCubicFullRepeatedModulus a * GNExcessCubicComplement a ≠ 0 := by
    intro hzero
    rw [hEq] at hzero
    exact (Nat.ne_of_gt hquadpos) hzero
  have hSne : GNExcessCubicComplement a ≠ 0 := by
    intro hS
    apply hprodne
    simp [hS]
  exact Nat.pos_of_ne_zero hSne

theorem GNExcessCubicRealizedLargeModulusShellMordellParameter_pos
    {X D S u : ℕ}
    (hSU : (S, u) ∈
      GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D) :
    0 < S ∧ 0 < u := by
  obtain ⟨a, ha, hS, hu⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellMordellParameterSpace_iff.mp hSU
  have hSpos := mordell_complement_pos_of_shell_witness ha
  have hMspace : GNExcessCubicFullRepeatedModulus a ∈
      GNExcessCubicRealizedLargeModulusSpace X := by
    have hW := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp ha
    rw [← GNExcessCubicRealizedLargeWitnessSpace_image_eq_modulusSpace X]
    exact Finset.mem_image.mpr ⟨a, hW.1, rfl⟩
  have hpack := GNExcessCubicRealizedLargeModulusSpace_squareCube_packet hMspace
  exact ⟨by simpa [hS] using hSpos, by simpa [hu] using hpack.2.2.2.2.1⟩

/-! ## Exact parameter-fiber partition and witness ledger -/

private theorem mordellParameter_fibers_pairwise_disjoint (X D : ℕ) :
    (↑(GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D) :
      Set (ℕ × ℕ)).PairwiseDisjoint
      (fun p =>
        GNExcessCubicRealizedLargeModulusShellMordellParameterFiber
          X D p.1 p.2) := by
  intro p _ q _ hpq
  change Disjoint
    (GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D p.1 p.2)
    (GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D q.1 q.2)
  rw [Finset.disjoint_left]
  intro a haP haQ
  have hP :=
    (mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mp
      haP).2
  have hQ :=
    (mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mp
      haQ).2
  exact hpq (Prod.ext (hP.1.symm.trans hQ.1) (hP.2.symm.trans hQ.2))

theorem GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_mordellParameterFibers
    (X D : ℕ) :
    (GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D).biUnion
        (fun p =>
          GNExcessCubicRealizedLargeModulusShellMordellParameterFiber
            X D p.1 p.2) =
      GNExcessCubicRealizedLargeModulusShellWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨p, hp, haF⟩ := Finset.mem_biUnion.mp ha
    exact
      (mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mp
        haF).1
  · intro ha
    apply Finset.mem_biUnion.mpr
    refine ⟨GNExcessCubicMordellParameter a, ?_, ?_⟩
    · exact mem_GNExcessCubicRealizedLargeModulusShellMordellParameterSpace_iff.mpr
        ⟨a, ha, rfl, rfl⟩
    · exact mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mpr
        ⟨ha, rfl, rfl⟩

theorem GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellParameterFiberCards
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
      ∑ p ∈ GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D,
        (GNExcessCubicRealizedLargeModulusShellMordellParameterFiber
          X D p.1 p.2).card := by
  classical
  unfold GNExcessCubicRealizedLargeModulusShellWitnessCount
  rw [← GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_mordellParameterFibers]
  exact Finset.card_biUnion (mordellParameter_fibers_pairwise_disjoint X D)

/-! ## Fixed-parameter Mordell coordinates -/

/-- The `Z` coordinate at fixed Mordell parameters `(S,u)`. -/
noncomputable def GNExcessCubicMordellZ (S u a : ℕ) : ℕ :=
  4 * S * u ^ 2 * oddPart (GNExcessCubicFullRepeatedModulus a)

/-- The `Y` coordinate at fixed Mordell parameters `(S,u)`. -/
noncomputable def GNExcessCubicMordellY (S u a : ℕ) : ℕ :=
  4 * S * u ^ 2 * (2 * a + 3)

/-- The production Mordell coordinate pair at fixed `(S,u)`. -/
noncomputable def GNExcessCubicMordellCoordinate (S u a : ℕ) : ℕ × ℕ :=
  (GNExcessCubicMordellZ S u a, GNExcessCubicMordellY S u a)

/-- The exact coordinate image of a fixed Mordell-parameter fiber. -/
noncomputable def GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
    (X D S u : ℕ) : Finset (ℕ × ℕ) :=
  (GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D S u).image
    (GNExcessCubicMordellCoordinate S u)

theorem mem_GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_iff
    {X D S u Z Y : ℕ} :
    (Z, Y) ∈
        GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
          X D S u ↔
      ∃ a ∈
          GNExcessCubicRealizedLargeModulusShellMordellParameterFiber X D S u,
        GNExcessCubicMordellZ S u a = Z ∧
          GNExcessCubicMordellY S u a = Y := by
  simp [GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace,
    GNExcessCubicMordellCoordinate]

theorem GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_equation
    {X D S u Z Y : ℕ}
    (hZY : (Z, Y) ∈
      GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
        X D S u) :
    Y ^ 2 + 48 * S ^ 2 * u ^ 4 = Z ^ 3 := by
  obtain ⟨a, ha, hZ, hY⟩ :=
    mem_GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_iff.mp hZY
  have hF :=
    mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mp ha
  have hMord :=
    GNExcessCubicRealizedLargeModulusShellWitness_mordell_identity hF.1
  rw [← hY, ← hZ]
  simpa [GNExcessCubicMordellZ, GNExcessCubicMordellY, hF.2.1, hF.2.2]
    using hMord

theorem GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_card
    {X D S u : ℕ}
    (hSU : (S, u) ∈
      GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D) :
    (GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
      X D S u).card =
      (GNExcessCubicRealizedLargeModulusShellMordellParameterFiber
        X D S u).card := by
  have hpos :=
    GNExcessCubicRealizedLargeModulusShellMordellParameter_pos hSU
  unfold GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have hza := congrArg Prod.fst hab
  have hya := congrArg Prod.snd hab
  have hfa :=
    (mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mp
      ha).1
  have hfb :=
    (mem_GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_iff.mp
      hb).1
  exact (mordellCoordinates_injective_fixed_SU hpos.1 hpos.2 hza hya).2

/-! ## Two-level exact cardinal ledger -/

theorem GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellCoordinateCards
    (X D : ℕ) :
    GNExcessCubicRealizedLargeModulusShellWitnessCount X D =
      ∑ p ∈ GNExcessCubicRealizedLargeModulusShellMordellParameterSpace X D,
        (GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace
          X D p.1 p.2).card := by
  rw [GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellParameterFiberCards]
  apply Finset.sum_congr rfl
  intro p hp
  exact
    (GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_card hp).symm

end DkMath.ABC

#print axioms DkMath.ABC.mem_GNExcessCubicRealizedLargeModulusShellMordellParameterSpace_iff
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellMordellParameterFiber_nonempty
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitnessSpace_eq_biUnion_mordellParameterFibers
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_equation
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellMordellCoordinateSpace_card
#print axioms DkMath.ABC.GNExcessCubicRealizedLargeModulusShellWitnessCount_eq_sum_mordellCoordinateCards

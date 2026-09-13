/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.GNExcessCubicSevenDepth
import DkMath.ABC.GNExcessCubicRealizedIncidence

#print "file: DkMath.ABC.GNExcessCubicSevenDepthIncidence"

/-!
# LUNA-021: finite seven-depth incidence ledger

The declarations here are exact finite filters over the existing realized
large-modulus shell.  They make no cardinality estimate and no asymptotic or
relative-height claim.
-/

namespace DkMath.ABC

open DkMath.CosmicFormulaBinom DkMath.NumberTheory

/-! ## Seven-sector and state witness spaces -/

noncomputable def GNCubicPairedSevenSectorWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D).filter
    (fun a => a % 7 = 1)

theorem mem_GNCubicPairedSevenSectorWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNCubicPairedSevenSectorWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        a % 7 = 1 := by
  simp [GNCubicPairedSevenSectorWitnessSpace]

noncomputable def GNCubicPairedForwardSevenDeepWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => a % 49 = 29)

theorem mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNCubicPairedForwardSevenDeepWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        a % 49 = 29 := by
  constructor
  · intro ha
    have ha' := Finset.mem_filter.mp ha
    have hs := mem_GNCubicPairedSevenSectorWitnessSpace_iff.mp ha'.1
    exact ⟨hs.1, ha'.2⟩
  · rintro ⟨ha, h29⟩
    have ha7 : a % 7 = 1 := by omega
    exact Finset.mem_filter.mpr ⟨
      mem_GNCubicPairedSevenSectorWitnessSpace_iff.mpr ⟨ha, ha7⟩, h29⟩

noncomputable def GNCubicPairedSwapSevenDeepWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => a % 49 = 22)

theorem mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNCubicPairedSwapSevenDeepWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        a % 49 = 22 := by
  constructor
  · intro ha
    have ha' := Finset.mem_filter.mp ha
    have hs := mem_GNCubicPairedSevenSectorWitnessSpace_iff.mp ha'.1
    exact ⟨hs.1, ha'.2⟩
  · rintro ⟨ha, h22⟩
    have ha7 : a % 7 = 1 := by omega
    exact Finset.mem_filter.mpr ⟨
      mem_GNCubicPairedSevenSectorWitnessSpace_iff.mpr ⟨ha, ha7⟩, h22⟩

noncomputable def GNCubicPairedShallowSevenWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => a % 49 ≠ 29 ∧ a % 49 ≠ 22)

theorem mem_GNCubicPairedShallowSevenWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNCubicPairedShallowSevenWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        a % 7 = 1 ∧ a % 49 ≠ 29 ∧ a % 49 ≠ 22 := by
  simp only [GNCubicPairedShallowSevenWitnessSpace, Finset.mem_filter,
    mem_GNCubicPairedSevenSectorWitnessSpace_iff]
  constructor
  · rintro ⟨⟨ha, ha7⟩, h29, h22⟩
    exact ⟨ha, ha7, h29, h22⟩
  · rintro ⟨ha, ha7, h29, h22⟩
    exact ⟨⟨ha, ha7⟩, h29, h22⟩

private theorem mod_seven_eq_one_of_mod_fortyNine_eq_twentyNine
    {a : ℕ} (h : a % 49 = 29) : a % 7 = 1 := by
  have ha : a = 49 * (a / 49) + a % 49 := by omega
  rw [ha, h]
  norm_num [Nat.add_mod, Nat.mul_mod]

private theorem mod_seven_eq_one_of_mod_fortyNine_eq_twentyTwo
    {a : ℕ} (h : a % 49 = 22) : a % 7 = 1 := by
  have ha : a = 49 * (a / 49) + a % 49 := by omega
  rw [ha, h]
  norm_num [Nat.add_mod, Nat.mul_mod]

/-! ## Exact finite partition and cardinal ledger -/

theorem GNCubicPairedSevenSectorWitnessSpace_eq_threeState_union
    (X D : ℕ) :
    GNCubicPairedSevenSectorWitnessSpace X D =
      GNCubicPairedForwardSevenDeepWitnessSpace X D ∪
        GNCubicPairedSwapSevenDeepWitnessSpace X D ∪
        GNCubicPairedShallowSevenWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    have hs := mem_GNCubicPairedSevenSectorWitnessSpace_iff.mp ha
    by_cases h29 : a % 49 = 29
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mpr ⟨hs.1, h29⟩))))
    by_cases h22 : a % 49 = 22
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mpr ⟨hs.1, h22⟩))))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_GNCubicPairedShallowSevenWitnessSpace_iff.mpr
          ⟨hs.1, hs.2, h29, h22⟩))
  · intro ha
    rcases Finset.mem_union.mp ha with hFG | hS
    · rcases Finset.mem_union.mp hFG with hF | hG
      · have hF' := mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mp hF
        exact mem_GNCubicPairedSevenSectorWitnessSpace_iff.mpr
          ⟨hF'.1, mod_seven_eq_one_of_mod_fortyNine_eq_twentyNine hF'.2⟩
      · have hG' := mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mp hG
        exact mem_GNCubicPairedSevenSectorWitnessSpace_iff.mpr
          ⟨hG'.1, mod_seven_eq_one_of_mod_fortyNine_eq_twentyTwo hG'.2⟩
    · have hS' := mem_GNCubicPairedShallowSevenWitnessSpace_iff.mp hS
      exact mem_GNCubicPairedSevenSectorWitnessSpace_iff.mpr ⟨hS'.1, hS'.2.1⟩

theorem GNCubicPairedForwardDeep_disjoint_SwapDeep (X D : ℕ) :
    Disjoint (GNCubicPairedForwardSevenDeepWitnessSpace X D)
      (GNCubicPairedSwapSevenDeepWitnessSpace X D) := by
  rw [Finset.disjoint_left]
  intro a hF hG
  have hF' := (mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mp hF).2
  have hG' := (mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mp hG).2
  omega

theorem GNCubicPairedForwardDeep_disjoint_Shallow (X D : ℕ) :
    Disjoint (GNCubicPairedForwardSevenDeepWitnessSpace X D)
      (GNCubicPairedShallowSevenWitnessSpace X D) := by
  rw [Finset.disjoint_left]
  intro a hF hS
  have hF' := (mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mp hF).2
  have hS' := (mem_GNCubicPairedShallowSevenWitnessSpace_iff.mp hS).2.2.1
  exact hS' hF'

theorem GNCubicPairedSwapDeep_disjoint_Shallow (X D : ℕ) :
    Disjoint (GNCubicPairedSwapSevenDeepWitnessSpace X D)
      (GNCubicPairedShallowSevenWitnessSpace X D) := by
  rw [Finset.disjoint_left]
  intro a hG hS
  have hG' := (mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mp hG).2
  have hS' := (mem_GNCubicPairedShallowSevenWitnessSpace_iff.mp hS).2.2.2
  exact hS' hG'

theorem GNCubicPairedSevenSectorWitnessSpace_card_eq_threeState_cards
    (X D : ℕ) :
    (GNCubicPairedSevenSectorWitnessSpace X D).card =
      (GNCubicPairedForwardSevenDeepWitnessSpace X D).card +
        (GNCubicPairedSwapSevenDeepWitnessSpace X D).card +
        (GNCubicPairedShallowSevenWitnessSpace X D).card := by
  classical
  rw [GNCubicPairedSevenSectorWitnessSpace_eq_threeState_union]
  have hFG := GNCubicPairedForwardDeep_disjoint_SwapDeep X D
  have hFSG : Disjoint
      (GNCubicPairedForwardSevenDeepWitnessSpace X D ∪
        GNCubicPairedSwapSevenDeepWitnessSpace X D)
      (GNCubicPairedShallowSevenWitnessSpace X D) := by
    rw [Finset.disjoint_left]
    intro a ha hS
    rcases Finset.mem_union.mp ha with hF | hG
    · exact (Finset.disjoint_left.mp
        (GNCubicPairedForwardDeep_disjoint_Shallow X D)) hF hS
    · exact (Finset.disjoint_left.mp
        (GNCubicPairedSwapDeep_disjoint_Shallow X D)) hG hS
  rw [Finset.card_union_of_disjoint hFSG,
    Finset.card_union_of_disjoint hFG]

private theorem pos_of_mem_GNCubicPairedSevenSectorShell
    {X D a : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D) :
    0 < a := by
  have hW := (mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp ha).1
  have hpos := (mem_GNExcessCubicRealizedLargeWitnessSpace_iff.mp hW).1
  omega

/-! ## State packet consumers -/

theorem GNCubicPairedForwardSevenDeepWitnessSpace_packet
    {X D a : ℕ}
    (ha : a ∈ GNCubicPairedForwardSevenDeepWitnessSpace X D) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧ 49 ∣ GN 3 a 1 ∧
    ¬ 49 ∣ GN 3 1 a ∧ 7 ∣ GNCubicForwardRepeatedPart a ∧
    ¬ 7 ∣ GNCubicSwapRepeatedPart a ∧
    ¬ 7 ∣ GNExcessCubicComplement a ∧
    7 ∣ GNExcessCubicSwapComplement a ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) = 7 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNCubicSwapRepeatedPart a) = 1 := by
  have hs := mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mp ha
  have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hs.1
  have hp := GNCubicPaired_forwardSevenDeep_packet haPos hs.2
  have hg := GNCubicPaired_forwardSevenDeep_crossGcd_packet haPos hs.2
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2,
    hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩

theorem GNCubicPairedSwapSevenDeepWitnessSpace_packet
    {X D a : ℕ}
    (ha : a ∈ GNCubicPairedSwapSevenDeepWitnessSpace X D) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧ ¬ 49 ∣ GN 3 a 1 ∧
    49 ∣ GN 3 1 a ∧ ¬ 7 ∣ GNCubicForwardRepeatedPart a ∧
    7 ∣ GNCubicSwapRepeatedPart a ∧
    7 ∣ GNExcessCubicComplement a ∧
    ¬ 7 ∣ GNExcessCubicSwapComplement a ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) = 7 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNCubicSwapRepeatedPart a) = 1 := by
  have hs := mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mp ha
  have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hs.1
  have hp := GNCubicPaired_swapSevenDeep_packet haPos hs.2
  have hg := GNCubicPaired_swapSevenDeep_crossGcd_packet haPos hs.2
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2,
    hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩

theorem GNCubicPairedShallowSevenWitnessSpace_packet
    {X D a : ℕ}
    (ha : a ∈ GNCubicPairedShallowSevenWitnessSpace X D) :
    7 ∣ GN 3 a 1 ∧ 7 ∣ GN 3 1 a ∧ ¬ 49 ∣ GN 3 a 1 ∧
    ¬ 49 ∣ GN 3 1 a ∧ ¬ 7 ∣ GNCubicForwardRepeatedPart a ∧
    ¬ 7 ∣ GNCubicSwapRepeatedPart a ∧
    7 ∣ GNExcessCubicComplement a ∧
    7 ∣ GNExcessCubicSwapComplement a ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNExcessCubicSwapComplement a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNCubicSwapRepeatedPart a) = 1 ∧
    Nat.gcd (GNExcessCubicComplement a)
        (GNExcessCubicSwapComplement a) = 7 ∧
    Nat.gcd (GNCubicForwardRepeatedPart a)
        (GNCubicSwapRepeatedPart a) = 1 := by
  have hs := mem_GNCubicPairedShallowSevenWitnessSpace_iff.mp ha
  have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hs.1
  have hp := GNCubicPaired_shallowSeven_packet haPos hs.2.1 hs.2.2.1 hs.2.2.2
  have hg := GNCubicPaired_shallowSeven_crossGcd_packet haPos hs.2.1
    hs.2.2.1 hs.2.2.2
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
    hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2,
    hg.1, hg.2.1, hg.2.2.1, hg.2.2.2⟩

/-! ## Repeated-product seven witnesses -/

noncomputable def GNCubicPairedRepeatedProductSevenWitnessSpace
    (X D : ℕ) : Finset ℕ :=
  (GNCubicPairedSevenSectorWitnessSpace X D).filter
    (fun a => 7 ∣ GNCubicForwardRepeatedPart a *
      GNCubicSwapRepeatedPart a)

theorem mem_GNCubicPairedRepeatedProductSevenWitnessSpace_iff
    {X D a : ℕ} :
    a ∈ GNCubicPairedRepeatedProductSevenWitnessSpace X D ↔
      a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D ∧
        a % 7 = 1 ∧
        7 ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a := by
  simp only [GNCubicPairedRepeatedProductSevenWitnessSpace, Finset.mem_filter,
    mem_GNCubicPairedSevenSectorWitnessSpace_iff]
  constructor
  · rintro ⟨⟨ha, ha7⟩, hprod⟩
    exact ⟨ha, ha7, hprod⟩
  · rintro ⟨ha, ha7, hprod⟩
    exact ⟨⟨ha, ha7⟩, hprod⟩

theorem GNCubicPairedRepeatedProductSevenWitnessSpace_eq_deep_union
    (X D : ℕ) :
    GNCubicPairedRepeatedProductSevenWitnessSpace X D =
      GNCubicPairedForwardSevenDeepWitnessSpace X D ∪
        GNCubicPairedSwapSevenDeepWitnessSpace X D := by
  classical
  ext a
  constructor
  · intro ha
    have hs := mem_GNCubicPairedRepeatedProductSevenWitnessSpace_iff.mp ha
    have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hs.1
    rcases (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState haPos hs.2.1).mp
      hs.2.2 with h29 | h22
    · exact Finset.mem_union.mpr (Or.inl
        (mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mpr ⟨hs.1, h29⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mpr ⟨hs.1, h22⟩))
  · intro ha
    rcases Finset.mem_union.mp ha with hF | hG
    · have hF' := mem_GNCubicPairedForwardSevenDeepWitnessSpace_iff.mp hF
      have ha7 := mod_seven_eq_one_of_mod_fortyNine_eq_twentyNine hF'.2
      have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hF'.1
      have hprod := (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState
        haPos ha7).mpr (Or.inl hF'.2)
      exact mem_GNCubicPairedRepeatedProductSevenWitnessSpace_iff.mpr
        ⟨hF'.1, ha7, hprod⟩
    · have hG' := mem_GNCubicPairedSwapSevenDeepWitnessSpace_iff.mp hG
      have ha7 := mod_seven_eq_one_of_mod_fortyNine_eq_twentyTwo hG'.2
      have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hG'.1
      have hprod := (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState
        haPos ha7).mpr (Or.inr hG'.2)
      exact mem_GNCubicPairedRepeatedProductSevenWitnessSpace_iff.mpr
        ⟨hG'.1, ha7, hprod⟩

theorem GNCubicPairedRepeatedProductSevenWitnessSpace_card_eq_deep_cards
    (X D : ℕ) :
    (GNCubicPairedRepeatedProductSevenWitnessSpace X D).card =
      (GNCubicPairedForwardSevenDeepWitnessSpace X D).card +
        (GNCubicPairedSwapSevenDeepWitnessSpace X D).card := by
  rw [GNCubicPairedRepeatedProductSevenWitnessSpace_eq_deep_union,
    Finset.card_union_of_disjoint
      (GNCubicPairedForwardDeep_disjoint_SwapDeep X D)]

theorem GNCubicPairedShallowSevenWitnessSpace_iff_not_repeatedProductSeven
    {X D a : ℕ} :
    a ∈ GNCubicPairedSevenSectorWitnessSpace X D ∧
        ¬ 7 ∣ GNCubicForwardRepeatedPart a * GNCubicSwapRepeatedPart a ↔
      a ∈ GNCubicPairedShallowSevenWitnessSpace X D := by
  constructor
  · rintro ⟨hs, hnot⟩
    have hsm := mem_GNCubicPairedSevenSectorWitnessSpace_iff.mp hs
    have haPos := pos_of_mem_GNCubicPairedSevenSectorShell hsm.1
    have h29 : a % 49 ≠ 29 := by
      intro h29
      apply hnot
      exact (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState
        haPos hsm.2).mpr (Or.inl h29)
    have h22 : a % 49 ≠ 22 := by
      intro h22
      apply hnot
      exact (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState
        haPos hsm.2).mpr (Or.inr h22)
    exact mem_GNCubicPairedShallowSevenWitnessSpace_iff.mpr
      ⟨hsm.1, hsm.2, h29, h22⟩
  · intro ha
    have hs := mem_GNCubicPairedShallowSevenWitnessSpace_iff.mp ha
    refine ⟨mem_GNCubicPairedSevenSectorWitnessSpace_iff.mpr ⟨hs.1, hs.2.1⟩, ?_⟩
    intro hprod
    rcases (seven_dvd_GNCubicPairedRepeatedProduct_iff_deepState
      (pos_of_mem_GNCubicPairedSevenSectorShell hs.1) hs.2.1).mp hprod with h29 | h22
    · exact hs.2.2.1 h29
    · exact hs.2.2.2 h22

end DkMath.ABC

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.PrimitiveSet.BranchBridge

#print "file: DkMath.NumberTheory.PrimitiveSet.DescentBridge"

namespace DkMath.NumberTheory.PrimitiveSet

open DkMath.CosmicFormula.Mass

/--
Mass monotonicity along divisibility descent.

The convention is that `a ∣ b` means `a` is a lower divisor of `b`, so a
divisibility-monotone mass satisfies `μ a <= μ b`.
-/
def DvdMonotoneMass (M : MassSpace ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, a ∣ b → M.μ a ≤ M.μ b

/--
A finite chain family controlled by divisibility below chosen source nodes.

This is the lightest descent provider: every point on the `i`-th chain divides
the source `source i`.
-/
structure DvdControlledChainFamily
    (ι : Type _) [DecidableEq ι]
    extends DivisibilityChainFamily ι where
  source : ι → ℕ
  chain_dvd_source :
    ∀ i ∈ index, ∀ h ∈ chain i, h ∣ source i

namespace DvdControlledChainFamily

/--
Divisibility-controlled one-step divisor-descent family at source `n`.

For each indexed divisor label `q`, the chain is `{n / q, n}` and the source is
`n`. The divisor hypothesis supplies `n / q ∣ n`, so each chain is comparable
by divisibility and lies below its source.
-/
def divisorStep
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    DvdControlledChainFamily ℕ where
  index := I
  chain := fun q => ({n / q, n} : Finset ℕ)
  chain_is_chain := by
    intro q hq a b ha hb
    have hchild : n / q ∣ n := Nat.div_dvd_of_dvd (hdiv q hq)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl (dvd_refl (n / q))
    · exact Or.inl hchild
    · exact Or.inr hchild
    · exact Or.inl (dvd_refl _)
  source := fun _ => n
  chain_dvd_source := by
    intro q hq h hh
    have hchild : n / q ∣ n := Nat.div_dvd_of_dvd (hdiv q hq)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · exact hchild
    · exact dvd_refl _

@[simp] theorem divisorStep_index
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (divisorStep n I hdiv).index = I := rfl

@[simp] theorem divisorStep_chain
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (divisorStep n I hdiv).chain = fun q => ({n / q, n} : Finset ℕ) := rfl

@[simp] theorem divisorStep_source
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (divisorStep n I hdiv).source = fun _ => n := rfl

/--
Convert a divisibility-controlled forest into a source-controlled forest using
a divisibility-monotone mass.
-/
def toSourceControlled
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    SourceControlledChainFamily M ι where
  index := F.index
  chain := F.chain
  chain_is_chain := F.chain_is_chain
  source := F.source
  mass_le_source := by
    intro i hi h hh
    exact hM (F.chain_dvd_source i hi h hh)

@[simp] theorem toSourceControlled_index
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).index = F.index := rfl

@[simp] theorem toSourceControlled_chain
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).chain = F.chain := rfl

@[simp] theorem toSourceControlled_source
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ}
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).source = F.source := rfl

/--
Primitive hitting bound supplied by divisibility descent plus monotone mass.
-/
theorem primitive_hitMass_le_sourceMass
    {ι : Type _} [DecidableEq ι]
    {M : MassSpace ℕ} {S : Finset ℕ}
    (hS : PrimitiveOn S)
    (F : DvdControlledChainFamily ι)
    (hM : DvdMonotoneMass M) :
    (F.toSourceControlled hM).hitMass S ≤
      (F.toSourceControlled hM).sourceMass := by
  exact (F.toSourceControlled hM).primitive_hitMass_le_sourceMass hS

end DvdControlledChainFamily

namespace SourceControlledChainFamily

/--
Source-controlled one-step divisor-descent family at source `n`.

This is `DvdControlledChainFamily.divisorStep` converted by a
divisibility-monotone mass. Its index is definitionally the supplied index,
which keeps compatibility with divisor-channel providers lightweight.
-/
def ofDivisorStep
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    SourceControlledChainFamily M ℕ :=
  (DvdControlledChainFamily.divisorStep n I hdiv).toSourceControlled hM

@[simp] theorem ofDivisorStep_index
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (ofDivisorStep hM n I hdiv).index = I := rfl

@[simp] theorem ofDivisorStep_chain
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (ofDivisorStep hM n I hdiv).chain = fun q => ({n / q, n} : Finset ℕ) := rfl

@[simp] theorem ofDivisorStep_source
    {M : MassSpace ℕ}
    (hM : DvdMonotoneMass M)
    (n : ℕ) (I : Finset ℕ)
    (hdiv : ∀ q ∈ I, q ∣ n) :
    (ofDivisorStep hM n I hdiv).source = fun _ => n := rfl

end SourceControlledChainFamily

/-- The unit natural mass is monotone along divisibility. -/
theorem unitNatMassSpace_dvdMonotone :
    DvdMonotoneMass unitNatMassSpace := by
  intro _a _b _hab
  rfl

/--
Indicator mass for nonunit natural nodes.

The node `1` has mass `0`; every other natural node has mass `1`. This is still
a bounded toy mass, but unlike `unitNatMassSpace` it can distinguish descent
chains that reach the terminal divisor `1`.
-/
def nonunitNatMassSpace : MassSpace ℕ where
  μ := fun n => if n = 1 then 0 else 1
  nonneg := by
    intro n
    by_cases hn : n = 1 <;> simp [hn]

/--
The nonunit indicator mass is monotone along divisibility.

If `a ∣ b` and `b = 1`, then `a = 1`; otherwise the target mass is already `1`.
-/
theorem nonunitNatMassSpace_dvdMonotone :
    DvdMonotoneMass nonunitNatMassSpace := by
  intro a b hab
  by_cases hb : b = 1
  · subst b
    have ha : a = 1 := Nat.dvd_one.mp hab
    simp [nonunitNatMassSpace, ha]
  · by_cases ha : a = 1 <;> simp [nonunitNatMassSpace, ha, hb]

/--
Tail-support indicator mass above a natural threshold.

The mass is `1` on `0` and on nodes `n` with `N ≤ n`, and `0` otherwise. The
special value at `0` keeps the mass monotone for the global relation `a ∣ b`.
On positive descent chains this behaves as the usual threshold indicator.
-/
def tailIndicatorNatMassSpace (N : ℕ) : MassSpace ℕ where
  μ := fun n => if n = 0 ∨ N ≤ n then 1 else 0
  nonneg := by
    intro n
    by_cases hn : n = 0 ∨ N ≤ n <;> simp [hn]

/-- The tail-support indicator mass is monotone along divisibility. -/
theorem tailIndicatorNatMassSpace_dvdMonotone (N : ℕ) :
    DvdMonotoneMass (tailIndicatorNatMassSpace N) := by
  intro a b hab
  by_cases hb : b = 0 ∨ N ≤ b
  · dsimp [tailIndicatorNatMassSpace]
    simp [hb]
    split <;> norm_num
  · have hb0 : b ≠ 0 := by
      intro hbz
      exact hb (Or.inl hbz)
    have hab_le : a ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hab
    have ha0 : a ≠ 0 := by
      intro haz
      rcases hab with ⟨c, hc⟩
      exact hb0 (by simpa [haz] using hc)
    have hNa : ¬ N ≤ a := by
      intro hNa
      exact hb (Or.inr (hNa.trans hab_le))
    have ha : ¬ (a = 0 ∨ N ≤ a) := by
      intro ha
      rcases ha with haz | hNa'
      · exact ha0 haz
      · exact hNa hNa'
    simp [tailIndicatorNatMassSpace, hb, ha]

/--
Scaled tail-support indicator mass above a natural threshold.

This keeps the same support as `tailIndicatorNatMassSpace`, but assigns a
nonnegative rational height `c` to the tail. It is a bounded toy model for
separating the support question from the weight-amplitude question.
-/
def scaledTailIndicatorNatMassSpace
    (N : ℕ) (c : ℚ) (hc : 0 ≤ c) : MassSpace ℕ where
  μ := fun n => if n = 0 ∨ N ≤ n then c else 0
  nonneg := by
    intro n
    by_cases hn : n = 0 ∨ N ≤ n
    · simp [hn, hc]
    · simp [hn]

/-- The scaled tail-support indicator mass is monotone along divisibility. -/
theorem scaledTailIndicatorNatMassSpace_dvdMonotone
    (N : ℕ) (c : ℚ) (hc : 0 ≤ c) :
    DvdMonotoneMass (scaledTailIndicatorNatMassSpace N c hc) := by
  intro a b hab
  by_cases hb : b = 0 ∨ N ≤ b
  · by_cases ha : a = 0 ∨ N ≤ a
    · simp [scaledTailIndicatorNatMassSpace, hb, ha]
    · simp [scaledTailIndicatorNatMassSpace, hb, ha, hc]
  · have hb0 : b ≠ 0 := by
      intro hbz
      exact hb (Or.inl hbz)
    have hab_le : a ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hab
    have ha0 : a ≠ 0 := by
      intro haz
      rcases hab with ⟨d, hd⟩
      exact hb0 (by simpa [haz] using hd)
    have hNa : ¬ N ≤ a := by
      intro hNa
      exact hb (Or.inr (hNa.trans hab_le))
    have ha : ¬ (a = 0 ∨ N ≤ a) := by
      intro ha
      rcases ha with haz | hNa'
      · exact ha0 haz
      · exact hNa hNa'
    simp [scaledTailIndicatorNatMassSpace, hb, ha]

/--
Two-step tail-support mass with a low and high tail height.

The mass is `cHigh` on `0` and on the upper tail `M ≤ n`, `cLow` on the
intermediate tail `N ≤ n` before the upper tail, and `0` below `N`. The
assumption `cLow ≤ cHigh` makes the height monotone as the natural label grows.
-/
def twoStepTailNatMassSpace
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh) : MassSpace ℕ where
  μ := fun n =>
    if n = 0 ∨ M ≤ n then cHigh else if N ≤ n then cLow else 0
  nonneg := by
    intro n
    have hHigh : 0 ≤ cHigh := hLow.trans hStep
    by_cases hnHigh : n = 0 ∨ M ≤ n
    · simp [hnHigh, hHigh]
    · by_cases hnLow : N ≤ n
      · simp [hnHigh, hnLow, hLow]
      · simp [hnHigh, hnLow]

/-- The two-step tail-support mass is monotone along divisibility. -/
theorem twoStepTailNatMassSpace_dvdMonotone
    (N M : ℕ) (cLow cHigh : ℚ)
    (hLow : 0 ≤ cLow) (hStep : cLow ≤ cHigh) :
    DvdMonotoneMass (twoStepTailNatMassSpace N M cLow cHigh hLow hStep) := by
  intro a b hab
  have hHigh : 0 ≤ cHigh := hLow.trans hStep
  by_cases hbHigh : b = 0 ∨ M ≤ b
  · by_cases haHigh : a = 0 ∨ M ≤ a
    · simp [twoStepTailNatMassSpace, hbHigh, haHigh]
    · by_cases haLow : N ≤ a
      · simp [twoStepTailNatMassSpace, hbHigh, haHigh, haLow, hStep]
      · simp [twoStepTailNatMassSpace, hbHigh, haHigh, haLow, hHigh]
  · have hb0 : b ≠ 0 := by
      intro hbz
      exact hbHigh (Or.inl hbz)
    have hab_le : a ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hab
    have ha0 : a ≠ 0 := by
      intro haz
      rcases hab with ⟨d, hd⟩
      exact hb0 (by simpa [haz] using hd)
    have hMa : ¬ M ≤ a := by
      intro hMa
      exact hbHigh (Or.inr (hMa.trans hab_le))
    have haHigh : ¬ (a = 0 ∨ M ≤ a) := by
      intro ha
      rcases ha with haz | hMa'
      · exact ha0 haz
      · exact hMa hMa'
    by_cases hbLow : N ≤ b
    · by_cases haLow : N ≤ a
      · simp [twoStepTailNatMassSpace, hbHigh, haHigh, hbLow, haLow]
      · simp [twoStepTailNatMassSpace, hbHigh, haHigh, hbLow, haLow, hLow]
    · have hNa : ¬ N ≤ a := by
        intro hNa
        exact hbLow (hNa.trans hab_le)
      simp [twoStepTailNatMassSpace, hbHigh, haHigh, hbLow, hNa]

/--
The sample Bool-indexed chain family is controlled by divisibility below
sources `8` and `9`.
-/
def sampleDvdControlledBoolChainFamily : DvdControlledChainFamily Bool where
  index := sampleBoolChainFamily.index
  chain := sampleBoolChainFamily.chain
  chain_is_chain := sampleBoolChainFamily.chain_is_chain
  source := fun b => if b then 9 else 8
  chain_dvd_source := by
    intro b hb h hh
    fin_cases hb
    · simp only [sampleBoolChainFamily] at hh ⊢
      fin_cases hh <;> norm_num
    · simp only [sampleBoolChainFamily] at hh ⊢
      fin_cases hh <;> norm_num

/--
Concrete divisibility-controlled sample: `{2, 3}` hitting the sample forest has
indexed unit hit mass bounded by source mass.
-/
theorem primitive_two_three_sampleDvdControlledBoolChainFamily_hitMass_le_sourceMass :
    (sampleDvdControlledBoolChainFamily.toSourceControlled
      unitNatMassSpace_dvdMonotone).hitMass ({2, 3} : Finset ℕ) ≤
      (sampleDvdControlledBoolChainFamily.toSourceControlled
        unitNatMassSpace_dvdMonotone).sourceMass := by
  exact sampleDvdControlledBoolChainFamily.primitive_hitMass_le_sourceMass
    primitiveOn_pair_two_three
    unitNatMassSpace_dvdMonotone

end DkMath.NumberTheory.PrimitiveSet

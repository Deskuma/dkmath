/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization

#print "file: DkMath.RH.CFBRC.EtaMirrorEndpointDefinedShares"

noncomputable section

namespace DkMath.RH.CFBRCProjection

/-!
# Defined value layer for eta mirror endpoint shares

The ordinary real-valued share functions are total because field division is
total in Lean.  This module separately records the mathematical domain on which
the individual Core and Gap shares are defined as ordinary quotients.

At `etaMirrorEndpointOuterBig N s = 0`, neither individual share has a
`DefinedRatioWitness`.  The total structural share remains defined and equal to
one, and the collapsed value layer is handled by the regularized punctured
limit from `EtaMirrorEndpointOuterNormalization`.
-/

/-- Existence witness for the ordinary Core share. -/
abbrev etaMirrorEndpointCoreShareDefined
    (N : ℕ) (s : ℂ) : Type :=
  DkMath.KUS.DefinedRatioWitness ℝ
    (etaMirrorEndpointCore N s)
    (etaMirrorEndpointOuterBig N s)

/-- Existence witness for the ordinary Gap share. -/
abbrev etaMirrorEndpointGapShareDefined
    (N : ℕ) (s : ℂ) : Type :=
  DkMath.KUS.DefinedRatioWitness ℝ
    (etaMirrorEndpointGapCore N s)
    (etaMirrorEndpointOuterBig N s)

/-- Both individual shares, defined against the same nonzero outer Big. -/
abbrev etaMirrorEndpointSharePairDefined
    (N : ℕ) (s : ℂ) : Type :=
  etaMirrorEndpointCoreShareDefined N s ×
    etaMirrorEndpointGapShareDefined N s

/-- A nonzero outer Big constructs the ordinary Core-share witness. -/
def etaMirrorEndpointCoreShareDefined_of_outer_ne
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointCoreShareDefined N s :=
  DkMath.KUS.DefinedRatioWitness.of_denominator_ne hOuter

/-- A nonzero outer Big constructs the ordinary Gap-share witness. -/
def etaMirrorEndpointGapShareDefined_of_outer_ne
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointGapShareDefined N s :=
  DkMath.KUS.DefinedRatioWitness.of_denominator_ne hOuter

/-- A nonzero outer Big constructs both ordinary share witnesses. -/
def etaMirrorEndpointSharePairDefined_of_outer_ne
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s ≠ 0) :
    etaMirrorEndpointSharePairDefined N s :=
  (etaMirrorEndpointCoreShareDefined_of_outer_ne N s hOuter,
    etaMirrorEndpointGapShareDefined_of_outer_ne N s hOuter)

/-- The defined Core-share witness evaluates to the existing numeric share. -/
@[simp] theorem etaMirrorEndpointCoreShareDefined_value_eq
    (N : ℕ) (s : ℂ)
    (r : etaMirrorEndpointCoreShareDefined N s) :
    r.value = etaMirrorEndpointCoreShare N s := by
  rfl

/-- The defined Gap-share witness evaluates to the existing numeric share. -/
@[simp] theorem etaMirrorEndpointGapShareDefined_value_eq
    (N : ℕ) (s : ℂ)
    (r : etaMirrorEndpointGapShareDefined N s) :
    r.value = etaMirrorEndpointGapShare N s := by
  rfl

/-- The ordinary Core share exists exactly when the shared outer Big is nonzero. -/
theorem etaMirrorEndpointCoreShareDefined_nonempty_iff
    (N : ℕ) (s : ℂ) :
    Nonempty (etaMirrorEndpointCoreShareDefined N s) ↔
      etaMirrorEndpointOuterBig N s ≠ 0 := by
  exact
    DkMath.KUS.DefinedRatioWitness.nonempty_iff_denominator_ne
      (etaMirrorEndpointCore N s) (etaMirrorEndpointOuterBig N s)

/-- The ordinary Gap share exists exactly when the shared outer Big is nonzero. -/
theorem etaMirrorEndpointGapShareDefined_nonempty_iff
    (N : ℕ) (s : ℂ) :
    Nonempty (etaMirrorEndpointGapShareDefined N s) ↔
      etaMirrorEndpointOuterBig N s ≠ 0 := by
  exact
    DkMath.KUS.DefinedRatioWitness.nonempty_iff_denominator_ne
      (etaMirrorEndpointGapCore N s) (etaMirrorEndpointOuterBig N s)

/-- The pair of ordinary shares exists exactly when the common denominator is nonzero. -/
theorem etaMirrorEndpointSharePairDefined_nonempty_iff
    (N : ℕ) (s : ℂ) :
    Nonempty (etaMirrorEndpointSharePairDefined N s) ↔
      etaMirrorEndpointOuterBig N s ≠ 0 := by
  constructor
  · rintro ⟨r⟩
    exact r.1.denominator_ne
  · intro hOuter
    exact ⟨etaMirrorEndpointSharePairDefined_of_outer_ne N s hOuter⟩

/-- Every defined pair is nonnegative componentwise. -/
theorem etaMirrorEndpointSharePairDefined_nonneg
    (N : ℕ) (s : ℂ)
    (r : etaMirrorEndpointSharePairDefined N s) :
    0 ≤ r.1.value ∧ 0 ≤ r.2.value := by
  have hOuterPos : 0 < etaMirrorEndpointOuterBig N s :=
    lt_of_le_of_ne
      (etaMirrorEndpointOuterBig_nonneg N s)
      (Ne.symm r.1.denominator_ne)
  rw [etaMirrorEndpointCoreShareDefined_value_eq,
    etaMirrorEndpointGapShareDefined_value_eq]
  exact etaMirrorEndpointShares_nonneg N s hOuterPos

/-- Every defined pair exhausts the shared outer Big. -/
theorem etaMirrorEndpointSharePairDefined_add_eq_one
    (N : ℕ) (s : ℂ)
    (r : etaMirrorEndpointSharePairDefined N s) :
    r.1.value + r.2.value = 1 := by
  rw [etaMirrorEndpointCoreShareDefined_value_eq,
    etaMirrorEndpointGapShareDefined_value_eq]
  exact etaMirrorEndpointCoreShare_add_gapShare N s r.1.denominator_ne

/-- A collapsed outer Big leaves no ordinary Core-share witness. -/
theorem etaMirrorEndpointCoreShareDefined_not_nonempty_of_outer_eq_zero
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s = 0) :
    ¬ Nonempty (etaMirrorEndpointCoreShareDefined N s) := by
  exact
    DkMath.KUS.DefinedRatioWitness.not_nonempty_of_denominator_eq_zero
      (etaMirrorEndpointCore N s) (etaMirrorEndpointOuterBig N s) hOuter

/-- A collapsed outer Big leaves no ordinary Gap-share witness. -/
theorem etaMirrorEndpointGapShareDefined_not_nonempty_of_outer_eq_zero
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s = 0) :
    ¬ Nonempty (etaMirrorEndpointGapShareDefined N s) := by
  exact
    DkMath.KUS.DefinedRatioWitness.not_nonempty_of_denominator_eq_zero
      (etaMirrorEndpointGapCore N s) (etaMirrorEndpointOuterBig N s) hOuter

/-- At collapse both individual ordinary shares are outside their defined domain. -/
theorem etaMirrorEndpointIndividualShares_not_defined_of_outer_eq_zero
    (N : ℕ) (s : ℂ)
    (hOuter : etaMirrorEndpointOuterBig N s = 0) :
    ¬ Nonempty (etaMirrorEndpointCoreShareDefined N s) ∧
      ¬ Nonempty (etaMirrorEndpointGapShareDefined N s) := by
  exact ⟨
    etaMirrorEndpointCoreShareDefined_not_nonempty_of_outer_eq_zero N s hOuter,
    etaMirrorEndpointGapShareDefined_not_nonempty_of_outer_eq_zero N s hOuter⟩

end DkMath.RH.CFBRCProjection

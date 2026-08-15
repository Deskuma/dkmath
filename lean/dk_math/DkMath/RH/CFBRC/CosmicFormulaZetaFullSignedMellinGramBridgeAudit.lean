/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.CosmicFormulaZetaSignedSpectralNodeFactorizationAudit
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.CosmicFormulaZetaFullSignedMellinGramBridgeAudit"

/-!
# CFZP-006F: full-support signed Mellin Gram bridge

The signed two-node feature from CFZP-006E is now indexed over the finite
canonical prime-power support.  The subtype stores the support-membership
certificate, while `Fintype.equivFin` supplies a finite enumeration for the
generic Mellin Gram API.

Only finite fixed-box identities are recorded here.  This module does not
identify the Gram energy with a completion remainder or a rectangle remainder,
does not assert an off-diagonal sign, and does not introduce an infinite limit
or an RH consequence.
-/

noncomputable section

namespace DkMath.RH.CFBRCProjection

open DkMath.Analysis
open DkMath.NumberTheory
open DkMath.NumberTheory.PrimitiveSet
open MeasureTheory
open Set
open scoped ComplexConjugate Interval Topology

/-! ## A. Finite canonical signed support -/

abbrev CfzpCanonicalPrimePowerIndex (X : ℕ) :=
  {q : ℕ // q ∈ canonicalPrimePowerSupportUpTo X}

abbrev CfzpCanonicalSignedSpectralIndex (X : ℕ) :=
  CfzpCanonicalPrimePowerIndex X × Fin 2

noncomputable def cfzpCanonicalSignedLogNodeRaw
    (X : ℕ) (i : CfzpCanonicalSignedSpectralIndex X) : ℂ :=
  cfzpPrimePowerSignedLogNodeFamily i.1.1 i.2

noncomputable def cfzpCanonicalSignedLogCoefficientRaw
    (X : ℕ) (s : ℂ) (i : CfzpCanonicalSignedSpectralIndex X) : ℂ :=
  cfzpPrimePowerSignedLogCoefficientFamily i.1.1 s i.2

theorem cfzpCanonicalSignedLogRawFeatureSum_eq_shiftedSource
    (X : ℕ) (s : ℂ) (τ : ℝ) :
    ∑ i : CfzpCanonicalSignedSpectralIndex X,
      cfzpCanonicalSignedLogCoefficientRaw X s i *
        (cfzpCanonicalSignedLogNodeRaw X i *
          Complex.exp ((τ : ℂ) * cfzpCanonicalSignedLogNodeRaw X i)) =
      cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
        (cfzpHorizontalRealShift s τ) := by
  classical
  unfold cfzpCanonicalSignedLogCoefficientRaw
    cfzpCanonicalSignedLogNodeRaw
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_eq_attach]
  rw [Finset.sum_attach (s := canonicalPrimePowerSupportUpTo X)
    (f := fun q => ∑ k : Fin 2,
      cfzpPrimePowerSignedLogCoefficientFamily q s k *
        (cfzpPrimePowerSignedLogNodeFamily q k *
          Complex.exp ((τ : ℂ) * cfzpPrimePowerSignedLogNodeFamily q k)))]
  calc
    (∑ q ∈ canonicalPrimePowerSupportUpTo X, ∑ k : Fin 2,
        cfzpPrimePowerSignedLogCoefficientFamily q s k *
          (cfzpPrimePowerSignedLogNodeFamily q k *
            Complex.exp ((τ : ℂ) * cfzpPrimePowerSignedLogNodeFamily q k))) =
      ∑ q ∈ canonicalPrimePowerSupportUpTo X,
        cfzpCanonicalFunctionalReflectionScaledMode q
          (cfzpHorizontalRealShift s τ) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact cfzpPrimePowerSignedLogFeatureFamily_sum_eq_scaledMode
        (one_lt_of_mem_canonicalPrimePowerSupportUpTo hq) s τ
    _ = _ := by rfl

/-! ## B. A canonical `Fin` enumeration -/

noncomputable def cfzpCanonicalSignedSpectralIndexEquivFin (X : ℕ) :
    CfzpCanonicalSignedSpectralIndex X ≃
      Fin (Fintype.card (CfzpCanonicalSignedSpectralIndex X)) :=
  Fintype.equivFin _

noncomputable def cfzpCanonicalSignedLogNodeFinFamily
    (X : ℕ) : Fin (Fintype.card (CfzpCanonicalSignedSpectralIndex X)) → ℂ :=
  fun j => cfzpCanonicalSignedLogNodeRaw X
    ((cfzpCanonicalSignedSpectralIndexEquivFin X).symm j)

noncomputable def cfzpCanonicalSignedLogCoefficientFinFamily
    (X : ℕ) (s : ℂ) :
    Fin (Fintype.card (CfzpCanonicalSignedSpectralIndex X)) → ℂ :=
  fun j => cfzpCanonicalSignedLogCoefficientRaw X s
    ((cfzpCanonicalSignedSpectralIndexEquivFin X).symm j)

noncomputable def cfzpCanonicalSignedLogFinFeatureSum
    (X : ℕ) (s : ℂ) (τ : ℝ) : ℂ :=
  ∑ j : Fin (Fintype.card (CfzpCanonicalSignedSpectralIndex X)),
    cfzpCanonicalSignedLogCoefficientFinFamily X s j *
      (cfzpCanonicalSignedLogNodeFinFamily X j *
        Complex.exp ((τ : ℂ) * cfzpCanonicalSignedLogNodeFinFamily X j))

theorem cfzpCanonicalSignedLogFinFeatureSum_eq_shiftedSource
    (X : ℕ) (s : ℂ) (τ : ℝ) :
    cfzpCanonicalSignedLogFinFeatureSum X s τ =
      cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
        (cfzpHorizontalRealShift s τ) := by
  classical
  unfold cfzpCanonicalSignedLogFinFeatureSum
    cfzpCanonicalSignedLogCoefficientFinFamily
    cfzpCanonicalSignedLogNodeFinFamily
  let e := cfzpCanonicalSignedSpectralIndexEquivFin X
  let f : CfzpCanonicalSignedSpectralIndex X → ℂ := fun i =>
    cfzpCanonicalSignedLogCoefficientRaw X s i *
      (cfzpCanonicalSignedLogNodeRaw X i *
        Complex.exp ((τ : ℂ) * cfzpCanonicalSignedLogNodeRaw X i))
  change (∑ j, f (e.symm j)) = _
  rw [e.symm.sum_comp]
  exact cfzpCanonicalSignedLogRawFeatureSum_eq_shiftedSource X s τ

/-! ## C. Full signed fixed-box energy -/

noncomputable def cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
    (ε : ℝ) (X : ℕ) (s : ℂ) : ℝ :=
  mellinQuadraticBoxGramEnergy ε
    (cfzpCanonicalSignedLogNodeFinFamily X)
    (cfzpCanonicalSignedLogCoefficientFinFamily X s)

theorem cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_eq_shiftedSource_integral
    (ε : ℝ) (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s =
      (2 * ε)⁻¹ *
        ∫ τ in (-ε)..ε,
          Complex.normSq
            (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X
              (cfzpHorizontalRealShift s τ)) := by
  unfold cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
    mellinQuadraticBoxGramEnergy
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with τ
  intro _
  change Complex.normSq (cfzpCanonicalSignedLogFinFeatureSum X s τ) = _
  rw [cfzpCanonicalSignedLogFinFeatureSum_eq_shiftedSource]

theorem cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_nonneg
    {ε : ℝ} (hε : 0 < ε) (X : ℕ) (s : ℂ) :
    0 ≤ cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s := by
  unfold cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
  exact mellinQuadraticBoxGramEnergy_nonneg hε _ _

/-! ## D. Zero-shift source mass -/

theorem cfzpCanonicalSignedLogFinFeatureSum_zeroShift
    (X : ℕ) (s : ℂ) :
    cfzpCanonicalSignedLogFinFeatureSum X s 0 =
      cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s := by
  rw [cfzpCanonicalSignedLogFinFeatureSum_eq_shiftedSource]
  simp [cfzpHorizontalRealShift]

theorem cfzpCanonicalSignedLogFinFeatureSum_zeroShift_normSq
    (X : ℕ) (s : ℂ) :
    Complex.normSq (cfzpCanonicalSignedLogFinFeatureSum X s 0) =
      cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s := by
  rw [cfzpCanonicalSignedLogFinFeatureSum_zeroShift]
  rfl

/-! ## E. Quadratic-form surface -/

noncomputable def cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm
    (ε : ℝ) (X : ℕ) (s : ℂ) : ℂ :=
  mellinQuadraticBoxGramQuadraticForm ε
    (cfzpCanonicalSignedLogNodeFinFamily X)
    (cfzpCanonicalSignedLogCoefficientFinFamily X s)

theorem cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_eq_energy
    {ε : ℝ} (hε : 0 < ε) (X : ℕ) (s : ℂ) :
    cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm ε X s =
      (cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s : ℂ) := by
  unfold cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm
    cfzpCanonicalFunctionalReflectionFullSignedGramEnergy
  exact mellinQuadraticBoxGramQuadraticForm_eq_energy hε _ _

theorem cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_im_eq_zero
    {ε : ℝ} (hε : 0 < ε) (X : ℕ) (s : ℂ) :
    (cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm ε X s).im = 0 := by
  rw [cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_eq_energy hε]
  simp

theorem cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_re_eq_energy
    {ε : ℝ} (hε : 0 < ε) (X : ℕ) (s : ℂ) :
    (cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm ε X s).re =
      cfzpCanonicalFunctionalReflectionFullSignedGramEnergy ε X s := by
  rw [cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_eq_energy hε]
  simp

theorem cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_re_nonneg
    {ε : ℝ} (hε : 0 < ε) (X : ℕ) (s : ℂ) :
    0 ≤ (cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm ε X s).re := by
  rw [cfzpCanonicalFunctionalReflectionFullSignedGramQuadraticForm_re_eq_energy hε]
  exact cfzpCanonicalFunctionalReflectionFullSignedGramEnergy_nonneg hε X s

end DkMath.RH.CFBRCProjection

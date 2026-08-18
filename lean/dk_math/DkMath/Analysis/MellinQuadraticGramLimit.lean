/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Analysis.MellinQuadraticGramKernel
import Mathlib.Tactic

#print "file: DkMath.Analysis.MellinQuadraticGramLimit"

/-!
# Fixed finite Mellin Gram zero-width limits

This module lifts the centered Mellin approximate-identity limit from the
spectral multiplier to the finite Gram kernel, quadratic form, and real
energy.  It contains no RH, zeta, or CFBRC-specific definitions.

All limits are one-sided limits along `𝓝[>] 0`; no value of a Gram energy at
`ε = 0` is used.
-/

noncomputable section

namespace DkMath.Analysis

open Filter
open scoped Topology

theorem tendsto_mellinQuadraticBoxMultiplier_one
    (z : ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxMultiplier ε z)
      (𝓝[>] 0) (𝓝 1) := by
  simpa [mellinQuadraticBoxMultiplier] using
    (tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one z)

theorem tendsto_mellinQuadraticBoxGramKernel_zeroWidth
    (z w : ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxGramKernel ε z w)
      (𝓝[>] 0)
      (𝓝 (z * starRingEnd ℂ w)) := by
  have hmult :=
    tendsto_mellinQuadraticBoxMultiplier_one (z + starRingEnd ℂ w)
  have hconst : Tendsto (fun _ : ℝ => z * starRingEnd ℂ w)
      (𝓝[>] 0) (𝓝 (z * starRingEnd ℂ w)) :=
    tendsto_const_nhds
  simpa [mellinQuadraticBoxGramKernel] using hconst.mul hmult

theorem tendsto_mellinQuadraticBoxGramQuadraticForm_zeroWidth
    {n : ℕ} (z : Fin n → ℂ) (c : Fin n → ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxGramQuadraticForm ε z c)
      (𝓝[>] 0)
      (𝓝 ((Complex.normSq (∑ j, c j * z j) : ℝ) : ℂ)) := by
  classical
  have hterm : ∀ i j : Fin n,
      Tendsto
        (fun ε : ℝ =>
          c i * starRingEnd ℂ (c j) *
            mellinQuadraticBoxGramKernel ε (z i) (z j))
        (𝓝[>] 0)
        (𝓝 (c i * starRingEnd ℂ (c j) *
          (z i * starRingEnd ℂ (z j)))) := by
    intro i j
    have hconst : Tendsto
        (fun _ : ℝ => c i * starRingEnd ℂ (c j))
        (𝓝[>] 0)
        (𝓝 (c i * starRingEnd ℂ (c j))) :=
      tendsto_const_nhds
    simpa [mul_assoc] using
      hconst.mul (tendsto_mellinQuadraticBoxGramKernel_zeroWidth
        (z i) (z j))
  have hinner : ∀ i : Fin n,
      Tendsto
        (fun ε : ℝ => ∑ j,
          c i * starRingEnd ℂ (c j) *
            mellinQuadraticBoxGramKernel ε (z i) (z j))
        (𝓝[>] 0)
        (𝓝 (∑ j,
          c i * starRingEnd ℂ (c j) *
            (z i * starRingEnd ℂ (z j)))) := by
    intro i
    exact tendsto_finsetSum (Finset.univ : Finset (Fin n))
      (fun j _ => hterm i j)
  have hdouble :
      Tendsto
        (fun ε : ℝ => ∑ i, ∑ j,
          c i * starRingEnd ℂ (c j) *
            mellinQuadraticBoxGramKernel ε (z i) (z j))
        (𝓝[>] 0)
        (𝓝 (∑ i, ∑ j,
          c i * starRingEnd ℂ (c j) *
            (z i * starRingEnd ℂ (z j)))) := by
    exact tendsto_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => hinner i)
  have hnorm :
      (Complex.normSq (∑ j, c j * z j) : ℂ) =
        ∑ i, ∑ j,
          c i * starRingEnd ℂ (c j) *
            (z i * starRingEnd ℂ (z j)) := by
    simpa [mul_assoc] using
      (mellinQuadraticBoxGram_feature_normSq_eq_double_sum z c 0)
  simpa [mellinQuadraticBoxGramQuadraticForm, hnorm] using hdouble

theorem tendsto_mellinQuadraticBoxGramEnergy_zeroWidth
    {n : ℕ} (z : Fin n → ℂ) (c : Fin n → ℂ) :
    Tendsto
      (fun ε : ℝ => mellinQuadraticBoxGramEnergy ε z c)
      (𝓝[>] 0)
      (𝓝 (Complex.normSq (∑ j, c j * z j))) := by
  have hform :=
    tendsto_mellinQuadraticBoxGramQuadraticForm_zeroWidth z c
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      mellinQuadraticBoxGramQuadraticForm ε z c =
        (mellinQuadraticBoxGramEnergy ε z c : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mellinQuadraticBoxGramQuadraticForm_eq_energy hε z c
  have henergyComplex :
    Tendsto
        (fun ε : ℝ => (mellinQuadraticBoxGramEnergy ε z c : ℂ))
        (𝓝[>] 0)
        (𝓝 ((Complex.normSq (∑ j, c j * z j) : ℝ) : ℂ)) :=
    hform.congr' (heq.mono fun ε hε => hε)
  have hre := (Complex.continuous_re.tendsto
    (Complex.normSq (∑ j, c j * z j))).comp henergyComplex
  simpa [Function.comp_def] using hre

end DkMath.Analysis

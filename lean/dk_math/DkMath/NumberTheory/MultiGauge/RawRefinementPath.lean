/-
Copyright (c) 2026 DkMath contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: DkMath contributors.
-/

import DkMath.NumberTheory.MultiGauge.RawNormalization
import Mathlib.Tactic

#print "file: DkMath.NumberTheory.MultiGauge.RawRefinementPath"

/-!
# Finite raw refinement paths

This module composes synchronized raw-coordinate refinements.  It deliberately
uses a factor list rather than manufacturing `GNGaugeTransition`s: common
scaling changes the raw common support while preserving the normalized
primitive coprime shape.
-/

namespace DkMath.NumberTheory.MultiGauge

open DkMath.CosmicFormula

private theorem GNGaugeStage.eq_of_coordinates_eq
    {a b : GNGaugeStage d} (hx : a.x = b.x) (hu : a.u = b.u) : a = b := by
  cases a with
  | mk ax au hac =>
    cases b with
    | mk bx bu hbc =>
      cases hx
      cases hu
      rfl

/-! ## Scale algebra -/

/-- Composition of two synchronized raw scalings. -/
theorem GNRawGaugeStage.scaleBy_scaleBy
    (k₁ k₂ : ℕ) (s : GNRawGaugeStage d) :
    GNRawGaugeStage.scaleBy k₂ (GNRawGaugeStage.scaleBy k₁ s) =
      GNRawGaugeStage.scaleBy (k₁ * k₂) s := by
  cases s with
  | mk x u =>
    simp only [GNRawGaugeStage.scaleBy]
    congr 1 <;> ring

/-- The gcd scale grows by the synchronized refinement factor. -/
theorem GNRawGaugeStage.scale_scaleBy
    (k : ℕ) (s : GNRawGaugeStage d) :
    (GNRawGaugeStage.scaleBy k s).scale = k * s.scale := by
  change Nat.gcd (k * s.x) (k * s.u) = k * Nat.gcd s.x s.u
  exact Nat.gcd_mul_left k s.x s.u

/-! ## Primitive-shape invariance -/

theorem GNRawGaugeStage.primitiveRawStage_scaleBy
    (s : GNRawGaugeStage d) (k : ℕ) (hk : 0 < k)
    (hg : 0 < s.scale) :
    (GNRawGaugeStage.scaleBy k s).primitiveRawStage = s.primitiveRawStage := by
  cases s with
  | mk x u =>
    simp only [GNRawGaugeStage.primitiveRawStage, GNRawGaugeStage.scale,
      GNRawGaugeStage.scaleBy]
    congr 1
    · rw [Nat.gcd_mul_left]
      simpa [Nat.mul_comm] using
        Nat.mul_div_mul_left x (Nat.gcd x u) hk
    · rw [Nat.gcd_mul_left, Nat.mul_comm]
      simpa [Nat.mul_comm] using
        Nat.mul_div_mul_left u (Nat.gcd x u) hk

/-- Positive synchronized scaling preserves the normalized primitive stage. -/
theorem GNRawGaugeStage.primitiveStage_scaleBy
    (s : GNRawGaugeStage d) (k : ℕ) (hk : 0 < k)
    (hg : 0 < s.scale) :
    (GNRawGaugeStage.scaleBy k s).primitiveStage
        (by rw [GNRawGaugeStage.scale_scaleBy]; exact mul_pos hk hg) =
      s.primitiveStage hg := by
  have hraw := s.primitiveRawStage_scaleBy k hk hg
  apply GNGaugeStage.eq_of_coordinates_eq
  · simpa [GNRawGaugeStage.primitiveStage] using
      congrArg GNRawGaugeStage.x hraw
  · simpa [GNRawGaugeStage.primitiveStage] using
      congrArg GNRawGaugeStage.u hraw

theorem GNRawGaugeStage.primitiveX_scaleBy
    (s : GNRawGaugeStage d) (k : ℕ) (hk : 0 < k)
    (hg : 0 < s.scale) :
    ((GNRawGaugeStage.scaleBy k s).primitiveStage
        (by rw [GNRawGaugeStage.scale_scaleBy]; exact mul_pos hk hg)).x =
      (s.primitiveStage hg).x := by
  exact congrArg GNGaugeStage.x (s.primitiveStage_scaleBy k hk hg)

theorem GNRawGaugeStage.primitiveU_scaleBy
    (s : GNRawGaugeStage d) (k : ℕ) (hk : 0 < k)
    (hg : 0 < s.scale) :
    ((GNRawGaugeStage.scaleBy k s).primitiveStage
        (by rw [GNRawGaugeStage.scale_scaleBy]; exact mul_pos hk hg)).u =
      (s.primitiveStage hg).u := by
  exact congrArg GNGaugeStage.u (s.primitiveStage_scaleBy k hk hg)

theorem GNRawGaugeStage.primitiveCaught_scaleBy_iff
    {q : ℕ} (s : GNRawGaugeStage d) (k : ℕ) (hk : 0 < k)
    (hg : 0 < s.scale) :
    PrimeCaught q
        ((GNRawGaugeStage.scaleBy k s).primitiveStage
          (by rw [GNRawGaugeStage.scale_scaleBy]; exact mul_pos hk hg)) ↔
      PrimeCaught q (s.primitiveStage hg) := by
  rw [s.primitiveStage_scaleBy k hk hg]

theorem GNRawGaugeStage.primitiveEscapes_scaleBy_iff
    {q : ℕ} (s : GNRawGaugeStage d) (k : ℕ) (hk : 0 < k)
    (hg : 0 < s.scale) :
    PrimeEscapes q
        ((GNRawGaugeStage.scaleBy k s).primitiveStage
          (by rw [GNRawGaugeStage.scale_scaleBy]; exact mul_pos hk hg)) ↔
      PrimeEscapes q (s.primitiveStage hg) := by
  rw [s.primitiveStage_scaleBy k hk hg]

/-! ## Raw refinement paths -/

def cumulativeFactorFrom : List ℕ → ℕ
  | [] => 1
  | k :: ks => k * cumulativeFactorFrom ks

def endStageFrom {d : ℕ} (s : GNRawGaugeStage d) : List ℕ → GNRawGaugeStage d
  | [] => s
  | k :: ks => endStageFrom (GNRawGaugeStage.scaleBy k s) ks

def stagesFrom {d : ℕ} (s : GNRawGaugeStage d) : List ℕ → List (GNRawGaugeStage d)
  | [] => [s]
  | k :: ks => s :: stagesFrom (GNRawGaugeStage.scaleBy k s) ks

/-- A finite raw refinement path with positive synchronized factors. -/
structure GNRawRefinementPath (d : ℕ) where
  start : GNRawGaugeStage d
  factors : List ℕ
  factors_pos : ∀ k ∈ factors, 0 < k

def GNRawRefinementPath.cumulativeFactor (p : GNRawRefinementPath d) : ℕ :=
  cumulativeFactorFrom p.factors

def GNRawRefinementPath.endStage (p : GNRawRefinementPath d) : GNRawGaugeStage d :=
  endStageFrom p.start p.factors

def GNRawRefinementPath.stages (p : GNRawRefinementPath d) :
    List (GNRawGaugeStage d) :=
  stagesFrom p.start p.factors

theorem endStageFrom_eq_scaleBy_cumulativeFactor
    (s : GNRawGaugeStage d) (ks : List ℕ) :
    endStageFrom s ks = GNRawGaugeStage.scaleBy (cumulativeFactorFrom ks) s := by
  induction ks generalizing s with
  | nil => simp [endStageFrom, cumulativeFactorFrom, GNRawGaugeStage.scaleBy]
  | cons k ks ih =>
      simp only [endStageFrom, cumulativeFactorFrom]
      calc
        endStageFrom (GNRawGaugeStage.scaleBy k s) ks =
            GNRawGaugeStage.scaleBy (cumulativeFactorFrom ks)
              (GNRawGaugeStage.scaleBy k s) := ih _
        _ = GNRawGaugeStage.scaleBy (k * cumulativeFactorFrom ks) s :=
          GNRawGaugeStage.scaleBy_scaleBy k (cumulativeFactorFrom ks) s

/-- The endpoint is the initial stage synchronized by the product of factors. -/
theorem GNRawRefinementPath.endStage_eq_scaleBy_cumulativeFactor
    (p : GNRawRefinementPath d) :
    p.endStage = GNRawGaugeStage.scaleBy p.cumulativeFactor p.start := by
  exact endStageFrom_eq_scaleBy_cumulativeFactor p.start p.factors

theorem endStageFrom_mem_stagesFrom
    (s : GNRawGaugeStage d) (ks : List ℕ) :
    endStageFrom s ks ∈ stagesFrom s ks := by
  induction ks generalizing s with
  | nil => simp [endStageFrom, stagesFrom]
  | cons k ks ih =>
      simp only [endStageFrom, stagesFrom, List.mem_cons]
      exact Or.inr (ih (GNRawGaugeStage.scaleBy k s))

/-- The endpoint is one of the visited raw stages. -/
theorem GNRawRefinementPath.endStage_mem_stages
    (p : GNRawRefinementPath d) : p.endStage ∈ p.stages := by
  exact endStageFrom_mem_stagesFrom p.start p.factors

/-! ## Homogeneous endpoint transport -/

theorem GNRawRefinementPath.endStage_value_eq
    (p : GNRawRefinementPath d) :
    p.endStage.value = p.cumulativeFactor ^ d * p.start.value := by
  have hstage := p.endStage_eq_scaleBy_cumulativeFactor
  have hvalue := congrArg GNRawGaugeStage.value hstage
  calc
    p.endStage.value =
        (GNRawGaugeStage.scaleBy p.cumulativeFactor p.start).value := hvalue
    _ = p.cumulativeFactor ^ d * p.start.value :=
      GNRawGaugeStage.value_scaleBy p.cumulativeFactor p.start

/-! ## Escape and capture along the finite path -/

private theorem rawEscapes_scaleBy_of_not_dvd
    {d q k : ℕ} (hq : Nat.Prime q) (s : GNRawGaugeStage d)
    (hEscape : RawPrimeEscapes q s) (hAvoid : ¬ q ∣ k) :
    RawPrimeEscapes q (GNRawGaugeStage.scaleBy k s) := by
  intro hCaught
  exact hAvoid (prime_dvd_scale_factor_of_rawEscape_of_scaledCaught hq s
    hEscape hCaught)

private theorem primeEscapes_stagesFrom
    {d q : ℕ} (hq : Nat.Prime q) (s : GNRawGaugeStage d)
    (ks : List ℕ) (hEscape : RawPrimeEscapes q s)
    (hAvoid : ∀ k ∈ ks, ¬ q ∣ k) :
    ∀ s' ∈ stagesFrom s ks, RawPrimeEscapes q s' := by
  induction ks generalizing s with
  | nil =>
      intro s' hs'
      simp only [stagesFrom, List.mem_singleton] at hs'
      simpa [hs'] using hEscape
  | cons k ks ih =>
      intro s' hs'
      simp only [stagesFrom, List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · exact hEscape
      · have hNext := rawEscapes_scaleBy_of_not_dvd hq s hEscape
          (hAvoid k (by simp))
        exact ih (GNRawGaugeStage.scaleBy k s) hNext (by
          intro k' hk'
          exact hAvoid k' (by simp [hk'])) s' hs'

/-- Initial escape persists at every visited stage when every factor avoids q. -/
theorem GNRawRefinementPath.primeEscapes_all_stages
    {q : ℕ} (hq : Nat.Prime q) (p : GNRawRefinementPath d)
    (hEscape : RawPrimeEscapes q p.start)
    (hAvoid : ∀ k ∈ p.factors, ¬ q ∣ k) :
    ∀ s ∈ p.stages, RawPrimeEscapes q s := by
  exact primeEscapes_stagesFrom hq p.start p.factors hEscape hAvoid

private theorem escapeCapture_step_from
    {d q : ℕ} (hq : Nat.Prime q) (s : GNRawGaugeStage d)
    (ks : List ℕ) (hEscape : RawPrimeEscapes q s)
    (hCaptured : ∃ s' ∈ stagesFrom s ks, RawPrimeCaught q s') :
    ∃ (s₀ : GNRawGaugeStage d) (k : ℕ),
      s₀ ∈ stagesFrom s ks ∧ k ∈ ks ∧ RawPrimeEscapes q s₀ ∧
        q ∣ k ∧ RawPrimeCaught q (GNRawGaugeStage.scaleBy k s₀) := by
  induction ks generalizing s with
  | nil =>
      rcases hCaptured with ⟨s', hs', hCaught⟩
      simp only [stagesFrom, List.mem_singleton] at hs'
      exact False.elim (hEscape (hs' ▸ hCaught))
  | cons k ks ih =>
      rcases hCaptured with ⟨s', hs', hCaught⟩
      simp only [stagesFrom, List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · exact False.elim (hEscape hCaught)
      · by_cases hNextEscape :
          RawPrimeEscapes q (GNRawGaugeStage.scaleBy k s)
        · rcases ih (GNRawGaugeStage.scaleBy k s) hNextEscape
            ⟨s', hs', hCaught⟩ with
            ⟨s₀, k', hs₀, hk', hBefore, hqk', hAfter⟩
          exact ⟨s₀, k', List.mem_cons_of_mem s hs₀,
            List.mem_cons_of_mem k hk', hBefore, hqk', hAfter⟩
        · have hNextCaught :
              RawPrimeCaught q (GNRawGaugeStage.scaleBy k s) := by
            by_contra hNotCaught
            exact hNextEscape hNotCaught
          exact ⟨s, k, List.mem_cons_self, List.mem_cons_self, hEscape,
            prime_dvd_scale_factor_of_rawEscape_of_scaledCaught hq s
              hEscape hNextCaught, hNextCaught⟩

/-- A captured visited stage yields an adjacent escape-to-capture step whose
factor contains q. -/
theorem GNRawRefinementPath.exists_escape_to_capture_step
    {q : ℕ} (hq : Nat.Prime q) (p : GNRawRefinementPath d)
    (hEscape : RawPrimeEscapes q p.start)
    (hCaptured : ∃ s ∈ p.stages, RawPrimeCaught q s) :
    ∃ (s₀ : GNRawGaugeStage d) (k : ℕ), s₀ ∈ p.stages ∧ k ∈ p.factors ∧
      RawPrimeEscapes q s₀ ∧ q ∣ k ∧
        RawPrimeCaught q (GNRawGaugeStage.scaleBy k s₀) := by
  exact escapeCapture_step_from hq p.start p.factors hEscape hCaptured

/-- In particular, a first/new capture along the path is supported by an
actual refinement factor. -/
theorem GNRawRefinementPath.exists_factor_dvd_q_of_captured_stage
    {q : ℕ} (hq : Nat.Prime q) (p : GNRawRefinementPath d)
    (hEscape : RawPrimeEscapes q p.start)
    (hCaptured : ∃ s ∈ p.stages, RawPrimeCaught q s) :
    ∃ k ∈ p.factors, q ∣ k := by
  rcases p.exists_escape_to_capture_step hq hEscape hCaptured with
    ⟨s₀, k, _, hk, _, hqk, _⟩
  exact ⟨k, hk, hqk⟩

/-! ## Endpoint and factor-product localization -/

theorem prime_dvd_factor_of_prime_dvd_cumulativeFactor
    {q : ℕ} (hq : Nat.Prime q) :
    ∀ {ks : List ℕ}, q ∣ cumulativeFactorFrom ks → ∃ k ∈ ks, q ∣ k := by
  intro ks
  induction ks with
  | nil =>
      intro hqOne
      have : q = 1 := Nat.dvd_one.mp (by simpa [cumulativeFactorFrom] using hqOne)
      exact False.elim (hq.ne_one this)
  | cons k ks ih =>
      intro hqProduct
      simp only [cumulativeFactorFrom] at hqProduct
      rcases hq.dvd_mul.mp hqProduct with hqk | hqTail
      · exact ⟨k, by simp, hqk⟩
      · rcases ih hqTail with ⟨k', hk', hqk'⟩
        exact ⟨k', by simp [hk'], hqk'⟩

/-- If an initially escaping prime is captured at the endpoint, it divides the
cumulative refinement factor. -/
theorem GNRawRefinementPath.prime_dvd_cumulativeFactor_of_startEscape_of_endCaught
    {q : ℕ} (hq : Nat.Prime q) (p : GNRawRefinementPath d)
    (hEscape : RawPrimeEscapes q p.start)
    (hCaught : RawPrimeCaught q p.endStage) :
    q ∣ p.cumulativeFactor := by
  change q ∣ p.endStage.value at hCaught
  rw [p.endStage_value_eq] at hCaught
  rcases hq.dvd_mul.mp hCaught with hqFactor | hqStart
  · exact hq.dvd_of_dvd_pow hqFactor
  · exact False.elim (hEscape hqStart)

/-! ## Concrete regressions -/

def regressionEscapePath : GNRawRefinementPath 2 :=
  { start := regressionRawStage
    factors := [2, 5]
    factors_pos := by
      intro k hk
      have hk' : k = 2 ∨ k = 5 := by simpa using hk
      rcases hk' with rfl | rfl <;> norm_num }

def regressionCapturePath : GNRawRefinementPath 2 :=
  { start := regressionRawStage
    factors := [2, 3]
    factors_pos := by
      intro k hk
      have hk' : k = 2 ∨ k = 3 := by simpa using hk
      rcases hk' with rfl | rfl <;> norm_num }

theorem regression_factors_avoiding_prime_escape_all_stages :
    ∀ s ∈ regressionEscapePath.stages, RawPrimeEscapes 7 s := by
  refine GNRawRefinementPath.primeEscapes_all_stages (q := 7)
    (p := regressionEscapePath) (by norm_num) ?_ ?_
  · change ¬ (7 : ℕ) ∣ regressionRawStage.value
    norm_num [RawPrimeEscapes, regressionRawStage, GNRawGaugeStage.value,
      GNRawGaugeStage.gnValue, GTail, Finset.sum_range_succ]
  · intro k hk
    have hk' : k = 2 ∨ k = 5 := by simpa [regressionEscapePath] using hk
    rcases hk' with rfl | rfl <;> norm_num

theorem regression_first_capture_after_supported_factor :
    RawPrimeEscapes 3 regressionCapturePath.start ∧
      RawPrimeEscapes 3 (GNRawGaugeStage.scaleBy 2 regressionCapturePath.start) ∧
      RawPrimeCaught 3
        (GNRawGaugeStage.scaleBy 3
          (GNRawGaugeStage.scaleBy 2 regressionCapturePath.start)) := by
  norm_num [RawPrimeEscapes, RawPrimeCaught, regressionCapturePath,
    regressionRawStage, GNRawGaugeStage.scaleBy, GNRawGaugeStage.value,
    GNRawGaugeStage.gnValue, GTail, Finset.sum_range_succ]

theorem regression_capture_factor_localization :
    ∃ k ∈ regressionCapturePath.factors, 3 ∣ k := by
  refine GNRawRefinementPath.exists_factor_dvd_q_of_captured_stage (q := 3)
    (p := regressionCapturePath) (by norm_num) (by
      change ¬ (3 : ℕ) ∣ regressionRawStage.value
      norm_num [RawPrimeEscapes, regressionRawStage, GNRawGaugeStage.value,
        GNRawGaugeStage.gnValue, GTail, Finset.sum_range_succ]) ?_
  refine ⟨GNRawGaugeStage.scaleBy 3
      (GNRawGaugeStage.scaleBy 2 regressionCapturePath.start), ?_, ?_⟩
  · simp [GNRawRefinementPath.stages, stagesFrom, regressionCapturePath]
  · norm_num [RawPrimeCaught, regressionCapturePath, regressionRawStage,
      GNRawGaugeStage.scaleBy, GNRawGaugeStage.value,
      GNRawGaugeStage.gnValue, GTail, Finset.sum_range_succ]

end DkMath.NumberTheory.MultiGauge

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.KUS.CosmicBridge
import DkMath.NumberTheory.StructuralArithmetic.InterPeriod

#print "file: DkMath.NumberTheory.StructuralArithmetic.KUSObservation"

/-!
## Explicit observations of retained KUS support

KUS retains a typed raw support independently of its visible coefficient.
`ObservationSpec` interprets that support as a coordinate function, while
`observePeriod` deliberately forgets periodic information through the existing
StructuralArithmetic projection.  The observer is explicit: arbitrary KUS
blueprints are not assumed to be prime-coordinate systems.

Transport compatibility is a separate proposition.  A `ScaleSpec` preserves an
observation only when that proposition is supplied, so the raw-source boundary
is not hidden by a global transport theorem.
-/

namespace DkMath.NumberTheory.StructuralArithmetic

open DkMath.KUS

universe u v

/--
An explicit interpretation of a KUS support as nonnegative structural
coordinates indexed by `ι`.  The support remains available to the observer;
no prime-factorization semantics are built into the blueprint type.
-/
structure ObservationSpec
    (U : Type u) (Blueprint : BlueprintFamily U) (ι : Type v) where
  coordinates : US U Blueprint → ι → ℕ

/-- The raw coordinate observation of a `GKUS` value, obtained from its support. -/
def rawObservation
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι)
    (x : GKUS C U Blueprint) : ι → ℕ :=
  ω.coordinates (extract_g x)

/-- The deliberately lossy period-`d` observation of a `GKUS` value. -/
def observePeriod
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι) (d : ℕ)
    (x : GKUS C U Blueprint) : ι → ℕ :=
  projectCoordinates d (rawObservation ω x)

/-- Observing a constructed `GKUS` value uses exactly its retained support. -/
@[simp] theorem rawObservation_mkGWith
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι) (c : C) (s : US U Blueprint) :
    rawObservation ω (mkGWith c s) = ω.coordinates s := by
  rfl

/-- Period-zero observation is the complete raw observation. -/
@[simp] theorem observePeriod_period_zero
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι) (x : GKUS C U Blueprint) :
    observePeriod ω 0 x = rawObservation ω x := by
  simp [observePeriod]

/-- Period-one observation collapses every observed coordinate to zero. -/
@[simp] theorem observePeriod_period_one
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι) (x : GKUS C U Blueprint) :
    observePeriod ω 1 x = fun _ => 0 := by
  simp [observePeriod]

/-- Period observation is definitionally the projection of the raw observation. -/
theorem observePeriod_eq_project
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι) (d : ℕ) (x : GKUS C U Blueprint) :
    observePeriod ω d x = projectCoordinates d (rawObservation ω x) :=
  rfl

/--
Inter-period coarsening of a KUS observation reuses the StructuralArithmetic
`m ∣ d` theorem and does not introduce a second projection calculus.
-/
theorem observePeriod_project_of_dvd
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U} {ι : Type v}
    (ω : ObservationSpec U Blueprint ι) {m d : ℕ} (hmd : m ∣ d)
    (x : GKUS C U Blueprint) :
    projectCoordinates m (observePeriod ω d x) = observePeriod ω m x := by
  unfold observePeriod
  exact projectCoordinates_project_of_dvd hmd (rawObservation ω x)

/--
`σ` is observation-compatible when it transports every support with the same
coordinate meaning.  This is an explicit semantic hypothesis, not a property
of arbitrary `ScaleSpec` values.
-/
def ObservationCompatible
    {U : Type u} {Blueprint : BlueprintFamily U}
    {V : Type*} {Blueprint' : BlueprintFamily V} {ι : Type v}
    (ω₁ : ObservationSpec U Blueprint ι)
    (ω₂ : ObservationSpec V Blueprint' ι)
    (σ : ScaleSpec U Blueprint V Blueprint') : Prop :=
  ∀ s : US U Blueprint,
    ω₂.coordinates (ScaleSpec.scaleUS σ s) = ω₁.coordinates s

/-- Raw observations commute with a transport satisfying `ObservationCompatible`. -/
theorem rawObservation_scaleGKUS_of_compatible
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U}
    {V : Type*} {Blueprint' : BlueprintFamily V} {ι : Type v}
    (ω₁ : ObservationSpec U Blueprint ι)
    (ω₂ : ObservationSpec V Blueprint' ι)
    (σ : ScaleSpec U Blueprint V Blueprint')
    (hσ : ObservationCompatible ω₁ ω₂ σ)
    (x : GKUS C U Blueprint) :
    rawObservation ω₂ (ScaleSpec.scaleGKUS σ x) = rawObservation ω₁ x := by
  unfold rawObservation
  rw [ScaleSpec.extract_g_scaleGKUS]
  exact hσ (extract_g x)

/--
Under explicit compatibility, period observations also commute with KUS
transport; this is a corollary of the raw observation theorem.
-/
theorem observePeriod_scaleGKUS_of_compatible
    {C : Type*} {U : Type u} {Blueprint : BlueprintFamily U}
    {V : Type*} {Blueprint' : BlueprintFamily V} {ι : Type v}
    (ω₁ : ObservationSpec U Blueprint ι)
    (ω₂ : ObservationSpec V Blueprint' ι)
    (σ : ScaleSpec U Blueprint V Blueprint')
    (hσ : ObservationCompatible ω₁ ω₂ σ) (d : ℕ)
    (x : GKUS C U Blueprint) :
    observePeriod ω₂ d (ScaleSpec.scaleGKUS σ x) = observePeriod ω₁ d x := by
  unfold observePeriod
  rw [rawObservation_scaleGKUS_of_compatible ω₁ ω₂ σ hσ x]

/-! ## Concrete KUS witness -/

open DkMath.KUS.Bridge
open DkMath.KUS.CosmicBridge

/--
Concrete support observer for the existing CosmicBridge terms.  Its coordinate
is the retained dimension unit, so it records genuine support data rather than
the constant-zero function.
-/
def cosmicUnitObservation :
    ObservationSpec ℕ DHNTBlueprint Unit where
  coordinates := fun s _ => s.unit

/-- The raw observation of an existing cosmic term records its support dimension. -/
@[simp] theorem rawObservation_cosmicTerm (d k : ℕ) :
    rawObservation cosmicUnitObservation (cosmicTerm d k) = fun _ => d := by
  funext i
  rfl

/--
The period observation of a cosmic term visibly reduces the retained dimension
modulo the selected gauge period.
-/
@[simp] theorem observePeriod_cosmicTerm (p d k : ℕ) :
    observePeriod cosmicUnitObservation p (cosmicTerm d k) = fun _ => d % p := by
  funext i
  rfl

/-- The identity `ScaleSpec` is compatible with the concrete cosmic observer. -/
theorem cosmicUnitObservation_id_compatible :
    ObservationCompatible cosmicUnitObservation cosmicUnitObservation
      (ScaleSpec.idScale (U := ℕ) (Blueprint := DHNTBlueprint)) := by
  intro s
  rfl

end DkMath.NumberTheory.StructuralArithmetic

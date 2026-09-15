/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/
import DkMath.NumberTheory.Goldbach.Basic
import DkMath.NumberTheory.GNPrimeTargetResidue

#print "file: DkMath.NumberTheory.Goldbach.Signature"

/-!
# Finite higher-degree GN signatures

Only positive nondegenerate representations enter the signature. This region
is essential for the degree, divisibility, and exponential bounds. A signature
is a finite classifier of one endpoint; these APIs do not transport primality
to its reflected partner. Degree two represents every odd target, including
composites, so signature nonemptiness alone cannot certify a prime pair.
-/

namespace DkMath.NumberTheory

/-- Prime degrees occurring among the complete finite positive representations of a target. -/
def goldbachGNSignature (P : ℕ) : Finset ℕ :=
  ((GNPositiveRepresentations P).image (fun t => t.1)).filter Nat.Prime

/-- Membership is precisely a prime degree with positive GN coordinates. -/
theorem mem_goldbachGNSignature {P d : ℕ} :
    d ∈ goldbachGNSignature P ↔
      Nat.Prime d ∧ ∃ x u, GNPositiveRepresentation P d x u := by
  simp only [goldbachGNSignature, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨e, x, u⟩, ht, he⟩, hd⟩
    dsimp at he
    subst e
    exact ⟨hd, x, u, mem_GNPositiveRepresentations_iff.mp ht⟩
  · rintro ⟨hd, x, u, hrep⟩
    exact ⟨⟨(d, x, u), mem_GNPositiveRepresentations_iff.mpr hrep, rfl⟩, hd⟩

/-- Prime targets impose the existing prime-degree, `P-1` divisibility, and exponential floor. -/
theorem goldbach_signature_constraints {P d : ℕ} (hP : Nat.Prime P)
    (hd : d ∈ goldbachGNSignature P) :
    Nat.Prime d ∧ d ∣ P - 1 ∧ 2 ^ d - 1 ≤ P := by
  obtain ⟨_, x, u, hrep⟩ := mem_goldbachGNSignature.mp hd
  exact hrep.prime_degree_constraints hP

/-- The finite prime-divisor and exponential filter is a necessary target constraint. -/
theorem goldbach_signature_subset_filter {P : ℕ} (hP : Nat.Prime P) :
    goldbachGNSignature P ⊆
      (Finset.range P).filter (fun d => Nat.Prime d ∧ d ∣ P - 1 ∧ 2 ^ d - 1 ≤ P) := by
  intro d hd
  obtain ⟨_, x, u, hrep⟩ := mem_goldbachGNSignature.mp hd
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hrep.bounds.2.2.2.1, goldbach_signature_constraints hP hd⟩

/-- Degree two is in every positive odd signature, whether the target is prime or composite. -/
theorem goldbach_two_mem_odd_signature {k : ℕ} (hk : 0 < k) :
    2 ∈ goldbachGNSignature (2 * k + 1) := by
  apply mem_goldbachGNSignature.mpr
  exact ⟨Nat.prime_two, 1, k, by norm_num, by norm_num, hk,
    goldbach_odd_GN_representation k⟩

/-- A positive offset embeds the right endpoint into the existing positive GN API. -/
theorem goldbach_right_positive_representation {n u : ℕ}
    (hu : u ∈ goldbachOffsets n) (hupos : 0 < u) :
    GNPositiveRepresentation (n + u) 2 (n - u) u := by
  have hb := goldbachOffset_bounds hu
  refine ⟨by omega, by omega, hupos, ?_⟩
  rw [goldbach_GN_two]
  omega

end DkMath.NumberTheory

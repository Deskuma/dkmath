/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition"

namespace DkMath.Collatz

/-!
# Sound finite signed-transition certificates

A finite projection is useful only after its edge weights are proved to bound
the concrete transition.  This module records a potential certificate, a
standard stronger form of the nonpositive-cycle condition.  It deliberately
does not instantiate the certificate with the experimental low-bit block
signatures: the cp-317 audit found drift collisions and nondeterministic
successors in those projections.

The exact interpretation of those diagnostics is deliberately asymmetric:

* a drift collision disproves exact deterministic recovery of drift from the
  selected signature;
* two realized successors of one signature disprove a deterministic automaton,
  but do not disprove a nondeterministic graph or a sound over-approximation;
* a realized related path with equal endpoint signatures and positive total
  weight contradicts any bounded potential certificate on that signature, by
  `pathWeight_nonpos_of_signature_eq` below.

Thus nondeterminism alone is not a potential obstruction.  The obstruction is
a positive closed-signature path whose adjacent transitions all satisfy the
certificate's `Step` relation.
-/

/--
A sound finite signed abstraction equipped with a bounded potential.  Concrete
edge weight is bounded by projected edge weight, and projected edge weight is
bounded by the change in potential.
-/
structure FiniteSignedTransitionPotentialCertificate
    (State Signature : Type*) [Fintype Signature] where
  signature : State → Signature
  actualWeight : State → State → ℤ
  projectedUpperWeight : Signature → Signature → ℤ
  potential : Signature → ℤ
  bound : ℕ
  actual_le_projected : ∀ a b,
    actualWeight a b ≤ projectedUpperWeight (signature a) (signature b)
  projected_le_potential_diff : ∀ s t,
    projectedUpperWeight s t ≤ potential t - potential s
  potential_nonneg : ∀ s, 0 ≤ potential s
  potential_le_bound : ∀ s, potential s ≤ bound

/--
A finite signed abstraction whose soundness obligation is restricted to actual
transitions.  This is the appropriate surface for a nondeterministic finite
graph: arbitrary pairs of concrete states need not be comparable.
-/
structure RelationalFiniteSignedTransitionPotentialCertificate
    (State Signature : Type*) [Fintype Signature] where
  Step : State → State → Prop
  signature : State → Signature
  actualWeight : State → State → ℤ
  projectedUpperWeight : Signature → Signature → ℤ
  potential : Signature → ℤ
  bound : ℕ
  actual_le_projected : ∀ a b, Step a b →
    actualWeight a b ≤ projectedUpperWeight (signature a) (signature b)
  projected_le_potential_diff : ∀ s t,
    projectedUpperWeight s t ≤ potential t - potential s
  potential_nonneg : ∀ s, 0 ≤ potential s
  potential_le_bound : ∀ s, potential s ≤ bound

namespace RelationalFiniteSignedTransitionPotentialCertificate

variable {State Signature : Type*} [Fintype Signature]

/-- Concrete signed weight along a finite sequence of related transitions. -/
def pathWeight
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
  ∑ i ∈ Finset.range length,
    C.actualWeight (stateAt (start + i)) (stateAt (start + i + 1))

/-- Projected upper weight along the same finite transition path. -/
def projectedPathWeight
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
  ∑ i ∈ Finset.range length,
    C.projectedUpperWeight
      (C.signature (stateAt (start + i)))
      (C.signature (stateAt (start + i + 1)))

/-- A path satisfies the certificate relation at each adjacent pair. -/
def IsPath
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) : Prop :=
  ∀ i, i < length → C.Step (stateAt (start + i)) (stateAt (start + i + 1))

/-- Relation soundness bounds every concrete weight along a certified path. -/
theorem pathWeight_le_projectedPathWeight
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ)
    (hpath : C.IsPath stateAt start length) :
    C.pathWeight stateAt start length ≤ C.projectedPathWeight stateAt start length := by
  unfold pathWeight projectedPathWeight
  exact Finset.sum_le_sum fun i hi =>
    C.actual_le_projected _ _ (hpath i (Finset.mem_range.mp hi))

/-- Projected weights telescope below the endpoint potential difference. -/
theorem projectedPathWeight_le_potential_sub
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) :
    C.projectedPathWeight stateAt start length ≤
      C.potential (C.signature (stateAt (start + length))) -
        C.potential (C.signature (stateAt start)) := by
  induction length with
  | zero => simp [projectedPathWeight]
  | succ length ih =>
      rw [projectedPathWeight, Finset.sum_range_succ]
      unfold projectedPathWeight at ih
      change
        (∑ i ∈ Finset.range length,
          C.projectedUpperWeight
            (C.signature (stateAt (start + i)))
            (C.signature (stateAt (start + i + 1)))) +
            C.projectedUpperWeight
              (C.signature (stateAt (start + length)))
              (C.signature (stateAt (start + length + 1))) ≤ _
      have hedge := C.projected_le_potential_diff
        (C.signature (stateAt (start + length)))
        (C.signature (stateAt (start + length + 1)))
      have hend : start + (length + 1) = start + length + 1 := by omega
      rw [hend]
      linarith

/-- Every related concrete path has weight at most the finite potential bound. -/
theorem pathWeight_le_bound
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ)
    (hpath : C.IsPath stateAt start length) :
    C.pathWeight stateAt start length ≤ C.bound := by
  have hweight := (C.pathWeight_le_projectedPathWeight stateAt start length hpath).trans
    (C.projectedPathWeight_le_potential_sub stateAt start length)
  have hnonneg := C.potential_nonneg (C.signature (stateAt start))
  have hbound := C.potential_le_bound (C.signature (stateAt (start + length)))
  omega

/-- A related closed-signature path cannot have positive concrete weight. -/
theorem pathWeight_nonpos_of_signature_eq
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ)
    (hpath : C.IsPath stateAt start length)
    (hclosed : C.signature (stateAt (start + length)) =
      C.signature (stateAt start)) :
    C.pathWeight stateAt start length ≤ 0 := by
  have hweight := (C.pathWeight_le_projectedPathWeight stateAt start length hpath).trans
    (C.projectedPathWeight_le_potential_sub stateAt start length)
  rw [hclosed, sub_self] at hweight
  exact hweight

end RelationalFiniteSignedTransitionPotentialCertificate

/-! ## Conditional canonical-block projection -/

/-- A canonical signed window is the corresponding consecutive range sum. -/
theorem canonicalWindowDriftInt_add_eq_sum_range
    (n : OddNat) (q length : ℕ) :
    canonicalWindowDriftInt n q (q + length) =
      ∑ i ∈ Finset.range (length + 1), endpointAccountingTerm n (q + i) := by
  induction length with
  | zero => simp [canonicalWindowDriftInt_self]
  | succ length ih =>
      change canonicalWindowDriftInt n q ((q + length) + 1) = _
      rw [canonicalWindowDriftInt_succ n (by omega), if_pos (by omega), ih]
      conv_rhs => rw [Finset.sum_range_succ]
      congr 2

/-- A sound relational finite projection of all canonical successor edges
bounds every canonical signed window. -/
theorem relationalFiniteSignedCertificate_canonicalWindowDrift_le
    {Signature : Type*} [Fintype Signature]
    (n : OddNat)
    (C : RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature)
    (hstep : ∀ k, C.Step k (k + 1))
    (hweight : ∀ k, C.actualWeight k (k + 1) = endpointAccountingTerm n k)
    {q m : ℕ} (hqm : q ≤ m) :
    canonicalWindowDriftInt n q m ≤ C.bound := by
  let length := m - q + 1
  have hm : q + (m - q) = m := Nat.add_sub_of_le hqm
  have hpath : C.IsPath (fun k => k) q length := by
    intro i hi
    simpa [length, add_assoc] using hstep (q + i)
  have hbound := C.pathWeight_le_bound (fun k => k) q length hpath
  unfold RelationalFiniteSignedTransitionPotentialCertificate.pathWeight at hbound
  simp only [hweight] at hbound
  rw [← canonicalWindowDriftInt_add_eq_sum_range n q (m - q), hm] at hbound
  exact hbound

/-- A sound canonical finite signed projection yields a uniform reflected-queue
bound without choosing its signature from an assumed queue ceiling. -/
theorem relationalFiniteSignedCertificate_to_queueUniformUpperBound
    {Signature : Type*} [Fintype Signature]
    (n : OddNat)
    (C : RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature)
    (hstep : ∀ k, C.Step k (k + 1))
    (hweight : ∀ k, C.actualWeight k (k + 1) = endpointAccountingTerm n k) :
    CanonicalOutstandingClaimQueueUniformUpperBound n C.bound := by
  rw [canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le]
  intro m q hqm
  exact relationalFiniteSignedCertificate_canonicalWindowDrift_le
    n C hstep hweight hqm

/-- The same sound finite projection gives the translated endpoint-width
ceiling. -/
theorem relationalFiniteSignedCertificate_to_endpointWidthUniformUpperBound
    {Signature : Type*} [Fintype Signature]
    (n : OddNat)
    (C : RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature)
    (hstep : ∀ k, C.Step k (k + 1))
    (hweight : ∀ k, C.actualWeight k (k + 1) = endpointAccountingTerm n k) :
    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + C.bound) :=
  (relationalFiniteSignedCertificate_to_queueUniformUpperBound
    n C hstep hweight).to_endpointWidthUniformUpperBound

/-! ## Canonical finite projection wrapper -/

/-- Candidate-facing finite signature certificate specialized to canonical
block edges and their exact endpoint accounting weights. -/
structure CanonicalFiniteSignedTransitionPotentialCertificate
    (n : OddNat) (Signature : Type*) [Fintype Signature] where
  signature : ℕ → Signature
  projectedUpperWeight : Signature → Signature → ℤ
  potential : Signature → ℤ
  bound : ℕ
  actual_le_projected : ∀ k,
    endpointAccountingTerm n k ≤
      projectedUpperWeight (signature k) (signature (k + 1))
  projected_le_potential_diff : ∀ s t,
    projectedUpperWeight s t ≤ potential t - potential s
  potential_nonneg : ∀ s, 0 ≤ potential s
  potential_le_bound : ∀ s, potential s ≤ bound

namespace CanonicalFiniteSignedTransitionPotentialCertificate

variable {n : OddNat} {Signature : Type*} [Fintype Signature]

/-- Forgetting specialization yields the generic relational certificate. -/
noncomputable def toRelational
    (C : CanonicalFiniteSignedTransitionPotentialCertificate n Signature) :
    RelationalFiniteSignedTransitionPotentialCertificate ℕ Signature where
  Step a b := b = a + 1
  signature := C.signature
  actualWeight a _ := endpointAccountingTerm n a
  projectedUpperWeight := C.projectedUpperWeight
  potential := C.potential
  bound := C.bound
  actual_le_projected := by
    intro a b hab
    subst b
    exact C.actual_le_projected a
  projected_le_potential_diff := C.projected_le_potential_diff
  potential_nonneg := C.potential_nonneg
  potential_le_bound := C.potential_le_bound

/-- A canonical finite projection directly bounds the reflected queue. -/
theorem to_queueUniformUpperBound
    (C : CanonicalFiniteSignedTransitionPotentialCertificate n Signature) :
    CanonicalOutstandingClaimQueueUniformUpperBound n C.bound := by
  apply relationalFiniteSignedCertificate_to_queueUniformUpperBound
    n C.toRelational
  · intro k
    rfl
  · intro k
    rfl

/-- A canonical finite projection directly bounds completed endpoint widths. -/
theorem to_endpointWidthUniformUpperBound
    (C : CanonicalFiniteSignedTransitionPotentialCertificate n Signature) :
    CanonicalEndpointWidthUniformUpperBound n (bitWidth n.1 + C.bound) :=
  C.to_queueUniformUpperBound.to_endpointWidthUniformUpperBound

/-!
Before searching for `potential`, a candidate signature must establish that
all realized canonical edges sharing one signature pair have a finite common
upper weight.  Exact drift collisions are harmless when such an upper bound
exists; an unbounded positive collision rejects the candidate immediately.
No currently audited low-bit signature has this edgewise theorem yet.
-/

end CanonicalFiniteSignedTransitionPotentialCertificate

namespace FiniteSignedTransitionPotentialCertificate

variable {State Signature : Type*} [Fintype Signature]

/-- The legacy all-pairs certificate is the relational certificate with universal steps. -/
def toRelational
    (C : FiniteSignedTransitionPotentialCertificate State Signature) :
    RelationalFiniteSignedTransitionPotentialCertificate State Signature where
  Step := fun _ _ => True
  signature := C.signature
  actualWeight := C.actualWeight
  projectedUpperWeight := C.projectedUpperWeight
  potential := C.potential
  bound := C.bound
  actual_le_projected := fun a b _ => C.actual_le_projected a b
  projected_le_potential_diff := C.projected_le_potential_diff
  potential_nonneg := C.potential_nonneg
  potential_le_bound := C.potential_le_bound

/-- Concrete signed weight along `length` successive transitions from `start`. -/
def pathWeight
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
  ∑ i ∈ Finset.range length,
    C.actualWeight (stateAt (start + i)) (stateAt (start + i + 1))

/-- Projected upper weight along the same finite transition path. -/
def projectedPathWeight
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
  ∑ i ∈ Finset.range length,
    C.projectedUpperWeight
      (C.signature (stateAt (start + i)))
      (C.signature (stateAt (start + i + 1)))

/-- Sound edge projection bounds every concrete finite path. -/
theorem pathWeight_le_projectedPathWeight
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) :
    C.pathWeight stateAt start length ≤
      C.projectedPathWeight stateAt start length := by
  unfold pathWeight projectedPathWeight
  exact Finset.sum_le_sum fun i _ => C.actual_le_projected _ _

/-- Projected path weight telescopes below the endpoint potential difference. -/
theorem projectedPathWeight_le_potential_sub
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) :
    C.projectedPathWeight stateAt start length ≤
      C.potential (C.signature (stateAt (start + length))) -
        C.potential (C.signature (stateAt start)) := by
  induction length with
  | zero => simp [projectedPathWeight]
  | succ length ih =>
      rw [projectedPathWeight, Finset.sum_range_succ]
      unfold projectedPathWeight at ih
      change
        (∑ i ∈ Finset.range length,
          C.projectedUpperWeight
            (C.signature (stateAt (start + i)))
            (C.signature (stateAt (start + i + 1)))) +
            C.projectedUpperWeight
              (C.signature (stateAt (start + length)))
              (C.signature (stateAt (start + length + 1))) ≤ _
      have hedge := C.projected_le_potential_diff
        (C.signature (stateAt (start + length)))
        (C.signature (stateAt (start + length + 1)))
      have hend : start + (length + 1) = start + length + 1 := by omega
      rw [hend]
      linarith

/-- Every concrete path weight is uniformly bounded by the certificate bound. -/
theorem pathWeight_le_bound
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ) :
    C.pathWeight stateAt start length ≤ C.bound := by
  have hpath := (C.pathWeight_le_projectedPathWeight stateAt start length).trans
    (C.projectedPathWeight_le_potential_sub stateAt start length)
  have hnonneg := C.potential_nonneg (C.signature (stateAt start))
  have hbound := C.potential_le_bound
    (C.signature (stateAt (start + length)))
  omega

/-- A projected closed path has nonpositive upper weight. -/
theorem projectedPathWeight_nonpos_of_signature_eq
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ)
    (hclosed : C.signature (stateAt (start + length)) =
      C.signature (stateAt start)) :
    C.projectedPathWeight stateAt start length ≤ 0 := by
  have h := C.projectedPathWeight_le_potential_sub stateAt start length
  rw [hclosed, sub_self] at h
  exact h

/-- Consequently a sound potential certificate excludes positive concrete cycles. -/
theorem pathWeight_nonpos_of_signature_eq
    (C : FiniteSignedTransitionPotentialCertificate State Signature)
    (stateAt : ℕ → State) (start length : ℕ)
    (hclosed : C.signature (stateAt (start + length)) =
      C.signature (stateAt start)) :
    C.pathWeight stateAt start length ≤ 0 :=
  (C.pathWeight_le_projectedPathWeight stateAt start length).trans
    (C.projectedPathWeight_nonpos_of_signature_eq stateAt start length hclosed)

/-!
The converse graph theorem, deriving such a bounded potential from only
"every reachable directed cycle has nonpositive weight", requires a separate
finite weighted-graph cycle-elimination argument.  More importantly for the
canonical block application, no current finite signature has a proved
`actual_le_projected` field.  The low-bit candidates fail even exact drift and
successor determinism in the finite audit, so manufacturing that field would
be unsound.
-/

end FiniteSignedTransitionPotentialCertificate

end DkMath.Collatz

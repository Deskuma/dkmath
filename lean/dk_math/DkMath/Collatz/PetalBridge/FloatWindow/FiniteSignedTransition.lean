/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource

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

/-! ## Generic coboundary reweighting -/

/-- Signed weight of a finite concrete path, independent of any certificate. -/
def finiteSignedTransitionPathWeight
    {State : Type*} (weight : State → State → ℤ)
    (stateAt : ℕ → State) (start length : ℕ) : ℤ :=
  ∑ i ∈ Finset.range length,
    weight (stateAt (start + i)) (stateAt (start + i + 1))

/-- Reweight an edge by the coboundary of a state correction. -/
def coboundaryReweight
    {State : Type*} (weight : State → State → ℤ)
    (correction : State → ℤ) (a b : State) : ℤ :=
  weight a b + correction a - correction b

/-- Coboundary reweighting changes every finite path only by its endpoint
correction. -/
theorem finiteSignedTransitionPathWeight_coboundaryReweight
    {State : Type*} (weight : State → State → ℤ)
    (correction : State → ℤ) (stateAt : ℕ → State)
    (start length : ℕ) :
    finiteSignedTransitionPathWeight
        (coboundaryReweight weight correction) stateAt start length =
      finiteSignedTransitionPathWeight weight stateAt start length +
        correction (stateAt start) -
          correction (stateAt (start + length)) := by
  induction length with
  | zero => simp [finiteSignedTransitionPathWeight]
  | succ length ih =>
      have hreweighted : finiteSignedTransitionPathWeight
          (coboundaryReweight weight correction) stateAt start (length + 1) =
          finiteSignedTransitionPathWeight
            (coboundaryReweight weight correction) stateAt start length +
            coboundaryReweight weight correction
              (stateAt (start + length))
              (stateAt (start + length + 1)) := by
        simp only [finiteSignedTransitionPathWeight,
          Finset.sum_range_succ]
      have hbase : finiteSignedTransitionPathWeight
          weight stateAt start (length + 1) =
          finiteSignedTransitionPathWeight weight stateAt start length +
            weight (stateAt (start + length))
              (stateAt (start + length + 1)) := by
        simp only [finiteSignedTransitionPathWeight,
          Finset.sum_range_succ]
      have hend : start + (length + 1) = start + length + 1 := by omega
      rw [hreweighted, hbase, ih, hend]
      unfold coboundaryReweight
      ring

/-- A state-closed finite path has exactly the same total weight after every
coboundary reweighting. -/
theorem finiteSignedTransitionPathWeight_coboundaryReweight_of_state_eq
    {State : Type*} (weight : State → State → ℤ)
    (correction : State → ℤ) (stateAt : ℕ → State)
    (start length : ℕ)
    (hclosed : stateAt (start + length) = stateAt start) :
    finiteSignedTransitionPathWeight
        (coboundaryReweight weight correction) stateAt start length =
      finiteSignedTransitionPathWeight weight stateAt start length := by
  rw [finiteSignedTransitionPathWeight_coboundaryReweight, hclosed]
  ring

/-- If the correction is determined by a projected signature, equality of the
endpoint signatures is sufficient for exact closed-path invariance. -/
theorem finiteSignedTransitionPathWeight_signatureCoboundary_of_signature_eq
    {State Signature : Type*} (weight : State → State → ℤ)
    (signature : State → Signature) (correction : Signature → ℤ)
    (stateAt : ℕ → State) (start length : ℕ)
    (hclosed : signature (stateAt (start + length)) =
      signature (stateAt start)) :
    finiteSignedTransitionPathWeight
        (coboundaryReweight weight (correction ∘ signature))
        stateAt start length =
      finiteSignedTransitionPathWeight weight stateAt start length := by
  rw [finiteSignedTransitionPathWeight_coboundaryReweight]
  change finiteSignedTransitionPathWeight weight stateAt start length +
      correction (signature (stateAt start)) -
        correction (signature (stateAt (start + length))) = _
  rw [hclosed]
  ring

/-- A positive closed-signature path remains positive after every correction
computed only from that signature. -/
theorem finiteSignedTransitionPathWeight_signatureCoboundary_pos
    {State Signature : Type*} (weight : State → State → ℤ)
    (signature : State → Signature) (correction : Signature → ℤ)
    (stateAt : ℕ → State) (start length : ℕ)
    (hclosed : signature (stateAt (start + length)) =
      signature (stateAt start))
    (hpos : 0 < finiteSignedTransitionPathWeight weight stateAt start length) :
    0 < finiteSignedTransitionPathWeight
      (coboundaryReweight weight (correction ∘ signature))
      stateAt start length := by
  rwa [finiteSignedTransitionPathWeight_signatureCoboundary_of_signature_eq
    weight signature correction stateAt start length hclosed]

/-! ## Exact recovery versus projected upper weights

An ordinary collision is not a potential-certificate obstruction.  It says
only that one projected edge does not determine one exact concrete weight.
A nondeterministic abstraction may still assign that edge an upper weight
covering every concrete realization.  Unbounded edge fibers or positive
projected cycles are the stronger obstructions relevant to a potential
certificate. -/

/-- Exact recovery of every concrete edge weight from its pair of endpoint
signatures. -/
def FiniteSignatureDeterministicallyRecoversEdgeWeight
    {State Signature : Type*}
    (signature : State → Signature) (weight : State → State → ℤ) : Prop :=
  ∀ a b a' b',
    signature a = signature a' →
      signature b = signature b' →
        weight a b = weight a' b'

/-- Two concrete edges with the same projected endpoints but different exact
weights. -/
def FiniteSignatureExactWeightCollision
    {State Signature : Type*}
    (signature : State → Signature) (weight : State → State → ℤ) : Prop :=
  ∃ a b a' b',
    signature a = signature a' ∧
      signature b = signature b' ∧
        weight a b ≠ weight a' b'

/-- Soundness of a projected upper weight, without any claim of exact
recovery or deterministic successor behavior. -/
def FiniteSignatureProjectedUpperWeightSound
    {State Signature : Type*}
    (signature : State → Signature) (weight : State → State → ℤ)
    (projectedUpperWeight : Signature → Signature → ℤ) : Prop :=
  ∀ a b,
    weight a b ≤ projectedUpperWeight (signature a) (signature b)

/-- An exact-weight collision refutes deterministic weight recovery. -/
theorem not_deterministicallyRecoversEdgeWeight_of_exactWeightCollision
    {State Signature : Type*}
    {signature : State → Signature} {weight : State → State → ℤ}
    (hcollision : FiniteSignatureExactWeightCollision signature weight) :
    ¬ FiniteSignatureDeterministicallyRecoversEdgeWeight signature weight := by
  rintro hrecover
  rcases hcollision with ⟨a, b, a', b', hsource, htarget, hne⟩
  exact hne (hrecover a b a' b' hsource htarget)

/-- The same collision remains compatible with a sound projected upper
weight: both unequal realizations are bounded by the common projected edge
weight.  Thus collision alone is not a certificate impossibility theorem. -/
theorem exactWeightCollision_compatible_with_projectedUpperWeight
    {State Signature : Type*}
    {signature : State → Signature} {weight : State → State → ℤ}
    {projectedUpperWeight : Signature → Signature → ℤ}
    (hcollision : FiniteSignatureExactWeightCollision signature weight)
    (hsound : FiniteSignatureProjectedUpperWeightSound
      signature weight projectedUpperWeight) :
    ∃ a b a' b',
      signature a = signature a' ∧
        signature b = signature b' ∧
          weight a b ≠ weight a' b' ∧
            weight a b ≤
              projectedUpperWeight (signature a) (signature b) ∧
              weight a' b' ≤
                projectedUpperWeight (signature a) (signature b) := by
  rcases hcollision with ⟨a, b, a', b', hsource, htarget, hne⟩
  refine ⟨a, b, a', b', hsource, htarget, hne, hsound a b, ?_⟩
  simpa [hsource, htarget] using hsound a' b'

/-- Soundness of a finite projected upper-weight table for a concrete
successor sequence. -/
def FiniteSignatureSuccessorUpperWeightSound
    {Signature : Type*}
    (signature : ℕ → Signature) (weight : ℕ → ℤ)
    (projectedUpperWeight : Signature → Signature → ℤ) : Prop :=
  ∀ m,
    weight m ≤ projectedUpperWeight (signature m) (signature (m + 1))

/-- A finite projected successor-edge upper table exists exactly when the
concrete successor weights have a uniform pointwise upper bound.  The forward
direction uses the finite sum of absolute table entries as a coarse bound;
the reverse direction uses a constant table.

Consequently, changing or refining a finite signature cannot by itself evade
an unbounded concrete edge family. -/
theorem exists_finiteSignatureSuccessorUpperWeight_iff_uniformUpperBound
    {Signature : Type*} [Finite Signature]
    (signature : ℕ → Signature) (weight : ℕ → ℤ) :
    (∃ projectedUpperWeight : Signature → Signature → ℤ,
      FiniteSignatureSuccessorUpperWeightSound
        signature weight projectedUpperWeight) ↔
      ∃ B : ℤ, ∀ m, weight m ≤ B := by
  classical
  let := Fintype.ofFinite Signature
  constructor
  · rintro ⟨upper, hupper⟩
    refine ⟨∑ s : Signature, ∑ t : Signature, |upper s t|, ?_⟩
    intro m
    have hinner : |upper (signature m) (signature (m + 1))| ≤
        ∑ t : Signature, |upper (signature m) t| := by
      exact Finset.single_le_sum
        (fun t _ => abs_nonneg (upper (signature m) t))
        (Finset.mem_univ _)
    have houter : (∑ t : Signature, |upper (signature m) t|) ≤
        ∑ s : Signature, ∑ t : Signature, |upper s t| := by
      exact Finset.single_le_sum
        (fun s _ => Finset.sum_nonneg fun t _ => abs_nonneg (upper s t))
        (Finset.mem_univ _)
    exact (hupper m).trans
      ((le_abs_self (upper (signature m) (signature (m + 1)))).trans
        (hinner.trans houter))
  · rintro ⟨B, hB⟩
    refine ⟨fun _ _ => B, ?_⟩
    exact hB

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

/-- A single related edge with positive concrete weight cannot close at one
projected signature under a sound bounded-potential certificate. -/
theorem false_of_step_of_signature_eq_of_actualWeight_pos
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    {a b : State}
    (hstep : C.Step a b)
    (hclosed : C.signature b = C.signature a)
    (hpos : 0 < C.actualWeight a b) : False := by
  have hactual := C.actual_le_projected a b hstep
  have hprojected := C.projected_le_potential_diff
    (C.signature a) (C.signature b)
  rw [hclosed] at hactual hprojected
  simp only [sub_self] at hprojected
  omega

/-- Two realized edges forming a projected two-cycle with positive total
concrete weight contradict every sound bounded-potential certificate.  The
four concrete states need not form one concrete orbit cycle. -/
theorem false_of_two_step_projected_cycle_of_actualWeight_add_pos
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    {a a' b b' : State}
    (hstepA : C.Step a a')
    (hstepB : C.Step b b')
    (hcloseA : C.signature a' = C.signature b)
    (hcloseB : C.signature b' = C.signature a)
    (hpos : 0 < C.actualWeight a a' + C.actualWeight b b') : False := by
  have hA := (C.actual_le_projected a a' hstepA).trans
    (C.projected_le_potential_diff (C.signature a) (C.signature a'))
  have hB := (C.actual_le_projected b b' hstepB).trans
    (C.projected_le_potential_diff (C.signature b) (C.signature b'))
  rw [hcloseA] at hA
  rw [hcloseB] at hB
  omega

/-- Three realized edges forming a projected three-cycle with positive total
concrete weight contradict every sound bounded-potential certificate. -/
theorem false_of_three_step_projected_cycle_of_actualWeight_add_pos
    (C : RelationalFiniteSignedTransitionPotentialCertificate State Signature)
    {a a' b b' c c' : State}
    (hstepA : C.Step a a')
    (hstepB : C.Step b b')
    (hstepC : C.Step c c')
    (hcloseA : C.signature a' = C.signature b)
    (hcloseB : C.signature b' = C.signature c)
    (hcloseC : C.signature c' = C.signature a)
    (hpos : 0 < C.actualWeight a a' + C.actualWeight b b' +
      C.actualWeight c c') : False := by
  have hA := (C.actual_le_projected a a' hstepA).trans
    (C.projected_le_potential_diff (C.signature a) (C.signature a'))
  have hB := (C.actual_le_projected b b' hstepB).trans
    (C.projected_le_potential_diff (C.signature b) (C.signature b'))
  have hC := (C.actual_le_projected c c' hstepC).trans
    (C.projected_le_potential_diff (C.signature c) (C.signature c'))
  rw [hcloseA] at hA
  rw [hcloseB] at hB
  rw [hcloseC] at hC
  omega

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

/-! ## Circular reverse construction audit -/

/-- The signed canonical edge is bounded by the actual reflected-queue
increment across that edge. -/
theorem endpointAccountingTerm_le_queueBeforeBlock_increment
    (n : OddNat) (k : ℕ) :
    endpointAccountingTerm n k ≤
      (canonicalOutstandingClaimQueueBeforeBlock n (k + 1) : ℤ) -
        canonicalOutstandingClaimQueueBeforeBlock n k := by
  rw [endpointAccountingTerm_eq_blockClaimCount_sub_capacityCount]
  change (canonicalQueueDemand n k : ℤ) - canonicalQueueService n k ≤ _
  rw [canonicalOutstandingClaimQueueBeforeBlock_succ]
  have hbalance := canonicalOutstandingClaimQueue_add_consumed n k
  have hconsumed := canonicalQueueConsumed_le_service n k
  omega

/-- A queue bound can manufacture a finite signed certificate by using the
bounded queue itself as the signature and potential.  This construction is a
semantic circularity regression, not an arithmetic solution. -/
noncomputable def canonicalFiniteSignedCertificateOfQueueBound
    {n : OddNat} {C : ℕ}
    (hC : CanonicalOutstandingClaimQueueUniformUpperBound n C) :
    CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1)) where
  signature k := ⟨canonicalOutstandingClaimQueueBeforeBlock n k, by
    cases k with
    | zero => simp
    | succ k =>
        simp only [canonicalOutstandingClaimQueueBeforeBlock_succ]
        exact Nat.lt_succ_of_le (hC k)⟩
  projectedUpperWeight s t := (t.val : ℤ) - s.val
  potential s := s.val
  bound := C
  actual_le_projected k := by
    exact endpointAccountingTerm_le_queueBeforeBlock_increment n k
  projected_le_potential_diff _ _ := le_rfl
  potential_nonneg _ := by omega
  potential_le_bound s := Int.ofNat_le.mpr (Nat.le_of_lt_succ s.isLt)

/-- Unrestricted existential canonical finite-certificate existence is exactly
as strong as existential queue boundedness. -/
theorem exists_canonicalFiniteSignedCertificate_iff_exists_queueUniformUpperBound
    (n : OddNat) :
    (∃ C, Nonempty
        (CanonicalFiniteSignedTransitionPotentialCertificate n (Fin (C + 1)))) ↔
      ∃ C, CanonicalOutstandingClaimQueueUniformUpperBound n C := by
  constructor
  · rintro ⟨_C, ⟨P⟩⟩
    exact ⟨P.bound, P.to_queueUniformUpperBound⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, ⟨canonicalFiniteSignedCertificateOfQueueBound hC⟩⟩

/-!
The reverse construction deliberately chooses its signature from `hC`.
Therefore only a structurally predefined signature, fixed independently of an
assumed queue ceiling, can provide a noncircular arithmetic certificate.

## cp-344 canonical-signature audit

The conservation form of one canonical edge weight is

`block length - claim holes - terminal valuation`.

A sound finite projected numeric upper-weight table must therefore either
recover these three terms or prove a common upper bound for every concrete
edge in each projected edge fiber.  The currently available candidate
coordinates do not yet do this:

* the full carry/claim word has unbounded length;
* block length and claim-hole count are unbounded `Nat` coordinates;
* terminal valuation is likewise unbounded unless reduced to a class, and no
  class-level theorem bounds the omitted quotient contribution;
* queue zero/nonzero and excursion phase are finite, but record no magnitude;
* bounded low residues remain finite but have known exact-weight collisions.

Thus storing the exact ledger violates finiteness, while discarding its
unbounded coordinates leaves the required bounded-edge-fiber theorem open.
This obstructs a finite *numeric edge table*, not every finite-control proof:
a finite controller coupled to an unbounded symbolic counter or an owned
arithmetic resource remains a valid architecture.  No canonical positive-cycle
exclusion may be inferred from the numeric-table route before the edge-fiber
theorem is proved.  The generic potential API below remains a valid consumer
of a future independent finite abstraction; manufacturing its signature from
an assumed queue bound remains intentionally classified as circular.
-/

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

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.RH.CFBRC.FiniteClosure
import Mathlib.Tactic

#print "file: DkMath.RH.CFBRC.FiniteClosurePermutation"

namespace DkMath.RH.CFBRCProjection

/-- Endpoint of an ordered finite vector path. -/
noncomputable def listEndpoint (L : List ℂ) : ℂ :=
  L.sum

/-- Closure predicate for an ordered finite vector path. -/
def ListPathClosed (L : List ℂ) : Prop :=
  listEndpoint L = 0

/-- Permuting the drawing order does not change the endpoint. -/
theorem listEndpoint_eq_of_perm
    {L K : List ℂ} (h : L.Perm K) :
    listEndpoint L = listEndpoint K := by
  induction h with
  | nil => rfl
  | cons z h ih =>
      unfold listEndpoint at ih ⊢
      simp only [List.sum_cons]
      rw [ih]
  | swap z w L =>
      unfold listEndpoint
      simp only [List.sum_cons]
      abel
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Closure is invariant under every finite reordering. -/
theorem listPathClosed_iff_of_perm
    {L K : List ℂ} (h : L.Perm K) :
    ListPathClosed L ↔ ListPathClosed K := by
  unfold ListPathClosed
  rw [listEndpoint_eq_of_perm h]

/-- Reversing a vector path preserves its endpoint sum. -/
theorem listEndpoint_reverse (L : List ℂ) :
    listEndpoint L.reverse = listEndpoint L := by
  exact listEndpoint_eq_of_perm (List.reverse_perm L)

/-- Concatenated paths add their endpoints. -/
theorem listEndpoint_append (L K : List ℂ) :
    listEndpoint (L ++ K) = listEndpoint L + listEndpoint K := by
  simp [listEndpoint]

/-- Negating every vector negates the endpoint. -/
theorem listEndpoint_map_neg (L : List ℂ) :
    listEndpoint (L.map fun z => -z) = -listEndpoint L := by
  induction L with
  | nil => simp [listEndpoint]
  | cons z L ih =>
      unfold listEndpoint at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      abel

/--
The historical control construction: follow a path and then append the
negatives of the same vectors in reverse order.

This construction is deliberately named as a forced closure.  It is useful for
visual and implementation controls, but it is not an analytic zero detector.
-/
noncomputable def forcedReverseClosure (L : List ℂ) : List ℂ :=
  L ++ (L.reverse.map fun z => -z)

/-- The historical reverse-copy control path closes by construction. -/
theorem forcedReverseClosure_endpoint_eq_zero (L : List ℂ) :
    listEndpoint (forcedReverseClosure L) = 0 := by
  rw [forcedReverseClosure, listEndpoint_append, listEndpoint_map_neg,
    listEndpoint_reverse]
  abel

/-- The forced reverse-copy control path satisfies the closure predicate. -/
theorem forcedReverseClosure_closed (L : List ℂ) :
    ListPathClosed (forcedReverseClosure L) := by
  exact forcedReverseClosure_endpoint_eq_zero L

end DkMath.RH.CFBRCProjection

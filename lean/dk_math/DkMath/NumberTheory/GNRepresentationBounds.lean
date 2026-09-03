/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Data.Nat.Prime.Basic
import DkMath.CosmicFormula.CosmicFormulaBinom

#print "file: DkMath.NumberTheory.GNRepresentationBounds"

open scoped BigOperators

namespace DkMath.NumberTheory

open DkMath.CosmicFormulaBinom

/-!
## Finite bounds for positive GN representations

For a fixed target `n`, this file bounds every representation in the positive
nondegenerate region `2 ≤ d`, `0 < x`, and `0 < u`.  The result is a finite
search surface; it is not a classification or a prime-generation theorem.
-/

/-- A positive, nondegenerate representation of `n` by the canonical GN. -/
def GNPositiveRepresentation (n d x u : ℕ) : Prop :=
  2 ≤ d ∧
    0 < x ∧
      0 < u ∧
        DkMath.CosmicFormulaBinom.GN d x u = n

instance instDecidableGNPositiveRepresentation (n d x u : ℕ) :
    Decidable (GNPositiveRepresentation n d x u) := by
  unfold GNPositiveRepresentation
  infer_instance

/--
At the positive diagonal point `(x,u) = (1,1)`, the GN kernel is the
nonconstant part of the binomial row, namely `2^d - 1`.
-/
theorem GN_one_one_eq_two_pow_sub_one (d : ℕ) :
    DkMath.CosmicFormulaBinom.GN d 1 1 = 2 ^ d - 1 := by
  rw [GN_eq_sum]
  simp only [one_pow, mul_one]
  have hsum := Nat.sum_range_choose d
  rw [Finset.sum_range_succ'] at hsum
  simp only [Nat.choose_zero_right] at hsum
  exact Nat.eq_sub_of_add_eq hsum

/--
Positive coordinates dominate the diagonal point `(1,1)` term by term, so
`2^d - 1` is an exact lower floor for every positive GN representation.
-/
theorem two_pow_sub_one_le_GN
    {d x u : ℕ}
    (hx : 0 < x) (hu : 0 < u) :
    2 ^ d - 1 ≤ DkMath.CosmicFormulaBinom.GN d x u := by
  rw [← GN_one_one_eq_two_pow_sub_one d]
  rw [GN_eq_sum, GN_eq_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hx)
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hu)
  calc
    (Nat.choose d (k + 1) : ℕ) * 1 ^ k * 1 ^ (d - 1 - k) = Nat.choose d (k + 1) := by
      simp
    _ ≤ (Nat.choose d (k + 1) : ℕ) * x ^ k * u ^ (d - 1 - k) := by
      simpa only [one_pow, mul_one, mul_assoc] using
        Nat.mul_le_mul_left (Nat.choose d (k + 1))
          (Nat.mul_le_mul (pow_le_pow_left' hx1 k)
            (pow_le_pow_left' hu1 (d - 1 - k)))

private lemma pow_le_GTail_two
    {d x u : ℕ}
    (hd : 2 ≤ d) :
    x ^ (d - 2) ≤ DkMath.CosmicFormula.GTail d 2 x u := by
  unfold DkMath.CosmicFormula.GTail
  have hmem : d - 2 ∈ Finset.range (d + 1 - 2) := by
    exact Finset.mem_range.mpr (by omega)
  have hsingle := Finset.single_le_sum
    (s := Finset.range (d + 1 - 2))
    (f := fun k : ℕ =>
      (Nat.choose d (2 + k) : ℕ) * x ^ k * u ^ (d - (2 + k)))
    (fun k hk => Nat.zero_le _) hmem
  have hidx : 2 + (d - 2) = d := by omega
  simpa [hidx] using hsingle

/--
The two endpoint contributions of the positive GN row are bounded by the
whole kernel.  The first endpoint is the boundary power `x^(d-1)` and the
second is the head term `d*u^(d-1)`.
-/
theorem boundary_pow_add_head_le_GN
    {d x u : ℕ}
    (hd : 2 ≤ d) :
    x ^ (d - 1) + d * u ^ (d - 1) ≤
      DkMath.CosmicFormulaBinom.GN d x u := by
  have htail : x ^ (d - 2) ≤ DkMath.CosmicFormula.GTail d 2 x u :=
    pow_le_GTail_two hd
  have hboundary : x ^ (d - 1) ≤ x * DkMath.CosmicFormula.GTail d 2 x u := by
    calc
      x ^ (d - 1) = x ^ (d - 2 + 1) := by congr 1; omega
      _ = x ^ (d - 2) * x := by rw [pow_succ]
      _ ≤ DkMath.CosmicFormula.GTail d 2 x u * x :=
        Nat.mul_le_mul_right x htail
      _ = x * DkMath.CosmicFormula.GTail d 2 x u := Nat.mul_comm _ _
  have hrec :
      DkMath.CosmicFormulaBinom.GN d x u =
        d * u ^ (d - 1) + x * DkMath.CosmicFormula.GTail d 2 x u := by
    simpa [DkMath.CosmicFormulaBinom.GN, Nat.choose_one_right] using
      (DkMath.CosmicFormula.GN_tail_rec (R := ℕ) d x u (by omega))
  calc
    x ^ (d - 1) + d * u ^ (d - 1) =
        d * u ^ (d - 1) + x ^ (d - 1) := Nat.add_comm _ _
    _ ≤ d * u ^ (d - 1) + x * DkMath.CosmicFormula.GTail d 2 x u :=
      Nat.add_le_add_left hboundary _
    _ = DkMath.CosmicFormulaBinom.GN d x u := hrec.symm

/-- The boundary endpoint is strictly below the GN total in the positive region. -/
theorem boundary_pow_lt_GN
    {d x u : ℕ}
    (hd : 2 ≤ d) (_hx : 0 < x) (hu : 0 < u) :
    x ^ (d - 1) < DkMath.CosmicFormulaBinom.GN d x u := by
  have hsum := boundary_pow_add_head_le_GN (d := d) (x := x) (u := u) hd
  have hhead : 0 < d * u ^ (d - 1) := by
    exact Nat.mul_pos (by omega) (Nat.pow_pos hu)
  omega

/-- The head endpoint is strictly below the GN total in the positive region. -/
theorem head_lt_GN
    {d x u : ℕ}
    (hd : 2 ≤ d) (hx : 0 < x) (_hu : 0 < u) :
    d * u ^ (d - 1) < DkMath.CosmicFormulaBinom.GN d x u := by
  have hsum := boundary_pow_add_head_le_GN (d := d) (x := x) (u := u) hd
  have hboundary : 0 < x ^ (d - 1) := Nat.pow_pos hx
  omega

/--
All principal target bounds and the resulting coarse coordinate bounds for a
positive representation of `n`.
-/
theorem GNPositiveRepresentation.bounds
    {n d x u : ℕ}
    (h : GNPositiveRepresentation n d x u) :
    2 ^ d - 1 ≤ n ∧
    x ^ (d - 1) < n ∧
    d * u ^ (d - 1) < n ∧
    d < n ∧
    x < n ∧
    u < n := by
  rcases h with ⟨hd, hx, hu, hrep⟩
  have hfloor : 2 ^ d - 1 ≤ n := by
    have h := two_pow_sub_one_le_GN (d := d) (x := x) (u := u) hx hu
    rw [hrep] at h
    exact h
  have hboundary : x ^ (d - 1) < n := by
    have h := boundary_pow_lt_GN (d := d) (x := x) (u := u) hd hx hu
    rw [hrep] at h
    exact h
  have hhead : d * u ^ (d - 1) < n := by
    have h := head_lt_GN (d := d) (x := x) (u := u) hd hx hu
    rw [hrep] at h
    exact h
  have hexp : d - 1 ≠ 0 := by omega
  have hxpow : x ≤ x ^ (d - 1) :=
    le_self_pow (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hx)) hexp
  have hupow : u ≤ u ^ (d - 1) :=
    le_self_pow (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hu)) hexp
  have hdle : d ≤ d * u ^ (d - 1) := by
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hu)
  have hule : u ≤ d * u ^ (d - 1) := by
    exact (hupow.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < d)))
  exact ⟨hfloor, hboundary, hhead, hdle.trans_lt hhead,
    hxpow.trans_lt hboundary, hule.trans_lt hhead⟩

/-! ### Explicit finite search surface -/

/-- The coarse `n × n × n` search box for positive GN representations. -/
def GNRepresentationBox (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (Finset.range n).product ((Finset.range n).product (Finset.range n))

/-- The exact positive GN representations retained inside the finite box. -/
def GNPositiveRepresentations (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (GNRepresentationBox n).filter fun t =>
    GNPositiveRepresentation n t.1 t.2.1 t.2.2

/--
Membership in the executable filtered search set is equivalent to being a
positive GN representation.  The reverse direction uses the strict bounds
from `GNPositiveRepresentation.bounds`, so the finite box is complete.
-/
theorem mem_GNPositiveRepresentations_iff
    {n d x u : ℕ} :
    (d, (x, u)) ∈ GNPositiveRepresentations n ↔
      GNPositiveRepresentation n d x u := by
  classical
  simp only [GNPositiveRepresentations, Finset.mem_filter]
  constructor
  · intro h
    exact h.2
  · intro h
    rcases GNPositiveRepresentation.bounds h with
      ⟨_, _, _, hdn, hxn, hun⟩
    refine ⟨?_, h⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hdn,
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr hxn, Finset.mem_range.mpr hun⟩⟩

/-! ### Lightweight regression anchors -/

example : DkMath.CosmicFormulaBinom.GN 2 1 1 = 3 := by
  simpa using (GN_one_one_eq_two_pow_sub_one 2)

example : DkMath.CosmicFormulaBinom.GN 3 1 1 = 7 := by
  simpa using (GN_one_one_eq_two_pow_sub_one 3)

example : DkMath.CosmicFormulaBinom.GN 5 1 1 = 31 := by
  simpa using (GN_one_one_eq_two_pow_sub_one 5)

end DkMath.NumberTheory

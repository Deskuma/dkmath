/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.WeightedGNBridge

#print "file: DkMath.NumberTheory.Goldbach.CrossGapExchange"

/-!
# Cross-Gap Exchange

This module records the algebraic exchange law for two full-coordinate cosmic
formula universes.  It deliberately does not encode primality of either cross
output or assert a Goldbach theorem.
-/

namespace DkMath.NumberTheory.GoldbachCrossGapExchange

open DkMath.CosmicFormulaBinom

/-- The Body of a full-coordinate cosmic formula universe. -/
def crossGapBody (d x u : ℕ) : ℕ := x * GN d x u

/-- The Gap of a full-coordinate cosmic formula universe. -/
def crossGapGap (d u : ℕ) : ℕ := u ^ d

/-- The Big of a full-coordinate cosmic formula universe. -/
def crossGapBig (d x u : ℕ) : ℕ := (x + u) ^ d

/-- The total Big carried by two cosmic formula universes. -/
def pairedBig (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) : ℕ :=
  crossGapBig d₁ x₁ u₁ + crossGapBig d₂ x₂ u₂

/-- The first output after exchanging the two Gaps. -/
def crossLeft (d₁ x₁ u₁ d₂ _x₂ u₂ : ℕ) : ℕ :=
  crossGapBody d₁ x₁ u₁ + crossGapGap d₂ u₂

/-- The second output after exchanging the two Gaps. -/
def crossRight (d₁ _x₁ u₁ d₂ x₂ u₂ : ℕ) : ℕ :=
  crossGapBody d₂ x₂ u₂ + crossGapGap d₁ u₁

/-- One full-coordinate universe conserves Body plus Gap as Big. -/
theorem crossGapBody_add_crossGapGap_eq_crossGapBig (d x u : ℕ) :
    crossGapBody d x u + crossGapGap d u = crossGapBig d x u := by
  simpa [crossGapBody, crossGapGap, crossGapBig, GN] using
    (DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap (R := ℕ) d x u).symm

/-- The paired Big decomposes into both Bodies and both original Gaps. -/
theorem pairedBig_eq_bodies_add_gaps (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    pairedBig d₁ x₁ u₁ d₂ x₂ u₂ =
      crossGapBody d₁ x₁ u₁ + crossGapBody d₂ x₂ u₂ +
        crossGapGap d₁ u₁ + crossGapGap d₂ u₂ := by
  have h₁ := crossGapBody_add_crossGapGap_eq_crossGapBig d₁ x₁ u₁
  have h₂ := crossGapBody_add_crossGapGap_eq_crossGapBig d₂ x₂ u₂
  unfold pairedBig
  omega

/-- Exchanging the two Gaps preserves the total Big exactly. -/
theorem crossLeft_add_crossRight_eq_pairedBig
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ + crossRight d₁ x₁ u₁ d₂ x₂ u₂ =
      pairedBig d₁ x₁ u₁ d₂ x₂ u₂ := by
  have h₁ := crossGapBody_add_crossGapGap_eq_crossGapBig d₁ x₁ u₁
  have h₂ := crossGapBody_add_crossGapGap_eq_crossGapBig d₂ x₂ u₂
  unfold crossLeft crossRight pairedBig
  omega

/-- Swapping universe labels exchanges the two cross outputs. -/
theorem crossLeft_swap_eq_crossRight
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    crossLeft d₂ x₂ u₂ d₁ x₁ u₁ = crossRight d₁ x₁ u₁ d₂ x₂ u₂ := by
  simp [crossLeft, crossRight]

/-- The reverse label swap exchanges the outputs back, expressing involution. -/
theorem crossRight_swap_eq_crossLeft
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    crossRight d₂ x₂ u₂ d₁ x₁ u₁ = crossLeft d₁ x₁ u₁ d₂ x₂ u₂ := by
  simp [crossLeft, crossRight]

/-- If the two Gaps agree, the first cross output is the first Big. -/
theorem crossLeft_eq_firstBig_of_gap_eq
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ)
    (hgap : crossGapGap d₁ u₁ = crossGapGap d₂ u₂) :
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ = crossGapBig d₁ x₁ u₁ := by
  have h₁ := crossGapBody_add_crossGapGap_eq_crossGapBig d₁ x₁ u₁
  unfold crossLeft
  omega

/-- If the two Gaps agree, the second cross output is the second Big. -/
theorem crossRight_eq_secondBig_of_gap_eq
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ)
    (hgap : crossGapGap d₁ u₁ = crossGapGap d₂ u₂) :
    crossRight d₁ x₁ u₁ d₂ x₂ u₂ = crossGapBig d₂ x₂ u₂ := by
  have h₂ := crossGapBody_add_crossGapGap_eq_crossGapBig d₂ x₂ u₂
  unfold crossRight
  omega

/-- Equal Bodies and equal Gaps form a fixed locus of the exchange. -/
theorem crossLeft_eq_crossRight_of_body_eq_of_gap_eq
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ)
    (hbody : crossGapBody d₁ x₁ u₁ = crossGapBody d₂ x₂ u₂)
    (hgap : crossGapGap d₁ u₁ = crossGapGap d₂ u₂) :
    crossLeft d₁ x₁ u₁ d₂ x₂ u₂ = crossRight d₁ x₁ u₁ d₂ x₂ u₂ := by
  unfold crossLeft crossRight
  omega

/-- The signed Gap transfer from the first universe to the second. -/
def crossGapTransfer (d₁ u₁ d₂ u₂ : ℕ) : ℤ :=
  (crossGapGap d₂ u₂ : ℤ) - crossGapGap d₁ u₁

/-- The first cross output is the first Big plus the signed Gap transfer. -/
theorem crossLeft_intCast_eq_firstBig_add_transfer
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    (crossLeft d₁ x₁ u₁ d₂ x₂ u₂ : ℤ) =
      (crossGapBig d₁ x₁ u₁ : ℤ) + crossGapTransfer d₁ u₁ d₂ u₂ := by
  have h₁ := crossGapBody_add_crossGapGap_eq_crossGapBig d₁ x₁ u₁
  have h₁z : (crossGapBody d₁ x₁ u₁ : ℤ) + crossGapGap d₁ u₁ =
      crossGapBig d₁ x₁ u₁ := by
    exact_mod_cast h₁
  simp only [crossLeft, crossGapTransfer, Nat.cast_add]
  omega

/-- The second cross output is the second Big minus the signed Gap transfer. -/
theorem crossRight_intCast_eq_secondBig_sub_transfer
    (d₁ x₁ u₁ d₂ x₂ u₂ : ℕ) :
    (crossRight d₁ x₁ u₁ d₂ x₂ u₂ : ℤ) =
      (crossGapBig d₂ x₂ u₂ : ℤ) - crossGapTransfer d₁ u₁ d₂ u₂ := by
  have h₂ := crossGapBody_add_crossGapGap_eq_crossGapBig d₂ x₂ u₂
  have h₂z : (crossGapBody d₂ x₂ u₂ : ℤ) + crossGapGap d₂ u₂ =
      crossGapBig d₂ x₂ u₂ := by
    exact_mod_cast h₂
  simp only [crossRight, crossGapTransfer, Nat.cast_add]
  omega

/-- A prime GN degree makes its full-coordinate Body congruent to its boundary. -/
theorem crossGapBody_modEq_left_of_prime_degree
    {p x u : ℕ} (hp : Nat.Prime p) (hx : ¬ p ∣ x) :
    crossGapBody p x u ≡ x [MOD p] := by
  have hgn : GN p x u ≡ 1 [MOD p] :=
    DkMath.NumberTheory.prime_GN_modEq_one_of_not_dvd_x hp hx
  simpa [crossGapBody] using (Nat.ModEq.refl x).mul hgn

/-- Foreign Gaps transport the prime-row Body residue without certifying a prime. -/
theorem crossLeft_modEq_left_add_foreignGap_of_prime_degree
    {p x₁ u₁ d₂ x₂ u₂ : ℕ}
    (hp : Nat.Prime p) (hx₁ : ¬ p ∣ x₁) :
    crossLeft p x₁ u₁ d₂ x₂ u₂ ≡ x₁ + crossGapGap d₂ u₂ [MOD p] := by
  have hbody : crossGapBody p x₁ u₁ ≡ x₁ [MOD p] :=
    crossGapBody_modEq_left_of_prime_degree hp hx₁
  simpa [crossLeft] using hbody.add (Nat.ModEq.refl (crossGapGap d₂ u₂))

end DkMath.NumberTheory.GoldbachCrossGapExchange

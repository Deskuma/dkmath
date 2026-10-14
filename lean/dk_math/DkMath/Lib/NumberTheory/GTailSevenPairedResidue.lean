/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GTailSevenPrimeOrder
import DkMath.Lib.NumberTheory.GTailSevenIdealSquareAddress

#print "file: DkMath.Lib.NumberTheory.GTailSevenPairedResidue"

/-!
# Paired roots in one finite residue field

The Eisenstein and seventh roots have the same scalar codomain. This does
not identify their integral source rings or transfer ideals between them.
-/

namespace DkMath.Lib.NumberTheory

open DkMath.CosmicFormula

/-- The normalized tail ratio in the prime residue field. -/
def gtailSevenTailRatio (q c g : ℕ) [Fact (Nat.Prime q)] : ZMod q :=
  ((c : ZMod q) + (g : ZMod q)) / (c : ZMod q)

/-- Cast the existing exact natural tail balance to obtain the seventh-power identity. -/
theorem gtailSevenTailRatio_pow_seven {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hT : q ∣ GTail 7 1 g c) : gtailSevenTailRatio q c g ^ 7 = 1 := by
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  have ht0 : ((GTail 7 1 g c : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hT
  have hshell := congrArg (fun n : ℕ => (n : ZMod q))
    (add_pow_eq_mul_GTail_one_add_gap 7 g c)
  push_cast at hshell
  rw [ht0, mul_zero, zero_add] at hshell
  dsimp [gtailSevenTailRatio]
  rw [div_pow, add_comm, hshell, div_self (pow_ne_zero _ hc0)]

/-- A nonzero gap residue makes the ratio nontrivial. -/
theorem gtailSevenTailRatio_ne_one {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) : gtailSevenTailRatio q c g ≠ 1 := by
  have hc0 : (c : ZMod q) ≠ 0 := fun hz => hc ((ZMod.natCast_eq_zero_iff c q).mp hz)
  have hg0 : (g : ZMod q) ≠ 0 := fun hz => hg ((ZMod.natCast_eq_zero_iff g q).mp hz)
  intro hone
  have hsum := (div_eq_one_iff_eq hc0).mp hone
  exact hg0 (add_left_cancel (by simpa only [add_zero] using hsum))

/-- A seventh-power-one ratio cannot vanish. -/
theorem gtailSevenTailRatio_ne_zero {q c g : ℕ} [Fact (Nat.Prime q)]
    (hc : ¬ q ∣ c) (hT : q ∣ GTail 7 1 g c) : gtailSevenTailRatio q c g ≠ 0 := by
  have hr7 := gtailSevenTailRatio_pow_seven hc hT
  intro hz
  rw [hz, zero_pow (by decide : 7 ≠ 0)] at hr7
  exact zero_ne_one hr7

/-- Nontriviality is essential when cancelling the seven-term geometric identity. -/
theorem seven_geom_sum_eq_zero_of_pow_eq_one {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1 = 0 := by
  have hid : (r - 1) * (r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 1) = r ^ 7 - 1 := by
    ring
  rw [hr7, sub_self] at hid
  exact (mul_eq_zero.mp hid).resolve_left (sub_ne_zero.mpr hr1)

/-- Independent quadratic and seventh roots share a field, with no hidden integral carrier map. -/
theorem gtailSeven_paired_residue {q a b c g : ℕ} [Fact (Nat.Prime q)]
    (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hT : q ∣ GTail 7 1 g c) (hb : ¬ q ∣ b) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) :
    q ≠ 3 ∧
      gtailSevenResidueRoot q a b ^ 2 - gtailSevenResidueRoot q a b + 1 = 0 ∧
      gtailSevenTailRatio q c g ^ 7 = 1 ∧
      gtailSevenTailRatio q c g ≠ 1 ∧ gtailSevenTailRatio q c g ≠ 0 ∧
      (gtailSevenTailRatio q c g ^ 6 + gtailSevenTailRatio q c g ^ 5 +
        gtailSevenTailRatio q c g ^ 4 + gtailSevenTailRatio q c g ^ 3 +
        gtailSevenTailRatio q c g ^ 2 + gtailSevenTailRatio q c g + 1 = 0) := by
  have hr7 := gtailSevenTailRatio_pow_seven hc hT
  have hr1 := gtailSevenTailRatio_ne_one hc hg
  exact ⟨prime_ne_three_of_gtail (Fact.out : Nat.Prime q) hq7 hc hg hT,
    gtailSevenResidueRoot_polynomial hQ hb, hr7, hr1, gtailSevenTailRatio_ne_zero hc hT,
    seven_geom_sum_eq_zero_of_pow_eq_one _ hr7 hr1⟩

end DkMath.Lib.NumberTheory

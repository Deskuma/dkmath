/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.RamifiedGNPhaseBridge
import DkMath.FLT.Kummer.GNKummerUnitAdapter

#print "file: DkMath.FLT.Kummer.RegularDescentState"

/-!
# Prime-degree Kummer states

The carrier, primitive pair, two nonramification guards, and unit are retained
throughout reconstruction. A new state need not have the same numeric Core.
The phase packet alone proves depth-one impossibility; arithmetic conditions
are needed only for extraction and normalization in `RegularStateTransport`.
-/

namespace DkMath.FLT.Kummer.RegularDescent

open DkMath.Lib.NumberTheory
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]
variable {p : ℕ} [hp : Fact p.Prime] (P : RamifiedPhasePacket R p)

/-- Repeated odd-power equation with the original primitive and away guards. -/
structure State (m : ℕ) where
  x : R
  y : R
  z : R
  epsilon : Rˣ
  coprime : IsCoprime x y
  y_away : ¬ P.lambda ∣ y
  z_away : ¬ P.lambda ∣ z
  equation : x ^ p + y ^ p = (epsilon : R) * (P.lambda ^ m * z) ^ p

variable {P}

/-- Positive depth supplies a common center for all phases. -/
theorem State.uniformizer_dvd_sum {m : ℕ} (E : State P m) (hm : 1 ≤ m) :
    P.lambda ∣ E.x + E.y := by
  apply (P.residue_zero_iff _).mp
  have hl : P.residue P.lambda = 0 := (P.residue_zero_iff _).mpr dvd_rfl
  have he := congrArg P.residue E.equation
  simp only [map_add, map_pow, map_mul, hl, ZMod.pow_card,
    zero_pow (by omega : m ≠ 0), zero_mul, mul_zero] at he
  simpa only [map_add] using he

/-- The same center is used for every normalized factor. -/
noncomputable def State.center {m : ℕ} (E : State P m) (hm : 1 ≤ m) : R :=
  (E.uniformizer_dvd_sum hm).choose

theorem State.center_spec {m : ℕ} (E : State P m) (hm : 1 ≤ m) :
    E.x + E.y = P.lambda * E.center hm := (E.uniformizer_dvd_sum hm).choose_spec

/-- The complete sum is the packet's Core; the same state witnesses are retained. -/
theorem State.product_quotients (hodd : Odd p) {m : ℕ} (E : State P m) (hm : 1 ≤ m) :
    E.x ^ p + E.y ^ p = P.lambda ^ p * ∏ i : Fin p, P.quotient (E.center hm) E.y i := by
  rw [← DkMath.Lib.Cosmic.powerCore_neg_sum hodd, E.center_spec hm]
  exact P.powerCore_eq_product _ _

/-- R1 specialized to a state, independently of its eventual impossibility. -/
theorem State.depth_dvd_iff (hodd : Odd p) {m : ℕ} (E : State P m) (hm : 1 ≤ m) (k : ℕ) :
    P.lambda ^ (p + k) ∣ E.x ^ p + E.y ^ p ↔
      P.lambda ^ k ∣ P.quotient (E.center hm) E.y (P.distinguished (E.center hm) E.y) :=
  P.sum_dvd_iff hodd E.x E.y _ (E.center_spec hm) E.y_away k

/-- Depth one is impossible before using any class-group or unit-power theorem. -/
theorem no_state_one (hodd : Odd p) : ¬ Nonempty (State P 1) := by
  rintro ⟨E⟩
  have hd : P.lambda ^ (p + 1) ∣ E.x ^ p + E.y ^ p :=
    (E.depth_dvd_iff hodd (by decide) 1).mpr (by
      simpa only [pow_one] using
        (P.quotient_dvd_iff _ _ E.y_away (P.distinguished (E.center (by decide)) E.y)).mpr rfl)
  obtain ⟨w, hw⟩ := hd
  have hc : (E.epsilon : R) * E.z ^ p = P.lambda * w := by
    apply mul_left_cancel₀ (pow_ne_zero p P.lambda_prime.ne_zero)
    calc
      _ = E.x ^ p + E.y ^ p := by rw [E.equation]; simp only [pow_one]; ring
      _ = _ := by rw [hw, pow_add, pow_one]; ring
  have hr := congrArg P.residue hc
  have hl : P.residue P.lambda = 0 := (P.residue_zero_iff _).mpr dvd_rfl
  simp only [map_mul, map_pow, hl, zero_mul] at hr
  have hz : P.residue E.z ^ p = 0 :=
    (mul_eq_zero.mp hr).resolve_left (E.epsilon.isUnit.map P.residue).ne_zero
  exact E.z_away ((P.residue_zero_iff _).mp (eq_zero_of_pow_eq_zero hz))

/-- A coefficient ratio may be absorbed only after its unit p-th root is supplied.
The resulting state retains exactly the supplied `y` and `z`. -/
theorem normalize_weighted (m : ℕ) (x y z : R) (u v e k : Rˣ)
    (hxy : IsCoprime x y) (hy : ¬ P.lambda ∣ y) (hz : ¬ P.lambda ∣ z)
    (h : (u : R) * x ^ p + (v : R) * y ^ p = (e : R) * (P.lambda ^ m * z) ^ p)
    (hk : u / v = k ^ p) :
    ∃ E : State P m, E.x = (k : R) * x ∧ E.y = y ∧ E.z = z := by
  have hu : u = v * k ^ p := by rw [← hk]; simp [div_eq_mul_inv, mul_left_comm]
  refine ⟨{
    x := (k : R) * x
    y := y
    z := z
    epsilon := e / v
    coprime := (isCoprime_mul_unit_left_left k.isUnit x y).mpr hxy
    y_away := hy
    z_away := hz
    equation := ?_ }, rfl, rfl, rfl⟩
  apply mul_left_cancel₀ v.isUnit.ne_zero
  have hcancel : (v : R) * ((e / v : Rˣ) : R) = (e : R) := by
    change ((v * (e / v) : Rˣ) : R) = _
    congr 1
    simp [div_eq_mul_inv]
  rw [← mul_assoc, hcancel]
  rw [hu, Units.val_mul, Units.val_pow_eq_pow_val, mul_pow] at h
  linear_combination h

end DkMath.FLT.Kummer.RegularDescent

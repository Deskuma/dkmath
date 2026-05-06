/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GTailNat

#print "file: DkMath.Lib.Cosmic.GTailCongruence"

/-!
## Congruence layer for `GTail`

This file contains `Nat.ModEq` propagation and head-collapse results for the
natural-number specialization of `GTail`.
-/

open scoped BigOperators

namespace DkMath.CosmicFormula

/-!
### Congruence properties of the tail family

The following theorems concern the behavior of `GTail d r x u` modulo a
natural number `n`, particularly when `n ∣ x`. They are independent of any FLT
hypothesis and hold for arbitrary naturals in the intended range.

**Key pattern**: since `GTail d r x u` is a polynomial in `x` and `u`,
congruences in `x` and `u` propagate to congruences in the tail value.
When `n ∣ x` (i.e., `x ≡ 0 [MOD n]`), the tail collapses to the
`x = 0` evaluation, which equals `C(d,r) * u^{d-r}` by `GTail_eval_zero`.
-/

/--
Congruence propagation for finite sums over `Finset.range`.
-/
private theorem sum_range_modEq
    {m n : ℕ} {f g : ℕ → ℕ}
    (hfg : ∀ i, i < m → f i ≡ g i [MOD n]) :
    ((Finset.range m).sum f) ≡ ((Finset.range m).sum g) [MOD n] := by
  induction m with
  | zero =>
      exact Nat.ModEq.rfl
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      exact (ih (by
        intro i hi
        exact hfg i (Nat.lt_succ_of_lt hi))).add (hfg m (Nat.lt_succ_self m))

/--
Congruence propagation for `GTail`: if `x ≡ x' [MOD n]` and `u ≡ u' [MOD n]`,
then `GTail d r x u ≡ GTail d r x' u' [MOD n]`.

This follows from the polynomial nature of `GTail`: each term
`C(d, r+k) * x^k * u^{d-(r+k)}` is a monomial in `x` and `u`, and congruences
compose multiplicatively.
-/
theorem GTail_congr_of_modEq
    {n d r : ℕ} {x x' u u' : ℕ}
    (hx : x ≡ x' [MOD n])
    (hu : u ≡ u' [MOD n]) :
    GTail d r x u ≡ GTail d r x' u' [MOD n] := by
  unfold GTail
  refine sum_range_modEq ?_
  intro k hk
  have hxk : x ^ k ≡ x' ^ k [MOD n] := hx.pow k
  have huk : u ^ (d - (r + k)) ≡ u' ^ (d - (r + k)) [MOD n] := hu.pow (d - (r + k))
  have hmul : x ^ k * u ^ (d - (r + k)) ≡ x' ^ k * u' ^ (d - (r + k)) [MOD n] :=
    hxk.mul huk
  simpa [mul_assoc] using (hmul.mul_left (Nat.choose d (r + k)))

/--
When `x ≡ 0 [MOD n]`, the tail `GTail d r x u` is congruent to
`GTail d r 0 u`, which equals `C(d,r) * u^{d-r}` by `GTail_eval_zero`.
-/
theorem GTail_modEq_eval_zero_of_dvd_x
    {n d r : ℕ} (x u : ℕ)
    (hpx : n ∣ x) :
    GTail d r x u ≡ GTail d r 0 u [MOD n] :=
  GTail_congr_of_modEq (Nat.modEq_zero_iff_dvd.mpr hpx) (Nat.ModEq.refl u)

/--
Under `n ∣ x`, the normalized `GN` tail is congruent to
`C(d, 1) * u^{d-1}` modulo `n`.

This is the fundamental "mod-`n` collapse" of the cosmic formula:
`GN d x u ≡ d * u^{d-1} [MOD n]` when `n ∣ x`
(using `Nat.choose d 1 = d`).
-/
theorem GN_modEq_choose_mul_pow_of_dvd_x
    {d n : ℕ} (x u : ℕ)
    (_hd : 1 ≤ d) (hnx : n ∣ x) :
    GTail d 1 x u ≡ Nat.choose d 1 * u ^ (d - 1) [MOD n] := by
  have h0 := GTail_modEq_eval_zero_of_dvd_x x u hnx (d := d) (r := 1)
  rw [GTail_eval_zero d 1 u] at h0
  exact h0

/--
Under `n ∣ x`, the normalized GN tail satisfies
`GTail d 1 x u ≡ Nat.choose d 1 * u^{d-1} [MOD n]`.

This uses `GTail_modEq_eval_zero_of_dvd_x` + `GTail_eval_zero`.
-/
theorem GN_modEq_head_of_dvd_x
    {d n : ℕ} (x u : ℕ)
    (hdpos : 1 ≤ d)
    (hnx : n ∣ x) :
    GTail d 1 x u ≡ Nat.choose d 1 * u ^ (d - 1) [MOD n] := by
  exact GN_modEq_choose_mul_pow_of_dvd_x x u hdpos hnx

/--
Specialization: when `d` is itself the modulus and `d ∣ x`, then
`GTail d 1 x u ≡ d * u^{d-1} [MOD d]`.

Uses `Nat.choose d 1 = d`.
-/
theorem GN_modEq_mul_pow_self_of_dvd_x
    {d : ℕ} (x u : ℕ)
    (hdpos : 1 ≤ d)
    (hdx : d ∣ x) :
    GTail d 1 x u ≡ d * u ^ (d - 1) [MOD d] := by
  have h := GN_modEq_head_of_dvd_x x u hdpos hdx
  simpa [Nat.choose_one_right] using h

/--
When `p` is prime and `p ∣ x`, then `GN p x u ≡ p * u^{p-1} [MOD p^2]`.

This is the `mod p^2` version of the cosmic formula collapse.
-/
theorem GN_modEq_head_mod_sq_of_prime_dvd_x
    {p : ℕ} (x u : ℕ)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpx : p ∣ x) :
    GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 2] := by
  have hlt : 1 < p := hp.one_lt
  rw [GN_tail_rec p x u hlt]
  simp only [Nat.choose_one_right]
  suffices h : p ^ 2 ∣ x * GTail p 2 x u by
    change (p * u ^ (p - 1) + x * GTail p 2 x u) % p ^ 2 = (p * u ^ (p - 1)) % p ^ 2
    have hmod := Nat.dvd_iff_mod_eq_zero.mp h
    rw [Nat.add_mod, hmod, Nat.add_zero, Nat.mod_mod]
  have hGTail2 : GTail p 2 x u =
      (Nat.choose p 2 : ℕ) * u ^ (p - 2) + x * GTail p 3 x u :=
    GTail_rec p 2 x u (by omega)
  rw [hGTail2]
  have hchoose2 : p ∣ Nat.choose p 2 :=
    hp.dvd_choose_self (by omega) (by omega)
  have h1 : p ^ 2 ∣ x * (Nat.choose p 2 * u ^ (p - 2)) := by
    have hpp : p ^ 2 ∣ x * Nat.choose p 2 :=
      pow_two p ▸ Nat.mul_dvd_mul hpx hchoose2
    have : x * (Nat.choose p 2 * u ^ (p - 2)) = x * Nat.choose p 2 * u ^ (p - 2) := by
      ring
    rw [this]
    exact dvd_mul_of_dvd_left hpp _
  have h2 : p ^ 2 ∣ x * (x * GTail p 3 x u) := by
    have : x * (x * GTail p 3 x u) = x * x * GTail p 3 x u := by
      ring
    rw [this]
    exact dvd_mul_of_dvd_left (pow_two p ▸ Nat.mul_dvd_mul hpx hpx) _
  have heq : x * (Nat.choose p 2 * u ^ (p - 2) + x * GTail p 3 x u) =
      x * (Nat.choose p 2 * u ^ (p - 2)) + x * (x * GTail p 3 x u) := by
    ring
  rw [heq]
  exact Nat.dvd_add h1 h2

/--
Plan-name alias: `mod p^2` head congruence for `GN`.
-/
theorem GN_mod_p2_head
    {p : ℕ} (x u : ℕ)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpx : p ∣ x) :
    GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 2] :=
  GN_modEq_head_mod_sq_of_prime_dvd_x x u hp hp5 hpx

/--
`mod p^2` congruence rewritten as a concrete equality with an explicit tail.
-/
theorem GN_eq_head_add_p_sq_mul_of_prime_dvd_x
    {p : ℕ} (x u : ℕ)
    (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (hpx : p ∣ x) :
    ∃ M : ℕ, GTail p 1 x u = p * u ^ (p - 1) + p ^ 2 * M := by
  have hmod : GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 2] :=
    GN_modEq_head_mod_sq_of_prime_dvd_x x u hp hp5 hpx
  have hle : p * u ^ (p - 1) ≤ GTail p 1 x u := by
    rw [GN_tail_rec p x u hp.one_lt]
    simp [Nat.choose_one_right]
  have hdiv : p ^ 2 ∣ GTail p 1 x u - (p * u ^ (p - 1)) :=
    (Nat.modEq_iff_dvd' hle).mp hmod.symm
  rcases exists_eq_mul_left_of_dvd hdiv with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  calc
    GTail p 1 x u = p * u ^ (p - 1) + (GTail p 1 x u - (p * u ^ (p - 1))) := by
      exact (Nat.add_sub_of_le hle).symm
    _ = p * u ^ (p - 1) + p ^ 2 * M := by
      rw [hM]
      ring

/--
Plan-name `mod p^3` head congruence under an explicit third-order tail
divisibility hypothesis.
-/
theorem GN_mod_p3_head
    {p : ℕ} (x u : ℕ)
    (hp1 : 1 < p)
    (htail : p ^ 3 ∣ x * GTail p 2 x u) :
    GTail p 1 x u ≡ p * u ^ (p - 1) [MOD p ^ 3] := by
  rw [GN_tail_rec p x u hp1]
  simp only [Nat.choose_one_right]
  change (p * u ^ (p - 1) + x * GTail p 2 x u) % p ^ 3 = (p * u ^ (p - 1)) % p ^ 3
  have hmod := Nat.dvd_iff_mod_eq_zero.mp htail
  rw [Nat.add_mod, hmod, Nat.add_zero, Nat.mod_mod]

/--
`mod p^3` head congruence rewritten as a concrete equality with an explicit
tail.
-/
theorem GN_eq_head_add_p_cube_mul_of_dvd_tail
    {p : ℕ} (x u : ℕ)
    (hp1 : 1 < p)
    (htail : p ^ 3 ∣ x * GTail p 2 x u) :
    ∃ M : ℕ, GTail p 1 x u = p * u ^ (p - 1) + p ^ 3 * M := by
  rw [GN_tail_rec p x u hp1]
  simp only [Nat.choose_one_right]
  rcases exists_eq_mul_left_of_dvd htail with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  rw [hM]
  simp [Nat.mul_comm]

end DkMath.CosmicFormula

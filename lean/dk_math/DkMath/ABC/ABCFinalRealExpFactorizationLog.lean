/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC

set_option linter.style.longLine false
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.style.emptyLine false
set_option linter.style.emptyLine false

-- NOTE: this file can become heavy for the elaborator; if needed, scope maxHeartbeats
-- with `set_option maxHeartbeats in` on the particular theorem.

-- Finset.prod_rpow (*AI use)
lemma Finset.prod_rpow {α : Type*} (s : Finset α) (f : α → ℝ) (r : ℝ) (_hr : 0 ≤ r) (hf : ∀ a, 0 ≤ f a) :
  (Finset.prod s f) ^ r = Finset.prod s (fun a => (f a) ^ r) := by
  classical
  -- Proof by induction on the finite set `s`
  induction s using Finset.induction_on with
  | empty =>
    -- Base case: s is empty, both sides equal 1
    simp only [Finset.prod_empty, Real.one_rpow]
  | insert a s ha ih =>
    -- Inductive case: s = insert a s' with s' nonempty
    rw [Finset.prod_insert ha]
    -- (f a * ∏ x ∈ s, f x) ^ r = (f a) ^ r * (∏ x ∈ s, f x) ^ r
    have ha_nonneg : 0 ≤ f a := hf a
    have hs_nonneg : 0 ≤ Finset.prod s f := Finset.prod_nonneg (fun x _ => hf x)
    rw [Real.mul_rpow ha_nonneg hs_nonneg]
    -- ここで ih : (∏ x ∈ s, f x) ^ r = ∏ a ∈ s, f a ^ r を使う
    rw [ih]
    -- (f a) ^ r * ∏ a ∈ s, f a ^ r = ∏ a ∈ insert a s, f a ^ r
    rw [Finset.prod_insert ha]

namespace ABC



section RX1_defs

/-- RX1 X := (↑X+1) -/
def RX1 (X : ℕ) : ℝ := (X + 1 : ℝ)  -- (↑X+1)

/-- RX1 is positive -/
lemma RX1_pos (X : ℕ) : 0 < RX1 X := by
  dsimp [RX1]
  norm_cast
  omega

/-- RX1 is nonnegative -/
lemma RX1_nonneg (X : ℕ) : 0 ≤ RX1 X := by
  dsimp [RX1]
  norm_cast
  omega

/-- RX1 is nonzero -/
lemma RX1_ne_zero (X : ℕ) : RX1 X ≠ 0 := ne_of_gt (RX1_pos X)


/-- One over RX1 -/
noncomputable def one_div_RX1 (X : ℕ) : ℝ := 1 / RX1 X

/-- One over RX1 is positive -/
lemma one_div_RX1_pos (X : ℕ) : 0 < one_div_RX1 X := by
  dsimp [one_div_RX1]
  apply div_pos
  · norm_num
  · exact RX1_pos X

/-- One over RX1 is nonnegative -/
lemma one_div_RX1_nonneg (X : ℕ) : 0 ≤ one_div_RX1 X := by
  dsimp [one_div_RX1]
  apply div_nonneg
  · norm_num
  · exact RX1_nonneg X

/-- RX1 inverse -/
noncomputable def RX1_inv (X : ℕ) : ℝ := 1 / RX1 X
/-- RX1 inverse (alternative definition) -/
noncomputable def RX1_inv' (X : ℕ) : ℝ := (RX1 X)⁻¹

lemma RX1_inv_eq_inv (X : ℕ) : RX1_inv X = RX1_inv' X := by
  dsimp [RX1_inv, RX1_inv']
  rw [inv_eq_one_div]

/-- RX1 inverse and one over RX1 are equal -/
lemma RX1_inv_one_div_eq (X : ℕ) : RX1_inv X = one_div_RX1 X := by rfl

/-- RX1 inverse rpow lemma -/
lemma RX1_inv_rpow (X : ℕ) (r : ℝ) (_hr : 0 ≤ r) : (RX1 X) ^ (-r) = 1 / (RX1 X) ^ r := by
  rw [Real.rpow_neg (le_of_lt (RX1_pos X)) r, inv_eq_one_div]

/-- Division definition for RX1 (a / (X + 1)) -/
noncomputable def div_RX1 (X : ℕ) (a : ℝ) : ℝ := a / RX1 X

/-- Positive division lemma for RX1 -/
lemma div_RX1_pos {X : ℕ} {a : ℝ} (ha : 0 < a) : 0 < div_RX1 X a := by
  dsimp [div_RX1]
  apply div_pos
  · exact ha
  · exact RX1_pos X

/-- Nonnegative division lemma for RX1 -/
lemma div_RX1_nonneg {X : ℕ} {a : ℝ} (ha : 0 ≤ a) : 0 ≤ div_RX1 X a := by
  dsimp [div_RX1]
  apply div_nonneg
  · exact ha
  · exact RX1_nonneg X


end RX1_defs





section real_exp_factorization_log

-- Real.exp (t *  ↑((2 * n + 1).factorization p - 2) * Real.log ↑p )
-- Real.exp (t * (↑((2 * n + 1).factorization p - 2) * Real.log ↑p))

noncomputable def real_exp (x : ℝ) : ℝ := Real.exp x

noncomputable def n2a1_fact_log (n p : ℕ) : ℝ :=
  (((Chernoff.n2a1 n).factorization p - 2) : ℝ) * Real.log (p : ℝ)

-- Real.exp (t *  ↑((2 * n + 1).factorization p - 2) * Real.log ↑p )
noncomputable def real_exp_factorization_log (n p : ℕ) (t : ℝ) : ℝ :=
  real_exp (t * n2a1_fact_log n p)

lemma real_exp_factorization_log_eq (n p : ℕ) (t : ℝ) :
  real_exp_factorization_log n p t =
    Real.exp (t * (((Chernoff.n2a1 n).factorization p - 2) : ℝ) * Real.log (p : ℝ)) := by
  dsimp [real_exp_factorization_log, real_exp, n2a1_fact_log]
  -- 括弧の位置の違いは乗算の結合法則で一致する
  rw [mul_assoc]
  -- t * (a * b) = (t * a) * b

lemma real_exp_factorization_log_eq' (n p : ℕ) (t : ℝ) :
  real_exp_factorization_log n p t =
    Real.exp (t * (↑((2 * n + 1).factorization p) - ↑2) * Real.log ↑p ) := by
  dsimp [real_exp_factorization_log, real_exp, n2a1_fact_log]
  rw [Chernoff.n2a1]
  -- Chernoff.n2a1 n = 2 * n + 1 なので両辺一致
  rw [mul_assoc]
  -- t * (a * b) = (t * a) * b


-- a: Real.exp (t *  ↑((2 * n + 1).factorization p  -  2) * Real.log ↑p )
-- b: Real.exp (t * (↑((2 * n + 1).factorization p  -  2) * Real.log ↑p))
-- c: Real.exp (t * (↑((2 * n + 1).factorization p) - ↑2) * Real.log ↑p )

-- c = a
example (n p : ℕ) (t : ℝ) (h : (2 * n + 1).factorization p ≥ 2) :
    Real.exp (t * (↑((2 * n + 1).factorization p) - ↑2) * Real.log ↑p )
  = Real.exp (t *  ↑((2 * n + 1).factorization p  -  2) * Real.log ↑p ) := by
  -- (↑a - ↑b) = ↑(a - b) if a ≥ b
  rw [Nat.cast_sub h]; rfl  -- 型が一致し、等式が証明できる

-- c = b
example (n p : ℕ) (t : ℝ) (h : (2 * n + 1).factorization p ≥ 2) :
    Real.exp (t * (↑((2 * n + 1).factorization p) - ↑2) * Real.log ↑p )
  = Real.exp (t * (↑((2 * n + 1).factorization p  -  2) * Real.log ↑p)) := by
  -- (↑a - ↑b) = ↑(a - b) if a ≥ b
  rw [Nat.cast_sub h, mul_assoc]
  rfl -- 型が一致し、等式が証明できるぞ

-- b = a
example (n p : ℕ) (t : ℝ) (h : (2 * n + 1).factorization p ≥ 2) :
    Real.exp (t *  ↑((2 * n + 1).factorization p  -  2) * Real.log ↑p )
  = Real.exp (t * (↑((2 * n + 1).factorization p  -  2) * Real.log ↑p)) := by
  -- (↑a - ↑b) = ↑(a - b) if a ≥ b
  rw [Nat.cast_sub h, mul_assoc]

end real_exp_factorization_log













/-!
Standard constants and small helper lemmas used throughout the T1--T4 workflow.
We fix a project-wide constant t_* = log 2 / log 3 and a few casting/exp/log helpers
so proofs can follow a single consistent style.
-/

noncomputable def t_star : ℝ := Real.log 2 / Real.log 3

private lemma t_star_pos : 0 < t_star := by
  dsimp [t_star]
  -- Real.log 2 > 0 and Real.log 3 > 0
  have h2 : (1 : ℝ) < 2 := by norm_num
  have h3 : (1 : ℝ) < 3 := by norm_num
  have l2 := Real.log_pos h2
  have l3 := Real.log_pos h3
  exact div_pos l2 l3

private lemma pow_pos_of_prime {p : ℕ} (hp : p.Prime) : 0 < (p : ℝ) := by
  norm_cast; exact hp.pos

private lemma rpow_pos_of_pos_cast {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < a ^ x :=
  Real.rpow_pos_of_pos ha x

/-! Note: mathlib provides `Real.exp_sum` which we prefer to use; we avoid reimplementing
the finite induction here to reduce duplication. -/

private lemma log_rpow_bridge {A B γ : ℝ} (h : Real.log A ≤ γ * Real.log B) (hA : 0 < A) (hB : 0 < B) :
  A ≤ B ^ γ := by
  have hexp := Real.exp_le_exp.mpr h
  rw [Real.exp_log hA] at hexp
  -- rewrite exp (γ * log B) as B ^ γ using rpow_def_of_pos
  rw [mul_comm γ (Real.log B)] at hexp
  rw [(Real.rpow_def_of_pos hB γ).symm] at hexp
  exact hexp

/-! Set up Finset cardinality cast lemmas for ℝ and ℕ -/

@[simp] def Rsc {α : Type*} (s : Finset α) := (s.card : ℝ)
@[simp] def Nsc {α : Type*} (s : Finset α) := (s.card : ℕ)

lemma scard_cast {α : Type*} (s : Finset α) : (s.card : ℝ) = Nsc s := by rfl

lemma scard_eq {α : Type*} (s : Finset α) : Rsc s = (Nsc s : ℝ) := by rw [Rsc, Nsc]

lemma scard_iff {α : Type*} (s : Finset α) [CharZero ℝ] : Rsc s = (Nsc s : ℝ) ↔ s.card = (Nsc s : ℕ) := by
  rw [Rsc, Nsc]
  -- Nat.cast_inj needs [CharZero ℝ] to be in scope, which is now explicit
  exact Nat.cast_inj

lemma scard_n_cast {α : Type*} (s : Finset α) (n : ℕ) : Rsc s = n ↔ s.card = n := by
  rw [Rsc]
  exact Nat.cast_inj

lemma scard_cast_iff {α : Type*} (s : Finset α) (n : ℕ) : (s.card : ℝ) = n ↔ s.card = n := by
  exact Nat.cast_inj

lemma scard_pos_iff {α : Type*} (s : Finset α) : 0 < Rsc s ↔ s.Nonempty := by
  rw [Rsc]
  -- s.card > 0 ならば (s.card : ℝ) > 0
  rw [Nat.cast_pos]
  exact Finset.card_pos

lemma scard_nonneg {α : Type*} (s : Finset α) : 0 ≤ Rsc s := by
  rw [Rsc]
  exact Nat.cast_nonneg s.card

lemma scard_one_iff {α : Type*} (s : Finset α) : Rsc s = 1 ↔ s.card = 1 := by
  rw [Rsc, Nat.cast_eq_one]

/-- Finset.card_insert_of_notMem を使って s.card + 1 = (insert a s).card を示す -/
lemma insert_scard_add_one_eq {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) :
  s.card + 1 = (insert a s).card := Eq.symm (Finset.card_insert_of_notMem ha)

lemma Finset_scard_eq {α : Type*} (s : Finset α) : Rsc s = (s.card : ℝ) := by rfl
lemma Finset_scard_N_eq {α : Type*} (s : Finset α) : Finset.card s = Nsc s := by rfl
lemma Finset_scard_R_eq {α : Type*} (s : Finset α) : Finset.card s = Rsc s := by rfl
lemma Finset_scard_R_eq' {α : Type*} (s : Finset α) : ↑(Finset.card s) = Rsc s := by rfl



/-
Chernoff.Vp p n is defined as (2 * n + 1).factorization p in MathlibHello.ABC.Chernoff
padicValNat p (2 * n + 1) is defined as the p-adic valuation of (2 * n + 1) in Mathlib.Nat.PadicValuation
The two are equal by the following lemma.
-/

lemma cheronoff_vp_eq_padic_val_nat (p : ℕ) (_hp : p.Prime) (n : ℕ) :
  Chernoff.Vp p n = padicValNat p (2 * n + 1) := by
  -- proof goes here
  rw [Chernoff.Vp, padicValNat]

lemma cheronoff_vp_eq_padic_val_nat' (p : ℕ) (_hp : p.Prime) (n : ℕ) :
  Chernoff.Vp p n = padicValNat p (Chernoff.n2a1 n) := by
  -- proof goes here
  rw [Chernoff.n2a1, Chernoff.Vp, padicValNat]





-- [T1] -- mgf_vp_base

-- mgf_vp_base: MGF の基礎補題
-- For p prime (p ≠ 2) and 0 < t ≤ log 2 / log 3, the average
--   (1/(X+1)) * ∑_{n=0}^X p^{t*(v_p(2n+1)-2)}
-- is bounded by an explicit constant C > 0 (we take C = 4 * p^{-2t}).
private lemma mgf_vp_base (p : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (t : ℝ) (ht0 : 0 < t) (ht_star : t ≤ t_star) :
  ∃ C > 0, ∀ X ≥ 3,
--  (Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * ((padicValNat p (2 * n + 1) : ℝ) - 2)))) / (X + 1) ≤ C := by
    (Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * ((Chernoff.Vp p n : ℝ) - 2)))) / (X + 1) ≤ C := by
  -- derive p ≥ 3 from primality and p ≠ 2
  have h2 : 2 ≤ p := hp.two_le
  have hneq2 : p ≠ 2 := hpodd
  have hp_ge_3 : 3 ≤ p := by
    have hlt : 2 < p := Nat.lt_of_le_of_ne h2 (Ne.symm hneq2)
    exact Nat.succ_le_of_lt hlt
  let hp_fact : Fact p.Prime := ⟨hp⟩
  let C := 4 * (p : ℝ) ^ (-2 * t)
  have hC_pos : 0 < C := by
    apply mul_pos
    · norm_num
    · apply Real.rpow_pos_of_pos
      norm_cast
      exact hp.pos
  use C, hC_pos
  intro X hX
  -- Apply telescoping bound for the unshifted exponent sum
  have h_sum_bound := @ABC.Telescoping.sum_pow_padicValNat_le_geom_log2_div_log3 p hp_fact hp_ge_3 t ht0 ht_star X hX

  -- p^{t(v-2)} = p^{-2t} * p^{t v} pointwise
  have hp_pos : 0 < (p : ℝ) := by norm_cast; exact hp.pos
  have h_elem (n : ℕ) : (p : ℝ) ^ (t * ((Chernoff.Vp p n : ℝ) - 2))
      = (p : ℝ) ^ (-2 * t) * (p : ℝ) ^ (t * (Chernoff.Vp p n : ℝ)) := by
    have : t * ((Chernoff.Vp p n : ℝ) - 2) = -2 * t + t * (Chernoff.Vp p n : ℝ) := by ring
    rw [this, Real.rpow_add hp_pos]

  have hsum : Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (t * ((Chernoff.Vp p n : ℝ) - 2)))
            = Finset.sum (Finset.Icc 0 X) (fun n => (p : ℝ) ^ (-2 * t) * (p : ℝ) ^ (t * (Chernoff.Vp p n : ℝ))) :=
    Finset.sum_congr rfl (fun n _ => h_elem n)

  -- Factor out p^{-2t} from the sum and divide by X + 1
  have hpos : 0 < (X + 1 : ℝ) := by norm_cast; omega
  -- rewrite the sum using the elementwise identity, factor out p^{-2t}, and apply the telescoping bound
  rw [hsum]
  rw [← Finset.mul_sum]
  rw [mul_div_assoc]
  have h_div := (Real.div_le_iff hpos).mpr h_sum_bound
  have hcoeff_pos : 0 < (p : ℝ) ^ (-2 * t) := by
    apply Real.rpow_pos_of_pos; norm_cast; exact hp.pos
  have hcoeff_nonneg : 0 ≤ (p : ℝ) ^ (-2 * t) := le_of_lt hcoeff_pos
  have h_mul := mul_le_mul_of_nonneg_left h_div hcoeff_nonneg
  -- C = 4 * (p : ℝ) ^ (-2 * t) so rewrite the RHS p^{-2t} * 4 to C and finish
  have heq : (p : ℝ) ^ (-2 * t) * 4 = C := by
    dsimp [C]; ring
  rw [heq] at h_mul
  exact h_mul
-- [T2] -- mgf_twoTail_log


/-! mgf_twoTail_log: define logarithmic twoTail sum S_X and give MGF upper bound -/
-- S_X := ∑_{n=0}^X log (twoTail (2n+1))
noncomputable def S_X (X : ℕ) : ℝ := Finset.sum (Finset.Icc 0 X) fun n => Real.log ((twoTail (2 * n + 1) : ℝ))

example (t : ℝ) (n : ℕ) :
  Real.exp (∑ p ∈ (2 * n + 1).primeFactors,   t * ↑((2 * n + 1).factorization p  - 2) * Real.log ↑p)
  = ∏ p ∈ (2 * n + 1).primeFactors, Real.exp (t * ↑((2 * n + 1).factorization p  - 2) * Real.log ↑p) := by
  rw [Real.exp_sum]

/-- Logarithmic twoTail sum S_X -/
example (t : ℝ) (X P₀ : ℕ) :
    (∑ n ∈ Finset.Icc 0 X, ∏ p ∈ (2 * n + 1).primeFactors with p > P₀,
      Real.exp (t *  ↑((2 * n + 1).factorization p - 2) * Real.log ↑p ) ≤ (Finset.Icc 0 X).card • 1)
  = (∑ n ∈ Finset.Icc 0 X, ∏ p ∈ (2 * n + 1).primeFactors with p > P₀,
      Real.exp (t * (↑((2 * n + 1).factorization p - 2) * Real.log ↑p)) ≤ (Finset.Icc 0 X).card • 1)
  := by
    -- 両辺の Real.exp の引数の括弧の位置が異なるが、乗算の結合法則で一致する
    congr
    funext n
    congr
    funext p
    rw [mul_assoc]

/-- Logarithmic twoTail sum S_X (iff version) -/
example (t : ℝ) (X P₀ : ℕ) :
    (∑ n ∈ Finset.Icc 0 X, ∏ p ∈ (2 * n + 1).primeFactors with p > P₀,
      Real.exp (t *  ↑((2 * n + 1).factorization p - 2) * Real.log ↑p ) ≤ (Finset.Icc 0 X).card • 1)
  ↔ (∑ n ∈ Finset.Icc 0 X, ∏ p ∈ (2 * n + 1).primeFactors with p > P₀,
      Real.exp (t * (↑((2 * n + 1).factorization p - 2) * Real.log ↑p)) ≤ (Finset.Icc 0 X).card • 1)
  := by
    -- 両辺の Real.exp の引数の括弧の位置が異なるが、乗算の結合法則で一致する
    apply iff_of_eq
    congr
    funext n
    congr
    funext p
    -- t * ↑((2 * n + 1).factorization p - 2) * Real.log ↑p = t * (↑((2 * n + 1).factorization p - 2) * Real.log ↑p)
    rw [mul_assoc]


private lemma twoTail_exp_prod_eq (t : ℝ) (n : ℕ) (hn : 2 * n + 1 ≠ 0) :
  Real.exp (t * Real.log (twoTail (2 * n + 1) : ℝ))
    = Finset.prod ((2 * n + 1).primeFactors) fun p =>
        Real.exp (t * ((((2 * n + 1).factorization p) - 2 : ℕ) : ℝ) * Real.log (p : ℝ)) := by
  -- Use the logarithmic representation and then `Real.exp_sum` to turn the sum into a product.
  have h_log := ABC.log_twoTail_eq_sum_vplus (2 * n + 1) hn
  -- rewrite using the log equality, push the scalar t into the finite sum, then apply exp_sum
  rw [h_log]
  rw [Finset.mul_sum]
  -- 和の中のスカラー倍を分配する
  rw [← Finset.sum_congr rfl (fun p _ => mul_assoc t _ _)]
  -- exp(∑ ...) = ∏ exp(...) を適用
  apply Real.exp_sum


end ABC

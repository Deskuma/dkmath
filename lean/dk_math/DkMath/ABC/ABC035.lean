/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC034

#print "file: DkMath.ABC.ABC035"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

namespace Chernoff

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

-- ==========================================
-- Layer D: Explicit Specialization
-- ==========================================
--
-- Just a one-line call to Uniform with t = log2/(2·log3)
open Classical in
lemma chernoff_single_prime_explicit'
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (hγ : 0 < γ) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), C = const_C ∧ 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C * (X : ℝ) * Real.exp (- t0 * γ * Real.log (p : ℝ)) := by
  intro t0
  -- Call uniform, which returns C0 and X0 (the implementation of uniform uses `use const_C (=5), const_X (=100)`)
  have ht0_pos : 0 < t0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
    have : 0 < 2 * Real.log 3 := by linarith
    exact div_pos hlog2 this
  have ht0_le : t0 ≤ Real.log 2 / Real.log 3 := by
    dsimp [t0]
    exact t_bound_log2_div_log3
  obtain ⟨C0, rfl, hC0_pos, hbound0⟩ :=
    chernoff_single_prime_uniform hp3 γ hγ t0 ht0_pos ht0_le
  -- return the fixed constant const_C (=5) and re-use the bound produced by the uniform lemma
  exact chernoff_single_prime_uniform hp3 γ hγ t0 ht0_pos ht0_le

-- -------------------------------------------------------

open Classical in
lemma chernoff_single_prime_explicit
    {p : ℕ} [Fact p.Prime] (hp3 : pge3 p)
    (γ : ℝ) (hγ : 0 < γ) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), C = const_C ∧ 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        ((Finset.filter (fun n => n ≤ X ∧ Excess p γ n) (Finset.Icc 0 X)).card : ℝ)
          ≤ C * (X : ℝ) * Real.exp (- t0 * γ * Real.log (p : ℝ)) := by
  intro t0
  -- t0 の条件をそろえて uniform を呼ぶ
  have ht0_pos : 0 < t0 := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
    have : 0 < 2 * Real.log 3 := by
      have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num : (1:ℝ) < 3)
      nlinarith
    exact div_pos hlog2 this
  have ht0_le : t0 ≤ Real.log 2 / Real.log 3 := by
    dsimp [t0]; exact t_bound_log2_div_log3
  -- uniform は C=const_C を等号で返す
  obtain ⟨C, hC, hCpos, hU⟩ :=
    chernoff_single_prime_uniform hp3 γ hγ t0 ht0_pos ht0_le
  -- そのまま返す
  refine ⟨C, hC, hCpos, ?_⟩
  intro X hX; simpa using hU X hX

-- ==========================================
-- Layer E: Union Bound
-- ==========================================
--
-- Uses Uniform directly - can optimize t per block if needed

open Classical in
lemma union_bound_chernoff
    (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        (∑ p ∈ primesUpTo X,
           ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ C * (X : ℝ) * ∑ p ∈ primesUpTo X,
             Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))) := by
  intro t0
  -- Use explicit (which uses uniform with t = t0)
  use const_C
  constructor
  · rw [const_C]; norm_num
  · /-
    ⊢ ∀ X ≥ 100,
  ∑ p ∈ range (X + 1) with Nat.Prime p ∧ p ≥ 3, ↑(#({n ∈ Icc 0 X | n ≤ X ∧ Excess p γ n})) ≤
    ↑const_C * ↑X * ∑ p ∈ range (X + 1) with Nat.Prime p ∧ p ≥ 3, Real.exp (-t0 * γ * Real.log ↑p)
    -/
    intro X hX
    calc (∑ p ∈ primesUpTo X,
          ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ ∑ p ∈ primesUpTo X,
            5 * (X : ℝ) * Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          -- hp : p ∈ primesUpTo X, extract components
          have hf := Finset.mem_filter.1 hp
          rcases hf with ⟨hp_in, hp_prop⟩
          rcases hp_prop with ⟨hpPrime, hp3⟩
          let hpFact : Fact p.Prime := ⟨hpPrime⟩
          obtain ⟨C, rfl, hC_pos, hbound⟩ := @chernoff_single_prime_explicit p hpFact hp3 (γ_values p) (hγ_values p)
          have h := hbound X hX
          calc ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
              ≤ const_C * ↑X * Real.exp (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := h
            _ = const_C * ↑X * Real.exp (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := by rfl
      _ = const_C * (X : ℝ) * ∑ p ∈ primesUpTo X, Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
          -- pull constants out of the sum over primesUpTo X
          rw [Finset.mul_sum]
          rfl

open Classical in
lemma union_bound_chernoff'
    (γ_values : ℕ → ℝ) (hγ_values : ∀ p, 0 < γ_values p) :
    let t0 := Real.log 2 / (2 * Real.log 3)
    ∃ (C : ℝ), 0 < C ∧
      ∀ (X : ℕ), X ≥ const_X →
        (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
           ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ C * (X : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
             Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))) := by
  intro t0
  -- Use explicit (which uses uniform with t = t0)
  use const_C
  constructor
  · rw [const_C]; norm_num
  · /-
    ⊢ ∀ X ≥ 100,
  ∑ p ∈ range (X + 1) with Nat.Prime p ∧ p ≥ 3, ↑(#({n ∈ Icc 0 X | n ≤ X ∧ Excess p γ n})) ≤
    ↑const_C * ↑X * ∑ p ∈ range (X + 1) with Nat.Prime p ∧ p ≥ 3, Real.exp (-t0 * γ * Real.log ↑p)
    -/
    intro X hX
    calc (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
          ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            5 * (X : ℝ) * Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          let hf := Finset.mem_filter.1 hp
          rcases hf with ⟨_, ⟨hpPrime, hp3⟩⟩
          let hpFact : Fact p.Prime := ⟨hpPrime⟩
          obtain ⟨C, rfl, hC_pos, hbound⟩ := @chernoff_single_prime_explicit p hpFact hp3 (γ_values p) (hγ_values p)
          -- From explicit: C is 5 by `use const_C` statement, brought in as rfl above
          have h := hbound X hX
          calc ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
              ≤ const_C * ↑X * Real.exp (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := h
            _ = const_C * ↑X * Real.exp (-(Real.log 2 / (2 * Real.log 3)) * (γ_values p) * Real.log ↑p) := by rfl
      _ = const_C * (X : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
          -- 各項に 5 * X を掛けてから総和を取るのは、総和を取ってから 5 * X を掛けるのと同じ
          have : ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
                    5 * (X : ℝ) * Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ))
                = 5 * (X : ℝ) * ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
                    Real.exp (- t0 * (γ_values p) * Real.log (p : ℝ)) := by
            rw [Finset.sum_congr rfl (fun p _ => rfl), ← Finset.mul_sum]
          rw [this]
          -- const_C = 5 なので一致
          rfl


open Classical in
/-- Union bound in pow-form: sum over primes ≤ X of `card(Excess)` is
    ≤ const_C · X · (∑ p≤X p^{-t(γ_p+2)}).  We plug `t = α := log 2 / log 3`. -/
lemma union_bound_chernoff_pow
    (γ_values : ℕ → ℝ) (hγ : ∀ p, 0 < γ_values p) :
    let α := Real.log 2 / Real.log 3
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ const_X,
        (∑ p ∈ primesUpTo X,
            ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ))
        ≤ C * (X : ℝ) *
            ∑ p ∈ primesUpTo X,
              (p : ℝ) ^ (- α * (γ_values p + 2)) := by
  intro α
  use const_C; constructor; · simp [const_C]
  intro X hX
  -- 1項ずつ `chernoff_single_prime_uniform_pow` を適用して総和
  -- まず各 p について chernoff_single_prime_uniform_rpow で
  -- (#Excess) ≤ const_C * X * p^{-α (γ_p + 2)} を得る
  have hle : ∀ p ∈ primesUpTo X,
      ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    intro p hp
    -- Extract properties from membership in primesUpTo X
    let ⟨hp_in, ⟨hpPrime, hp3⟩⟩ := Finset.mem_filter.1 hp
    haveI : Fact p.Prime := ⟨hpPrime⟩
    have hαpos : 0 < α := by
      have : 1 < (3:ℝ) := by norm_num
      exact (div_pos (Real.log_pos (by norm_num)) (Real.log_pos this))
    exact chernoff_single_prime_uniform_rpow hp3 (γ_values p) (hγ p) α hαpos (le_of_eq rfl) X hX
  -- これで各項の不等式が得られたので、sum_le_sum で総和
  have := Finset.sum_le_sum hle
  -- 右辺の定数を外に出す
  have h_sum :
    ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
      const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2))
    = const_C * (X : ℝ) *
      ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
        (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    rw [Finset.mul_sum]
  -- 右辺の定数を外に出す等式 h_sum を right-hand side に適用する
  -- インデックス集合 primesUpTo X = Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)) なので書き換え
  have h_sum' :
    ∑ p ∈ primesUpTo X, const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2))
    = const_C * (X : ℝ) * ∑ p ∈ primesUpTo X, (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    rw [Finset.mul_sum]
  rw [h_sum'] at this
  exact this

open Classical in
lemma union_bound_chernoff_pow'
    (γ_values : ℕ → ℝ) (hγ : ∀ p, 0 < γ_values p) :
    let α := Real.log 2 / Real.log 3
    ∃ (C : ℝ), 0 < C ∧
      ∀ X ≥ const_X,
        (∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
            ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ))
        ≤ C * (X : ℝ) *
            ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
              (p : ℝ) ^ (- α * (γ_values p + 2)) := by
  intro α
  use const_C; constructor; · simp [const_C]
  intro X hX
  -- 1項ずつ `chernoff_single_prime_uniform_pow` を適用して総和
  -- まず各 p について chernoff_single_prime_uniform_rpow で
  -- (#Excess) ≤ const_C * X * p^{-α (γ_p + 2)} を得る
  have hle : ∀ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
      ((Finset.filter (fun n => n ≤ X ∧ Excess p (γ_values p) n) (Finset.Icc 0 X)).card : ℝ)
        ≤ const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    intro p hp
    -- Extract properties from membership in the filtered set
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have ⟨hp_in, ⟨hpPrime, hp3⟩⟩ := hp
    haveI : Fact p.Prime := ⟨hpPrime⟩
    have hαpos : 0 < α := by
      have : 1 < (3:ℝ) := by norm_num
      exact (div_pos (Real.log_pos (by norm_num)) (Real.log_pos this))
    exact chernoff_single_prime_uniform_rpow hp3 (γ_values p) (hγ p) α hαpos (le_of_eq rfl) X hX
  -- これで各項の不等式が得られたので、sum_le_sum で総和
  have := Finset.sum_le_sum hle
  -- 右辺の定数を外に出す
  have h_sum :
    ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
      const_C * (X : ℝ) * (p : ℝ) ^ (-α * (γ_values p + 2))
    = const_C * (X : ℝ) *
      ∑ p ∈ Finset.filter (fun (p : ℕ) => p.Prime ∧ p ≥ 3) (Finset.range (X + 1)),
        (p : ℝ) ^ (-α * (γ_values p + 2)) := by
    rw [Finset.mul_sum]
  -- 右辺の定数を外に出す等式 h_sum を right-hand side に適用する
  rw [h_sum] at this
  exact this

end Chernoff

end ABC

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC025

#print "file: DkMath.ABC.ABC026"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-
# ABCFinal: Complete Proof Structure for ABC Conjecture

## Architecture Overview

This file contains the final assembly of the ABC conjecture proof,
focusing on the analytic and structural components that are fully formalized.
-/
noncomputable def K_of (γ : ℝ) : ℕ := 2 + (Nat.ceil γ : ℕ)


/--
`S_heavy_def` は、実数 `γ` と自然数 `X` を受け取り、有限集合 `Finset ℕ` を返す関数です。
この集合は、`X + 2` 未満の自然数のうち、素数であり、かつ `p ^ (K_of γ) ≤ X + 1` を満たすものから構成されます。
ここで `K_of γ` は `γ` に依存する関数です（詳細は定義を参照）。
この関数は非計算的（`noncomputable`）であり、主に解析的な数論の文脈で用いられます。
-/
noncomputable def S_heavy_def (γ : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 2)).filter fun p => p.Prime ∧ p ^ (K_of γ) ≤ X + 1


/--
`mem_S_heavy_of_pow_le` 補題は、素数 `p` が条件 `p ^ (K_of γ) ≤ X + 1` を満たすとき、
`p` が集合 `S_heavy_def γ X` に属することを示します。

- `γ : ℝ` はパラメータです。
- `X, p : ℕ` は自然数で、`p` は素数です。
- `hp : p.Prime` は `p` が素数であることを表します。
- `hpow : p ^ (K_of γ) ≤ X + 1` はべき乗の条件です。

この補題は、`S_heavy_def` の定義に基づき、べき乗条件から集合への包含を導きます。
-/
lemma mem_S_heavy_of_pow_le {γ : ℝ} {X p : ℕ} (hp : p.Prime) (hpow : p ^ (K_of γ) ≤ X + 1) :
  p ∈ S_heavy_def γ X := by
  dsimp [S_heavy_def]
  -- p is prime so p ≥ 2; K_of γ ≥ 2, hence p ≤ p ^ (K_of γ). Combine with hpow.
  have hp_ge2 : 2 ≤ p := Nat.Prime.two_le hp
  have two_le_K : 2 ≤ K_of γ := by
    dsimp [K_of]
    exact Nat.le_add_right 2 (Nat.ceil γ)
  have one_le_K : 1 ≤ K_of γ := by linarith [two_le_K]
  have p_le_pK : p ≤ p ^ (K_of γ) := by
   have hpow_p := (Nat.pow_le_pow_left_iff (Nat.Prime.two_le hp)).mpr one_le_K
   simp only [pow_one] at hpow_p
   exact hpow_p
  have : (p : ℕ) ≤ (X + 1) := Nat.le_trans p_le_pK hpow
  let hlt := Nat.lt_succ_of_le this
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_range.mpr hlt
  · exact ⟨hp, hpow⟩


/--
`S_heavy_subset_range` 補題は、実数 `γ` と自然数 `X` に対して、`S_heavy_def γ X` で定義される有限集合が `Finset.range (X + 2)` の部分集合であることを示します。
この補題は、`S_heavy_def` の構成要素が `0` から `X + 1` までの範囲に含まれることを保証します。
-/
lemma S_heavy_subset_range (γ : ℝ) (X : ℕ) :
  (S_heavy_def γ X : Finset ℕ) ⊆ Finset.range (X + 2) := by
  intro p hp
  simp only [S_heavy_def, Finset.mem_filter, Finset.mem_range] at hp
  exact Finset.mem_range.mpr hp.1


/--
`S_heavy_basic` 補題は、実数 `γ` と自然数 `X` に対して、有限集合 `S` が存在し、
- `S = S_heavy_def γ X` であること
- `S.card ≤ X + 2` であること
- `S` のすべての要素 `p` が素数であること

を示します。
この補題は、`S_heavy_def` で定義される集合が、要素数の上限と素数性を満たすことを保証します。
-/
lemma S_heavy_basic (γ : ℝ) (X : ℕ) :
  ∃ S : Finset ℕ, S = S_heavy_def γ X ∧ S.card ≤ (X + 2) ∧ (∀ p ∈ S, p.Prime) := by
  let S := S_heavy_def γ X
  use S
  -- first conjunct: definitional equality
  constructor
  · rfl
  -- second conjunct: card and primality
  constructor
  · -- cardinality bound: S ⊆ range (X+2)
    have hsub : S ⊆ Finset.range (X + 2) := S_heavy_subset_range γ X
    calc S.card ≤ (Finset.range (X + 2)).card := Finset.card_le_card hsub
    _ = X + 2 := by simp [Finset.card_range]
  · -- primality of elements is by construction
    intro p hp
    let h := Finset.mem_filter.mp hp
    have hprange := h.1
    have hp_pr := (h.2).1
    exact hp_pr


/--
`witness_n_for_S_heavy` 補題は、実数 `γ` と自然数 `X`, `p` に対して、`p` が集合 `S_heavy_def γ X` に属する場合、
ある自然数 `n` が存在し、`n ≤ X` かつ `(n * (n + 1)).factorization p ≥ K_of γ` を満たすことを主張します。
この補題は、`S_heavy_def` の定義に基づき、`p` の因数分解に関する下限を与えるものです。
-/
lemma witness_n_for_S_heavy {γ : ℝ} {X p : ℕ} (h : p ∈ S_heavy_def γ X) :
  ∃ n, n ≤ X ∧ (n * (n + 1)).factorization p ≥ K_of γ := by
  -- Unpack membership: p.Prime and p ^ (K_of γ) ≤ X + 1
  rcases Finset.mem_filter.1 h with ⟨_, ⟨hp, hpow⟩⟩
  let n := p ^ (K_of γ) - 1

  -- n ≤ X because p^K ≤ X + 1
  have n_le : n ≤ X := by
    dsimp [n]
    exact Nat.sub_le_sub_right hpow 1

  -- prove n ≠ 0 and (n+1) ≠ 0
  have two_le_K : 2 ≤ K_of γ := by dsimp [K_of]; exact Nat.le_add_right 2 (Nat.ceil γ)
  have one_le_K : 1 ≤ K_of γ := by
    have : 1 ≤ 2 := by norm_num
    exact Nat.le_trans this two_le_K
  have p_ge2 : 2 ≤ p := Nat.Prime.two_le hp
  have p_pow_ge_two : 2 ≤ p ^ (K_of γ) := by
    have p_le_pK := by simpa [pow_one] using (Nat.pow_le_pow_left_iff p_ge2).mpr one_le_K
    exact Nat.le_trans p_ge2 p_le_pK
  -- n+1 = p ^ K and its factorization at p equals K_of γ
  have hn1 : n + 1 = p ^ (K_of γ) := by
    dsimp [n]
    apply Nat.sub_add_cancel
    exact Nat.le_of_lt (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2) p_pow_ge_two)

  -- n+1 is nonzero
  have n1_ne_zero : (n + 1) ≠ 0 := by
    rw [hn1]
    exact pow_ne_zero (K_of γ) (Nat.Prime.ne_zero hp)

  -- n ≠ 0 because p^K - 1 ≥ 1
  have n_ne_zero : n ≠ 0 := by
    dsimp [n]
    have : 0 < p ^ (K_of γ) - 1 := by apply Nat.sub_pos_of_lt; linarith [p_pow_ge_two]
    exact Nat.pos_iff_ne_zero.mp this
  have hfac_n1 : (n + 1).factorization p = K_of γ := by
    rw [hn1, Nat.Prime.factorization_pow hp]
    simp

  -- multiplicativity of factorization: extract p-coordinate and conclude
  have fac_eq := Nat.factorization_mul n_ne_zero n1_ne_zero
  have sum_eq_dot : (n * (n + 1)).factorization p = n.factorization p + K_of γ := by
    have h := Nat.factorization_mul n_ne_zero n1_ne_zero
    have h' := congrArg (fun f => f p) h
    simp only [Finsupp.add_apply] at h'
    rw [hfac_n1] at h'
    exact h'

  have fac_ge_dot : (n * (n + 1)).factorization p ≥ K_of γ := by
    rw [sum_eq_dot]
    rw [add_comm]
    exact Nat.le_add_right (K_of γ) (n.factorization p)

  exact ⟨n, n_le, fac_ge_dot⟩

end ABC

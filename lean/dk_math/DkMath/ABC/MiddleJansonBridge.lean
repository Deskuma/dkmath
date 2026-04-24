/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.RpowExtras
import DkMath.ABC.MiddleBlockJS
import DkMath.ABC.MiddleDyadicCompose

#print "file: DkMath.ABC.MiddleJansonBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace DkMath.ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/-
  ABCMiddle.lean — Middle band scaffold (Janson/Suen bridge → block sum)
  目的：
    1) 中域の “使い方API” を固定
    2) Janson/Suen の確率版上界をブロックに適用する導線を用意
    3) 既存の Head/Tail 工具（幾何和・吸収）と合流する総和定理の型を定義
-/

namespace Middle

/- ---------------------------------------------
## 2. 中域の総和：`k` にわたる和を多項式上界へ

ここでは、ブロックごとの定数 `Cblk(k,X)` を幾何和で束ねるだけの層。
`geom_sum_pow_two_le` など既存の「2^k の幾何和」道具を利用する。
---------------------------------------------- -/

/-- 中域：`k ≤ ⌊log₂(X+1)⌋` にわたる合計を `X^(α+ε)` に閉じ込める上界の型。
    ここでは、各 `k` に対し `BlockJS X k` を「供給できる」ことを仮定として要求する。 -/
-- 中域：`k ≤ ⌊log₂(X+1)⌋` にわたる合計を `X^(α+ε)` に閉じ込める上界。
-- ここでは (1) 各 `k` に BlockJS を供給でき、
--         (2) 各項が C0 · 2^{(α+ε)k} で支配される、
-- の2仮定を受け取り、それを幾何和で畳み込む実装。
lemma middle_band_sum_bound
  (P : Params)
  (C0 : ℝ) (hC0 : 0 ≤ C0)
  -- 成長支配：各項が C0 · 2^{(α+ε)·k} で抑えられる（指数を掛けた形）
  (growth :
    ∀ ⦃X k⦄, 1 ≤ X → k ∈ Finset.range (Nat.log2 (X + 1) + 1) →
      (BadCountOn (P.θ) (MidBlock k X) : ℝ)
        ≤ C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
  :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
      (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1),
        (BadCountOn (P.θ) (MidBlock k X) : ℝ))
      ≤ C * (X : ℝ)^(P.α + P.ε)
  := by
    classical
    have hpos : 0 < P.α + P.ε := P.hpos
    -- choose the same C' as geom_sum_pow_two_le provides
    let X0' := 1
    let C' := (Real.rpow (2 : ℝ) (3 * (P.α + P.ε)) / (Real.rpow (2 : ℝ) (P.α + P.ε) - 1))
    have hC'nonneg : 0 ≤ C' := by
      have hnum_nonneg : 0 ≤ Real.rpow (2 : ℝ) (3 * (P.α + P.ε)) := by apply Real.rpow_nonneg; norm_num
      have denom_pos : 0 < Real.rpow (2 : ℝ) (P.α + P.ε) - 1 := by
        have : 1 < Real.rpow (2 : ℝ) (P.α + P.ε) := by
          have two_pos : (2 : ℝ) > 1 := by norm_num
          exact Real.one_lt_rpow two_pos (by exact_mod_cast hpos)
        exact sub_pos.mpr this
      exact div_nonneg hnum_nonneg (le_of_lt denom_pos)

    refine ⟨X0', C0 * C', by exact mul_nonneg hC0 hC'nonneg, ?_⟩
    intro X hXpos hXge

    -- sum over k ≤ log2(X+1)
    set S := Finset.range (Nat.log2 (X + 1) + 1) with hS
    -- define the sum to be bounded
    set BadSum : ℝ := ∑ k ∈ S, (BadCountOn (P.θ) (MidBlock k X) : ℝ) with hBad

    -- step1: termwise bound using the provided growth (rpow with multiplied exponent)
    have step1 : (BadSum)
      ≤ (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ))) := by
      apply Finset.sum_le_sum; intro k hk; exact growth (X:=X) (k:=k) hXpos hk

    -- step2: rewrite the sum into geometric series shape
    have step2 :
      (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
        = C0 * (∑ k ∈ S, (Real.rpow (2 : ℝ) (P.α + P.ε)) ^ k) := by
      have two_pos : 0 < (2 : ℝ) := by norm_num
      set q : ℝ := Real.rpow (2 : ℝ) (P.α + P.ε)
      calc
        (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
          = C0 * (∑ k ∈ S, Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ))) := by
            rw [Finset.mul_sum]
        _ = C0 * (∑ k ∈ S, q ^ k) := by
          apply congrArg (fun s => C0 * s)
          refine Finset.sum_congr rfl ?_
          intro k hk
          -- use the general rpow_mul_nat lemma: Real.rpow 2 ((α+ε) * k) = (2^(α+ε))^k
          exact RpowExtras.rpow_mul_nat (x := (2 : ℝ)) (a := (P.α + P.ε)) (hx := two_pos) k
    -- step3: apply geom_sum_pow_two_le to bound the geometric sum
    have Hgeo := geom_sum_pow_two_le (α := P.α) (ε := P.ε) (h := hpos)
    have step3 : (∑ k ∈ S, (Real.rpow (2 : ℝ) (P.α + P.ε)) ^ k)
      ≤ C' * (X : ℝ)^(P.α + P.ε) := by apply Hgeo; exact hXpos

    -- combine steps
    have final : (BadSum)
      ≤ C0 * C' * (X : ℝ)^(P.α + P.ε) := by
      calc
        (BadSum)
         ≤ (∑ k ∈ S, C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ))) := step1
        _ = C0 * (∑ k ∈ S, (Real.rpow (2 : ℝ) (P.α + P.ε)) ^ k) := by exact step2
        _ ≤ C0 * (C' * (X : ℝ)^(P.α + P.ε)) := by
          apply mul_le_mul_of_nonneg_left
          · exact step3
          · exact hC0
        _ = C0 * C' * (X : ℝ)^(P.α + P.ε) := by ring
    exact final

/- ---------------------------------------------
## 3. Top-level: Middle band を Head/Tail と合流

`head_absorb` / `tail_geom_bound` と合流して、全域の BadCount を
`C * X^(α+ε)` に収束させる。ここでは型だけ用意しておく。
---------------------------------------------- -/

/-- 中域を含む最終合流（Top-level 版）の外側 API。 -/
-- 中域を含む最終合流。Head/Middle/Tail をまとめて `C·X^(α+ε)` に収束させる。
theorem middle_band_bound_top
  (P : Params)
  (C0 : ℝ) (hC0 : 0 ≤ C0)
  (growth :
    ∀ ⦃X k⦄, 1 ≤ X → k ∈ Finset.range (Nat.log2 (X + 1) + 1) →
      (BadCountOn (P.θ) (MidBlock k X) : ℝ)
        ≤ C0 * Real.rpow (2 : ℝ) ((P.α + P.ε) * (k : ℝ)))
  (hε_pos : 0 < P.ε)
  (hα_eq : P.Hblock.α = P.α)
  :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
      (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1),
        (BadCountOn (P.θ) (MidBlock k X) : ℝ))
      ≤ C * (X : ℝ)^(P.α + P.ε) := by
  classical
  -- Head
  obtain ⟨X0h, Ch, hCh, Hh⟩ := head_absorb (θ:=P.θ) (α:=P.α) (ε:=P.ε) P.hpos (k0 := 3)
  -- Middle（直上の lemma）
  obtain ⟨X0m, Cm, hCm, Hm⟩ := middle_band_sum_bound P C0 hC0 growth
  -- Tail
  obtain ⟨k0t, Ct, hCt, Ht⟩ := tail_geom_bound P.Hblock P.ε (by have := P.hpos; linarith)

  -- X0 と C を合成
  refine ⟨Nat.max X0h X0m, Ch + Cm + Ct, by nlinarith, ?_⟩
  intro X hXpos hXge
  have h1 := Hh hXpos (le_trans (Nat.le_max_left _ _) hXge)
  have h2 := Hm hXpos (le_trans (Nat.le_max_right _ _) hXge)
  have h3 := Ht hXpos

  -- sum over k ≤ log2(X+1)
  set S := Finset.range (Nat.log2 (X + 1) + 1) with hS
  -- define the sum to be bounded
  set BadSum : ℝ := ∑ k ∈ S, (BadCountOn (P.θ) (MidBlock k X) : ℝ) with hBad
  -- split the sum into three parts: k < 3, 3 ≤ k < k0t, k ≥ k0t
  set sum_k0t := (∑ k ∈ S, if k ≥ k0t then (BadCountOn (P.θ) (MidBlock k X) : ℝ) else 0) with hsum_k0t
  -- the rest is the finite sum k=0,1,2
  set sum3 := (∑ k ∈ Finset.range 3, (BadCountOn (P.θ) (MidBlock k X) : ℝ)) with hsum3

  -- rewrite tail exponent from P.Hblock.α to P.α using the provided equality
  have h3' : sum_k0t
    ≤ Ct * (X : ℝ)^(P.α + P.ε) := by
    have heq_exp : P.Hblock.α + P.ε = P.α + P.ε := by rw [hα_eq]
    rwa [heq_exp] at h3
  have hsum_final : (BadSum)
    ≤ (Ch + Cm + Ct) * (X : ℝ)^(P.α + P.ε) := by
    -- 中域の和は、非負の余分な和を加えた三項和より小さい（あるいは等しい）
    have hstep1 : (BadSum)
      ≤ sum3
        + (BadSum)
        + sum_k0t := by
      -- 右辺に足す二つの項は非負なので加えても不等式は保たれる
      have h_nonneg_sum3 : 0 ≤ sum3 := by
        apply Finset.sum_nonneg; intro k hk; exact_mod_cast (Nat.zero_le _)
      have h_nonneg_sumif : 0 ≤ sum_k0t := by
        apply Finset.sum_nonneg
        intro k hk
        by_cases hge : k ≥ k0t
        · simp [hge]
        · exact_mod_cast (Nat.zero_le _)
      have hsum_nonneg : 0 ≤ sum3 + sum_k0t :=
        by simpa using add_nonneg h_nonneg_sum3 h_nonneg_sumif
      -- 並びを (a + (b + c)) から (b + (a + c)) の形に変えてから適用する
      have heq : sum3 + (BadSum) + sum_k0t
                = (BadSum) + (sum3 + sum_k0t) := by ring
      rw [heq]
      apply le_add_of_nonneg_right
      exact hsum_nonneg
    -- 三項和については h1, h2, h3' が上界を与えるので合成して使う
    have hstep2 : sum3 + (BadSum) + sum_k0t
      ≤ Ch * (X : ℝ)^(P.α + P.ε) + Cm * (X : ℝ)^(P.α + P.ε) + Ct * (X : ℝ)^(P.α + P.ε) := by
      apply add_le_add (add_le_add h1 h2) h3'
    -- 最後に右辺を合成して目的形にする
    have hfinal := le_trans hstep1 hstep2
    calc
      (BadSum)
        ≤ Ch * (X : ℝ)^(P.α + P.ε) + Cm * (X : ℝ)^(P.α + P.ε) + Ct * (X : ℝ)^(P.α + P.ε) := hfinal
      _ = (Ch + Cm + Ct) * (X : ℝ)^(P.α + P.ε) := by ring
  exact hsum_final

-- #check middle_band_sum_bound
-- #check middle_band_bound_top

end Middle

end DkMath.ABC

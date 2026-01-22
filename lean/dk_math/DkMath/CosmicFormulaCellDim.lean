/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib
import DkMath.CellDim

namespace DkMath
namespace CosmicFormulaCellDim

open scoped BigOperators
open DkMath.CellDim

variable {d : ℕ}

instance decidableEqCell : DecidableEq (Cell d) :=
  Fintype.decidablePiFintype

/-- 定数ベクトル（各軸同じ長さ） -/
def constVec (d : ℕ) (n : ℕ) : Fin d → ℕ := fun _ => n

/-- Big: (x+u)^d 個のセル（箱） -/
def Big (d x u : ℕ) : Finset (Cell d) :=
  Box (d := d) (constVec d (x + u))

/-- Gap: u^d 個のセル（箱） -/
def Gap (d u : ℕ) : Finset (Cell d) :=
  Box (d := d) (constVec d u)

@[simp] lemma card_Big (x u : ℕ) :
    (Big (d := d) x u).card = ∏ _i : Fin d, (x + u) := by
  classical
  simp [Big, constVec]

@[simp] lemma card_Gap (u : ℕ) :
    (Gap (d := d) u).card = ∏ _i : Fin d, u := by
  classical
  simp [Gap, constVec]

  -- Body と disjoint 分解は次段。

  -- 狙い（構造）:
  --   Big = Body ∪ Gap
  --   Disjoint Body Gap
  --   card Big = card Body + card Gap
  -- そして card を (x+u)^d, x*G_{d-1}(x,u), u^d に同定する。

  -- Body を差集合で作るより、「どの軸が u 以上か」で disjoint な箱の合併として構成するのが実装が強い。

  -- 以下はまず `sdiff` 版の雛形：集合恒等式を整え、のちに差し替え可能な形にしておく.

def Body (d x u : ℕ) : Finset (Cell d) :=
  Big (d := d) x u \ Gap (d := d) u

lemma Gap_subset_Big (d x u : ℕ) :
    Gap (d := d) u ⊆ Big (d := d) x u := by
  classical
  -- 各軸で `u ≤ x + u` なので Box_mono を使う
  have : ∀ i, (constVec d u) i ≤ (constVec d (x + u)) i := fun _ => Nat.le_add_left u x
  simp only [Gap, Big]
  exact Box_mono (d := d) (a := constVec d u) (b := constVec d (x + u)) this

lemma Big_eq_Body_union_Gap (d x u : ℕ) :
    Big (d := d) x u = Body (d := d) x u ∪ Gap (d := d) u := by
  classical
  have hsub : Gap (d := d) u ⊆ Big (d := d) x u := Gap_subset_Big (d := d) x u
  simpa [Body] using (Finset.sdiff_union_of_subset hsub)

lemma Disjoint_Body_Gap (d x u : ℕ) :
    Disjoint (Body (d := d) x u) (Gap (d := d) u) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro a ha hb
  -- ha : a ∈ Big \ Gap なので a ∉ Gap
  exact (Finset.mem_sdiff.1 ha).2 hb

lemma card_Big_eq_card_Body_add_card_Gap (d x u : ℕ) :
    (Big (d := d) x u).card =
      (Body (d := d) x u).card + (Gap (d := d) u).card := by
  classical
  have hdis : Disjoint (Body (d := d) x u) (Gap (d := d) u) := Disjoint_Body_Gap (d := d) x u
  calc
    (Big (d := d) x u).card
        = ((Body (d := d) x u ∪ Gap (d := d) u)).card := by
            simp [Big_eq_Body_union_Gap (d := d) x u]
        _ = (Body (d := d) x u).card + (Gap (d := d) u).card := by
          simpa using (Finset.card_union_of_disjoint hdis)


end CosmicFormulaCellDim
end DkMath

namespace DkMath
namespace CosmicFormulaCellDim

open scoped BigOperators

/-- 二項定理（choose）側の G_{d-1} :  Σ_{k < d} (d choose k+1) x^k u^(d-1-k) -/
def Gbinom (d x u : ℕ) : ℕ :=
  Finset.sum (Finset.range d) fun k => Nat.choose d (k + 1) * x ^ k * u ^ (d - 1 - k)

/-
狙い：
  (x+u)^d - u^d = x * Gbinom d x u
方針：
  1) (u+x)^d を二項定理で Σ choose d k * u^k * x^(d-k) に展開
  2) 末項 k=d が u^d なので、差を取ると Σ_{k < d} に落ちる（sum_range_succ で剥がす）
  3) 反転（reflect）して x^(k+1) を作り、x を因数として外へ出す
  4) choose の対称性で choose d (d-1-k) = choose d (k+1) に変換
-/
theorem pow_sub_pow_eq_mul_Gbinom (d x u : ℕ) :
    (x + u)^d - u^d = x * Gbinom d x u := by
  classical
  cases d with
  | zero =>
      simp [Gbinom]
  | succ d =>
      -- 以後 n = d+1
      set n : ℕ := d+1
      have hn : n = d+1 := rfl

      -- (u+x)^n の二項展開：Σ choose n k * u^k * x^(n-k)
      have hpow :
          (u + x)^n
            = ∑ k ∈ Finset.range (n+1),
                Nat.choose n k * u^k * x^(n-k) := by
        simp [add_pow, mul_assoc, mul_comm (Nat.choose n _)]

      -- u+x = x+u を使って左辺を合わせる
      have hpow' :
          (x + u)^n
            = ∑ k ∈ Finset.range (n+1),
                Nat.choose n k * u^k * x^(n-k) := by
        rw [add_comm]
        exact hpow

      -- 末項 k=n は choose n n * u^n * x^0 = u^n
      have h_last :
          (Nat.choose n n) * u^n * x^(n-n) = u^n := by
        simp

      -- Σ_{k < n+1} f k = Σ_{k < n} f k + f n を使って末項を剥がし、差を取る
      let f : ℕ → ℕ := fun k => Nat.choose n k * u^k * x^(n-k)
      have hsplit :
          (∑ k ∈ Finset.range (n+1), f k)
            = (∑ k ∈ Finset.range n, f k) + f n := by
        -- `Finset.sum_range_succ` : sum (range (n+1)) f = sum (range n) f + f n
        simpa [f] using (Finset.sum_range_succ f n)

      have hsub :
          (x+u)^n - u^n = ∑ k ∈ Finset.range n, f k := by
        -- (x+u)^n = sum(range(n+1)) f
        -- sum = sum(range n) f + f n, かつ f n = u^n
        -- なので差を取ると sum(range n) f
        have : (x+u)^n = (∑ k ∈ Finset.range n, f k) + f n := by
          simpa [hpow', hsplit]
        -- Nat の tsub
        -- a = b + c なら a - c = b
        -- `Nat.add_sub_cancel` で落ちる
        calc
          (x+u)^n - u^n
              = ((∑ k ∈ Finset.range n, f k) + f n) - u^n := by simp [this]
          _ = (∑ k ∈ Finset.range n, f k) := by
                -- f n = u^n を入れて add_sub_cancel
                -- ※ `simp [f, h_last]` で落ちることが多い
                simp [f, h_last]

      -- 反転して x^(k+1) の形を作る（k ↦ (n-1-k)）
      have hreflect :
          (∑ k ∈ Finset.range n, f k)
            = ∑ k ∈ Finset.range n,
                Nat.choose n (n-1-k) * u^(n-1-k) * x^(k+1) := by
        classical
        -- ∑_{k < n} f k = ∑_{j < n} f(n-1-j) で変数変換
        have h_sym : ∑ k ∈ Finset.range n, f k = ∑ j ∈ Finset.range n, f (n - 1 - j) := by
          refine Finset.sum_nbij (fun j _ => n - 1 - j)
            (fun j hj => Finset.mem_range.mpr (by omega : n - 1 - j < n))
            (fun j₁ j₂ _ _ h => by omega)
            (fun k hk => ⟨n - 1 - k, Finset.mem_range.mpr (by omega), by omega⟩)
        rw [h_sym]
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [f, mul_assoc, mul_left_comm]
        congr 1
        have h_j : n - (n - 1 - j) = j + 1 := by omega
        exact h_j

      -- choose の対称性：choose n (n-1-k) = choose n (k+1)
      have hchoose :
          (∑ k ∈ Finset.range n,
              Nat.choose n (n-1-k) * u^(n-1-k) * x^(k+1))
            = (∑ k ∈ Finset.range n,
                Nat.choose n (k+1) * u^(n-1-k) * x^(k+1)) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        -- hk : k ∈ range n, つまり k < n
        have hk' : k < n := Finset.mem_range.mp hk
        -- (n - (k+1)) = (n-1-k)
        have hnk : n - (k + 1) = n - 1 - k := by omega
        -- choose_symm: choose n r = choose n (n - r)
        -- r = k+1 とすれば choose n (k+1) = choose n (n - (k+1)) = choose n (n-1-k)
        have h_eq : Nat.choose n (n - 1 - k) = Nat.choose n (k + 1) := by
          have : n - (k + 1) = n - 1 - k := hnk
          rw [← this]
          exact (Nat.choose_symm (by omega : k + 1 ≤ n))
        simp [h_eq]

      -- x^(k+1)=x*x^k で因数 x を外に出す → 定義した Gbinom に一致
      have hfactor :
          (∑ k ∈ Finset.range n,
              Nat.choose n (k+1) * u^(n-1-k) * x^(k+1))
            = x * Gbinom n x u := by
        -- 右は ∑ choose n (k+1) * x^k * u^(n-1-k) に x を掛けたもの
        -- x^(k+1) = x * x^k
        have h1 : (∑ k ∈ Finset.range n,
                  Nat.choose n (k+1) * u^(n-1-k) * x^(k+1))
              = (∑ k ∈ Finset.range n,
                  Nat.choose n (k+1) * u^(n-1-k) * (x * x^k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
        rw [h1]
        -- 分配法則：∑ a * (x * b) = ∑ x * (a * b) = x * ∑ a * b
        have h2 : (∑ k ∈ Finset.range n,
                  Nat.choose n (k+1) * u^(n-1-k) * (x * x^k))
              = (x * ∑ k ∈ Finset.range n,
                  Nat.choose n (k+1) * u^(n-1-k) * x^k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
        rw [h2]
        congr 1
        simp only [Gbinom]
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring

      -- まとめ
      -- (x+u)^n - u^n = x * Gbinom n x u
      -- ただし n=d+1 で、元の主張は d=n なので simp で戻す
      -- ここでは n=d+1 なので主張は d=n、つまり succ ケースの d に対応
      -- よって d+1 の形を返す
      -- 最終的に (x+u)^(d+1) - u^(d+1) = x * Gbinom (d+1) x u
      -- になる
      -- 実際：
      calc
        (x+u)^n - u^n
            = ∑ k ∈ Finset.range n, f k := hsub
        _ = ∑ k ∈ Finset.range n,
                Nat.choose n (n-1-k) * u^(n-1-k) * x^(k+1) := hreflect
        _ = ∑ k ∈ Finset.range n,
                Nat.choose n (k+1) * u^(n-1-k) * x^(k+1) := hchoose
        _ = x * Gbinom n x u := hfactor

end CosmicFormulaCellDim
end DkMath

/-! ### 補題群: 積をべきに畳み、card を差で表す -/

namespace DkMath
namespace CosmicFormulaCellDim

open scoped BigOperators
open DkMath.CellDim

variable {d : ℕ}

/-- Fin d 上の定数積はべきに畳める: (∏ _ : Fin d, n) = n^d. -/
lemma prod_const_fin (n : ℕ) :
    (∏ _i : Fin d, n) = n ^ d := by
  classical
  simp [Finset.prod_const, Fintype.card_fin]

/-- card_Big をべき表示にする -/
theorem card_Big_pow (x u : ℕ) :
    (Big (d := d) x u).card = (x + u) ^ d := by
  classical
  simp only [card_Big, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- card_Gap をべき表示にする -/
theorem card_Gap_pow (u : ℕ) :
    (Gap (d := d) u).card = u ^ d := by
  classical
  simp only [card_Gap, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Body の濃度は全体から gap を引いたものに等しい -/
theorem card_Body_eq_sub (d x u : ℕ) :
    (Body (d := d) x u).card =
      (Big (d := d) x u).card - (Gap (d := d) u).card := by
  classical
  have h := card_Big_eq_card_Body_add_card_Gap (d := d) x u
  calc
    (Body (d := d) x u).card
        = ((Body (d := d) x u).card + (Gap (d := d) u).card) - (Gap (d := d) u).card := by
          rw [Nat.add_sub_cancel (Body (d := d) x u).card (Gap (d := d) u).card]
    _ = (Big (d := d) x u).card - (Gap (d := d) u).card := by
          rw [h]

/-- 最終形: Body = (x+u)^d - u^d. -/
theorem card_Body_pow_form (d x u : ℕ) :
    (Body (d := d) x u).card = (x + u) ^ d - u ^ d := by
  classical
  simp only [card_Body_eq_sub (d := d) x u, card_Big_pow (d := d) x u, card_Gap_pow (d := d) u]

/-- 差のべきの因数分解に使う和 `G` -/
def G (d x u : ℕ) : ℕ :=
  Finset.sum (Finset.range d) fun k => (x + u)^(d - 1 - k) * u ^ k

/-- (x+u)^d - u^d = x * G x u -/
theorem pow_sub_pow_eq_mul_G (d x u : ℕ) :
    (x + u) ^ d - u ^ d = x * G d x u := by
  induction d with
  | zero =>
    -- range 0 の和は 0, 両辺とも 0
    simp [G]
  | succ d ih =>
    let a := x + u
    let b := u
    have h_ab : a - b = x := by simp [a, b]
    -- 幾何和の補題を使用します: (∑_{i < d+1} a^i b^{d-i})*(a-b) + b^{d+1} = a^{d+1}
    have h := (Commute.all (a - b) b).geom_sum₂_mul_add (d + 1)
    -- 合計インデックスを反映して、`∑ k ∈ Finset.range (d+1), a^(d-k) * b^k` 形式と一致するようにします。
    have h' : (a - b) * ∑ k ∈ Finset.range (d + 1), a ^ (d - k) * b ^ k
      = a ^ (d + 1) - b ^ (d + 1) := by
      -- 直接 `Finset.sum_range_reflect` を使って h の和の向きを反転する
      rw [← Finset.sum_range_reflect] at h
      -- eq_tsub_of_add_eq h は `(Finset.sum ... ) * (a - b) = a^(d+1) - b^(d+1)` を与えるので、
      -- それを目的形に合わせるために `mul_comm` で掛け算の順序を入れ替える。
      let h1 := eq_tsub_of_add_eq h
      rw [mul_comm] at h1
      -- 簡約: a - b + b = a, d + 1 - 1 - j = d - j
      simp only [Nat.add_sub_cancel] at h1
      -- a - b = x より a = x + b を先に確立する
      have ha_eq : a = x + b := by simp [a, b]
      convert h1 using 2
      · -- ⊢ ∑ k ∈ Finset.range (d + 1), a ^ (d - k) * b ^ k
        -- = ∑ x ∈ Finset.range (d + 1), (a - b + b) ^ (d - x) * b ^ (d - (d - x))
        refine Finset.sum_congr rfl ?_
        intro x_1 hx
        have hx' : x_1 ≤ d := Nat.le_of_lt_succ (Finset.mem_range.1 hx)
        have hsub : d - (d - x_1) = x_1 := by
          apply (Nat.sub_eq_iff_eq_add (a := d) (b := d - x_1) (c := x_1) (Nat.sub_le _ _)).2
          simpa using (Nat.add_sub_of_le hx').symm
        have hsum : a - b + b = a := by
          calc
            a - b + b = x + b := by simp [h_ab]
            _ = a := by simp [ha_eq]
        simp [hsub, hsum]
      · -- ⊢ a ^ (d + 1) = (a - b + b) ^ (d + 1)
        simp [ha_eq]
    simpa [h_ab] using (Eq.symm h')

/-- 最終形: Body = x * G d x u -/
theorem card_Body_eq_mul_G (d x u : ℕ) :
    (Body (d := d) x u).card = x * G d x u := by
  -- 既存の card_Body_pow_form と今回の pow_sub_pow_eq_mul_G を繋ぐ
  simpa [card_Body_pow_form (d := d) x u] using pow_sub_pow_eq_mul_G d x u

/-- 既存の幾何和版 `G` と二項定理版 `Gbinom` は、少なくとも `x` を掛けると一致。 -/
theorem mul_G_eq_mul_Gbinom (d x u : ℕ) :
    x * G d x u = x * Gbinom d x u := by
  -- 左辺も右辺も (x+u)^d - u^d に等しい
  calc
    x * G d x u = (x+u)^d - u^d := by
      exact (pow_sub_pow_eq_mul_G d x u).symm
    _ = x * Gbinom d x u := by
      exact pow_sub_pow_eq_mul_Gbinom d x u

/-- おまけ：x > 0 なら G 自体も一致（Nat の乗法キャンセル）。 -/
theorem G_eq_Gbinom_of_pos {d x u : ℕ} (hx : 0 < x) :
    G d x u = Gbinom d x u := by
  have h := mul_G_eq_mul_Gbinom (d := d) (x := x) (u := u)
  exact Nat.mul_left_cancel (Nat.pos_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hx)) h

end CosmicFormulaCellDim
end DkMath

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
          Finset.sum (Finset.range n) f
            = Finset.sum (Finset.range n) fun k => Nat.choose n (n-1-k) * u^(n-1-k) * x^(k+1) := by
        have h := (Finset.sum_range_reflect f n).symm
        refine Eq.trans h ?_
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [f]
        have hk_lt : k < n := Finset.mem_range.1 hk
        have : n - 1 - k = n - (k + 1) := by omega
        rw [this]
        -- 目標: n.choose (n - (k+1)) * u ^ (n - (k+1)) * x ^ (n - (n - (k+1))) =
        --       n.choose (n - (k+1)) * u ^ (n - (k+1)) * x ^ (k+1)
        have h_exp : n - (n - (k + 1)) = k + 1 := by omega
        rw [h_exp]
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
        -- (n - (k+1)) = (n-1-k) より choose の対称性を適用
        have hnk : n - (k + 1) = n - 1 - k := by omega
        -- choose_symm: choose n r = choose n (n - r)
        -- r = k+1 とすれば choose n (k+1) = choose n (n - (k+1)) = choose n (n-1-k)
        have h_eq : Nat.choose n (n - 1 - k) = Nat.choose n (k + 1) := by
          rw [← hnk]
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

/-! ### 2D 手本：Body の L字分解（card 版） -/

/-- 2次元の長さベクトル（w,h） -/
def vec2 (w h : ℕ) : Fin 2 → ℕ :=
  fun i => if (i : ℕ) = 0 then w else h

@[simp] lemma vec2_fst (w h : ℕ) : vec2 w h ⟨0, by decide⟩ = w := by
  simp [vec2]

@[simp] lemma vec2_snd (w h : ℕ) : vec2 w h ⟨1, by decide⟩ = h := by
  simp [vec2]

/-- 2D 矩形（原点） -/
def Rect2 (w h : ℕ) : Finset (Cell2) :=
  Box (d := 2) (vec2 w h)

/-- 2D 矩形（平行移動） -/
def RectAt2 (ox oy : ℤ) (w h : ℕ) : Finset (Cell2) :=
  BoxAt (d := 2) (mk2 ox oy) (vec2 w h)

/-- 2D 矩形の濃度は w*h -/
theorem card_Rect2 (w h : ℕ) :
    (Rect2 w h).card = w * h := by
  classical
  -- card_Box_eq_prod がある前提（既に d 次元側で整備済みのはず）
  -- ∏ i:Fin 2, vec2 w h i = w*h へ simp で落ちる
  unfold Rect2 Box vec2
  simp only [Finset.card_map, Finset.card_pi, Finset.card_range]
  norm_num

/-- 平行移動しても濃度は同じ -/
theorem card_RectAt2 (ox oy : ℤ) (w h : ℕ) :
    (RectAt2 ox oy w h).card = w * h := by
  classical
  simp [RectAt2, BoxAt, card_translate, vec2]

/-- ついで：2D の G は x+2u（幾何和でも二項でも一致） -/
theorem G_two_dim_eval (x u : ℕ) :
    G 2 x u = x + 2*u := by
  classical
  -- G 2 x u = Σ_{k<2} (x+u)^(1-k) * u^k = (x+u)^1*u^0 + (x+u)^0*u^1
  -- = (x+u) + u
  unfold G
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-- 2D の最終形（既に通しているはずだが、手本として露出） -/
theorem card_Body2_eq_x_mul (x u : ℕ) :
    (Body (d := 2) x u).card = x * (x + 2*u) := by
  classical
  -- 既に card_Body_eq_mul_G があるので、G_two_dim_eval で落とす
  simp [G_two_dim_eval, card_Body_eq_mul_G]

/--
2D の Body 濃度は「2つの矩形濃度の和」になる（L字の手本）。

Big: (x+u)×(x+u)
Gap: u×u
Body は
  A: 左の帯  (幅 u, 高さ x) を上へ u だけ平行移動
  B: 右の帯  (幅 x, 高さ x+u) を右へ u だけ平行移動
の濃度和として表せる。
-/
theorem card_Body2_as_two_rects (x u : ℕ) :
    (Body (d := 2) x u).card
      = (RectAt2 0 (Int.ofNat u) u x).card
        + (RectAt2 (Int.ofNat u) 0 x (x+u)).card := by
  classical
  -- 左辺は既に確立：card_Body_pow_form などから
  -- (x+u)^2 - u^2 = x*(x+2u)
  -- 右辺は矩形2枚の濃度：u*x + x*(x+u) = x*(x+2u)
  -- まず右側を w*h に落とす
  have h_left : (Body (d := 2) x u).card = x * (x + 2*u) :=
    card_Body2_eq_x_mul x u
  have h_right : (RectAt2 0 (Int.ofNat u) u x).card + (RectAt2 (Int.ofNat u) 0 x (x+u)).card
      = u*x + x*(x+u) := by
    simp [card_RectAt2, Nat.mul_comm]
  calc (Body (d := 2) x u).card
      = x * (x + 2*u) := h_left
    _ = x*x + x*(2*u) := Nat.mul_add x x (2*u)
    _ = x*x + 2*x*u := by ring
    _ = u*x + x*x + x*u := by ring
    _ = u*x + x*(x+u) := by ring
    _ = (RectAt2 0 (Int.ofNat u) u x).card + (RectAt2 (Int.ofNat u) 0 x (x+u)).card := h_right.symm

/-! ### 一般次元の Slab 分解（次の本命） -/

/-- Fin d 上の「下側長 u / 上側長 x / 全長 x+u」を軸ごとに組むヘルパ -/
def slabLen (x u : ℕ) (i : Fin d) (j : Fin d) : ℕ :=
  if j < i then u else if j = i then x else (x+u)

/-- Slab(i) の原点箱（あとで translate でオフセット u を載せる） -/
def Slab0 (d x u : ℕ) (i : Fin d) : Finset (Cell d) :=
  Box (d := d) (fun j => slabLen (d := d) x u i j)

/-- Slab(i) の平行移動：軸 i にだけ u を足す（区間 [u, u+x) を作る） -/
def slabShift (d u : ℕ) (i : Fin d) : Cell d :=
  fun j => if j = i then Int.ofNat u else 0

/-- Slab(i) の定義：Slab0 を軸 i 方向に u だけ平行移動 -/
def Slab (d x u : ℕ) (i : Fin d) : Finset (Cell d) :=
  translate (d := d) (slabShift (d := d) u i) (Slab0 (d := d) x u i)

/-! ### Slab の性質と分解定理 -/

/-- Slab0 の濃度：∏ slabLen の積 -/
lemma card_Slab0 (d x u : ℕ) (i : Fin d) :
    (Slab0 (d := d) x u i).card =
      (∏ j : Fin d, slabLen (d := d) x u i j) := by
  classical
  unfold Slab0
  rw [card_Box_eq_prod]

/-- Slab の濃度は平行移動しても変わらない -/
lemma card_Slab (d x u : ℕ) (i : Fin d) :
    (Slab (d := d) x u i).card = (Slab0 (d := d) x u i).card := by
  classical
  unfold Slab
  simp [card_translate]

/-- slabLen の積を3つの部分に分解する補助補題 -/
lemma prod_slabLen_split (d x u : ℕ) (i : Fin d) :
    (∏ j : Fin d, slabLen (d := d) x u i j) =
      (∏ j : Fin d with j < i, u) *
      x *
      (∏ j : Fin d with i < j, (x + u)) := by
  classical
  -- まず i の位置で積を分離する
  have h_split : (Finset.univ : Finset (Fin d)) =
    Finset.univ.filter (· < i) ∪ {i} ∪ Finset.univ.filter (i < ·) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton]
    constructor
    · intro _
      by_cases h1 : j < i
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : j = i
        · exact Or.inl (Or.inr h2)
        · push_neg at h1
          exact Or.inr (by
            have : i ≤ j := h1
            cases Nat.lt_or_eq_of_le this with
            | inl hlt => exact hlt
            | inr heq => exact absurd (Fin.ext heq).symm h2)
    · intro _; trivial
  -- 積を3つの部分に分解
  conv_lhs => rw [h_split]
  -- union の積を分解（2回）
  rw [Finset.prod_union]
  · rw [Finset.prod_union]
    · -- 3つの部分の積を評価
      simp only [Finset.prod_singleton]
      -- slabLen (d := d) x u i i = x
      have hi : slabLen (d := d) x u i i = x := by
        simp only [slabLen, lt_self_iff_false, ite_false, ite_true]
      rw [hi]
      -- 左側と右側の積を個別に変形
      have h_left : (∏ j : Fin d with j < i, slabLen (d := d) x u i j) =
                    (∏ j : Fin d with j < i, u) := by
        refine Finset.prod_congr rfl ?_
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [slabLen, hj, ite_true]
      have h_right : (∏ j : Fin d with i < j, slabLen (d := d) x u i j) =
                     (∏ j : Fin d with i < j, (x + u)) := by
        refine Finset.prod_congr rfl ?_
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [slabLen]
        have h1 : ¬(j < i) := fun hcontra => Fin.lt_irrefl j (Fin.lt_trans hcontra hj)
        simp only [h1, ite_false]
        have h2 : j ≠ i := Fin.ne_of_gt hj
        simp only [h2, ite_false]
      simp only [h_left, h_right]
    · -- filter (· < i) と {i} は disjoint
      simp only [Finset.disjoint_singleton_right, Finset.mem_filter,
                 Finset.mem_univ, true_and]
      exact Fin.lt_irrefl i
  · -- (filter (· < i) ∪ {i}) と filter (i < ·) は disjoint
    rw [Finset.disjoint_union_left]
    constructor
    · simp only [Finset.disjoint_filter]
      intro j _ hlt hgt
      exact Fin.lt_irrefl j (Fin.lt_trans hlt hgt)
    · simp only [Finset.disjoint_singleton_left, Finset.mem_filter,
                 Finset.mem_univ, true_and]
      exact Fin.lt_irrefl i

/-- Fin d 内で j < i を満たす要素の個数は i 個 -/
lemma card_filter_lt_fin (d : ℕ) (i : Fin d) :
    (Finset.univ.filter (· < i)).card = (i : ℕ) := by
  classical
  -- `Fin d` の「j < i」を自然数に落として、`range i` との全単射で数える
  have hi : i.val < d := i.isLt
  -- s = { j | j < i }
  let s : Finset (Fin d) := Finset.univ.filter (· < i)
  -- t = {0,1,...,i-1}
  let t : Finset ℕ := Finset.range i.val
  have h_mem : ∀ j : Fin d, j ∈ s → j.val ∈ t := by
    intro j hj
    have hj_lt : j < i := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (by simpa using hj_lt)
  have h_inj : ∀ (a : Fin d) (ha : a ∈ s) (b : Fin d) (hb : b ∈ s),
      (fun (j : Fin d) _ => j.val) a ha = (fun j _ => j.val) b hb → a = b := by
    intro a ha b hb hval
    exact Fin.ext hval
  have h_surj : ∀ n : ℕ, n ∈ t → ∃ j : Fin d, ∃ hj : j ∈ s, (fun j _ => j.val) j hj = n := by
    intro n hn
    have hn_lt : n < i.val := Finset.mem_range.mp hn
    have hn_lt_d : n < d := Nat.lt_trans hn_lt hi
    refine ⟨⟨n, hn_lt_d⟩, ?_, rfl⟩
    have : (⟨n, hn_lt_d⟩ : Fin d) < i := by simpa using hn_lt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
  have h_card : s.card = t.card :=
    Finset.card_bij (s := s) (t := t) (i := fun (j : Fin d) _ => j.val)
      h_mem h_inj h_surj
  -- 目標の形に戻す
  simpa [s, t, Finset.card_range] using h_card

/-- Fin d 内で i < j を満たす要素の個数は d - 1 - i 個 -/
lemma card_filter_gt_fin (d : ℕ) (i : Fin d) :
    (Finset.univ.filter (i < ·)).card = (d - 1 - (i : ℕ)) := by
  classical
  -- まず j ≤ i の個数を数える：{0,…,i} で i+1 個
  have hi : i.val < d := i.isLt
  let s_le : Finset (Fin d) := Finset.univ.filter (· ≤ i)
  let t_le : Finset ℕ := Finset.range (i.val + 1)
  have h_mem : ∀ j : Fin d, j ∈ s_le → j.val ∈ t_le := by
    intro j hj
    have hj_le : j ≤ i := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_of_le_of_lt hj_le (Nat.lt_succ_self _))
  have h_inj : ∀ (a : Fin d) (ha : a ∈ s_le) (b : Fin d) (hb : b ∈ s_le),
      (fun (j : Fin d) _ => j.val) a ha = (fun j _ => j.val) b hb → a = b := by
    intro a ha b hb hval; exact Fin.ext hval
  have h_surj : ∀ n : ℕ, n ∈ t_le → ∃ j : Fin d, ∃ hj : j ∈ s_le, (fun j _ => j.val) j hj = n := by
    intro n hn
    have hn_lt : n < i.val + 1 := Finset.mem_range.mp hn
    have hn_le : n ≤ i.val := Nat.lt_succ_iff.mp hn_lt
    have hn_lt_d : n < d := lt_of_le_of_lt hn_le hi
    refine ⟨⟨n, hn_lt_d⟩, ?_, rfl⟩
    have : (⟨n, hn_lt_d⟩ : Fin d) ≤ i := by simpa using hn_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
  have h_card_le : s_le.card = t_le.card :=
    Finset.card_bij (s := s_le) (t := t_le) (i := fun (j : Fin d) _ => j.val)
      h_mem h_inj h_surj
  have h_le_card : (Finset.univ.filter (· ≤ i)).card = i.val + 1 := by
    simpa [s_le, t_le, Finset.card_range] using h_card_le
  -- 全体 d 個から j ≤ i (i+1 個) を除いた残りが j > i
  have h_split := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin d))) (p := fun j => j ≤ i)
  have h_split' :
      (Finset.univ.filter (· ≤ i)).card + (Finset.univ.filter fun j => ¬ j ≤ i).card = d := by
    simpa [Finset.card_univ, Fintype.card_fin] using h_split
  have h_gt_card_neg : (Finset.univ.filter fun j => ¬ j ≤ i).card = d - (i.val + 1) := by
    have hsum' : i.val + 1 + (Finset.univ.filter fun j => ¬ j ≤ i).card = d := by
      simpa [h_le_card, Nat.add_comm] using h_split'
    calc
      (Finset.univ.filter fun j => ¬ j ≤ i).card
          = (i.val + 1 + (Finset.univ.filter fun j => ¬ j ≤ i).card) - (i.val + 1) := by
              have h := Nat.add_sub_cancel_left
                (i.val + 1) (Finset.univ.filter fun j => ¬ j ≤ i).card
              exact h.symm
      _ = d - (i.val + 1) := by
        have h := congrArg (fun n => n - (i.val + 1)) hsum'
        -- h : (i.val + 1 + card_gt) - (i.val + 1) = d - (i.val + 1)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  have h_neg_eq_gt : (Finset.univ.filter fun j => ¬ j ≤ i) = Finset.univ.filter fun j => i < j := by
    ext j; simp [not_le]
  have h_subst : d - (i.val + 1) = d - 1 - i.val := by
    calc
      d - (i.val + 1) = d - (1 + i.val) := by ac_rfl
      _ = d - 1 - i.val := (Nat.sub_sub d 1 i.val).symm
  simpa [h_neg_eq_gt, h_subst] using h_gt_card_neg

/-- slabLen の積における左側（j < i）の部分は u^(i : ℕ) に等しい -/
lemma prod_slabLen_left (d _x u : ℕ) (i : Fin d) :
    (∏ j : Fin d with j < i, u) = u ^ (i : ℕ) := by
  classical
  conv_lhs => rw [Finset.prod_const]
  simp [card_filter_lt_fin (d := d) (i := i)]

/-- slabLen の積における右側（i < j）の部分は (x + u)^(d - 1 - (i : ℕ)) に等しい -/
lemma prod_slabLen_right (d x u : ℕ) (i : Fin d) :
    (∏ j : Fin d with i < j, (x + u)) = (x + u) ^ (d - 1 - (i : ℕ)) := by
  classical
  conv_lhs => rw [Finset.prod_const]
  rw [card_filter_gt_fin d i]

/-- Slab(i) の濃度の明示的な形 -/
theorem card_Slab_explicit (d x u : ℕ) (i : Fin d) :
    (Slab (d := d) x u i).card =
      x * u ^ (i : ℕ) * (x + u) ^ (d - 1 - (i : ℕ)) := by
  classical
  rw [card_Slab, card_Slab0]
  rw [prod_slabLen_split (d := d) x u i]
  rw [prod_slabLen_left (d := d) x u i, prod_slabLen_right (d := d) x u i]
  ring

-- 目標1: Slab は互いに交わらない（pairwise disjoint）
lemma Slab_pairwise_disjoint (d x u : ℕ) :
    ∀ i j : Fin d, i ≠ j → Disjoint (Slab (d := d) x u i) (Slab (d := d) x u j) := by
  classical
  intro i j hij
  -- 交わると仮定して矛盾を導く（軸 i と j の区間が食い違う）
  refine Finset.disjoint_left.mpr ?_
  intro p hp_i hp_j
  -- Slab(i) の membership を Slab0 の元 + shift に分解
  rcases Finset.mem_map.mp hp_i with ⟨qi, hqi, hpi⟩
  rcases Finset.mem_map.mp hp_j with ⟨qj, hqj, hpj⟩
  -- qi ∈ Slab0 i, qj ∈ Slab0 j
  -- 軸をケース分け：i < j か j < i
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- ケース i < j：軸 i で区間が食い違う
    -- qi の軸 i は [0,x) を u だけ平行移動 → [u,u+x)
    -- qj の軸 i は [0,u) のまま → 矛盾
    -- まず qi の軸 i の上界
    have hqi_axis : ∃ ri : ℕ, ri < x ∧ qi i = Int.ofNat ri := by
      -- Slab0 は Box の map なので、成分は 0..len-1 の Int.ofNat
      rcases Finset.mem_map.mp hqi with ⟨riFun, hri_mem, hqi_eq⟩
      rcases Finset.mem_pi.mp hri_mem i (Finset.mem_univ _) with hri_range
      have hlen : slabLen (d := d) x u i i = x := by simp [slabLen]
      rcases Finset.mem_range.mp hri_range with hri_lt_raw
      have hri_lt : riFun i (Finset.mem_univ _) < x := by simpa [hlen] using hri_lt_raw
      refine ⟨riFun i (Finset.mem_univ _), hri_lt, ?_⟩
      -- qi = ofNatCellEmb … riFun
      have := congrArg (fun f => f i) hqi_eq
      simpa [CellDim.ofNatCellEmb, Function.Embedding.trans, CellDim.piToFunEmb] using this.symm
    -- qj の軸 i の上界（i < j なので長さは u）
    have hqj_axis : ∃ rj : ℕ, rj < u ∧ qj i = Int.ofNat rj := by
      rcases Finset.mem_map.mp hqj with ⟨rjFun, hrj_mem, hqj_eq⟩
      rcases Finset.mem_pi.mp hrj_mem i (Finset.mem_univ _) with hrj_range
      have hlen : slabLen (d := d) x u j i = u := by
        simp [slabLen, hlt]
      have hrj_lt : rjFun i (Finset.mem_univ _) < u := by
        have := Finset.mem_range.mp hrj_range
        simpa [hlen] using this
      refine ⟨rjFun i (Finset.mem_univ _), hrj_lt, ?_⟩
      have := congrArg (fun f => f i) hqj_eq
      simpa [CellDim.ofNatCellEmb, Function.Embedding.trans, CellDim.piToFunEmb] using this.symm
    rcases hqi_axis with ⟨ri, hri_lt, hqi_eq⟩
    rcases hqj_axis with ⟨rj, hrj_lt, hqj_eq⟩
    -- p i を両方の表現から計算
    have hp_i_from_qi : p i = Int.ofNat ri + Int.ofNat u := by
      have h0 := congrArg (fun f => f i) hpi
      dsimp [CellDim.addEmb] at h0
      have h : qi i + slabShift (d := d) u i i = p i := by simpa using h0
      have h' : qi i + Int.ofNat u = p i := by simpa [slabShift] using h
      calc
        p i = qi i + Int.ofNat u := h'.symm
        _ = Int.ofNat ri + Int.ofNat u := by simp [hqi_eq]
    have hp_i_from_qj : p i = Int.ofNat rj := by
      have h0 := congrArg (fun f => f i) hpj
      dsimp [CellDim.addEmb] at h0
      have h : qj i + slabShift (d := d) u j i = p i := by simpa using h0
      have h' : qj i = p i := by
        have : slabShift (d := d) u j i = 0 := by simp [slabShift, hij]
        simpa [this] using h
      calc
        p i = qj i := h'.symm
        _ = Int.ofNat rj := by simp [hqj_eq]
    -- 片方は u 以上、もう片方は u 未満で矛盾
    have hge : (Int.ofNat u : ℤ) ≤ p i := by
      have hp := hp_i_from_qi
      have hnonneg : (0 : ℤ) ≤ (Int.ofNat ri : ℤ) := by exact Int.natCast_nonneg ri
      have : (Int.ofNat u : ℤ) ≤ Int.ofNat ri + Int.ofNat u := by
        have := add_le_add_right hnonneg (Int.ofNat u)
        simp only [Int.ofNat_eq_natCast, le_add_iff_nonneg_left, Nat.cast_nonneg]
      simp only [Int.ofNat_eq_natCast, hp, le_add_iff_nonneg_left, Nat.cast_nonneg]
    have hltu : p i < Int.ofNat u := by
      have : Int.ofNat rj < Int.ofNat u := by exact Int.ofNat_lt.mpr hrj_lt
      simpa [hp_i_from_qj] using this
    exact (not_le_of_gt hltu) hge
  · -- ケース j < i：軸 j で同様に矛盾を作る（左右対称）
    have hqj_axis : ∃ rj : ℕ, rj < x ∧ qj j = Int.ofNat rj := by
      rcases Finset.mem_map.mp hqj with ⟨rjFun, hrj_mem, hqj_eq⟩
      rcases Finset.mem_pi.mp hrj_mem j (Finset.mem_univ _) with hrj_range
      have hlen : slabLen (d := d) x u j j = x := by simp [slabLen]
      have hrj_lt : rjFun j (Finset.mem_univ _) < x := by
        have := Finset.mem_range.mp hrj_range
        simpa [hlen] using this
      refine ⟨rjFun j (Finset.mem_univ _), hrj_lt, ?_⟩
      have := congrArg (fun f => f j) hqj_eq
      simpa [CellDim.ofNatCellEmb, Function.Embedding.trans, CellDim.piToFunEmb] using this.symm
    have hqi_axis : ∃ ri : ℕ, ri < u ∧ qi j = Int.ofNat ri := by
      rcases Finset.mem_map.mp hqi with ⟨riFun, hri_mem, hqi_eq⟩
      rcases Finset.mem_pi.mp hri_mem j (Finset.mem_univ _) with hri_range
      have hri_lt : riFun j (Finset.mem_univ _) < u := by
        have := Finset.mem_range.mp hri_range
        -- slabLen (index i) at axis j は u（j < i）
        have hcase : slabLen (d := d) x u i j = u := by
          have hjlt : j < i := hgt
          have hjne : j ≠ i := Fin.ne_of_lt hgt
          simp [slabLen, hjlt]
        simpa [hcase] using this
      refine ⟨riFun j (Finset.mem_univ _), hri_lt, ?_⟩
      have := congrArg (fun f => f j) hqi_eq
      simpa [CellDim.ofNatCellEmb, Function.Embedding.trans, CellDim.piToFunEmb] using this.symm
    rcases hqj_axis with ⟨rj, hrj_lt, hqj_eq⟩
    rcases hqi_axis with ⟨ri, hri_lt, hqi_eq⟩
    have hp_j_from_qj : p j = Int.ofNat rj + Int.ofNat u := by
      have h0 := congrArg (fun f => f j) hpj
      dsimp [CellDim.addEmb] at h0
      have h : qj j + slabShift (d := d) u j j = p j := by simpa using h0
      have h' : qj j + Int.ofNat u = p j := by simpa [slabShift] using h
      calc
        p j = qj j + Int.ofNat u := h'.symm
        _ = Int.ofNat rj + Int.ofNat u := by simp [hqj_eq]
    have hp_j_from_qi : p j = Int.ofNat ri := by
      have h0 := congrArg (fun f => f j) hpi
      dsimp [CellDim.addEmb] at h0
      have h : qi j + slabShift (d := d) u i j = p j := by simpa using h0
      have h' : qi j = p j := by
        have hjne : j ≠ i := Fin.ne_of_lt hgt
        have : slabShift (d := d) u i j = 0 := by simp [slabShift, hjne]
        simpa [this] using h
      calc
        p j = qi j := h'.symm
        _ = Int.ofNat ri := by simp [hqi_eq]
    have hge : (Int.ofNat u : ℤ) ≤ p j := by
      have hp := hp_j_from_qj
      have hnonneg : (0 : ℤ) ≤ (Int.ofNat rj : ℤ) := by exact Int.natCast_nonneg rj
      have : (Int.ofNat u : ℤ) ≤ Int.ofNat rj + Int.ofNat u := by
        have := add_le_add_right hnonneg (Int.ofNat u)
        simp
      simp [hp]
    have hltu : p j < Int.ofNat u := by
      have : Int.ofNat ri < Int.ofNat u := by exact Int.ofNat_lt.mpr hri_lt
      simpa [hp_j_from_qi] using this
    exact (not_le_of_gt hltu) hge

-- 目標2: Body の card は Slab の card の和
theorem card_Body_eq_sum_card_Slab (d x u : ℕ) :
    (Body (d := d) x u).card =
      ∑ i : Fin d, (Slab (d := d) x u i).card := by
  classical
  -- まず、Slab の union が Body になることを示す
  -- その後、pairwise disjoint から和の公式を得る
  sorry

-- 目標3: その和が x * G d x u（さらに choose 版）に一致
theorem card_Body_eq_mul_G_constructive (d x u : ℕ) :
    (∑ i : Fin d, (Slab (d := d) x u i).card) = x * G d x u := by
  classical
  -- Slab の濃度の明示形を使って、和が G に一致することを示す
  -- 詳細な証明は後で実装
  sorry

end CosmicFormulaCellDim
end DkMath

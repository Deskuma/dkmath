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

end CosmicFormulaCellDim
end DkMath

/- 解説
よし、ぬしよ。ここまでで Lean 上に「無次元化された宇宙式（Cell/Finset 版）」が **“集合として”** も **“数式として”** も噛み合って閉じた。
つまり――“平面のトロミノ絵”から始まった話が、**任意次元 (d)** の抽象格子で **不変量の法則**として成立した、ということじゃ。

以下、ここでの到達点を一旦まとめるぞ。

---

## 1. 何を作ったか：無次元 Cell と translate の核

* 2次元 \((\mathbb{Z}\times\mathbb{Z})\) に縛られず、一般形として
  \[
  \mathrm{Cell}\ d := \mathrm{Fin}\ d \to \mathbb{Z}
  \]
  を採用した。
* 平行移動 `translate` を `Finset.map`（埋め込み）で実装し、**card が保存される**ことを証明した：
  \[
  \#(\mathrm{translate}\ v\ S)=\#S
  \]
  これは「座標原点や位置は本質ではない」という、無次元化の土台になっておる。

---

## 2. “箱” Box と “量＝card” の次元一般化

* 各軸で区間 ([0,a_i)) を取る直方体（箱）`Box` を Finset として定義した。
* その card を “軸ごとの積” に落とせる（仕上げた補題群で）：
  \[
  \#\mathrm{Box}(a)=\prod_{i\in \mathrm{Fin}\ d} a_i
  \]
  特に `constVec` で全軸同一長を与えると、
  \[
  \prod_{i\in\mathrm{Fin}\ d} n = n^d
  \]
  が確立し、箱の card が **べき**として畳めるようになった。

---

## 3. Big / Gap / Body の三分割を“集合”で作り、分解法則を得た

* 全体：
  \[
  \mathrm{Big}(d,x,u)=\mathrm{Box}(x+u)
  \]
* 余白：
  \[
  \mathrm{Gap}(d,u)=\mathrm{Box}(u)
  \]
* 実体：
  \[
  \mathrm{Body}=\mathrm{Big}\setminus \mathrm{Gap}
  \]
  そして、**集合として**
  \[
  \mathrm{Big}=\mathrm{Body}\cup \mathrm{Gap},\qquad
  \mathrm{Body}\cap\mathrm{Gap}=\varnothing
  \]
  が成り立つので、card による加法則：
  \[
  \#\mathrm{Big}=\#\mathrm{Body}+\#\mathrm{Gap}
  \]
  が出た。

これは「#Big = #Body + #Gap」という、あなたの言う **“Big/Body/Gap の構造”** を、完全に Lean の定理として固定した瞬間じゃ。

---

## 4. card を次元 (d) のべきへ畳み、Body を差で表した

あなたが仕上げた補題群で、
\[
\#\mathrm{Big}=(x+u)^d,\quad \#\mathrm{Gap}=u^d
\]
ゆえに
\[
\#\mathrm{Body}=(x+u)^d-u^d
\]
が確定した。

ここまででも「余白を引くと実体が出る」が、次元に依存せず成立する、と解ったわけじゃな。

---

## 5. 差のべき因数分解で “本体は必ず x 倍” が確定した

そして核心。あなたが通した：

\[
(x+u)^d-u^d = x\cdot G(d,x,u)
\]
（幾何和補題を用いた差のべき因数分解）

これと、上の \(\#\mathrm{Body}=(x+u)^d-u^d\) が繋がって、

\[
\boxed{\ \#\mathrm{Body} = x\cdot G(d,x,u)\ }
\]

が Lean 上で確定した。

### ここで解った“本質”

* Body は「Big から Gap を引いた残り」だが、その濃度は **常に x の倍数**になる。
* つまり、**余白 (u^d) を除いた実体は、必ず x 個ぶんの“層/束”に分解できる**。
* あなたの言葉で言えば
  **「#Body := xG_{d-1}(x,u) が、次元一般化の複雑さの受け皿」**
  が、単なる直観ではなく “定理” になった。

---

## 6. 何が嬉しいか：平面の絵から、次元不変の法則へ

この一連の成果は、単に \((x+u)^d-u^d\) を計算しただけではない。

* **集合（タイル）側**で Big/Body/Gap の分解が成り立ち、
* **数式側**で差のべきが (x) を因数にもつことが証明され、
* その二つが **card を介して完全に一致**した。

ゆえに、あなたの宇宙式は「図の比喩」ではなく、

> **“格子上の有限集合の不変量（card）として成立する、次元 (d) によらない保存則”**

として確立された、ということじゃ。

---

## 7. 次の展望（ここから先に何が乗るか）

ここまでで「無次元化の骨」が通ったので、次は二方向に伸ばせる：

1. **Body の“構成”を改善**
   いまは `sdiff`（差集合）で Body を定義している。
   これを、あなたの本命どおり「軸の最小位置で分類した disjoint union」として **明示構成**に置換すると、
   `x * G` が “数式” ではなく “タイルの実分解” として見えるようになる。

2. **二項係数版 (G_{d-1}) との同値**
   今の `G` は幾何和型。
   二項定理版の
   \[
   \sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}
   \]
   と同値を示すと、あなたの「情報増加＝係数構造」の物語が、そのまま Lean の定理カタログになる。

---

まとめると、こうじゃ：

**“Cell を d 次元へ無次元化しても、Big/Body/Gap の分解保存則は壊れない。
そして Body の濃度は必ず x 倍で、差のべき因数分解がその理由である。”**

これが今回の到達点じゃよ。
リンゴ酒でも開けたい気分じゃの🍎🍷
-/

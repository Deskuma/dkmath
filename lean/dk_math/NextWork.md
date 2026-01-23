# 次の作業メモ

## d次元の “層 (Slab)” を定義して、disjoint union で Body を作る

ある。しかも「美味しい次」じゃ🍎
いまお主がやった 2D 手本は、**一般次元の disjoint union 構成**へ行くための踏み台として完璧。

次の実装作業は、目的をはっきりさせるとこうじゃ：

> **`Body := Big \ Gap` をやめて、最初から “構成的に” Body を定義する**
> そして
> \[
> \mathrm{Body} = \bigsqcup (\text{Slab群})
> \quad\Rightarrow\quad
> \#\mathrm{Body} = x\cdot G(d,x,u)
> \]
> を “集合の分割” として証明する

二項係数同値まで通してあるから、最終的に choose 版とも繋がる。これが「係数＝分類数」が Lean で牙を剥く場面じゃ。

---

## 次のタスク（おすすめ順）

## A. d次元の “層 (Slab)” を定義して、disjoint union で Body を作る

### 1. 最小の定義案（軸を固定して切る）

各軸 (i) に対し「その軸が上側（(\ge u)）に入っている部分」を slab として取る：

* **縦スラブ**（軸 (i) に沿う）
  長さ (x) の方向と、残りの軸は (x+u) の方向

イメージは 2D の

* 左帯 \(u\times x\)
* 右帯 \(x\times(x+u)\)
  を “軸ごとに一本” 作る感じ。

ただしこのままだと **重なり（複数軸が上側）** が出て disjoint にならない。
そこで次へ。

### 2. disjoint にするための「最小軸」規則

**「最初に上側に入った軸」** で分類すると disjoint になる。

* `Slab (i : Fin d)` を

  * 軸 (i) は区間 \([u, u+x)\)（長さ (x)、オフセット (u)）
  * 軸 (j < i) は \([0,u)\)（下側に固定）
  * 軸 (j > i) は \([0, x+u)\)（自由）
    みたいに定義する（`Fin` の順序が必要）

すると

* どんな点も「最小の上側軸」が一意に決まり
* `Big \ Gap` の点は必ずどれかに入る
* 異なる i の slab は disjoint

これが “分類数＝係数” の正体に直結する。

---

## B. まずは「集合等式」ではなく「card 分解」だけを通す（安全策）

いきなり
\[
\mathrm{Body} = \bigcup_i \mathrm{Slab}\ i
\]
の `ext` で membership を詰めるのは手間なので、まずは

* `pairwise_disjoint` を示し
* `card` の加法で
  \[
  \#\mathrm{Body} = \sum_i \#\mathrm{Slab}\ i
  \]
* 右辺を計算して `x * G(d,x,u)` に一致

という順が最短じゃ。

---

## すぐ書ける「次の雛形」（d次元 Slab の骨）

お主が「まず動く骨が欲しい」タイプなので、コンパイルの通りやすさ重視で置く。

```lean
/-! ### 一般次元の Slab 分解（次の本命） -/

open scoped BigOperators
open DkMath.CellDim

namespace DkMath
namespace CosmicFormulaCellDim

variable {d : ℕ}

/-- Fin d 上の「下側長 u / 上側長 x / 全長 x+u」を軸ごとに組むヘルパ -/
def slabLen (x u : ℕ) (i : Fin d) (j : Fin d) : ℕ :=
  if j < i then u else if j = i then x else (x+u)

/-- Slab(i) の原点箱（あとで translate でオフセット u を載せる） -/
def Slab0 (d x u : ℕ) (i : Fin d) : Finset (Cell d) :=
  Box (d := d) (fun j => slabLen (d := d) x u i j)

/-- Slab(i) の平行移動：軸 i にだけ u を足す（区間 [u, u+x) を作る） -/
def slabShift (d u : ℕ) (i : Fin d) : Cell d :=
  fun j => if j = i then Int.ofNat u else 0

def Slab (d x u : ℕ) (i : Fin d) : Finset (Cell d) :=
  translate (d := d) (slabShift (d := d) u i) (Slab0 (d := d) x u i)

/-- 目標1: Slab は互いに交わらない（pairwise disjoint） -/
-- lemma Slab_pairwise_disjoint ...

/-- 目標2: Body の card は Slab の card の和 -/
-- theorem card_Body_eq_sum_card_Slab ...

/-- 目標3: その和が x * G d x u（さらに choose 版）に一致 -/
-- theorem card_Body_eq_mul_G_constructive ...

end CosmicFormulaCellDim
end DkMath
```

ここから先は「不等式（j < i）」を使うので、`Fin d` に `LT` を入れる部分や `simp` の補助補題が少し要る。が、既にお主は `fin_cases` と `simp` で勝てる筋肉が付いておるから、いける。

---

## 結論：次はある。しかも本命

* いまは **差集合で Body が“存在”**している状態。
* 次は **Slab 分解で Body を“構成”**する状態。
* そうすると choose 係数が「分類数」として現れ、あなたの物語が完全に一致する。

この次段へ進むと、宇宙式の “#Body の情報増大” が、数学的にも視覚的にも最も美しくなるぞ。

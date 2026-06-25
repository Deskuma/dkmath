# review

うむ、DKMK-015C は **きれいに成功** じゃ。
C でやったことは小さいが、意味は大きい。finite geometric-sum の **代数層** が、Lean 上で副条件なしに固定された。

## 1. 今回閉じたもの

追加された定理はこれじゃな。

```lean
theorem geomSum_range_mul_one_sub
    (ratio : ℝ) (K : ℕ) :
    (1 - ratio) *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
      =
    1 - ratio ^ (K + 1) := by
  exact mul_neg_geom_sum ratio (K + 1)
```

数学的には、

$$
(1-r)\sum_{k=0}^{K}r^k = 1-r^{K+1}
$$

じゃ。

これは DKMK-015B で決めた denominator-cleared shape そのもの。
`mul_neg_geom_sum ratio (K + 1)` による薄い wrapper で閉じたのも良い判断じゃ。自前 induction に入らず、mathlib の既存定理を DkMath 側の名前で再公開した形になっておる。

## 2. この C の価値

今回の価値は、 **副条件を一切混ぜなかった** ことじゃ。

ここではまだ、

```lean
ratio != 1
0 <= ratio
ratio < 1
0 <= base
```

のどれも入っていない。

これはとてもよい。
この定理はあくまで多項式恒等式であって、解析評価ではない。
したがって、この時点では division も order も持ち込まないのが正しい。

つまり DKMK-015 の層構造は今こうなった。

```text
DKMK-015B: theorem shape 決定
DKMK-015C: denominator-cleared identity 実装
DKMK-015D: 次に division form へ進むか upper-bound shape へ進むか判断
```

山道が乱れておらぬ。よいぞ。

## 3. Real 版 wrapper にした判断

`R = Real` 固定も、現段階では妥当じゃ。

理屈だけなら可換環や線形順序体へ一般化できるが、`SourceMassTruncation.lean` の周辺はすでに `ℝ` 評価、`ℚ` から `ℝ` への cast、`error : ℝ` などが絡む。
ここで generic theorem を作り始めると、証明の価値より型一般化の手間が勝ってしまう。

今は `SourceMassTruncation` の caller-facing theorem に供給するための補題なので、Real 版で十分じゃ。

必要になれば後から、

```lean
geomSum_range_mul_one_sub_real
```

と分けるか、generic 版を別ファイルへ昇格すればよい。

## 4. DKMK-015D はどちらへ進むべきか

次の分岐は、

1. division form を作る
2. upper-bound theorem の exact shape を決める

のどちらかじゃ。

わっちの推奨は、 **DKMK-015D は upper-bound theorem の exact shape review に進む** ことじゃ。

理由は、最終的に DKMK-014J が欲しいのは等式ではなく、

$$
base\cdot \sum_{k=0}^{K}ratio^k \le 1+error
$$

という不等式だからじゃ。

division form

$$
\sum_{k=0}^{K}r^k = \frac{1-r^{K+1}}{1-r}
$$

は美しいが、必須ではない。
実際、上界は C の定理から直接出せる。

$$
(1-r)\sum_{k=0}^{K}r^k = 1-r^{K+1}
$$

ここで (0\le r) なら (0\le r^{K+1})。
さらに (r<1) なら (0<1-r)。
したがって、

$$
1-r^{K+1}\le 1
$$

より、

$$
(1-r)\sum_{k=0}^{K}r^k\le 1
$$

となり、正の (1-r) で割って、

$$
\sum_{k=0}^{K}r^k \le \frac{1}{1-r}
$$

が得られる。

つまり division equality を theorem として経由せずとも、upper-bound は出る。

## 5. DKMK-015D の推奨 exact shape

次に固定すべき形はこれじゃ。

```lean
theorem geomSum_range_le_one_div_one_sub
    {ratio : ℝ} (K : ℕ)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1) :
    (Finset.sum (Finset.range (K + 1))
      (fun k : ℕ => ratio ^ k))
      ≤
    1 / (1 - ratio)
```

名前は既存方針に合わせるなら、こちらでもよい。

```lean
geomSum_range_le_inv_one_sub
```

ただ、Lean の式が `1 / (1 - ratio)` なら、名前も `one_div_one_sub` のほうが読みやすいかもしれぬ。

## 6. DKMK-015E 以降の流れ

その後は、base-scaled theorem へ進める。

```lean
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : ℝ} (K : ℕ)
    (hbase : 0 ≤ base)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) ≤ 1 + error) :
    base *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
      ≤
    1 + error
```

これは DKMK-014J の

```text
base * sum ratio^k <= 1 + error
```

にかなり近い。
ここまで行けば、caller 側は

$$
base\cdot \frac{1}{1-ratio}\le 1+error
$$

を示すだけで済む。

## 7. 注意点

一点だけ意識しておくとよい。

`geomSum_range_mul_one_sub` の range は `K + 1` なので、和は (k=0,\dots,K)。
右辺が (1-ratio^{K+1}) なのは正しい。

今後 `n` を range length として扱う補題と混ぜる場合、

```lean
Finset.range n
```

なら右辺は (1-ratio^n)。
`Finset.range (K + 1)` なら右辺は (1-ratio^{K+1})。

ここだけ off-by-one に気をつければよい。

## 8. 総括

DKMK-015C は、 **代数恒等式 layer の Lean 実装完了** と見てよい。

しかも、

* mathlib 既存 theorem を利用
* local wrapper として DkMath 側の名前を付与
* side condition なし
* division form なし
* order layer なし
* route theorem 変更なし

という切り方が、非常に堅い。

次はわっちなら、division form ではなく **upper-bound exact shape** へ進む。
このままなら DKMK-015 は、代数から解析上界へ、かなり滑らかに橋が架かるぞい。

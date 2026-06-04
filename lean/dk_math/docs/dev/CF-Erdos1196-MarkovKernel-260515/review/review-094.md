# review

うむ、DKMK-015E は **実装フェーズとして明確に一段進んだ** じゃ。
DKMK-015D で固定した upper-bound theorem が、Lean 上で実際に閉じた。これは docs-only 設計から、使える補題層へ移ったという意味で大きい。

## 1. 何が閉じたのか

今回追加された中核はこれじゃ。

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

つまり有限等比和について、

$$
0\le ratio,\quad ratio<1
$$

から

$$
\sum_{k=0}^{K} ratio^k \le \frac{1}{1-ratio}
$$

を Lean で得られるようになった。`SourceMassTruncation.lean` にこの定理を追加し、division-form equality や explicit `ratio != 1` は導入していない、という報告になっておる。

## 2. 証明経路の評価

証明経路はかなりよい。

まず DKMK-015C の denominator-cleared identity

$$
(1-ratio)\sum_{k=0}^{K}ratio^k = 1-ratio^{K+1}
$$

を使う。

次に `0 ≤ ratio` から

$$
0\le ratio^{K+1}
$$

を出し、

$$
1-ratio^{K+1}\le 1
$$

を得る。

したがって、

$$
(1-ratio)\sum_{k=0}^{K}ratio^k \le 1
$$

となる。

最後に `ratio < 1` から

$$
0<1-ratio
$$

を得て、`le_div_iff₀` で

$$
\sum_{k=0}^{K}ratio^k \le \frac{1}{1-ratio}
$$

へ落とす。報告にも、`geomSum_range_mul_one_sub` から積の上界を作り、`sub_pos.mpr hr1` と `le_div_iff₀` で upper-bound へ変形したとある。

これは、division equality を経由しない設計として正しい。
「閉形式を得るための定理」ではなく、「下流が必要とする上界の定理」へ直行しておる。

## 3. 副条件の管理が綺麗

今回の定理が消費する仮定は、

```lean
0 ≤ ratio
ratio < 1
```

だけじゃ。

ここで `ratio != 1` を明示しない判断は正しい。
なぜなら、この定理で実際に必要なのは (1-ratio) の正値性であり、それは `ratio < 1` から直接出るからじゃ。

つまり DKMK-015 の設計原則、

```text
side conditions appear only in the theorem that consumes them
```

が維持されておる。

## 4. DKMK-015 の現在地

ここまでで、DKMK-015 の主要な階段はこうなった。

```text
DKMK-015B:
  denominator-cleared identity の exact shape を固定

DKMK-015C:
  geomSum_range_mul_one_sub を Lean 実装

DKMK-015D:
  upper-bound theorem の exact shape を固定

DKMK-015E:
  geomSum_range_le_one_div_one_sub を Lean 実装
```

ここで重要なのは、 **division-form theorem がなくても進んでいる** ことじゃ。

普通なら

$$
\sum_{k=0}^{K}r^k = \frac{1-r^{K+1}}{1-r}
$$

を作りたくなる。
だが、この route では最終的に欲しいのが

$$
base\cdot \sum_{k=0}^{K}ratio^k \le 1+error
$$

なので、上界だけを先に固めるほうが Lean 的に軽い。

## 5. 検証面

報告では、

```text
lake build DkMath.NumberTheory.PrimitiveSet.SourceMassTruncation
lake build DkMath.NumberTheory.PrimitiveSet
git diff --check
long-line check on changed docs
```

が通っておる。加えて、最初に repository top で `lake build` して lakefile が見つからず、`lean/dk_math` に移動して再実行し成功した、という失敗事例も記録されている。

これは良い記録じゃ。
後から同じ作業をする時に、作業ディレクトリの前提を忘れずに済む。

## 6. 次の DKMK-015F

次は予定通り、base-scaled layer じゃな。

候補はこれでよい。

```lean
theorem base_mul_geomSum_range_le_of_base_mul_one_div_le
    {base ratio error : ℝ} (K : ℕ)
    (hbase : 0 ≤ base)
    (hr0 : 0 ≤ ratio)
    (hr1 : ratio < 1)
    (hbudget : base * (1 / (1 - ratio)) ≤ 1 + error) :
    base *
      Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k)
      ≤
    1 + error
```

証明は、おそらく短い。

```lean
have hsum :
    (Finset.sum (Finset.range (K + 1))
      (fun k : ℕ => ratio ^ k))
      ≤
    1 / (1 - ratio) :=
  geomSum_range_le_one_div_one_sub K hr0 hr1

have hscaled :
    base *
      (Finset.sum (Finset.range (K + 1))
        (fun k : ℕ => ratio ^ k))
      ≤
    base * (1 / (1 - ratio)) :=
  mul_le_mul_of_nonneg_left hsum hbase

exact le_trans hscaled hbudget
```

これが閉じれば、DKMK-014J が要求する

$$
base\cdot \sum ratio^k \le 1+error
$$

へかなり直接つながる。

## 7. 総括

DKMK-015E は、 **finite geometric-sum の order upper-bound layer 完了** と見てよい。

ここまでで、

$$
(1-r)\sum r^k = 1-r^{K+1}
$$

から

$$
\sum r^k \le \frac{1}{1-r}
$$

までが Lean 上で接続された。

次の F で base を掛ける補題が入れば、DKMK-015 は DKMK-014J への実用的な供給路をほぼ獲得する。
よいぞ、D.。ここは派手な頂上ではないが、荷車の車輪がようやく滑らかに回り始めた場所じゃ。

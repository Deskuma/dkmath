# Next tasks

*TODO* 2026/07/04 17:36

## のこる２つの山

うむ、残る２山は **思ったほど重くない** 。
ただし、重さの種類が違う。

## 1. `HasProd` / 無限積 API の山

これは **中くらい** じゃ。

すでに部分積列としては

$$
\lim_{m\to\infty} C_m=\frac{\pi}{2}
$$

まで閉じておる。今回の差分でも、`centralRatioQ * mirror`、`wallisPartialQ`、`cosmicPartialQ` の 3 列が実数上で pointwise equal になり、`Real.pi / 2` へ収束することが実装済みじゃ。

つまり `HasProd` 山は、新しい数学ではなく、

```text
部分積列の Tendsto
  ↓
Mathlib の infinite product API 形式
```

へ **表記を持ち替える山** じゃ。

重い可能性があるのは、Mathlib の `HasProd` 定義が要求する部分積の形と、こちらの `Finset.range m` の indexing がぴったり合うかどうか。
ここで少し Lean との格闘はあり得る。

体感では、

```text
数学難度: 低い
Lean 難度: 中
```

じゃな。

## 2. 「宇宙式 Gap 無限積そのもの」定理の山

これは **中〜やや重い** 。

目標はたぶんこういう形じゃ。

$$
\prod_{k=0}^{\infty}\left(1+\frac{1}{(2k+1)(2k+3)}\right)=\frac{\pi}{2}
$$

DkMath 名で言えば、

```lean
HasProd
  (fun k : ℕ => (((cosmicFactorQ k : ℚ) : ℝ)))
  (Real.pi / 2)
```

のような形。

これは 1 の `HasProd` 山とほぼ同じに見えるが、DkMath 的にはもう一段意味づけがある。

```text
cosmicFactorQ k
  = 1 + 1 / cosmicBodyQ k
```

を使って、

```text
宇宙式 Gap 比率の無限積
  = π / 2
```

として公開するところまで整える必要がある。

つまり、証明自体は軽めでも、 **API と命名と docstring の設計** が少し重い。

## 重さの結論

わっちの見立てはこうじゃ。

```text
HasProd 形式化:
  1〜2差分で閉じる可能性あり。
  Mathlib API 探索が主な作業。

宇宙式 Gap 無限積 theorem:
  HasProd が閉じればすぐ近い。
  ただし定理名・公開 API・説明をきれいにする分だけ重い。
```

なので、恐れる山ではない。
**Wallis 極限定理そのものを自前で証明する山ではない** からの。そこは Mathlib が既に背負ってくれておる。

今回の本丸はすでに閉じた。残る２山は、どちらかと言えば **山頂の標識を立てる作業** じゃ。
ただし Lean の無限積 API は足場が滑るので、油断すると転ぶ。りんごを片手に、慎重に登ればよいぞい。

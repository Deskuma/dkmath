# review

うむ、DKMK-017J は **かなり良い節目** じゃ。
DKMK-017I で残っていた first-band budget、

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

を、今回は canonical choice

```text
base = 1 - ratio
```

で内部的に閉じ、`TruncationEnvelopeEstimate` まで通しておる。これは **route-validation source として一段完成** したと言ってよい。

## 1. 何が閉じたのか

追加された中心補題はこれじゃな。

```lean
geometricIncrement_baseEqOneSub_budget
```

これは、

```text
base = 1 - ratio
(ratio : Real) < 1
0 <= error
```

から、

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

を出す補題じゃ。

数学的には単純で、

$$
base=1-ratio
$$

かつ

$$
1\le 1+error
$$

なので、

$$
1-ratio\le (1+error)(1-ratio)
$$

となる。さらに (ratio<1) から (0\le 1-ratio) が出るので、右から掛ける不等式が正しく使える。Lean でもその形で閉じておる。

## 2. route がかなり短くなった

DKMK-017I では、`geometricIncrement` から envelope までは通ったが、caller はまだ

```text
(base : Real) <= (1 + error) * (1 - (ratio : Real))
```

を渡す必要があった。

今回 J では、caller surface がこうなった。

```text
base = 1 - ratio
0 <= ratio
(ratio : Real) < 1
0 <= error
```

これだけで、

```text
TruncationEnvelopeEstimate
  (Finset.range (K + 1))
  (fun k : Nat => x * 2^k)
  (geometricIncrement base ratio)
  error
```

まで到達する。

つまり、`hbaseBudget` が caller-side obligation から外れた。これは大きい。

## 3. `base` の非負性も内部で閉じた

`FirstBandDecayBudgetSource.ofGeometricIncrementBaseEqOneSub` では、`base` の非負性も内部で処理しておる。

`base = 1 - ratio` と `(ratio : Real) < 1` から、

$$
0<1-ratio
$$

が出る。よって、

$$
0\le base
$$

が得られる。

この処理により、caller は `0 <= base` を別途渡さずに済む。
これも良い整理じゃ。

## 4. これは本命解析ではなく route-validation source

ここは大事じゃ。

今回の `base = 1 - ratio` はとても綺麗だが、これはまだ最終的な analytic/logarithmic source ではない。
roadmap でも、この specialization は route-validation source であり、最終的な解析・対数由来 source ではないと整理されている。

つまり、今回閉じたのは、

```text
幾何増分 source が標準 route で envelope まで到達できる
```

という事実じゃ。

Erdős #1196 の本丸へ向かうには、次にこの `ratio` や `base` を実際の数論・解析構造からどう得るかが問題になる。

## 5. 次の分岐

次は報告にもある通り、三択じゃな。

```text
1. explicit base を持たない base := 1 - ratio 型 theorem を足す
2. finite-step mass theorem へ接続する
3. logarithmic / capacity-derived source へ進む
```

わっちの推奨は、 **1 は薄いので急がず、2 を確認し、その後 3 へ進む** じゃ。

理由は、`base := 1 - ratio` の theorem は ergonomics として便利だが、また wrapper 追加になりがち。
一方、finite-step mass route への接続を確認すれば、今回の envelope が既存 route で本当にどこまで使えるか見える。

## 6. 現在の到達点

ここまでで DKMK-017 は、かなり明確な段階に入った。

```text
geometricIncrement base ratio
  -> nonnegativity
  -> exact decay
  -> base = 1 - ratio budget
  -> FirstBandDecayBudgetSource
  -> TruncationEnvelopeEstimate
```

つまり、抽象 source surface の検証はほぼ成功しておる。

残るのは、

```text
この geometric source を有限ステップ route へ流す
または
より本命の logarithmic / capacity source に置き換える
```

のどちらかじゃ。

## 7. 総括

DKMK-017J は、 **canonical first-band budget を内部化し、geometric increment の envelope route を完成形に近づけた回** じゃ。

採用でよい。

今回の成果は、

```text
base = 1 - ratio
```

という自然な幾何選択により、DKMK-017I で残っていた first-band budget を caller から消したこと。

これで `geometricIncrement` は、単なる試験用 increment から、 **標準 route の正常動作を示す canonical source** へ昇格したと言える。

よいぞ、D.。
これで幾何級数の荷車は、`base = 1 - ratio` という釣り合い荷重で、truncation envelope まで綺麗に走った。次はこの荷車を finite-step route へ乗せるか、より深い logarithmic/capacity の鉱脈へ向かうか、その分岐じゃな。

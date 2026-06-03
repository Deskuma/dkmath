# review

## 1. 状況総括

うむ、これは **DKMK-014G 完了** と見てよい。

今回の差分で `SourceMassTruncation.lean` に

```lean
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

が追加された。これは DKMK-014F で固定した設計通り、具体的な majorant

```lean
fun k : ℕ => base * ratio ^ k
```

を明示しつつ、有限幾何級数の評価そのものは外部入力 `hgeom_bound` に残す薄い provider じゃ。History でも、`ofMajorant` を `majorant := fun k : ℕ => base * ratio ^ k` で呼ぶ実装にした、と記録されておる。

つまり DKMK-014 の majorant route は、

```text
general majorant
  -> pointwise geometric majorant
```

へ一段具体化された。

## 2. 何が閉じたのか

DKMK-014C では、一般形として

```lean
DyadicBandAnalyticEstimate.ofMajorant
```

が入った。

これは、

```text
increment k <= majorant k
sum majorant <= 1 + error
```

から `DyadicBandAnalyticEstimate` を作る provider じゃった。

今回の DKMK-014G では、その `majorant` を幾何型に固定した。

```text
majorant k = base * ratio ^ k
```

したがって、流れはこうなる。

```text
increment nonnegativity
  -> hinc_nonneg

pointwise geometric bound
  -> hgeom : increment k <= base * ratio ^ k

external finite geometric-sum bound
  -> hgeom_bound :
       sum (base * ratio ^ k) <= 1 + error

therefore:
  DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

これで、`increment` が (k)-依存していても、幾何型の上界に乗れば DKMK route へ渡せるようになった。

## 3. 実装評価

実装は非常に良い。
中身は本当に薄く、

```lean
exact
  ofMajorant x K increment
    (fun k : ℕ => base * ratio ^ k)
    hinc_nonneg hgeom hgeom_bound
```

という形じゃ。

これは正しい。
今回の theorem は幾何級数を証明する theorem ではない。`ofMajorant` に渡す majorant を「幾何型」として明示する provider じゃ。

そして今回も、次を入れていない。

```text
geometric-series lemma
0 <= ratio
ratio < 1
route theorem
Mertens / big-O
logarithmic threshold
real-to-Nat rounding
```

この抑制がよい。`ratio < 1` は幾何級数評価を証明するときの条件であって、今回の provider 自体はそれを消費しない。消費しない field を入れない判断が一貫しておる。

## 4. 数学的な意味

数学的には、今回の theorem は次の形じゃ。

$$
increment(k) \le base \cdot ratio^k
$$

かつ

$$
\sum_{k=0}^{K} base \cdot ratio^k \le 1 + error
$$

ならば、

$$
\sum_{k=0}^{K} increment(k) \le 1 + error
$$

が従う。

つまり `increment` の詳細を知らなくても、幾何型 majorant に包めば finite total estimate が得られる。
これは dyadic tail upper envelope に向かう自然な橋じゃな。

特に今後、

```text
increment k が dyadic band の tail contribution を表す
```

となったとき、直接 `sum increment` を扱うより、

```text
increment k <= base * ratio ^ k
```

で押さえて `ofPointwiseGeometricMajorant` に流す方が見通しがよい。

## 5. whitespace linter の失敗事例

今回の失敗事例として、

```text
ratio^k
```

の whitespace linter warning が出て、

```text
ratio ^ k
```

へ修正した、と記録されている。

これは小さいが、Lean 文書・コード整備として良い記録じゃ。
DkMath は theorem の積み上げだけでなく、後から読む人間と Codex が迷わぬようにするのが大事じゃからの。

## 6. DKMK-014 の現在地

ここまでの DKMK-014 は、かなり明確に進んでおる。

```text
DKMK-014A:
  k-dependent provider roadmap 完了

DKMK-014B:
  majorant provider exact shape docs 完了

DKMK-014C:
  DyadicBandAnalyticEstimate.ofMajorant 実装完了

DKMK-014D:
  majorant provider usage summary 完了

DKMK-014E:
  decreasing / decay to majorant design 完了

DKMK-014F:
  ofPointwiseGeometricMajorant shape docs 完了

DKMK-014G:
  ofPointwiseGeometricMajorant Lean provider 完了
```

これで、DKMK-014 は **general majorant provider** と **geometric majorant provider** の両方を持った。

## 7. 次の一手

History では、次の課題として

```text
DKMK-014H:
  geometric finite-sum bound を外部入力のまま使う usage summary
  または caller-facing finite-sum theorem の設計
```

とされておる。

わっちのおすすめは、まず **usage summary** じゃ。

理由は、今回追加した theorem は「幾何級数評価を外部入力に残す」という境界が肝だからじゃ。ここを docs で固定してから、caller-facing finite-sum theorem へ進む方がよい。

次の DKMK-014H では、こういう流れを書くとよい。

```text
increment
  -> hinc_nonneg
  -> hgeom : increment k <= base * ratio ^ k
  -> hgeom_bound : sum (base * ratio ^ k) <= 1 + error
  -> ofPointwiseGeometricMajorant
  -> DyadicBandAnalyticEstimate
  -> toTruncationEnvelopeEstimate
  -> existing route theorem
  -> weightedHitMass <= 1 + error
```

そして、その後で DKMK-014I として、

```text
geometric finite-sum theorem shape
```

を設計するのが美しい。

## 8. 賢狼の判定

わっちの判定はこうじゃ。

```text
DKMK-014G: 完了
成果:
  幾何型 majorant provider が Lean 上で利用可能になった

次:
  DKMK-014H usage summary 推奨

方針:
  幾何級数評価はまだ外部入力に残す
  ratio 条件や geometric-series lemma は後段で扱う
```

よいぞ、ぬしよ。
ここで `base * ratio ^ k` という形が Lean surface に出たのは大きい。定数 band から始まった山道が、いよいよ減衰する band の稜線へ入った。次はその使い方を固め、それから有限幾何級数の小山へ登るのがよいじゃろう。

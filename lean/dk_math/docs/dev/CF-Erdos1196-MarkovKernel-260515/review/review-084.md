# review

## 1. 状況総括

うむ、これは **DKMK-014F 完了** と見てよい。

今回の更新で、`roadmap-DKMK-014.md` に **Explicit Majorant Construction Exact Shape** が追加され、次の Lean-facing provider として

```lean id="w2ig4q"
DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
```

を採用する方針が固定された。History でも、単なる `ofMajorant` の別名 theorem は避け、`majorant k = base * ratio^k` という concrete な majorant family を露出しつつ、有限幾何級数評価は外部入力に残す、と整理されておる。

つまり DKMK-014F は、`ofMajorant` の次段として **幾何型 majorant provider の exact shape を docs 上で固定した phase** じゃ。

## 2. 何が決まったのか

固定された形はこれじゃ。

```lean id="y3a913"
theorem DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
    (x K : Nat)
    (increment : Nat -> Q)
    (base ratio : Q)
    (hinc_nonneg :
      forall k in Finset.range (K + 1), 0 <= increment k)
    (hgeom :
      forall k in Finset.range (K + 1),
        increment k <= base * ratio^k)
    {error : R}
    (hgeom_bound :
      ((Finset.sum (Finset.range (K + 1))
          (fun k : Nat => base * ratio^k) : Q) : R) <=
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error
```

Lean では `Nat`, `Q`, `R` はそれぞれ `ℕ`, `ℚ`, `ℝ` になる。

これにより、`increment` を直接合計するのではなく、

```text id="g7plvf"
majorant k = base * ratio^k
```

で上から包み、その majorant の有限和 bound を外部から渡す形になる。

## 3. 設計判断の良い点

一番よいのは、`ofMajorant` の単なる別名を作らなかったことじゃ。

たとえば、

```lean id="fjf5hd"
DyadicBandAnalyticEstimate.ofMajorantBoundedBy
```

のような theorem を、`ofMajorant` とほぼ同じ仮定で追加しても、API は増えるが意味は増えぬ。

今回の `ofPointwiseGeometricMajorant` は違う。
`majorant` の形を

```text id="i8p2oc"
base * ratio^k
```

に固定することで、後続の geometric-sum theorem や dyadic tail estimate へ接続できる形になっている。

つまり、これは単なる convenience wrapper ではなく、 **次の解析 majorant 形への入口** じゃ。

## 4. なぜ有限和 bound を外部に残すのがよいか

ここも良い判断じゃ。

今回の theorem は、幾何級数の有限和

```text id="ea9b6s"
Finset.sum (Finset.range (K + 1))
  (fun k : Nat => base * ratio^k)
```

を簡約しない。

これは DKMK-013 の `constantBand` と同じ登り方じゃな。

まずは、

```text id="jk79k0"
pointwise geometric majorization
external geometric-sum bound
  -> DyadicBandAnalyticEstimate
```

を通す。

その後で必要なら、

```text id="ltu2yg"
geometric finite-sum assumptions
  -> sum (base * ratio^k) <= 1 + error
  -> ofPointwiseGeometricMajorant
```

を別 theorem として追加する。

この二段構えなら、provider の骨格と幾何級数 infrastructure が混ざらない。
Lean ではこの分離が非常に効く。わっちはこの慎重さを好むぞい。

## 5. `ratio` 条件をまだ入れない判断

今回、`0 <= ratio` や `ratio < 1` を入れていないのも正しい。

理由は、`ofPointwiseGeometricMajorant` 自体は、幾何級数評価を証明しないからじゃ。
必要なのは、

```text id="a1l8c3"
increment k <= base * ratio^k
```

と

```text id="se9xbb"
sum (base * ratio^k) <= 1 + error
```

だけ。

`ratio < 1` は、後で有限幾何級数や tail bound を証明する theorem が消費する条件じゃ。
今回の provider が消費しない条件を field に入れない。これは DKMK-014A-E で守ってきた設計原則と一貫しておる。

## 6. DKMK-014G の Lean 実装予想

次の Lean 実装はかなり薄くなるはずじゃ。

```lean id="svo7ly"
namespace DyadicBandAnalyticEstimate

theorem ofPointwiseGeometricMajorant
    (x K : ℕ)
    (increment : ℕ → ℚ)
    (base ratio : ℚ)
    (hinc_nonneg :
      ∀ k ∈ Finset.range (K + 1), 0 ≤ increment k)
    (hgeom :
      ∀ k ∈ Finset.range (K + 1),
        increment k ≤ base * ratio^k)
    {error : ℝ}
    (hgeom_bound :
      ((Finset.sum (Finset.range (K + 1))
          (fun k : ℕ => base * ratio^k) : ℚ) : ℝ) ≤
        1 + error) :
    DyadicBandAnalyticEstimate x K increment error := by
  exact
    DyadicBandAnalyticEstimate.ofMajorant
      x K increment
      (fun k : ℕ => base * ratio^k)
      hinc_nonneg hgeom hgeom_bound

end DyadicBandAnalyticEstimate
```

たぶんこれでほぼ通る。
もし型推論が渋るなら、`majorant := fun k : ℕ => base * ratio ^ k` を明示する形にすればよい。

## 7. 数学的な意味

数学的には、今回固定した provider はこう読める。

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

したがって、

$$
DyadicBandAnalyticEstimate(x,K,increment,error)
$$

が得られる。

つまり、`increment` の実体が複雑でも、幾何型 majorant に乗れば DKMK route へ渡せる。
これは dyadic tail upper envelope へ向かう自然な足場じゃ。

## 8. DKMK-014 の現在地

ここまでの DKMK-014 はこうじゃ。

```text id="sy8akk"
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
  ofPointwiseGeometricMajorant exact shape docs 完了

DKMK-014G:
  次、ofPointwiseGeometricMajorant Lean provider 実装
```

DKMK-014F によって、majorant provider から geometric majorant provider への自然な次段が決まった。

## 9. 賢狼の判定

わっちの判定はこうじゃ。

```text id="kkqrxk"
DKMK-014F: 完了
次: DKMK-014G
実装対象:
  DyadicBandAnalyticEstimate.ofPointwiseGeometricMajorant
方針:
  ofMajorant を薄く呼ぶ
  幾何級数評価はまだ外部入力
  ratio 条件や geometric-series lemma は後段へ分離
```

よいぞ、ぬしよ。
これで (k)-dependent band の手すりが、単なる majorant から幾何型 majorant へ一段具体化された。次は薄く Lean に通すだけでよい。幾何級数の本丸は、焦らず次の小山に分ければよいのじゃ。

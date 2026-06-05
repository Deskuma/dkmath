# review

## 考察：次の作業

- R 可除性定理の整備が先か、現行維持か

> 実数体 R でも、差分、構造差、残差を、構造維持条件の下で等分割の可否を問う。
> 差分商の存在有無の定理。これにより、何でも割れるから→構造解析的に割れない。が言える。
> 素数が何故、割れないのかを構造的に多角的、フラクタル解析する理論、定理群。\(p=\sqrt[n]{p}^n\)

### 結論：現行維持で進める

うむ。ここで GN 可除性 / (\N\to \R) 構造可除性を入れると、たしかに **組み直し** になる。
なので今は置いておく判断でよい。あれは強いが、今の DKMK-017 本線とは章の深さが違う。

## 1. 今の本線

現状の DKMK-017 本線は、まだこちらじゃ。

```text id="mxjjv7"
concrete increment : Nat -> Rat
  -> hinc_nonneg
  -> hbaseBudget
  -> hdecay
  -> TruncationEnvelopeEstimate
```

直近の探索では、既存 PrimitiveSet / SourceMassTruncation 周辺に、そのまま使える concrete dyadic-band `increment : Nat -> Rat` は見つかっていない。既存の concrete candidate は `Bool -> Rat` や arbitrary index 型寄りで、DKMK-017 標準 route の `Nat -> Rat` には直接合わない、という結論だった。

したがって次の自然な一手は、予定通り

```lean
geometricIncrement base ratio : Nat -> Rat
```

を導入して、まず標準 route が本当に動くか試すことじゃ。

## 2. GN / N→R を今入れない理由

GN 可除性は、おそらく将来かなり重要になる。

だが、それを今入れると、

```text id="g427hg"
Rat increment route
```

から、

```text id="h2t1dv"
Real geometric divisibility / structural divisibility route
```

へ章が変わる。

つまり、今の `increment : Nat -> Rat` の地ならしを飛び越えて、`Real` 上の構造的可除性 predicate や rational envelope の話へ進んでしまう。これは DKMK-017 の current route から見ると横道が深すぎる。

だから今は、

```text id="dcmv6f"
GN / N→R 構造可除性:
  後続 branch 候補として保留

DKMK-017:
  Nat -> Rat increment route を先に通す
```

でよい。

## 3. 次の DKMK-017I の具体像

次はこれでよいと思う。

```lean
def geometricIncrement (base ratio : ℚ) (k : ℕ) : ℚ :=
  base * ratio ^ k
```

そして狙う lemma は、まずこのあたり。

```lean
theorem geometricIncrement_nonneg
    {base ratio : ℚ}
    (hbase : 0 ≤ base)
    (hr0 : 0 ≤ ratio) :
    ∀ k, 0 ≤ geometricIncrement base ratio k
```

次に、

```lean
theorem geometricIncrement_zero
    (base ratio : ℚ) :
    geometricIncrement base ratio 0 = base
```

そして余裕があれば、

```lean
theorem geometricIncrement_decay
    (base ratio : ℚ) :
    geometricIncrement base ratio (k + 1)
      =
    ratio * geometricIncrement base ratio k
```

または provider が欲しい形に合わせて、

```lean
geometricIncrement base ratio (k + 1)
  ≤ ratio * geometricIncrement base ratio k
```

を equality から `le_of_eq` で出す。

この `geometricIncrement` は解析的に深い increment ではない。
だが、DKMK-017 の標準搬送路を concrete `Nat -> Rat` で試すには最適じゃ。

## 4. これで何が確認できるか

`geometricIncrement` を使うと、標準 route の仮定がかなり自然に閉じる。

```text id="u0u7qg"
hinc_nonneg:
  base >= 0, ratio >= 0 から出る

hdecay:
  定義展開で equality

hbaseBudget:
  increment 0 = base なので、
  base <= (1 + error) * (1 - ratio)
```

つまり、DKMK-017C-E で整えた helper が本当に実用になるかを、最小 concrete candidate で検査できる。

## 5. 今の判断

わっちの判断はこうじゃ。

```text id="k0pkxw"
GN / N→R:
  保留。別 branch として後で扱う。

DKMK-017I:
  geometricIncrement を導入。
  hinc_nonneg と decay をまず閉じる。

その後:
  self-base route で TruncationEnvelopeEstimate まで通す。
```

これなら、組み直しではなく、現在の搬送路の検証として前へ進める。

## 6. 総括

今は GN の大狼を放つ時ではない。
まずは小さな猟犬として `geometricIncrement` を走らせる。

これで DKMK-017 の抽象 route が concrete `Nat -> Rat` 上で動くか見える。
その後、Real/log/幾何構造を持ち込む必要がはっきりしてから、GN 可除性や (N\to R) 構造可除性を別章で立てればよい。

つまり次は、 **組み直しではなく、現行 route の試走** じゃな。

---

## 考察メモ

### GN 型 R 可除性定理の整備の優先度の検討

うむ。結論から言うと、 **今すぐ GN 可除性原理を DKMK-017 に本格投入するのは早い** と思う。
ただし、 **N→R / R→Rat の橋が未実装で、いずれ必要になる** という感覚は正しい。

今回の DKMK-017H では、既存には concrete dyadic-band `increment : Nat -> Rat` が見つからず、次は `geometricIncrement base ratio : Nat -> Rat` を導入して、まず `hinc_nonneg`、余裕があれば exact decay lemma を試すのが妥当、という結論になっておる。
だから今の直近ルートは、まだ **Rat 側の標準幾何 increment を立てる段階** じゃ。

## 1. N→R API は必要になるが、今の main route ではない

お主の言う通り、実数 ( \mathbb{R} ) では通常の意味の「割り切れない」は消える。

任意の (a\ne 0), (b\in\mathbb{R}) に対して、

$$
b = a\cdot \frac{b}{a}
$$

だから、体としては全部割れる。

しかし、幾何構造や数論構造では話が違う。
「任意の実数係数で割れる」ではなく、

$$
b = a\cdot n,\quad n\in\mathbb{N}
$$

あるいは、

$$
b = a\cdot q,\quad q\in\mathbb{Q}
$$

あるいは、

$$
b = a\cdot GN(d,u,x)
$$

のように、 **係数がどの構造に属しているか** で可除性を読む。
ここが「R の離散化された可除性」じゃな。

つまり、Lean でやるなら `Real` 上の通常の `Dvd` を使うのではなく、別 predicate がよい。

例えば概念的には、

```lean
def NatScaleDivides (a b : ℝ) : Prop :=
  ∃ n : ℕ, b = (n : ℝ) * a
```

または、

```lean
def RatScaleDivides (a b : ℝ) : Prop :=
  ∃ q : ℚ, b = (q : ℝ) * a
```

のようなものじゃ。
これは「実数体では割れる」ではなく、 **自然数倍率・有理数倍率として構造的に割れる** という意味になる。

## 2. GN 可除性原理は強いが、今入れるとスコープが広がる

GN の可除性原理は、おそらくこういう形じゃ。

$$
(x+u)^d-x^d = u\cdot GN(d,u,x)
$$

または、差分商として、

$$
GN(d,u,x)=\sum_{i=0}^{d-1}(x+u)^{d-1-i}x^i
$$

という構造を使う。

ここで (u) が整数・有理数・格子単位なら、

$$
(x+u)^d-x^d
$$

は (u) で **構造的に割れる** と読める。

ただし、これを DKMK-017 に持ち込むと、章の主題が変わる。

今 DKMK-017 は、

```text
concrete dyadic-band increment : Nat -> Rat
```

を探している段階じゃ。
一方 GN 可除性は、

```text
Nat / Rat / Real の構造的埋め込み
実数幾何上の離散可除性
差分商 GN の構造
```

を扱う別レイヤーになる。

つまり、今入れると DKMK-017 がまた API 境界設計章に戻ってしまう危険がある。

## 3. 今の DKMK-017 に必要なのは N→R ではなく Rat increment

現在の標準 route は、

```text
increment : Nat -> Rat
```

を前提にしている。

残っている入力は、

```text
hbaseBudget:
  (increment 0 : Real) <= (1 + error) * (1 - (ratio : Real))

hinc_nonneg:
  forall k, k <= K -> 0 <= increment k

hdecay:
  forall k, k < K -> increment (k + 1) <= ratio * increment k
```

じゃ。

なので、直近ではまず

```lean
geometricIncrement base ratio k := base * ratio ^ k
```

のような `Nat -> Rat` 候補を立てて、

```text
非負性
初期値
減衰
```

を閉じるのがよい。

これは DKMK-017H の結論とも一致しておる。

## 4. N→R / GN 可除性は次の別枝として置くのがよい

ただし、完全に捨てるべきではない。
むしろ、次のような別章または side branch にすると強い。

```text
DKMK-018 candidate:
  Nat/Rat-to-Real Structural Divisibility Bridge
```

主題は、

```text
Real 上では通常可除性は自明
しかし Nat/Rat/lattice coefficient に制限すると可除性が復活する
GN factorization はその代表例
```

というものじゃ。

Lean surface の候補は、

```lean
def NatScaleDivides (a b : ℝ) : Prop :=
  ∃ n : ℕ, b = (n : ℝ) * a

def RatScaleDivides (a b : ℝ) : Prop :=
  ∃ q : ℚ, b = (q : ℝ) * a
```

あるいは、宇宙式・GN 側なら、

```lean
theorem powerGap_structurally_divisible_by_unit
    ...
```

のような形になる。

ただしこれは DKMK-017 の `increment : Nat -> Rat` 探索が一段落してからでよい。

## 5. 今の判断

わっちの判断はこうじゃ。

```text
今すぐ DKMK-017 に GN 可除性原理を持ち込む:
  非推奨

N→R / R の構造的可除性を忘れず候補として記録:
  推奨

次の DKMK-017I:
  geometricIncrement base ratio : Nat -> Rat を実装して hinc_nonneg / hdecay を試す

その後:
  Real/log analytic candidate が必要になった段階で N→R / Rat→Real envelope bridge を検討
```

## 6. まとめ

お主の直感は正しい。

実数 ( \mathbb{R} ) では割り切れない概念は消える。
しかし、 **係数を (\mathbb{N}), (\mathbb{Q}), 格子単位, GN 構造に制限した瞬間に、可除性は幾何構造として復活する** 。

これは DkMath 的にはかなり重要な橋じゃ。

ただ、今の DKMK-017 はまだそこへ行く直前ではない。
まずは `geometricIncrement : Nat -> Rat` で dyadic-band route を動かす。
その後、Real/log/幾何候補を rational envelope へ落とす必要が見えた時に、N→R / 構造的可除性ブリッジを立てるのがよい。

今は本線を保つ。
GN 可除性は、強い獣じゃ。檻も柵も作らずに今放つと、畑を踏み荒らす。だが然るべき章で放てば、山を切り開く狼になるぞい。

# Note

[review-028](./review-petal-028.md)

## Zsigmondy との交渉が始まる

うむ。
**ついに交渉開始の段階** じゃ。ただし、まだ「Zsigmondy 本体を証明する」ではなく、

```text
Petal cubic surface closure
  -> Zsigmondy が欲しがる入力形式へ翻訳する
```

という交渉じゃな。

言い換えると、今はこういう局面。

```text
Petal 側:
  S0/GN3/BoundaryD3/Anchor/Eisenstein は閉じた

Zsigmondy 側:
  primitive prime divisor を要求する

交渉点:
  Petal の anchored primitive S0 carrier は、
  Zsigmondy の primitive divisor witness として読めるか？
```

## 今できること

今の Petal からは、reduced branch でこう言える。

```lean
BoundaryD3Reduced c b
```

なら、

```text
3 ∤ c - b
```

であり、さらに条件つきで、

```text
S0_nat c b と c - b は互いに素
```

そして、

```text
S0_nat c b 上に boundary を割らない primitive witness がある
```

さらにそれは、

```text
AnchoredS0Carrier q c b q
```

として読める。

つまり Petal 側はすでに、

```text
境界ではなく S0/GN3 側にいる素数 witness
```

を提供できる。

これは Zsigmondy にとってかなり近い入力じゃ。

## まだ足りないもの

Zsigmondy が本当に欲しいのは普通、

```text
q ∣ a^n - b^n
かつ
任意の k < n に対して q ∤ a^k - b^k
```

のような「低次数には出てこない新しい素因子」じゃ。

一方、今の Petal が提供しているのは主に、

```text
q ∣ S0_nat c b
q ∤ c - b
```

つまり、

```text
q ∣ c^3 - b^3
q ∤ c - b
```

に相当する。

これは (n=3) の primitive divisor 条件にかなり近い。
なぜなら、(3) の真の低次数は基本的に (1) だけなので、

```text
q ∤ c - b
```

がそのまま

```text
q は 3 次差の primitive 側にいる
```

へ読める。

だから (d=3) では、Petal と Zsigmondy の距離はかなり短い。

## 交渉用 API の形

次に作るなら、たぶん `DkMath.Petal.ZsigmondyBridge` ではなく、もう少し控えめに、

```text
DkMath.Petal.PrimitiveD3
```

または、

```text
DkMath.Petal.ZsigmondyD3Bridge
```

が良い。

最初の theorem はこういう方向じゃ。

```lean
theorem exists_boundary_free_prime_dvd_cube_sub_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ c^3 - b^3 ∧
      ¬ q ∣ c - b
```

これは Petal から Zsigmondy へ渡すための最初の翻訳文じゃな。

さらに、`S0_nat` 経由を明示するなら、

```lean
theorem exists_primitiveD3Witness_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      AnchoredS0Carrier q c b q ∧
      q ∣ c^3 - b^3 ∧
      ¬ q ∣ c - b
```

これがかなり良い。
Petal の言葉と Zsigmondy の言葉を両方持つ witness になる。

## 名前としては

おすすめはこれ。

```text
DkMath.Petal.ZsigmondyD3Bridge
```

内容はまだ一般 Zsigmondy ではなく、あくまで三次 bridge。

```text
BoundaryD3Reduced
  -> AnchoredS0Carrier witness
  -> prime divisor of c^3 - b^3
  -> not divisor of c - b
```

この範囲なら、今の Petal closure から自然に出せる。

## 交渉の核心

Zsigmondy に対して、Petal はこう言える。

```text
わしらは一般 n の原始素因子まではまだ主張しない。
しかし n = 3 の reduced cubic surface では、
boundary から分離された S0/GN3 witness を持っている。
これは primitive divisor の局所モデルである。
```

つまり、これは Zsigmondy 本体への突撃ではなく、

```text
Zsigmondy が要求する primitive witness 型を、
Petal d=3 で一度満たす
```

という交渉じゃ。

## 結論

うむ、いよいよじゃ。

```text
今すぐ証明するもの:
  Zsigmondy theorem ではない

今すぐ作るべきもの:
  ZsigmondyD3Bridge / PrimitiveD3Bridge

目的:
  Petal の anchored S0 witness を
  “3 次差の primitive divisor witness” として翻訳する
```

これが通れば、次に一般 (d) へ進む時の型が決まる。

わっちなら次の一手は、

```text
Add: DkMath.Petal.ZsigmondyD3Bridge
```

として、まず **三次だけの原始素因子 witness API** を作る。
ついに交渉開始じゃ。Zsigmondy 城の門前まで来たぞい。

## 交渉の契約書はどうなっている？

おお、そこは大事じゃ。
ただ、手元のスナップショットを見る限り、`DkMath.Zsigmondy.lean` は **docs-only ではなく実体あり** じゃった。

少なくとも含まれていた中身はこれ。

```lean
namespace DkMath.Zsigmondy

def BodyN (x u : ℕ) (d : ℕ) : ℕ :=
  (x + u) ^ d - u ^ d

def KernelN (x u : ℕ) (d : ℕ) :=
  diffPowSum' (x + u) u d

def PrimitivePrimeDivisor (a b n q : ℕ) : Prop :=
  Nat.Prime q ∧
  q ∣ a ^ n - b ^ n ∧
  ∀ m : ℕ, 0 < m → m < n → ¬ q ∣ a ^ m - b ^ m
```

さらに重要なのは、この API がすでにあることじゃ。

```lean
exists_primitivePrimeDivisor_prime_exp
exists_primitivePrimeDivisor_body_nat
exists_primitivePrimeDivisor_kernel_nat
primitivePrimeDivisor_body_three_imp_dvd_GN
prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN
```

なので、もし現在のワークスペースで `DkMath.Zsigmondy` が本当に docs-only なら、ブランチ差分か移動漏れかもしれぬ。だが設計上は、**Zsigmondy との交渉口はすでにかなり具体的に存在していた** と見てよい。

## docs に書いてある大事な契約

`ZsigmondyCyclotomic` 側の docs で重要なのはこの整理じゃ。

```text
層A: 存在層
  primitive prime divisor の存在だけを保証

層B: 精密層
  padicValNat q (a^d - b^d) = 1 などの評価
```

今回 Petal が接続すべきなのは、まず **層A**。
つまり、いきなり p-adic 精密評価や squarefree へ行くのではなく、

```text
BoundaryD3Reduced
  -> primitive prime divisor exists
  -> witness lies on S0/GN3 side
  -> witness can be read as anchored carrier
```

を作るのが正しい。

## Petal との一致点

Petal closure では、すでにこう言える。

```text
BoundaryD3Reduced c b
  -> ¬ 3 ∣ c - b
  -> S0 と boundary は分離
  -> anchored primitive S0 carrier exists
```

一方、Zsigmondy の prime-exponent API は概念的にこう要求する。

```lean
Nat.Prime d
3 ≤ d
b < a
0 < b
Nat.Coprime a b
¬ d ∣ a - b
```

そして結論は、

```lean
∃ q, PrimitivePrimeDivisor a b d q
```

三次なら `d = 3` なので、Petal の

```lean
BoundaryD3Reduced c b
```

はそのまま Zsigmondy の

```lean
¬ 3 ∣ c - b
```

に一致する。

つまり、交渉条件がぴったり合っておる。

## 次に作るべき橋

名前はたぶんこれがよい。

```text
DkMath.Petal.ZsigmondyD3Bridge
```

最初の定理はこの形。

```lean
theorem exists_primitivePrimeDivisor_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
```

これは `DkMath.Zsigmondy.exists_primitivePrimeDivisor_prime_exp` を `d := 3` で呼べばよいはず。

その次に欲しいのが Petal 側への翻訳。

```lean
theorem exists_primitivePrimeDivisor_anchoredS0Carrier_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
      AnchoredS0Carrier q c b q ∧
      ¬ q ∣ c - b
```

ここが本当の交渉成立点じゃな。

## 注意点

`exists_anchoredS0Carrier_of_boundaryD3Reduced` はすでに Petal 側で witness を出す。
しかしそれは Zsigmondy の `PrimitivePrimeDivisor` 型とは限らない。

なので、Zsigmondy bridge では **Zsigmondy 側から q を取り、その q が S0/Anchor 側にも入る** ことを示す方がよい。

流れはこう。

```text
1. Zsigmondy.exists_primitivePrimeDivisor_prime_exp で q を取る
2. PrimitivePrimeDivisor.not_dvd_lower を m = 1 に適用
3. q ∤ c - b を得る
4. q ∣ c^3 - b^3 を得る
5. c^3 - b^3 = (c-b) * S0_nat c b
6. q ∤ c-b より q ∣ S0_nat c b
7. hasPositiveAnchorPrime_self_of_prime で AnchoredS0Carrier q c b q
```

これで、Petal と Zsigmondy が同じ witness を共有できる。

## 結論

うむ、docs に書いてある大事なことはこれじゃ。

```text
Zsigmondy は層A/層B に分かれる。
今 Petal が交渉すべきは層A。
三次 d=3 では BoundaryD3Reduced が Zsigmondy の非例外条件 ¬3 | c-b と一致する。
```

だから次は、

```text
Add: DkMath.Petal.ZsigmondyD3Bridge
```

でよい。

ただし、現在のワークスペースで `DkMath.Zsigmondy` が本当に無いなら、まずは `DkMath.NumberTheory.ZsigmondyCyclotomic` の存在層を直接見るか、`DkMath.Zsigmondy` を復帰・昇格するのが先じゃな。
設計としては、`DkMath.Zsigmondy` はかなり良い「交渉窓口」になっておる。

## 交渉成立か？

うむ、交渉はかなりうまくいきそうじゃ。

整理すると、構造はこうじゃな。

```text
DkMath.Zsigmondy/
  docs だけのパッケージディレクトリ

DkMath/Zsigmondy.lean
  実体定義・定理が集約されている本体
```

つまり、まだ `Zsigmondy` パッケージは大きく分割されておらず、docs で構想を置きつつ、Lean 実体は単一ファイルにまとまっている段階。ここは今すぐ細分化しなくてよいと思う。

## 交渉がうまくいきそうな理由

Petal 側で閉じた条件が、Zsigmondy 側の (d=3) 条件とほぼ一致しているからじゃ。

Zsigmondy 側が欲しいのは概念的に、

```text
a^3 - b^3 に出る素因子 q が、
a - b には出ない
```

という primitive divisor 条件。

Petal 側ではもう、

```text
BoundaryD3Reduced c b
  := ¬ 3 ∣ c - b
```

のもとで、

```text
S0_nat c b と c - b が分離する
primitive S0 witness が anchored carrier として読める
```

ところまで来ている。

しかも、

```text
c^3 - b^3 = (c - b) * S0_nat c b
```

なので、Zsigmondy の「三次差にいるが一次差にはいない素因子」は、そのまま Petal の「境界ではなく S0/GN3 側にいる素因子」と読める。

## 次の橋の形

実装するなら、最初は控えめにこれじゃ。

```text
DkMath.Petal.ZsigmondyD3Bridge
```

ここでやることは、Zsigmondy 本体を再証明するのではなく、

```text
Zsigmondy の primitive witness
  -> Petal の AnchoredS0Carrier
```

へ翻訳すること。

狙う定理はこの形。

```lean
theorem exists_primitivePrimeDivisor_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q
```

次に、Petal らしい本命はこれ。

```lean
theorem exists_primitivePrimeDivisor_anchoredS0Carrier_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b)
    (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
      AnchoredS0Carrier q c b q ∧
      ¬ q ∣ c - b
```

この定理が通れば、交渉成立じゃ。

```text
Zsigmondy witness
  = Petal anchored S0/GN3 witness
```

と読める。

## 注意点

Zsigmondy 側の witness と、Petal 側の `exists_anchoredS0Carrier_of_boundaryD3Reduced` が出す witness は、同じ (q) とは限らない。

だから橋では、できれば **Zsigmondy 側から取った (q)** を Petal に持ち込むのがよい。

流れはこう。

```text
1. Zsigmondy から q を取得
2. q ∣ c^3 - b^3
3. primitive 条件から q ∤ c - b
4. c^3 - b^3 = (c - b) * S0_nat c b
5. q ∤ c - b より q ∣ S0_nat c b
6. q は prime なので HasPositiveAnchorPrime q q
7. AnchoredS0Carrier q c b q
```

ここが一番綺麗。

## 結論

うむ。
`Zsigmondy.lean` が単一実体なら、今はそれをそのまま交渉相手にしてよい。

```text
Petal 側は d=3 の受け皿が完成
Zsigmondy 側は primitive divisor の存在語彙を持っている
次は ZsigmondyD3Bridge で同じ witness を共有させる
```

これはかなり筋が良い。
Zsigmondy 城の門番と話すための通行証は、もう Petal 側で揃っておる。

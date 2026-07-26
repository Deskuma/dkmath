# Note: Review: Ultra-001-I

## 総合判定

**全面採用。Ultra-001I 完了じゃ。** ⚔️🐺

重大問題 0。
数学的過大主張 0。
旧 ABC 塔との接続も、単なる命名 wrapper ではなく **exact な factorization／tail／counting bridge** になっている。

`GNLegacyTailCountingBridge.lean` 自身も、

```text
旧 piSqRad / twoTail 座標
旧 residue counting / finite layer-cake
現行 GN non-exceptional channel
```

を再接続しつつ、Hensel cover の構成と pointwise contract は未証明だと明確に境界を引いている。

## 1. `GNNonExceptionalPart` は正しい再構成

```lean
noncomputable def GNNonExceptionalPart (p a b : ℕ) : ℕ :=
  (GNNonExceptionalSupport p a b).prod
    (fun q => q ^ (GN p a b).factorization q)
```

これは support だけを残す `GNNonExceptionalSupportProduct` と異なり、各非例外素数の valuation を完全に保持する。

factorization が、

```text
q ∈ non-exceptional support
  → factorization q = v_q(GN)

q ∉ non-exceptional support
  → factorization q = 0
```

と exact に証明されている。

そこから、

```lean
GNNonExceptionalPart_factorization_support
rad_GNNonExceptionalPart_eq_supportProduct
valuationExcess_GNNonExceptionalPart_eq
```

が順に閉じている。

したがって現在の二座標、

```text
S = fresh support mass
E = extra multiplicity mass
```

を、一つの自然数 `GNNonExceptionalPart` の、

```text
radical
valuationExcess
```

として読める。

これは非常に良い。現行戦線と旧 ABC 塔が同じ整数を観測するようになった。

## 2. `piSqRad / twoTail` bridge は exact

今回最も重要な定理はこれじゃ。

```lean
GNNonExceptionalValuationExcess_eq_log_piSqRad_add_log_twoTail
```

数式では、

$$E=\log\operatorname{piSqRad}(N)+\log\operatorname{twoTail}(N)$$

ただし、

$$N=\operatorname{GNNonExceptionalPart}(p,a,b)$$

じゃ。

Lean コードでは先に、

$$E=\log\operatorname{sqTail}(N)$$

を証明し、

$$\operatorname{sqTail}(N)=\operatorname{piSqRad}(N)\operatorname{twoTail}(N)$$

を通して二層へ分解している。

旧 ABC 塔の読みでは、

```text
piSqRad
  = valuation の第2層

twoTail
  = valuation の第3層以後
```

じゃった。

したがって現在の $E$ が、

```text
第二層 + deep tail
```

へ exact に戻った。

これは「過去の似たアイデアを再利用した」のではない。

> **現在の non-exceptional valuation excess と、旧 ABC の square-tail 座標が同一物である**

ことを Lean が確定したのじゃ。

## 3. `GNDeepLiftResidueCover` の設計も正しい

```lean
def GNDeepLiftResidueCover
    (p q b k : ℕ) (R : Finset ℕ) : Prop :=
  ∀ a, q ^ k ∣ GN p a b →
    ∃ r ∈ R, Nat.ModEq (q ^ k) a r
```

この interface は中立でよい。

Hensel の内部実装、cyclotomic polynomial、`ZMod` unit、multiplicative order のいずれにも依存していない。算術側は単に有限住所集合 `R` を返せば、counting 側が受け取れる。

さらに cover から、

$$#{0\le a\le X:q^k\mid GN_p(a,b)}\le |R|\left(\frac{X+1}{q^k}+1\right)$$

を出し、$|R|\le p-1$ を投入して、

$$#{0\le a\le X:q^k\mid GN_p(a,b)}\le(p-1)\left(\frac{X+1}{q^k}+1\right)$$

まで閉じている。

union の重複を許して上から `sum` で押さえる設計なので、`R` に同じ residue class の別代表が混ざっても不正にはならない。構成側では canonical residue を選べば最良になる。

## 4. divisibility と `padicValNat` の接続も正しい

```lean
gn_deep_lift_filter_eq_padic_depth_filter
```

は、$GN\ne0$ の範囲で、

$$q^k\mid GN_p(a,b)\iff k\le v_q(GN_p(a,b))$$

を Finset filter の equality として固定している。

続く、

```lean
exp_gn_padic_layer_cake
```

によって、旧 `exp_layer_cake` に、

$$a\longmapsto v_q(GN_p(a,b))$$

を直接入力できる。

つまり現在は、

```text
Hensel住所
  ↓
divisibility層の個数
  ↓
padic depth層
  ↓
exponential layer-cake / MGF
```

という旧解析ルートが、現行 GN に完全接続された。

## 5. 一点だけ、厳密に分離すべきもの

`exp_gn_padic_layer_cake` は、

```lean
hVbd :
  ∀ a ≤ X, padicValNat q (GN p a b) ≤ X + 1
```

を仮定している。

これは正しい conditional wrapper だが、**residue cover から自動的に出る仮定ではない。**

residue cover は、

```text
各深度 k の bad address 数
```

を抑える。

`hVbd` は、

```text
有限区間内で valuation がどこまで深くなり得るか
```

を抑える。

別の義務じゃ。

現 report は、この wrapper を「旧 layer-cake に入力可能にした」とだけ述べており、`hVbd` を証明済みとはしていないので問題はない。

将来、本格使用時に `X+1` が強すぎる場合は、

```text
区間上の valuation 最大値 K
```

を独立変数にした general layer-cake を作る余地がある。

## 6. 次の魔核の正確な仮定

残る theorem は、裸の、

```lean
∃ R, R.card ≤ p - 1 ∧
  GNDeepLiftResidueCover p q b k R
```

では少し広すぎる。

算術的に必要な発動条件は概ね、

```lean
hp  : Nat.Prime p
hq  : Nat.Prime q
hqp : ¬ q ∣ p
hqb : ¬ q ∣ b
hk  : 0 < k
```

じゃ。

現行 Triple の non-exceptional support prime から使うなら、`hqp` と `hqb` は freshness packet から供給できる。

狙う production theorem は、この形がよい。

```lean
theorem exists_gnDeepLiftResidueCover_of_prime
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    ∃ R : Finset ℕ,
      R ⊆ Finset.range (q ^ k) ∧
      R.card ≤ p - 1 ∧
      GNDeepLiftResidueCover p q b k R
```

`k=0` は modulus $1$ の自明 branch として分離すればよい。

## 7. Existential より canonical residue set が強い

実装上は、最初から existential witness を直接構成するより、canonical set を定義する方が美しい。

```lean
def GNDeepLiftResidues (p q b k : ℕ) : Finset ℕ :=
  (Finset.range (q ^ k)).filter
    (fun r => q ^ k ∣ GN p r b)
```

すると cover は、$a$ を $a\bmod q^k$ へ送るだけで出る。

```lean
theorem GNDeepLiftResidues_cover :
    GNDeepLiftResidueCover p q b k
      (GNDeepLiftResidues p q b k)
```

本当の魔核は、

```lean
theorem card_GNDeepLiftResidues_le_pred
    ...
    (GNDeepLiftResidues p q b k).card ≤ p - 1
```

だけになる。

この cardinal theorem は、次の二段へ分けられる。

```text
mod q の非自明 p-th root は高々 p−1 個
```

と、

```text
同じ mod q root から出る mod q^k root は高々一個
```

後者が simple-root Hensel uniqueness じゃ。

## 8. 最短の Hensel 証明設計

深度 $k$ の root 集合から mod $q$ root 集合への reduction map を考える。

```text
Root(q^k) → Root(q)
```

ここで示すべきは injectivity。

```text
q^k ∣ GN p a b
q^k ∣ GN p a' b
a ≡ a' [MOD q]
  →
a ≡ a' [MOD q^k]
```

これが simple-root uniqueness の最も直接的な API になる。

すると、

$$|\operatorname{Root}(q^k)|\le|\operatorname{Root}(q)|\le p-1$$

で終わる。

mod $q$ 側では、$b$ が unit なので、

$$t=(a+b)b^{-1}$$

と変換すれば、

$$GN_p(a,b)=0\Longrightarrow t^p=1,\qquad t\ne1$$

となる。

従って root は非自明な $p$ 乗根であり、高々 $p-1$ 個。

また derivative の simple 性は、恒等式、

$$a,GN_p(a,b)=(a+b)^p-b^p$$

を微分して root 上で読むと、

$$a,\partial_a GN_p(a,b)=p(a+b)^{p-1}$$

となるため、$q\nmid a,p,a+b$ なら derivative は非零。

ここまで分解すれば、Hensel の実装方式を変えても上位 API は変わらない。

## 9. ただし cover 完成後も裏ボスは残る

report が明記している通り、cover が返すのは平均・密度評価であって、全 Triple の pointwise joint contract ではない。

```text
deep lift が希薄
```

は、

```text
deep lift が存在しない
```

ではない。

一つの ABC triple は、その希薄な residue class に入ることができる。

したがって cover 完成後の次の本当の課題は、

```text
同じ Triple が
複数深度・複数指数・反復 lift にわたり
希薄住所へ入り続けることが可能か
```

じゃ。

つまり、

```text
Hensel cover
  ↓
平均・密度制御
  ↓
repeated-lift / adjacent-exponent sieve
  ↓
pointwise compensation
```

というもう一段が必要になる可能性が高い。

## 最終評価

```text
legacy factorization bridge       完成
piSqRad / twoTail exact bridge    完成
residue-cover interface           完成
finite counting transport         完成
divisibility / padic bridge       完成
legacy layer-cake wrapper         完成

Hensel cover construction         未証明
pointwise compensation            未証明
```

**Ultra-001I は全面採用。**

旧 ABC 塔は廃墟ではなかった。

```text
現行 GN 戦線の valuation depth を、
平均・密度・layer-cake へ送る地下通路
```

として正式に復活したのじゃ。公開 aggregator にも正しく import されている。

PR #69 は現在 head `0e1387c...`、5 commits、18 files、3570 additions、mergeable の状態。

🧙‍♀️✨️ **次は「Hensel で root を持ち上げる」のではなく、「持ち上がった root を mod $q$ へ戻す写像が単射」として攻略するのが最短じゃ。**

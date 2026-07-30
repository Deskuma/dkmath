# RAMIFIED-003

## FLT7-RAMIFIED-002 総合判定

exact gap-unit equivalence

**Outcome A、全面採用です。** 🧙‍♀️✨️

重大問題・主要問題・修正必須事項はありません。

PR head は報告どおり、

```text
1b22a680e708e15fb78d203c60b71bda86d832e6
```

へ更新されています。PR #65 は open / draft / mergeable、148 commits・66 changed files です。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5080817059)

公開 CI run 376 は監査時点では `in_progress` です。focused build と `lake build DkMath.FLT.Seven` の成功報告は確認対象の差分と整合しています。

## Root 座標の primitive 性

```lean
PrimitiveRamifiedSummitPacket.root_coordinates_isCoprime
```

は、root の両座標を割る素数 $q$ があれば、ramified seventh-power coordinates の双方も $q$ で割れることを示し、summit が保持する cyclotomic coordinate coprimality と衝突させています。

これは単なる norm coprimality ではなく、

$$\operatorname{IsCoprime}(u,v)$$

を直接回収しています。

そのため、以後の $T,L,R$ の gcd 監査に必要な最小 primitive core が正しく得られました。

### $T,L,R$ の $7$-unit 性

RAMIFIED-001 の exact depth により、

$$7\mid v$$

です。

ここから mod $7$ では、

$$T=2u+v\equiv2u$$

$$L\equiv u^3$$

$$R\equiv u^3$$

となります。

もし $7$ が $T,L,R$ のいずれかを割れば $7\mid u$ が従い、すでに $7\mid v$ なので primitive root coordinates と矛盾します。

実装はこの構造をそれぞれ独立 theorem に落としています。

```lean
ramifiedLinear_not_seven_dvd
ramifiedLeftCubic_not_seven_dvd
ramifiedRightCubic_not_seven_dvd
```

正確です。

## Root 三因子の pairwise coprimality

ここが RAMIFIED-002 の最も厚い証明です。

### $T$ と $L$

共通素因子 $q$ を仮定し、多項式恒等式により、

$$q\mid49v^3$$

へ押し込みます。

そこから、

```text
q | 49
```

または、

```text
q | v
```

に分岐します。

前者は $q=7$ となって $T$ の $7$-unit 性と矛盾し、後者は $L$ と $v$ から $q\mid u$ を導いて root primitive 性と矛盾します。

### $T$ と $R$

同様に別の恒等式から、

$$q\mid49v^3$$

へ落とし、同じ二分岐を排除しています。

### $L$ と $R$

差の恒等式、

$$R-L=7vN(u,v)$$

により、共通素因子は、

```text
7
v
norm root
```

のいずれかへ送られます。

norm 側へ入った場合も、追加恒等式で、

$$q\mid49v^4$$

へ押し戻し、最終的に $q=7$ または $q\mid u,v$ へ還元しています。

この証明は単なる `ring` の副産物ではありません。

> 任意の root-factor 共通素因子は、ramified prime $7$ または primitive root coordinates の共通素因子でなければならない。

という完全な排除原理になっています。

### 正式な `CoprimeTripleRouting`

endpoint 側は、

```text
|endpointLeft|
|endpointRight|
|endpointLeft + endpointRight|
```

root 側は、

```text
|T|
|L|
|R|
```

です。

両 triple の非零性・pairwise coprimalityと、

$$|c|\cdot|e|\cdot|c+e|=|T|\cdot|L|\cdot|R|$$

を既存、

```lean
nonempty_coprimeTripleRouting
```

へ供給しています。

`CoprimeTripleRouting` は九つの cell と、三本の row factorization、三本の column factorization、各行・各列の cell coprimalityを保持します。

最終的に、

```lean
RamifiedCubicRoutingPacket
AwaySevenBaseTerminalUnitSectorPacket.ramifiedCubicRouting
```

が無条件で得られています。

これで前回の用語境界だった、

```text
ramified 3×3 routing candidate
```

から、

```text
formal ramified 3×3 coprime routing
```

への昇格は本当に完了しました。

## Gap depth synchronization

二つの gap は、

$$R-L=7vN(u,v)$$

$$c-e=7^6A^7$$

です。

RAMIFIED-001 で、

$$v_7(|v|)=5+7v_7(A)$$

かつ、

$$v_7(N(u,v))=0$$

が得られています。

したがって、

$$v_7(|R-L|)=1+5+7v_7(A)=6+7v_7(A)$$

です。

endpoint 側も直接、

$$v_7(|c-e|)=6+7v_7(A)$$

なので、

$$\boxed{v_7(|R-L|)=v_7(|c-e|)}$$

が成立します。

実装された三定理、

```lean
cubicGap_padicValNat
endpointGap_padicValNat
cubicGap_depth_eq_endpointGap_depth
```

は、この計算を完全に exact theorem として固定しています。

## 露出した本当の魔核

今回の depth equality は、さらに強い **整数恒等式**の影です。

記号を、

```text
S := seventhPowerSndCore u v
Q := (ramifiedGapQuotient (7^5 * A^7) e).snd
B := norm root = residualRoot
```

とします。

RAMIFIED-001 には、

$$7vS=(c-e)Q$$

があります。

RAMIFIED-002 の cubic difference は、

$$R-L=7vB$$

です。

第一式に $B$ を掛け、第二式に $S$ を掛けると、

$$\boxed{(R-L)S=(c-e)QB}$$

を得ます。

しかも、

$$7\nmid S$$

$$7\nmid Q$$

$$7\nmid B$$

です。

したがって二つの gap は、単に同じ valuation を持つだけではありません。

> endpoint gap と root-cubic gap は、$7$-進局所世界において明示的な unit 倍で一致する。

ということです。

局所化して書けば、

$$R-L=(c-e)\cdot QB,S^{-1}$$

であり、

$$QB,S^{-1}$$

は $7$-unit です。

これが RAMIFIED-002 で露出した新しい魔核です。

## 次 checkpoint

```text
FLT7-RAMIFIED-003
exact ramified gap-unit bridge
```

第一目標は、division を避けた整数 theorem です。

```lean
theorem
  PrimitiveRamifiedSummitPacket
    .cubicGap_mul_sndCore_eq_endpointGap_mul_bridge :
  (ramifiedRightCubic root.fst root.snd -
      ramifiedLeftCubic root.fst root.snd) *
      seventhPowerSndCore root.fst root.snd =
    (endpointLeft - endpointRight) *
      (ramifiedGapQuotient
        (7 ^ 5 * (gapRoot : ℤ) ^ 7)
        endpointRight).snd *
      norm root
```

続いて packet 化します。

```lean
structure RamifiedGapUnitBridgePacket where
  endpointGap : ℤ
  cubicGap : ℤ
  leftUnit : ℤ
  rightUnit : ℤ
  leftUnit_not_seven_dvd : ¬ (7 : ℤ) ∣ leftUnit
  rightUnit_not_seven_dvd : ¬ (7 : ℤ) ∣ rightUnit
  bridge_eq :
    cubicGap * leftUnit =
      endpointGap * rightUnit
```

最後に任意の $7^k$ modulus 上で、

```lean
cubicGap
  =
endpointGap * explicitUnit
```

を得ます。

## API 上の小さな注意

`CoprimeTripleRouting` の九 cell は、存在証明内部では、

```lean
cij := Nat.gcd ai bj
```

として作られています。

ただし、structure 自体には、

```lean
c11 = Nat.gcd a₁ b₁
```

のような field はありません。

これは RAMIFIED-002 の blocker ではありません。row/column factorization には十分です。

今後、prime-address や exact cell support を調べる段階では、

```lean
RamifiedCubicRoutingPacket.c11_eq_gcd
...
RamifiedCubicRoutingPacket.c33_eq_gcd
```

または一般的な cell characterization theorem を追加すると、away 側の prime-address API を再利用しやすくなります。

## 現在地

```text
RAMIFIED-001
  common summit
  root-snd exact depth
  linear-cubic-cubic factorization

RAMIFIED-002
  primitive root coordinates
  root triple pairwise coprime
  endpoint triple pairwise coprime
  formal CoprimeTripleRouting
  exact gap-depth synchronization

RAMIFIED-003
  exact gap-unit equivalence
```

**九つの住所が完成し、二つの gap が同じ深さであることも確定しました。次は「同じ深さ」を「同じ gap の unit 変換」へ昇格させる段階です。**

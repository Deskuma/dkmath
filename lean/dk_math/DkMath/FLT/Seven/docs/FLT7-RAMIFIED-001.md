# FLT7-RAMIFIED-001

## TERM-010 再レビュー

**Outcome A、全面採用です。blocker はありません。** 🧙‍♀️✨️

PR head は報告どおり、

```text
abdb0186b0b2061c1d420ed4326fe4c1fd043eb1
```

です。PR #65 は open / draft / mergeable、Lean CI run 348 も **success** を確認しました。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5080405760)

提出された差分・レポート・公開 head の内容も一致しています。

# 実装評価

## 1. 交代型因子は完全に自然数世界へ戻った

```lean
alternatingCyclotomicSeven x y
```

について、

$$ (x+y)A_7(x,y)=x^7+y^7 $$

および、

$$ (A_7(x,y):\mathbb Z)=\operatorname{cyclotomicSeven}(x,-y) $$

が証明されています。

これにより Row-Z は「負 endpoint を含む未知の signed arithmetic」ではなく、**正の自然数 $x,y$ から構成される交代型因子**として処理可能になりました。

## 2. gcd-seven と $49$ 排除

primitive 条件から、

$$\gcd(x+y,A_7(x,y))\mid7$$

を証明し、Row-Z の $7\mid x+y$ と合わせて、

$$\gcd(x+y,A_7(x,y))=7$$

まで閉じています。さらに signed cyclotomic depth を再利用して、

$$49\nmid A_7(x,y)$$

も確定しています。

## 3. exact power split

中心 packet は予定どおりです。

```text
x + y   = 7^6 * a^7
A₇(x,y) = 7 * b^7
z       = 7 * a * b
Coprime a b
```

単なる valuation shape ではなく、正値性・coprimality・distinguished factor まで同梱されています。

構成証明も、共通因子 $7$ を除去した後、

```text
(7² * c) * residual = (7 * d)^7
```

を作り、既存の `seventh_power_factor_split` へ接続する正しい流れです。

## 4. signed residual core

signed cubic coordinates の共通素因子が元の $x,y$ の双方を割ることを示し、`source.hxy` から coordinate coprimality を得ています。

続いて、

```lean
exists_cyclotomicSeven_terminal_core
```

を整数 endpoint $(x,-y)$ に直接適用し、

```text
cyclotomicSevenToTraceOne x (-y)
  = sevenAxis * residualCore
```

を取得しています。

その norm を exact split の $b^7$ と同定する部分も、$7$ を整数環上でキャンセルするだけの明確な証明です。

## 5. residual core 自身の七乗抽出

residual core と共役の gcd が unit であることを示し、

```lean
exists_eq_seventh_power_of_coprime_mul_eq_pow
```

へ接続しています。

したがって、

$$\operatorname{residualCore}=r^7$$

が本当に得られ、TERM-009 の receiver は無条件で inhabit されました。

## 6. terminal away branch の最終正規化

最終 API、

```lean
AwaySevenBaseTerminalUnitSectorPacket.ramifiedChartResolution
```

は、

```text
natural ramified
signed ramified
```

の二 constructor だけを持ちます。

```text
Row Y   → natural ramified
Row Z   → signed ramified
Row Sum → impossible
```

が完全に型へ固定されました。

---

# TERM-010 により露出した共通魔核

ここから自然 Row-Y と signed Row-Z を別々に追う必要はありません。

両者は次の一つの整数 chart に統合できます。

```text
endpoint pair       (c,e)
distinguished term  d
gap root            A
residual root        B
quadratic root       ρ = (u,v)
```

保持する式は、

$$c^7-e^7=d^7$$

$$c-e=7^6A^7$$

$$\operatorname{cyclotomicSeven}(c,e)=7B^7$$

$$d=7AB$$

$$\operatorname{cyclotomicSevenToTraceOne}(c,e)=\operatorname{sevenAxis}\rho^7$$

です。

対応は、

```text
natural Row-Y:
  (c,e,d) = (z,x,y)

signed Row-Z:
  (c,e,d) = (x,-y,z)
```

となります。

自然 ramified packet はすでに同じ `sevenAxis * root^7` を保持しています。

signed 側も TERM-010 によって同一形へ到達しました。

# 第一の新魔核：root.snd の exact depth transfer

これは現時点では**次に証明すべき推論候補**ですが、かなり強く見えています。

$g=c-e$ とし、$7\mid g$ なので $g=7h$ と置きます。

次の quotient を定義します。

```lean
def ramifiedGapQuotient (h e : ℤ) : TraceOneInt (-2) :=
  ⟨7*h^2 - e^2,
    -e^2 - 7*e*h - 14*h^2⟩
```

直接展開すると、次の恒等式が成立するはずです。

$$\operatorname{cyclotomicSevenToTraceOne}(e+7h,e)=\operatorname{sevenAxis}\left(-e^3+7h\operatorname{ramifiedGapQuotient}(h,e)\right)$$

一方 ramified summit では、

$$\operatorname{cyclotomicSevenToTraceOne}(c,e)=\operatorname{sevenAxis}\rho^7$$

です。

`sevenAxis` を整数環でキャンセルすると、

$$\rho^7+e^3=gQ$$

を得ます。

第二座標だけを見ると、

$$\operatorname{seventhPowerSnd}(u,v)=g,Q_{\mathrm{snd}}$$

です。

既存の分解は、

$$\operatorname{seventhPowerSnd}(u,v)=7v\operatorname{seventhPowerSndCore}(u,v)$$

です。root norm が $7$-unit なら `seventhPowerSndCore` も $7$-unit になります。

また、

$$Q_{\mathrm{snd}}=-e^2-7eh-14h^2\equiv-e^2\pmod7$$

であり、primitive ramified endpoint $e$ も $7$-unit です。

そして、

$$g=7^6A^7$$

なので、両辺の exact $7$-adic valuation を比較すると、

$$\boxed{v_7(|v|)=5+7v_7(A)}$$

が予測されます。

Lean theorem の形はこれです。

```lean
theorem PrimitiveRamifiedSummitPacket.rootSnd_padicValNat :
    padicValNat 7 (Int.natAbs root.snd) =
      5 + 7 * padicValNat 7 gapRoot
```

これは単なる下界、

```text
7^5 ∣ root.snd
```

より強いです。

```text
root.snd の深さは必ず 5 mod 7
```

という、ramified summit 固有の保存核になります。

# 第二の新魔核：ramified 3×3 因子分解

もう一つ、直接 `ring` で閉じられる候補があります。

```lean
def ramifiedLinear (u v : ℤ) :=
  2*u + v

def ramifiedLeftCubic (u v : ℤ) :=
  u^3 - 2*u^2*v - 15*u*v^2 - 13*v^3

def ramifiedRightCubic (u v : ℤ) :=
  u^3 + 5*u^2*v - 8*u*v^2 + v^3
```

すると、

$$\boxed{\operatorname{ramifiedSeventhSnd}(u,v)=(2u+v)L_R(u,v)R_R(u,v)}$$

という三因子分解が成立します。

さらに、

$$R_R-L_R=7v\operatorname{norm}(\rho)$$

$$L_R+R_R=(u-3v)(u+4v)(2u+v)$$

です。

一方 endpoint 側では、

$$\operatorname{cyclotomicSevenSnd}(c,e)=-ce(c+e)$$

なので ramified coordinate equationから、

$$-ce(c+e)=(2u+v)L_RR_R$$

を得ます。

つまり新しい世界にも、

```text
endpoint triple:
  c
  e
  c+e

root triple:
  2u+v
  ramifiedLeftCubic
  ramifiedRightCubic
```

という **3×3 routing board** が現れます。

TERM-003〜008 で構築した away routing の経験を、今度は ramified root triple に適用できます。

# API 上の一点

TERM-010 の、

```lean
ramifiedChartResolution
```

は最終 decision として正しいです。

ただし signed constructor は薄い `SignedRamifiedCoordinateNormalForm` だけを保持し、今回作った、

```text
alternating power split
signed residual core
root norm source
```

を保持しません。

これは TERM-010 の欠陥ではありません。

ただし RAMIFIED-001 では、`ramifiedChartResolution` だけを入力にせず、terminal packet から次の強い共通 packet を作るのがよいです。

```lean
structure PrimitiveRamifiedSummitPacket where
  endpointLeft endpointRight distinguished : ℤ
  gapRoot residualRoot : ℕ
  root : TraceOneInt (-2)

  endpoint_coprime :
    IsCoprime endpointLeft endpointRight

  fermat_eq :
    endpointLeft^7 - endpointRight^7 =
      distinguished^7

  gap_eq :
    endpointLeft - endpointRight =
      7^6 * gapRoot^7

  residual_eq :
    cyclotomicSeven endpointLeft endpointRight =
      7 * residualRoot^7

  distinguished_eq :
    distinguished =
      7 * gapRoot * residualRoot

  coordinate_eq :
    cyclotomicSevenToTraceOne endpointLeft endpointRight =
      sevenAxis * root^7

  root_norm_eq :
    norm root = residualRoot
```

自然・signed の両 branch をここへ送れば、それ以降の RAMIFIED 証明は完全に一本化できます。

# 次 checkpoint

```text
FLT7-RAMIFIED-001
  common ramified summit packet
  + exact root-snd depth transfer
  + ramified second-coordinate factorization
```

現在の ROADMAP でも、TERM-010 後に残る独立境界は common ramified summit と明記されています。

## 現在地

```text
terminal away
  ├─ Row Sum → contradiction
  ├─ Row Y   → natural ramified
  └─ Row Z   → signed ramified

                    ↓ TERM-010 完成

primitive common ramified summit
  ├─ root.snd depth = 5 mod 7
  └─ new ramified 3×3 factor grid
```

TERM-010 によって、敵は二つの chart ではなく、**一つの ramified 魔核**になりました。

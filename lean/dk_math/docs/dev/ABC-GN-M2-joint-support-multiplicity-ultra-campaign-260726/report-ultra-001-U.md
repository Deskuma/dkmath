# Ultra-001 U 実装報告

## 判定

**Branch A：Exact GN-Wieferich / Petal / orientation bridge complete**

U-001T の exact repeated-part packet を、clean な GN-Wieferich 語彙と
cubic Petal primitive witness へ接続した。

これは large-boundary absorption や ABC の無条件証明ではない。
最後の oriented contract は raw ABC と同じ強さであることを監査した
API であり、contract 自体を無条件構成してはいない。

## Part A — generic GN-Wieferich layer

新規：

```text
DkMath/NumberTheory/GNWieferich.lean
```

実装：

- `GNWieferichLift`
- `primePow_dvd_GN_iff_primePow_dvd_diff`
- `GNWieferichLift_iff_diffLift`

正の `a,b`、`2 ≤ p`、素数 `q`、`q ∤ a` の下で、全ての深度 `k`
について

```text
q^k ∣ GN p a b
  ↔
q^k ∣ (a+b)^p - b^p
```

を得た。従って二段 lift の GN 表示と差冪表示は完全に同値である。

## Part B — exact target active support

新規：

```text
DkMath/ABC/GNWieferichAccumulation.lean
```

実装：

- `mem_GNExcessActivePrimeSet_target_iff_GNWieferichLift`
- `GNNonExceptionalWieferichPrimeSet`
- `GNNonExceptionalWieferichPrimeSet_eq_repeatedSupport`
- `GNNonExceptionalRepeatedPart_eq_wieferichPrimePowerProduct`
- `GNWieferichAccumulationPacket`
- `GNWieferichAccumulationPacket.of_target`

canonical interval family の正の coprime target では、

```text
q ∈ excess-active support
  ↔
q ∤ p ∧ GNWieferichLift p a b q
```

が成立する。

また、

```text
GNNonExceptionalRepeatedPart p a b
  =
∏ q ∈ GNNonExceptionalWieferichPrimeSet p a b,
  q ^ padicValNat q (GN p a b)
```

を証明した。従って T の large modulus は、全 nonexceptional
GN-Wieferich prime の完全な GN prime-power depth の積である。

## Part C — cubic Petal orientation

新規：

```text
DkMath/ABC/GNCubicPetalWieferich.lean
```

実装：

- `Triple.swap`
- swap による `c`、coprimality、ABC radical、pointwise conclusion の不変性
- `Triple.cubicReduced_or_swapReduced`
- `GNCubicPetalWieferichPacket`
- `exists_cubicPetalWieferichPacket_of_reduced`
- `exists_oriented_cubicPetalWieferichPacket`

任意の正の coprime Triple は、

```text
BoundaryD3Reduced T.c T.b
  or
BoundaryD3Reduced T.c T.a
```

を満たす。

選ばれた向きで既存の Zsigmondy/Petal witness を取り、同じ prime `q`
について次の分岐を証明した。

```text
NoLift:
  padicValNat q (GN 3 a b) ≤ 1

Lift:
  GNWieferichLift 3 a b q
  and
  q ∈ exact repeated support
```

全 primitive prime の NoLift や GN 全体の squarefreenessは仮定も主張も
していない。

## Part D — oriented cubic contract

新規：

```text
DkMath/ABC/GNCubicOrientedContract.lean
```

実装：

- `GNCubicOrientedJointBudgetAffine`
- `ABCGNCubicOrientedContract`
- `abc_positive_of_GNCubicOrientedContract`
- `ABCRawBound_of_GNCubicOrientedContract`
- `GNCubicOrientedContract_of_ABCRawBound`
- `ABCRawBound_iff_nonempty_GNCubicOrientedContract`

各 Triple で `T` または `T.swap` の cubic joint budget を選べる契約を
定義し、

```text
ABCRawBound ε
  ↔
Nonempty (ABCGNCubicOrientedContract ε)
```

を `0 < ε` の下で証明した。

逆向きは通常向きだけを使う監査である。これは oriented contract の
無条件構成が ABC 本体と同じ強さであることを再確認するものであり、
新しい無条件 ABC 証明ではない。

## 依存境界

U の新規 production module は次を import していない。

```text
CosmicPetalBridgeGNNoWieferichResearch
CosmicPetalBridgeGNNoWieferichDefault
CosmicPetalBridgeGNDescentBQuarantine
```

使用した Petal 経路は、

```text
BoundaryD3
ZsigmondyD3Bridge
PrimitiveD3ValuationBridge の clean NoLift theorem
```

のみである。

## 公開入口

`DkMath/ABC.lean` から `DkMath.ABC.GNCubicOrientedContract` を公開した。

## 検証

成功：

```text
lake build DkMath.NumberTheory.GNWieferich
lake build DkMath.ABC.GNWieferichAccumulation
lake build DkMath.ABC.GNCubicPetalWieferich
lake build DkMath.ABC.GNCubicOrientedContract
lake build DkMath.ABC
lake build DkMath
```

代表 endpoint の `#print axioms` は全て次のみだった。

```text
propext
Classical.choice
Quot.sound
```

新規 production code に `sorry`、`admit`、新規 `axiom`、
`native_decide` はない。

全体ビルドで表示される既存 research module の `sorry` warning は
今回の変更外であり、U endpoint の axiom 依存には現れない。

## 残る境界

未証明：

- Petal probe の反復による一様 support growth
- Wieferich lift accumulation の一様補償
- large-boundary sum absorption
- oriented pointwise packet から uniform raw ABC bound を無条件に構成すること
- `abc_main_axiom` の除去

従って次の戦場 U-001V は、

```text
iterate Petal probes
  →
NoLift support growth versus Wieferich lift growth
  →
large accumulation compensation
```

である。

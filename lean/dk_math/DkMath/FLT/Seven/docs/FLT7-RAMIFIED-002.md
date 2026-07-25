# FLT7-RAMIFIED-002

## FLT7-RAMIFIED-001 判定

**Outcome A、全面採用です。重大問題・実装 blocker はありません。** 🧙‍♀️✨️

公開 PR head も報告どおり、

```text
eb2528060e3899e8d4b5239e2ef7395e7fe094ac
```

へ更新されています。PR #65 は open / draft / mergeable です。

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5080562919)

なお、Lean CI run 353 は監査時点ではまだ `in_progress` です。ローカルの focused build・`DkMath.FLT.Seven` build 成功報告とは整合していますが、CI 完走判定だけはまだ保留です。

## 共通 summit の統合

`PrimitiveRamifiedSummitPacket` は、必要な情報を適切な強さで保持しています。

```text
endpointLeft / endpointRight / distinguished
gapRoot / residualRoot
quadratic root
endpoint coprimality
endpointRight の 7-unit 性
residualRoot の 7-unit 性
Fermat equation
7^6 gap split
7 residual split
distinguished factor
sevenAxis × seventh power
root norm
```

特に、

$$\operatorname{endpointLeft}^7-\operatorname{endpointRight}^7=\operatorname{distinguished}^7$$

という整数版に統一したことで、自然 Row-Y と signed Row-Z の違いが summit より下へ隠れました。

対応も正確です。

```text
Row Y:
  (endpointLeft, endpointRight, distinguished) = (z,x,y)

Row Z:
  (endpointLeft, endpointRight, distinguished) = (x,-y,z)
```

両 branch で exact split、primitive 性、root norm まで埋められています。

Row Sum は既存矛盾で消え、terminal packet から共通 summit が無条件で得られます。

## exact depth transfer

最も強い成果は予定どおり、

```lean
PrimitiveRamifiedSummitPacket.rootSnd_padicValNat
```

です。

まず exact second-coordinate equation、

$$\operatorname{seventhPowerSnd}(u,v)=7^6A^7Q$$

を、`sevenAxis` のキャンセルと gap expansion から構成しています。

その後、

$$\operatorname{seventhPowerSnd}(u,v)=7v,S(u,v)$$

と比較し、$S$ と $Q$ がともに $7$-unit であることを使って、

$$\boxed{v_7(|v|)=5+7v_7(A)}$$

を exact に得ています。

これは単なる、

```text
7^5 ∣ root.snd
```

ではありません。

```text
root.snd の深さは必ず 5 mod 7
```

という ramified summit 固有の保存核です。

## linear–cubic–cubic 分解

新しい三因子、

```lean
ramifiedLinear
ramifiedLeftCubic
ramifiedRightCubic
```

について、

$$\operatorname{ramifiedSeventhSnd}=T,L,R$$

が証明されました。

さらに、

$$R-L=7v,N(u,v)$$

$$L+R=(u-3v)(u+4v)T$$

も exact polynomial identity です。

second-coordinate equationとの接続により、

$$-ce(c+e)=T,L,R$$

まで到達しています。

## 一点だけ、用語境界

今回 Lean が構築したものは、厳密には、

```text
ramified 3×3 factor grid
```

または、

```text
3×3 routing candidate
```

です。

既存の正式な、

```lean
CoprimeTripleRouting
```

はまだ inhabit されていません。

現時点では未証明なのが、

```text
endpoint 三因子の非零・pairwise coprime
root 三因子の非零・pairwise coprime
natAbs product equality
CoprimeTripleRouting の構築
```

だからです。

したがって RAMIFIED-001 の実装内容に問題はありませんが、「3×3 routing board 完成」と呼ぶのは次 checkpoint 後が正確です。

## 露出した次の魔核

すでに証明された、

$$R-L=7v,N(u,v)$$

に、

$$v_7(|v|)=5+7v_7(A)$$

$$N(u,v)=B,\qquad7\nmid B$$

を入れると、次が直ちに見えます。

$$v_7(|R-L|)=6+7v_7(A)$$

一方、

$$c-e=7^6A^7$$

なので、

$$v_7(|c-e|)=6+7v_7(A)$$

です。

したがって次の theorem が本命です。

```lean
theorem PrimitiveRamifiedSummitPacket.cubicGap_depth_eq_endpointGap_depth :
    padicValNat 7
        (Int.natAbs
          (ramifiedRightCubic root.fst root.snd -
           ramifiedLeftCubic root.fst root.snd)) =
      padicValNat 7
        (Int.natAbs (endpointLeft - endpointRight))
```

すなわち、

$$\boxed{\text{endpoint gap と root-cubic gap は同じ exact 7-adic depth を持つ}}$$

です。

これは ramified 世界の自己相似核です。

## 次 checkpoint

```text
FLT7-RAMIFIED-002
ramified coprime triple routing
```

目標は次です。

```text
1. root coordinates の coprimality
2. T, L, R の非零性と 7-unit 性
3. T, L, R の pairwise coprimality
4. |c|, |e|, |c+e| の非零性と pairwise coprimality
5. natAbs endpoint/root product equality
6. RamifiedCubicRoutingPacket
7. endpoint-gap / root-cubic-gap exact depth synchronization
```

停止位置は、

```text
formal 3×3 routing packet 完成
+
gap depth synchronization 完成
```

です。

まだ小さい Fermat 解や descent provider は作りません。

**RAMIFIED-001 によって、一つの summit・一つの深さ保存則・一つの三因子魔核まで露出しました。次は、その魔核に九つの正式な住所を与える段階です。**

# FLT7-TERM-002

## FLT7-TERM-001／DESCENT 前監査

**TERM-001 の実装は採用。判定は Outcome C: exact missing bridges identified.**

対象コミット：

```text
45e6780cd5b9e79239a0c96b85eb5e9953287fe7
```

[PR レビューコメント](https://github.com/Deskuma/dkmath/pull/65#issuecomment-5075862345)

PR は open / draft / mergeable、Lean CI run 334 は **success** です。

## TERM-001 で完成したもの

terminal arithmetic は正しく三枝へ固定されました。

```text
Row Y
Row Z
Row Sum
```

各 profile は次を保持します。

```text
row の確定
endpoint = 7 × carrierUnit
ZMod 7 上の unit sign
cubic-root load の exact product identity
```

また、

```lean
AwaySevenBaseTerminalRowSensitiveDecisionPacket
```

が、

```text
row profile
endpoint quotient normal form
signed reconstruction outcome
```

を同時に保持しています。row を消さず、LIFT-003 の結果も失わない packaging は正しいです。

## DESCENT 前の不足 1：receiver が未充足

現在の receiver は、

```lean
rowY_impossible :
  AwaySevenBaseTerminalRowYProfile terminal → False

rowZ_impossible :
  AwaySevenBaseTerminalRowZProfile terminal → False

rowSum_impossible :
  AwaySevenBaseTerminalRowSumProfile terminal → False
```

を要求します。

しかし、この三定理を構成する証明はまだありません。したがって、

```lean
terminal_exclusion_of_receiver
```

は正しい conditional bridge ですが、**terminal exclusion 自体は未完成**です。

さらに、decision packet に保存した

```lean
AwaySevenBaseTerminalSignedReconstructionOutcome signed
```

は receiver の三条件には使われていません。

現状は、

```text
row arithmetic
+
reconstruction / obstruction
```

を並べたところまでで、両者を衝突させる定理はまだありません。

## 不足 2：receiver がまだ広すぎる

設計書では、receiver は「残った算術事実だけ」を表し、terminal exclusion 全体を言い換えてはならない、とされています。

現在の、

```text
RowYProfile → False
RowZProfile → False
RowSumProfile → False
```

は、実質的に row ごとの terminal exclusion です。

したがって、DESCENT 前に receiver を次のような小さい魔核へ縮約する必要があります。

```text
defect coordinate の strict bound
nonzero winding の不可能性
endpoint quotient と weighted reconstruction の不整合
特定因子の exact divisibility contradiction
```

有力なのは LIFT-003 の defect を使う形です。

$$M\mid d_i$$

に加えて、

$$|d_i|<M$$

を row ごとに証明できれば、既存の `integerWeightedDefect_eq_zero_of_abs_lt` により defect が消えます。

ただし、その後に reconstructed branch が各 row profile と矛盾する theorem も必要です。現在の資料からは、その矛盾はまだ証明されていません。

## 不足 3：base-layer から terminal exclusion への統合橋

terminal packet の constructor 自体はあります。

```lean
nonempty_awaySevenBaseTerminalUnitSectorPacket
```

は、`p.exponent = 1` から exact terminal packet を構成します。

一方、descent audit の terminal branch が保持するのは、

```lean
AwaySevenBaseLayerPacket p
AwaySevenTerminalExclusionStatement source p
```

です。

そのため、次のような end-to-end theorem が不足しています。

```lean
theorem no_terminal_base_layer_of_receiver
    (hreceiver :
      ∀ terminal : AwaySevenBaseTerminalUnitSectorPacket source r p,
        AwaySevenBaseTerminalArithmeticReceiver terminal)
    (layer : AwaySevenBaseLayerPacket p) :
    False
```

最終形はできれば receiver なしの、

```lean
theorem no_awaySevenBaseTerminalPacket
    (source : CounterexamplePack x y z)
    (r : AwayCubicRoutingPacket x y z)
    (p : AwaySevenPivotDepthPacket r)
    (hbase : p.exponent = 1) :
    False
```

です。

## 不足 4：lifted branch の closure provider

`AwayDescentClosureProvider` が必要とするデータは明確です。

```lean
nextX nextY nextZ : ℕ
nextPack  : CounterexamplePack nextX nextY nextZ
nextRoute : AwayValuationTransferPacket nextX nextY nextZ
carrier_match :
  nextRoute.carrier =
    Int.natAbs oldTransfer.normal.root.snd
```

現在の CRT／MODEL／LIFT／TERM 系列は、この `nextPack` をまだ構成していません。

つまり `1 < p.exponent` の branch は依然として、

```lean
liftedOpen
```

であり、

```lean
liftedClosed provider
```

にはなっていません。

### すでに足りているもの

provider が一度構成されれば、strict decrease は既存定理から自動で出ます。

```lean
away_depth_descent_of_closureProvider
```

したがって、新しい measure は不要です。

また、

```text
positivity
primitive normalization
FLT7 equation
```

は `nextPack` の構築責務に含まれます。

`nextRoute` が away normalization と valuation transfer を保持し、`carrier_match` が strict depth drop へ接続します。

## 推奨する次の順序

```text
FLT7-TERM-002
  row profile と reconstruction outcome を実際に接続
  receiver を exact arithmetic lemma へ縮約
  receiver を inhabit
  terminal depth-one branch を unconditional に排除
```

その後、

```text
FLT7-DESCENT-001
  liftedOpen から AwayDescentClosureProvider を構築
```

最後に、

```text
FLT7-DESCENT-002
  terminalOpen を contradiction で除去
  liftedOpen を liftedClosed へ変換
  AwaySevenPivotDescentAuditResult の全 away branch を閉じる
```

ROADMAP 自身も、recursive closure へ進む条件を「terminal result が unconditional、または最終 receiver が明確かつ独立にレビュー可能」としています。

## 結論

```text
TERM-001 decision packet     完成
row-sensitive data retention 完成
final arithmetic receiver    未縮約
receiver の証明              未完成
terminal exclusion           未完成
lifted closure provider       未構築
strict decrease theorem       完成済み
```

**現時点では DESCENT 本体へ進む前に、FLT7-TERM-002 を一枚挟むのが正しいです。** 現 receiver のまま DESCENT へ進むと、terminal branch を未解決のまま provider 側だけ構築する二重未閉路になります。

# Note: No.237 cp

## Status

## 現在地まとめ

いまの Collatz/PetalBridge 圧力解析は、**局所 pulse の存在・符号・高さの有限箱**まで来ている。

まだ Collatz 収束ではない。
ただし、局所構造としてはかなり見えるようになった。

大きく言うと、ここまでで

```text
局所 pulse の住所を W.val に正規化
  -> 非正・正・非正の sign pattern 化
  -> margin の有限高さ bound [-k, 2k]
```

まで到達した。

## 直近 checkpoint の流れ

## cp232 / cp233

ここは no-code audit。
Pulse diagnostic API は十分で、右 endpoint wrapper や branch-kind-preserving wrapper を機械的に増やさない判断をした。

ただし、この時点では「caller がないので追加しない」という判断が続き、攻めとしてはやや空振り気味だった。

## cp234

ここで球筋を変えた。

問題は caller 不在ではなく、

```text
Core は W.val で話している
Pulse は interval-pulse address で話している
```

という座標ズレだった。

そこで追加されたのが、

```lean
sourcePressureIntervalPulseAddress_of_localIslandWitness_start_eq
sourcePressureBeamPulse_witness_singleton_full_diagnostic_at_center
exists_sourcePressureBeamPulse_witness_center_full_diagnostic_of_seed
```

これにより singleton witness の Pulse diagnostic を、native depth `W.val` 中心で読めるようになった。

## cp235

cp234 の centered diagnostic を、margin sign へ変換した。

追加 theorem は、

```lean
exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
```

これにより、seed から witness `W` を取り出して、

```text
SourcePressureMarginInt n k (r + (W.val - 1)) ≤ 0
0 < SourcePressureMarginInt n k (r + W.val)
SourcePressureBeamAddressedDepthTarget L W.val
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

が言えるようになった。

つまり、`W.val` を中心に

```text
非正 -> 正 -> 非正
```

という局所 pulse が Lean theorem として見えるようになった。
添字規約も確定し、mass-balance at edge `j` は next margin `r + j + 1` を分類する、と整理された。

## cp236

cp235 で sign pattern が出たので、次に高さの有限箱を作った。

追加 theorem は、

```lean
sourcePressureMarginInt_le_two_mul_window
neg_window_le_sourcePressureMarginInt
sourcePressureMarginInt_bounds_window
```

これで任意の margin について、

```text
-k ≤ SourcePressureMarginInt n k r ≤ 2k
```

が使える。
これは **finite local Big bound**、つまり点ごとの有限高さの箱じゃ。

## いま言えていること

現時点で Lean 上に立った構造はこう。

```text
SourcePressureBeamSeed L
  -> ∃ W ∈ L,
       previous margin ≤ 0
       center margin > 0
       W.val is addressed depth target
       next margin ≤ 0
```

さらに、任意の margin は

```text
-k ≤ margin ≤ 2k
```

に入る。

したがって、seed が与える局所 pulse は、

```text
有限 window k の中で発生する
非正 -> 正 -> 非正 の孤立正圧イベント
```

として読める。

## まだ言えていないこと

ここは大事。

まだ言えていないのは、

```text
pulse がどれだけ連鎖するか
positive run がどれだけ続くか
net drop がどれだけ跳ぶか
window family を覆えるか
時間方向へ伝播するか
全軌道が下降するか
Collatz 予想が従うか
```

じゃ。

いまは **局所 Core** が見えた段階。
Beam、つまり伝播・連鎖・大域支配はまだこれから。

## DkMath 的な整理

いまの構図はこう。

```text
Core:
  W.val 中心の局所 pulse
  margin sign pattern
  finite height box [-k, 2k]

Beam:
  その pulse が深さ方向・時間方向へどう連鎖するか
  まだ未解析

Gap:
  net drop の有限 jump bound
  positive run / pulse family / propagation
  まだ未支配
```

つまり、現在は

```text
Core がかなり固まった
Beam へ入る前の jump bound が次
```

という段階じゃ。

## 次の本命

次は **net drop の有限ジャンプ箱**。

cp236 で高さは包めた。

```text
margin ∈ [-k, 2k]
```

次に欲しいのは、

```text
net drop ∈ [-3k, 3k]
```

のような遷移幅 bound。

対象はこれ。

```lean
SourceRetentionDropInt
SourceContinuationDropInt
SourcePressureNetDropInt
```

狙いは、

```text
RetentionDrop, ContinuationDrop は [-k, k]
NetDrop は [-3k, 3k]
```

を立てること。

これが通ると、

```text
局所 pulse の高さも有限
隣接遷移のジャンプ幅も有限
```

となり、local Big の輪郭がかなりはっきりする。

## 総合判断

ここ数手は、かなり良い流れ。

```text
cp234:
  座標正規化

cp235:
  sign transition 化

cp236:
  finite height box 化

next:
  finite jump box 化
```

もう一度言うが、まだ大域収束ではない。
しかし、局所 pressure の「形」「高さ」「次に狙うべき跳び幅」までは見えた。

ここからは、**局所 Core を有限箱で包み、Beam 伝播へ渡す準備段階**じゃ。

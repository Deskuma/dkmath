# Prime mirror energy 実装開始 checkpoint

cid: `6a7469f9-7968-83e8-bd4d-a5f044d2ee1a`

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
base: wip/RH-CFBRC-moving-line-collision-260805-v2
```

設計正本は次である。

[PPW-000-Pascal-prime-wave-CFBRC-energy-bridge-design.md](./PPW-000-Pascal-prime-wave-CFBRC-energy-bridge-design.md)

本 checkpoint では設計の Phase A と Phase B を先行実装した。

## 2. 追加 module

```text
DkMath.RH.CFBRC.PrimeMirrorOffsetCore
DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
DkMath.RH.CFBRC.PrimeMirrorEnergy
```

`PrimeMirrorEnergy` は前二 module の入口である。現時点では `DkMath.RH` root へ import していない。単体 Green を確認した後に export を判断する。

## 3. Phase A の内容

一つの整数 mode `n` と横 offset `δ` に対して、左右 mirror amplitude を次で定義した。

$$
a_n(\delta):=\exp(-\delta\log n)
$$

$$
b_n(\delta):=\exp(\delta\log n)
$$

実装済み候補 theorem は次である。

```lean
primeMirrorAmplitude_mul_eq_one
primeMirrorOffsetGap_nonneg
primeMirrorOffsetGap_eq_zero_iff_delta_eq_zero
primeMirrorOffsetGap_pos_of_delta_ne_zero
primeMirrorOffsetState_interaction_eq_two
primeMirrorOffsetState_minusWhole_eq_gap
primeMirrorOffsetState_squareMass_eq_two_add_gap
primeMirrorOffsetGapAt_eq_zero_iff_re_eq_half
primeMirrorOffsetGapAt_pos_of_re_ne_half
```

数学的 Core は次である。

$$
a_nb_n=1
$$

$$
2a_nb_n=2
$$

$$
a_n^2+b_n^2=2+(a_n-b_n)^2
$$

`1 < n` では次が成立する。

$$
(a_n-b_n)^2=0\iff\delta=0
$$

## 4. Phase B の内容

有限 mode 集合 `S` と weight に対して、座標 energy を次で定義した。

$$
E_S(\delta):=\sum_{n\in S}w_n\bigl(a_n(\delta)-b_n(\delta)\bigr)^2
$$

実装済み候補 theorem は次である。

```lean
primeMirrorEnergy_nonneg
primeMirrorEnergy_mode_le
primeMirrorEnergy_pos_of_mode
primeMirrorEnergy_eq_zero_iff_delta_eq_zero
primeMirrorEnergyAt_eq_zero_iff_re_eq_half
primeMirrorEnergyAt_pos_of_re_ne_half
primeMirrorEnergyUpTo_succ_sub
primeMirrorEnergyUpTo_succ_eq
```

最後の二 theorem は `(N, N + 1)` 観測窓の最小 Core である。

$$
E_{N+1}(\delta)-E_N(\delta)
=w_NG_N(\delta)
$$

これにより、累積 energy の隣接差分から新しく追加された mode energy を exact に復元する。

## 5. 妥当性境界

この checkpoint は次を主張しない。

1. `S` が Pascal から生成されること
2. weight が Mangoldt weight と一致すること
3. finite energy が PHZ または Euler-zeta observation と一致すること
4. 非自明零点から energy collapse が得られること
5. RH または既存 research `sorry` が閉じたこと

現段階は off-critical positive Core と隣接差分 decoder の型を置いたところである。

## 6. Codex build handoff

最初に次を単体確認する。

```bash
lake env lean DkMath/RH/CFBRC/PrimeMirrorOffsetCore.lean
lake env lean DkMath/RH/CFBRC/PrimeMirrorFiniteEnergy.lean
lake env lean DkMath/RH/CFBRC/PrimeMirrorEnergy.lean
```

細かな Mathlib API、`change` の elaboration、`simp` の正規形、暗黙引数の推論は build 結果に従って修正する。

修正時に数学的 statement を弱めない。特に次を保持する。

1. mirror amplitude の積は exact に `1`
2. interaction は exact に `2`
3. Gap zero の逆向きは `1 < n` を要求する
4. finite energy の正値は一つ以上の正 weight mode を要求する
5. energy は座標平方和であり、複素総和の norm-square ではない

`PrimeMirrorEnergy` の単体 Green 後、`DkMath.RH` root import を追加する。

## 7. 次の bridge

次の実装候補は、既存の次の定理を新 Core へ接続することである。

```lean
etaMirrorAmplitudeRatio_eq_rpow
etaEndpointIncrementMirrorRatio_eq_etaMirrorAmplitudeRatio
etaEndpointIncrementDecoder_eq_centeredSigma
```

既存 eta endpoint increment は `(N, N + 1)` により一項を exact に復元している。新 Core では、その mirror amplitude ratio を左右 amplitude pair の比として読み直す。

目標形は概念的に次である。

$$
\frac{b_n(\delta)}{a_n(\delta)}
=\exp(2\delta\log n)
=n^{2\delta}
$$

この bridge が Green になれば、現在の eta increment decoder と prime mirror offset Core が同じ centered coordinate を読むことが確認できる。

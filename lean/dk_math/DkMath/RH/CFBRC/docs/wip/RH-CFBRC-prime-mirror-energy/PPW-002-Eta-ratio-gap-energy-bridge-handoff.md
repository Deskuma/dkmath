# Eta ratio-gap energy bridge 実装指示

cid: `6a7469f9-7968-83e8-bd4d-a5f044d2ee1a`

## 1. 対象

```text
repository: Deskuma/dkmath
branch: wip/RH-CFBRC-prime-mirror-energy-260807-v0
previous checkpoint: PPW-001-Prime-mirror-energy-implementation-checkpoint.md
```

PPW-001 で予定していた eta endpoint increment と prime mirror offset Core の座標一致は、次の module に実装された。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaBridge
```

主要 theorem は次である。

```lean
primeMirrorAmplitudeRatio_eq_rpow
primeMirrorAmplitudeRatio_eq_etaMirrorAmplitudeRatio
etaEndpointIncrementMirrorRatio_eq_primeMirrorAmplitudeRatio
etaEndpointIncrementDecoder_eq_primeMirrorCenteredOffset
```

## 2. レビュー結果

### 2.1 同じ centered coordinate を読んでいる

prime mirror pair の比は次である。

$$
\frac{b_{m+1}(\delta)}{a_{m+1}(\delta)}=(m+1)^{2\delta}
$$

eta endpoint increment の mirror/original norm ratio も、`δ = centeredSigma s.re` において同じ値になる。

したがって、prime mirror Core と eta endpoint increment decoder は、別々の仮想座標ではなく同じ centered coordinate を exact に読んでいる。

### 2.2 `(N, N + 1)` の添字は整合している

`etaEndpointIncrement N s` は、finite endpoint の隣接差分から `etaSignedVector s N` を復元する。その正の底は `N + 1` である。

新 bridge でも prime mirror amplitude の底を `N + 1` としているため、index shift は一致している。

### 2.3 循環はない

新 module は `NontrivialRiemannZetaZero`、`RiemannHypothesis`、RH-equivalent provider を仮定していない。既存の eta 一項 norm identity と実指数の恒等式を接続した純粋な decoder bridge である。

### 2.4 現在まだ得ていないもの

現在得られたのは ratio と centered coordinate の一致であり、prime mirror offset Gap または finite energy と eta endpoint observation の同一性までは未実装である。

次は ratio から非負 Gap を構成し、その Gap が既存の `primeMirrorOffsetGap` と exact に一致することを証明する。

## 3. 次の数学的 Core

正の mirror amplitude `a`, `b` が次を満たすとする。

$$
ab=1
$$

ratio を `r = b / a` とすると、次が成立する。

$$
r+r^{-1}-2=(a-b)^2
$$

したがって eta endpoint increment ratio だけから、prime mirror offset Gap を復元できる。

$$
\mathrm{EtaGap}_N(s):=R_N(s)+R_N(s)^{-1}-2
$$

ここで、

$$
R_N(s):=\mathrm{etaEndpointIncrementMirrorRatio}(s,N)
$$

目標 identity は次である。

$$
\mathrm{EtaGap}_N(s)=\mathrm{primeMirrorOffsetGap}(N+1,\mathrm{centeredSigma}(s.re))
$$

これにより ratio decoder から、CF2D の difference whole と同じ非負 energy へ進める。

## 4. 新規 module

次を追加する。

```text
DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
```

推奨 import は次である。

```lean
import DkMath.RH.CFBRC.PrimeMirrorEtaBridge
import Mathlib.Tactic
```

namespace は既存と同じものを使う。

```lean
namespace DkMath.RH.CFBRCProjection
```

## 5. 実装対象

### 5.1 Eta ratio-gap

```lean
noncomputable def etaEndpointIncrementMirrorGap
    (s : ℂ) (N : ℕ) : ℝ :=
  etaEndpointIncrementMirrorRatio s N +
    (etaEndpointIncrementMirrorRatio s N)⁻¹ - 2
```

ratio が正であることを先に証明する。

```lean
theorem etaEndpointIncrementMirrorRatio_pos
    (s : ℂ) (N : ℕ) :
    0 < etaEndpointIncrementMirrorRatio s N
```

既存の `etaEndpointIncrementMirrorRatio_eq_primeMirrorAmplitudeRatio` と `Real.exp_pos` を再利用してよい。

### 5.2 Ratio-gap と prime mirror Gap の一致

中心 theorem は次の形とする。

```lean
theorem etaEndpointIncrementMirrorGap_eq_primeMirrorOffsetGap
    (s : ℂ) (N : ℕ) :
    etaEndpointIncrementMirrorGap s N =
      primeMirrorOffsetGap (N + 1) (centeredSigma s.re)
```

証明では、prime mirror left/right amplitude を `a`, `b` と読み、次を使用する。

```lean
primeMirrorAmplitude_mul_eq_one
primeMirrorLeftAmplitude_pos
primeMirrorRightAmplitude_pos
etaEndpointIncrementMirrorRatio_eq_primeMirrorAmplitudeRatio
```

`field_simp`、`ring`、積が `1` であることによる書き換えを使ってよい。数学的 statement を近似式へ弱めない。

### 5.3 非負性と零点一意性

```lean
theorem etaEndpointIncrementMirrorGap_nonneg
    (s : ℂ) (N : ℕ) :
    0 ≤ etaEndpointIncrementMirrorGap s N
```

底 `N + 1` が非定数になるため、臨界線の特徴付けでは `0 < N` を要求する。

```lean
theorem etaEndpointIncrementMirrorGap_eq_zero_iff_re_eq_half
    {N : ℕ} (hN : 0 < N) (s : ℂ) :
    etaEndpointIncrementMirrorGap s N = 0 ↔
      s.re = (1 : ℝ) / 2
```

```lean
theorem etaEndpointIncrementMirrorGap_pos_of_re_ne_half
    {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < etaEndpointIncrementMirrorGap s N
```

`N = 0` は底 `1` となり、任意の offset で Gap が零になるため、逆向き theorem から除外する。

### 5.4 Eta-indexed finite energy

eta index `m` の底が `m + 1` であることを定義に保持する。

```lean
noncomputable def etaEndpointIncrementMirrorEnergyUpTo
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m in Finset.range M,
    weight m * etaEndpointIncrementMirrorGap s m
```

prime mirror 表示も同じ eta index で定義する。

```lean
noncomputable def etaIndexedPrimeMirrorEnergyUpTo
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) : ℝ :=
  ∑ m in Finset.range M,
    weight m *
      primeMirrorOffsetGap (m + 1) (centeredSigma s.re)
```

両者の exact equality を証明する。

```lean
theorem etaEndpointIncrementMirrorEnergyUpTo_eq_primeMirrorEnergy
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight M s =
      etaIndexedPrimeMirrorEnergyUpTo weight M s
```

### 5.5 `(M, M + 1)` energy increment

```lean
@[simp]
theorem etaEndpointIncrementMirrorEnergyUpTo_succ_sub
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight (M + 1) s -
        etaEndpointIncrementMirrorEnergyUpTo weight M s =
      weight M * etaEndpointIncrementMirrorGap s M
```

```lean
@[simp]
theorem etaEndpointIncrementMirrorEnergyUpTo_succ_eq
    (weight : ℕ → ℝ) (M : ℕ) (s : ℂ) :
    etaEndpointIncrementMirrorEnergyUpTo weight (M + 1) s =
      etaEndpointIncrementMirrorEnergyUpTo weight M s +
        weight M * etaEndpointIncrementMirrorGap s M
```

これは endpoint の `(N, N + 1)` decoder と energy の `(M, M + 1)` decoder を同じ index discipline に置く theorem である。

### 5.6 固定 base-two mode による off-critical 下界

後の極限衝突では、全 cutoff に共通する一つの正 mode が必要になる。eta index `1` は底 `2` を表す。

少なくとも次の lower-bound theorem を置く。

```lean
theorem etaEndpointIncrementMirrorEnergy_mode_one_le
    {weight : ℕ → ℝ} {M : ℕ} {s : ℂ}
    (hM : 2 ≤ M)
    (hweight : ∀ m < M, 0 ≤ weight m) :
    weight 1 * etaEndpointIncrementMirrorGap s 1 ≤
      etaEndpointIncrementMirrorEnergyUpTo weight M s
```

さらに `0 < weight 1` と off-critical 条件から正値を得る。

```lean
theorem etaEndpointIncrementMirrorEnergy_pos_of_re_ne_half
    {weight : ℕ → ℝ} {M : ℕ} {s : ℂ}
    (hM : 2 ≤ M)
    (hweight : ∀ m < M, 0 ≤ weight m)
    (hweightOne : 0 < weight 1)
    (hre : s.re ≠ (1 : ℝ) / 2) :
    0 < etaEndpointIncrementMirrorEnergyUpTo weight M s
```

実装しやすい同値な仮定形へ調整してよい。ただし base-two mode が cutoff 全体に共通する一様な正 obstruction を与える構造を保持する。

## 6. 入口と export

単体 Green 後、次を更新する。

```text
DkMath.RH.CFBRC.PrimeMirrorEnergy
DkMath.RH
```

追加 import は次である。

```lean
import DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
```

循環 import が生じる場合は root export を最後に行う。

## 7. Build checkpoint

```bash
lake env lean DkMath/RH/CFBRC/PrimeMirrorEtaEnergyBridge.lean
lake env lean DkMath/RH/CFBRC/PrimeMirrorEnergy.lean
lake env lean DkMath/RH.lean
```

可能なら次も実行する。

```bash
lake build DkMath.RH.CFBRC.PrimeMirrorEtaEnergyBridge
lake build DkMath.RH
```

新規 module に `sorry`、`axiom`、`admit` を残さない。

## 8. 妥当性境界

この実装では次を主張しない。

1. eta finite endpoint の総和が零なら各 ratio-gap が零になること
2. 非自明零点から finite energy collapse が得られること
3. weight が Pascal または Mangoldt 由来であること
4. standard zeta zero と prime-coordinate energy の同一性
5. RH または既存 research goal の閉鎖

この段階の成果は、eta endpoint increment が読む mirror ratio と、prime mirror Core の difference whole を、同じ非負 energy object として exact に接続することである。

## 9. 完了報告に含めるもの

1. 追加・変更した file
2. Green になった theorem 一覧
3. index shift `N ↦ N + 1` の扱い
4. `N = 0` を零点一意性から除外した理由
5. base-two mode lower bound の statement
6. 実行した build command と結果
7. 残る warning または linter 指摘

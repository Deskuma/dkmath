# 0011 — Eta critical mirror endpoint の energy collapse と outer normalization

## 1. この文書の位置づけ

`0010-Eta-critical-mirror-endpoint-limits.md` では、非実な standard nontrivial Riemann-zeta zero `s` とその same-height critical mirror `criticalMirror s` に対して、同一 truncation index `N` を用いる genuine finite eta endpoint が双方とも `0` へ収束することを固定した。

本書では、その二本の endpoint を有限 pair として読み直し、対称成分・反対称成分・total energy・Big・Gap を導入したときに何が Lean Core として従うかを記録する。

主対象は次の三モジュールである。

```text
DkMath.RH.CFBRC.EtaMirrorEndpointPairEnergy
DkMath.RH.CFBRC.EtaMirrorEndpointOuterNormalization
DkMath.RH.CFBRC.EtaCriticalMirrorEnergyCollapse
```

この層で重要なのは、単に `Gap → 0` を得ることではない。

むしろ、endpoint Gap の消失は original / mirror endpoint の双方が `0` へ行くことから自動的に起こるため、それだけでは臨界線を選別できない、という負の audit まで Lean 上で明確になっている。

---

## 2. original / mirror endpoint を一つの有限 pair として読む

各 truncation `N` と複素数 `s` に対し、二つの endpoint

```lean
etaPartialEndpoint N s
etaPartialEndpoint N (criticalMirror s)
```

を一組として扱う。

その symmetric center と antisymmetric offset は次で定義される。

```lean
etaMirrorEndpointCenter N s
etaMirrorEndpointOffset N s
```

一般の pair decomposition を用いて、original endpoint は center と offset の和、mirror endpoint は center と offset の差として exact に復元される。

```lean
theorem etaMirrorEndpointCenter_add_offset ...
theorem etaMirrorEndpointCenter_sub_offset ...
```

したがって、この段階には極限もゼータ関数の零点条件も必要ない。

これは有限複素ベクトル二本に対する純粋な algebraic Core である。

---

## 3. Total Energy / Big / Gap

有限 endpoint pair に対し、次の三つの非負実数値を定義する。

```lean
etaMirrorEndpointTotalEnergy N s
etaMirrorEndpointBig N s
etaMirrorEndpointGap N s
```

意味はそれぞれ次である。

- `TotalEnergy` は original と mirror の squared norm の和。
- `Big` は original と mirror の和の squared norm。
- `Gap` は original と mirror の差の squared norm。

式で書けば、`a = etaPartialEndpoint N s`、`b = etaPartialEndpoint N (criticalMirror s)` としたとき、概念的には

$$
T_N=\|a\|^2+\|b\|^2
$$

$$
B_N=\|a+b\|^2
$$

$$
G_N=\|a-b\|^2
$$

である。

Lean では parallelogram identity が exact finite theorem として固定されている。

```lean
theorem etaMirrorEndpointBig_add_gap_eq_two_mul_totalEnergy
    (N : ℕ) (s : ℂ) :
    etaMirrorEndpointBig N s + etaMirrorEndpointGap N s =
      2 * etaMirrorEndpointTotalEnergy N s
```

すなわち、有限段階ごとに

$$
B_N+G_N=2T_N
$$

が成立する。

ここにも analytic continuation や RH は使われない。

---

## 4. endpoint 二本がともに 0 へ行けば全 absolute energy が潰れる

`EtaMirrorEndpointPairEnergy` は次の一般 theorem を持つ。

```lean
theorem etaMirrorEndpointBig_tendsto_zero_of_endpoint_limits ...
theorem etaMirrorEndpointGap_tendsto_zero_of_endpoint_limits ...
theorem etaMirrorEndpointTotalEnergy_tendsto_zero_of_endpoint_limits ...
```

仮定は original endpoint と mirror endpoint の双方が `0` へ収束することだけである。

すると連続性により、その和、差、および squared norm も `0` へ収束する。

したがって

$$
a_N\to0,\quad b_N\to0
$$

ならば

$$
T_N\to0,\quad B_N\to0,\quad G_N\to0
$$

が自動的に従う。

`0010` で standard nontrivial zero に対して original / mirror endpoint の零極限が得られているので、`EtaCriticalMirrorEnergyCollapse` はこれをそのまま package する。

```lean
structure EtaCriticalMirrorEnergyCollapse (s : ℂ) : Prop where
  totalEnergy : ... → 0
  core : ... → 0
  gapCore : ... → 0
  outerBig : ... → 0
```

実際、次の theorem が証明済みである。

```lean
theorem etaCriticalMirrorEnergyCollapse_of_nontrivialRiemannZetaZero
    {s : ℂ} (hs : NontrivialRiemannZetaZero s) (him : s.im ≠ 0) :
    EtaCriticalMirrorEnergyCollapse s
```

したがって、この energy collapse は standard zeta zero から無条件に得られる Lean Core である。

---

## 5. endpoint Big / Gap を inner Core / GapCore として再配置する

絶対量 `Big` と `Gap` は両方とも `0` へ崩壊する。

このため `EtaMirrorEndpointOuterNormalization` では、既存の endpoint `Big` を inner `Core`、endpoint `Gap` を inner `GapCore` として読み替え、その二つを一つの共通 outer Big の中で比較する。

```lean
etaMirrorEndpointCore N s
etaMirrorEndpointGapCore N s
etaMirrorEndpointOuterBig N s
```

定義上、

```lean
etaMirrorEndpointCore N s = etaMirrorEndpointBig N s
etaMirrorEndpointGapCore N s = etaMirrorEndpointGap N s
```

であり、共通 denominator は

$$
O_N=C_N+G_N
$$

として定義される。

Lean theorem は次である。

```lean
theorem etaMirrorEndpointOuterBig_eq_core_add_gapCore ...
```

さらに parallelogram identity により

```lean
theorem etaMirrorEndpointOuterBig_eq_two_mul_totalEnergy ...
```

すなわち

$$
O_N=2T_N
$$

も exact に成立する。

したがって standard nontrivial zero では `T_N → 0` から `O_N → 0` も従う。

---

## 6. 共通 denominator による share

inner Core と GapCore を別々の尺度で割るのではなく、同じ outer Big で割る。

```lean
etaMirrorEndpointCoreShare N s
etaMirrorEndpointGapShare N s
```

通常の実数除算としては

$$
\operatorname{CoreShare}_N=\frac{C_N}{O_N}
$$

$$
\operatorname{GapShare}_N=\frac{G_N}{O_N}
$$

である。

`O_N ≠ 0` のときは

```lean
theorem etaMirrorEndpointCoreShare_add_gapShare ... :
    etaMirrorEndpointCoreShare N s + etaMirrorEndpointGapShare N s = 1
```

が成立する。

また `O_N > 0` のとき、両 share は非負である。

ここで重要なのは、standard nontrivial zero に沿って outer Big 自体が `0` へ収束することである。

したがって absolute energy collapse の極限点では、通常の real division による share を単純に `0 / 0` の比として解釈してはならない。

---

## 7. StructuralRatio による total share と `0 / 0` audit

`EtaMirrorEndpointOuterNormalization` は total expression

$$
\frac{C_N+G_N}{O_N}
$$

について、numerator と denominator が定義上同じ source expression であることを `DkMath.KUS.StructuralRatioWitness` として保持する。

```lean
etaMirrorEndpointTotalStructuralRatio N s
etaMirrorEndpointTotalStructuralShare N s
```

その structural share は denominator の数値が zero かどうかに依存せず、構造上 `1` として保持される。

```lean
@[simp] theorem etaMirrorEndpointTotalStructuralShare_eq_one ...
```

これは ordinary real division の `0 / 0 = 1` を主張する theorem ではない。

実際、ordinary division との一致は明示的に

```lean
hOuter : etaMirrorEndpointOuterBig N s ≠ 0
```

を要求する。

さらに collapsed outer Big に対しては offset regularization

```lean
etaMirrorEndpointRegularizedTotalShare N s ε
```

を導入し、punctured neighborhood または positive side から `ε → 0` とすると structural unit value `1` へ行くことを証明している。

したがって現行実装は、

- source-level self-ratio
- ordinary real division
- regularized limit

を意図的に区別している。

この区別は `0 / 0` の不正な代入を避けるための重要な audit firewall である。

---

## 8. 臨界線上では GapCore は有限段階ごとに exact zero

critical mirror geometry から

$$
\operatorname{criticalMirror}(s)=s
$$

と

$$
\Re(s)=\frac12
$$

は同値である。

そのため臨界線上では original endpoint と mirror endpoint は有限 `N` ごとに同一対象となり、差の squared norm である GapCore は exact に zero となる。

```lean
theorem etaMirrorEndpointGapCore_eq_zero_of_re_eq_half
    (N : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    etaMirrorEndpointGapCore N s = 0
```

さらに

```lean
theorem etaMirrorEndpointOuterBig_eq_core_of_re_eq_half ...
theorem etaMirrorEndpointGapShare_eq_zero_of_re_eq_half ...
```

があり、outer Big が非零なら Core share は `1` になる。

ここでは方向に注意が必要である。

臨界線なら finite GapCore は exact zero である。

しかし standard nontrivial zero から得られる `GapCore → 0` だけでは臨界線は従わない。

---

## 9. 最重要 audit: endpoint Gap collapse は臨界線検出器ではない

この文書で最も重要な負の事実はここである。

standard nontrivial zero `s` とその critical mirror の eta endpoint は両方とも `0` へ収束する。

したがって endpoint difference も自動的に `0` へ収束し、その squared norm である endpoint Gap も自動的に `0` へ収束する。

しかしこれは `criticalMirror s = s` を意味しない。

つまり

$$
G_N\to0
$$

は、ここでは二本の shrinking vectors が同じ原点へ消える結果として起こりうる。

そのため `EtaMirrorEndpointPairEnergy` 自身が次の candidate coupling を独立した命題として隔離している。

```lean
def EtaMirrorEndpointGapControlsUnitGapAt (s : ℂ) : Prop :=
  Tendsto (fun N : ℕ => etaMirrorEndpointGap N s) atTop (nhds 0) →
    etaMirrorUnitGap s 1 = 0
```

`etaMirrorUnitGap` は endpoint の absolute difference ではなく、term-amplitude 側の critical-line decoder である。

さらに、original / mirror endpoint が既に双方 `0` へ行く状況では、Lean はこの coupling が臨界線条件そのものと同値であることを証明している。

```lean
theorem etaMirrorEndpointGapControlsUnitGapAt_iff_re_eq_half ... :
    EtaMirrorEndpointGapControlsUnitGapAt s ↔
      s.re = (1 : ℝ) / 2
```

したがってこの coupling を独立に仮定して RH を閉じることは、新しい証明内容を追加したことにはならない。

それはまさに load-bearing condition を別名で置いたことになる。

この theorem は、endpoint Gap route の論理的限界を明示する Obstruction / audit theorem と読むべきである。

---

## 10. Core / Gap / Obstruction の整理

### Core

現時点で Lean により固定されている事実は次である。

1. original / mirror endpoint pair の center-offset decomposition。
2. TotalEnergy / Big / Gap の有限 exact 定義。
3. parallelogram identity `Big + Gap = 2 * TotalEnergy`。
4. endpoint 二本が `0` へ行けば TotalEnergy / Big / Gap もすべて `0` へ行く。
5. standard nontrivial zero ではその energy collapse が成立する。
6. Big と Gap を inner Core / GapCore として共通 outer Big に載せられる。
7. outer Big は `2 * TotalEnergy`。
8. structural total share は source equality により常に `1`。
9. ordinary numeric shares の和が `1` になるのは outer Big 非零時。
10. critical line 上では finite GapCore が全 `N` で exact zero。

### Gap

まだ必要なのは、off-critical な mirror pair を排除する追加機構である。

単なる endpoint Gap collapse はこの役割を果たさない。

### Obstruction / audit

`EtaMirrorEndpointGapControlsUnitGapAt` は、その不足を term-amplitude `UnitGap` へ押し込む candidate bridge である。

しかし endpoint zero limits の下では、その candidate bridge は `s.re = 1/2` と同値である。

よってこれは独立な解析 bridge として無料で導入できる仮定ではない。

---

## 11. この段階で言ってよいこと／まだ言ってはいけないこと

言ってよいことは次である。

> standard nontrivial zeta zero とその critical mirror では、genuine finite eta endpoint の absolute pair-energy coordinates がすべて zero へ collapse する。

また、

> critical line 上では endpoint GapCore は有限 truncation ごとに exact zero である。

とも言える。

一方、まだ次は言えない。

> endpoint Gap が zero へ収束するから `s` は critical line 上にある。

この推論は成立しない。

両 endpoint 自体が zero へ shrink するため、off-critical pair でも absolute difference が消える可能性を排除していないからである。

したがって次の文書では、absolute endpoint collapse 後にも位置情報を失わないために導入された normalization / moving-frame / relative-carrier 系の次の依存層を読む必要がある。

---

## 12. 依存関係の現在地

この時点までの流れは次である。

```text
standard nontrivial zeta zero
  ↓
critical mirror も standard nontrivial zeta zero
  ↓
original / mirror genuine eta endpoints → 0
  ↓
TotalEnergy / Big / Gap → 0
  ↓
Core / GapCore / outer Big → 0
  ↓
absolute quantitiesだけでは位置情報を失う
  ↓
relative / normalized / moving-frame 構造が必要
```

`0011` の役割は、energy collapse を成果として記録すると同時に、**なぜ `Gap → 0` だけでは RH を閉じられないのか**を Lean の theorem 構造そのものから固定することにある。

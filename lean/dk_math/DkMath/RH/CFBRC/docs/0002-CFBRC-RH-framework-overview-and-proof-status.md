# DkMath.RH.CFBRC Framework 全体構造と証明到達点

## 1. 文書の目的

この文書は、`DkMath.RH.CFBRC` Framework によるリーマン予想形式化について、現在の全体構造、証明済みの Core、抽象 bridge、標準ゼータ関数との接続、および未解決の Gap を整理する。

本書は個々の補題の詳細解説ではなく、形式化全体を俯瞰するための地図である。

対象 branch は次のとおり。

```text
repository: Deskuma/dkmath
branch: docs/RH-CFBRC-260806-v0
root: lean/dk_math/DkMath/RH/CFBRC
```

## 2. 全体の論理構造

現在の CFBRC による RH 形式化は、大きく次の三層に分かれる。

```text
Layer A:
  CFBRC の零点幾何

Layer B:
  標準リーマンゼータ関数の非自明零点との bridge

Layer C:
  Mathlib の RiemannHypothesis への最終接続
```

集合として書けば、次の三つを考える。

$$
Z_{\mathrm{nt}}:=\{s\in\mathbb C\mid \operatorname{NontrivialRiemannZetaZero}(s)\}
$$

$$
Z_{\mathrm{CFBRC}}:=\{s\in\mathbb C\mid \operatorname{offCriticalCFBRC}(d,s.re,\phi(s))=0\}
$$

$$
L_{1/2}:=\{s\in\mathbb C\mid s.re=1/2\}
$$

CFBRC 側では、正次数 `d` に対して次が証明済みである。

$$
Z_{\mathrm{CFBRC}}=L_{1/2}
$$

Mathlib のリーマン予想は、DkMath の局所 predicate を使えば次と同値である。

$$
\operatorname{RiemannHypothesis}
\iff
Z_{\mathrm{nt}}\subseteq L_{1/2}
$$

したがって、CFBRC route の最終的な主 Gap は次の包含である。

$$
Z_{\mathrm{nt}}\subseteq Z_{\mathrm{CFBRC}}
$$

## 3. CFBRC の零点幾何

### 3.1 基本 module

```text
DkMath.RH.CFBRC.OffCriticalExclusionGeneral
```

主要 theorem は次の二つである。

```lean
cfbrcR_eq_zero_iff_x_eq_zero

offCriticalCFBRC_eq_zero_iff_re_eq_half
```

### 3.2 一般次数 CFBRC の零点

`cfbrcR_eq_zero_iff_x_eq_zero` は、任意の正次数 `d` に対して次を証明する。

$$
\operatorname{cfbrcR}(d,X,\Theta)=0
\iff
X=0
$$

Lean の型は次の形である。

```lean
theorem cfbrcR_eq_zero_iff_x_eq_zero
    {d : ℕ} (hd : 0 < d) (X Θ : ℝ) :
    cfbrcR d X Θ = 0 ↔ X = 0
```

証明では、複素数等式

$$
(X+i\Theta)^d=(i\Theta)^d
$$

から両辺のノルムを比較する。正の自然数冪を消去した後、ノルム平方を比較すると次が得られる。

$$
X^2+\Theta^2=\Theta^2
$$

したがって `X = 0` である。

この theorem はゼータ関数に依存しない。CFBRC 自体の代数的・幾何学的 Core である。

### 3.3 臨界線への中心化

`offCriticalCFBRC` は実部を `centeredSigma` によって中心化する。

概念的には次の座標を使う。

$$
X=\sigma-\frac12
$$

そのため、一般零点 theorem と中心化零点 theorem を合成すると次が得られる。

$$
\operatorname{offCriticalCFBRC}(d,\sigma,\Theta)=0
\iff
\sigma=\frac12
$$

Lean の型は次の形である。

```lean
theorem offCriticalCFBRC_eq_zero_iff_re_eq_half
    {d : ℕ} (hd : 0 < d) (σ Θ : ℝ) :
    offCriticalCFBRC d σ Θ = 0 ↔ σ = (1 : ℝ) / 2
```

ここで位相 `Θ` は任意である。零点位置は位相値に依存せず、中心実部だけで決まる。

## 4. 一般 zero-to-CFBRC bridge

### 4.1 抽象構造

同じ module には、任意の複素零点 predicate を CFBRC 零点へ写すための抽象構造がある。

```lean
structure ZeroToCFBRCBridge (Zero : ℂ → Prop) where
  d : ℕ
  hd : 0 < d
  phase : ℂ → ℝ
  map_zero : ∀ {s : ℂ}, Zero s →
    offCriticalCFBRC d s.re (phase s) = 0
```

この構造の load-bearing field は `map_zero` である。

```text
Zero s
  → offCriticalCFBRC d s.re (phase s) = 0
```

`d`、`hd`、`phase` は CFBRC 側の構成データであり、`map_zero` が解析対象と CFBRC を結ぶ本体である。

### 4.2 bridge から臨界線へ

次の theorem が証明済みである。

```lean
re_eq_half_of_zeroToCFBRCBridge
```

これは、選択された零点 `s` が bridge により CFBRC 零点へ写るなら、その実部が `1 / 2` であることを返す。

論理鎖は次のとおり。

```text
Zero s
  → map_zero
  → offCriticalCFBRC d s.re (phase s) = 0
  → offCriticalCFBRC_eq_zero_iff_re_eq_half
  → s.re = 1 / 2
```

この層は完全に証明済みである。ただし、特定の解析対象に対して `map_zero` を構成すること自体は別問題である。

## 5. 標準リーマンゼータ関数との接続

### 5.1 基本 module

```text
DkMath.RH.CFBRC.StandardZetaBridge
```

### 5.2 非自明零点 predicate

DkMath 側では次を定義する。

```lean
def NontrivialRiemannZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1
```

これは次を同時に要求する。

1. `riemannZeta s = 0`
2. 負の偶数にある自明零点ではない
3. 極の位置 `s = 1` ではない

### 5.3 Mathlib の RH 型との一致

次の theorem が証明済みである。

```lean
riemannHypothesis_iff_nontrivialZero_re_eq_half
```

数学的には次を与える。

$$
\operatorname{RiemannHypothesis}
\iff
\forall s\in Z_{\mathrm{nt}},\ s.re=\frac12
$$

この theorem により、DkMath の `NontrivialRiemannZetaZero` と Mathlib の `RiemannHypothesis` の間に翻訳上の Gap はない。

## 6. 標準ゼータ専用 bridge

### 6.1 型の特殊化

一般 bridge を標準ゼータ零点へ特殊化した型がある。

```lean
abbrev StandardZetaToCFBRCBridge :=
  ZeroToCFBRCBridge NontrivialRiemannZetaZero
```

さらに有限中心 realization 用に次がある。

```lean
abbrev StandardZetaFiniteCenteredBridge (ι : Type*) :=
  FiniteCenteredZeroBridge ι NontrivialRiemannZetaZero
```

### 6.2 bridge から RH

次の theorem が証明済みである。

```lean
riemannHypothesis_of_standardZetaToCFBRCBridge
```

意味は次のとおり。

```text
標準ゼータの全非自明零点について
CFBRC zero-preserving bridge が存在する
  → Mathlib.RiemannHypothesis
```

有限中心 realization に対しても次がある。

```lean
riemannHypothesis_of_standardZetaFiniteCenteredBridge
```

この theorem では、有限 endpoint realization と `center_identification` が主要な解析的 obligation になる。

### 6.3 直接 map-zero 形式

もっとも直接的な theorem は次である。

```lean
theorem riemannHypothesis_of_standardZeta_map_zero
    {d : ℕ} (hd : 0 < d) (phase : ℂ → ℝ)
    (map_zero : ∀ {s : ℂ},
      NontrivialRiemannZetaZero s →
      offCriticalCFBRC d s.re (phase s) = 0) :
    RiemannHypothesis
```

この theorem は、最終 obligation を明瞭に露出している。

$$
\forall s\in Z_{\mathrm{nt}},\quad
\operatorname{offCriticalCFBRC}(d,s.re,\phi(s))=0
$$

を供給すれば RH が得られる。

## 7. map-zero と RH の同値監査

root module `DkMath.RH` には次の theorem がある。

```lean
standardZeta_map_zero_iff_riemannHypothesis
```

型は概略として次である。

```lean
(∀ {s : ℂ},
  NontrivialRiemannZetaZero s →
  offCriticalCFBRC d s.re (phase s) = 0)
↔ RiemannHypothesis
```

したがって、universal `map_zero` は RH を導く十分条件であるだけではない。現在の CFBRC 零点 theorem の下では RH と同値である。

これは重要な監査結果である。

```text
誤った理解:
  map_zero は、あとで容易に埋めればよい接続補題である。

正しい理解:
  universal map_zero の供給が、現在の形式化における主数学そのものである。
```

bridge API を追加するだけでは主 Gap は縮まらない。実際の解析構造から `map_zero` を導かなければならない。

## 8. critical mirror の幾何

### 8.1 基本 module

```text
DkMath.RH.CFBRC.CriticalMirrorGeometry
```

critical mirror は次で定義される。

```lean
noncomputable def criticalMirror (s : ℂ) : ℂ :=
  ⟨1 - s.re, s.im⟩
```

したがって、実部を `1 - s.re` へ反射し、虚部を保存する。

証明済みの基本性質は次である。

```lean
criticalMirror_re
criticalMirror_im
criticalMirror_involutive
criticalMirror_eq_self_iff_re_eq_half
```

特に固定点集合は臨界線と一致する。

$$
\operatorname{criticalMirror}(s)=s
\iff
s.re=\frac12
$$

この幾何は CFBRC の中心化と整合する。

ただし、mirror 対称性だけでは、零点が mirror と一致することは導けない。零点集合が mirror により閉じていることと、各零点が mirror の固定点であることは異なる主張である。

## 9. Framework 内の主要 bridge 系統

現在の CFBRC Framework には、複数の bridge route が存在する。

### 9.1 Direct map-zero route

```text
ZeroToCFBRCBridge
StandardZetaToCFBRCBridge
riemannHypothesis_of_standardZeta_map_zero
```

最終 obligation を直接表す最短 route である。

### 9.2 Finite centered route

```text
FiniteCenteredZeroBridge
StandardZetaFiniteCenteredBridge
riemannHypothesis_of_standardZetaFiniteCenteredBridge
```

有限 endpoint、非零質量、中心同定を用いて `s.re = 1 / 2` を導く route である。

### 9.3 Energy route

```text
EtaEnergyBridge
EtaProjectedEnergyBridge
```

同一の energy 列または projected energy 列について、零点条件による極限と CFBRC 幾何による極限を衝突させる route である。

この route では、二つの極限が同じ Lean object に対して記述されていることが必須である。

### 9.4 Factorization route

```text
ZeroLocusFactorBridge
StandardZetaCFBRCFactorization
```

標準ゼータ関数と CFBRC 項を、非零 multiplier を介して factorization する route である。

この場合、multiplier の非零性と factorization identity が load-bearing obligation になる。

### 9.5 Eta / critical-mirror route

`EtaCriticalMirror*` 系 module 群では、有限 eta、paired eta、mirror defect、frame rotation、tail、energy、projection、Abel 分解などを通じて標準ゼータ零点と CFBRC 幾何の間を接続しようとしている。

この系統は解析的な主研究線であるが、個別の Green theorem が直ちに universal `map_zero` を与えるわけではない。

## 10. 証明済み Core と未解決 Gap

### 10.1 証明済み Core

現時点で少なくとも次は証明済みである。

```text
Core A:
  正次数 CFBRC の実入力零点は X = 0 のみ

Core B:
  offCriticalCFBRC の零点は σ = 1 / 2 のみ

Core C:
  ZeroToCFBRCBridge から零点実部 1 / 2 を導出可能

Core D:
  DkMath の非自明ゼータ零点 predicate と Mathlib RH が一致

Core E:
  標準ゼータ zero-to-CFBRC bridge から Mathlib RH を導出可能

Core F:
  universal standard-zeta map-zero と RH は同値

Core G:
  critical mirror の固定点集合は臨界線
```

### 10.2 主 Gap

最も重要な未解決項目は次である。

```text
Gap A:
  標準ゼータの全非自明零点を
  CFBRC 零点へ写す universal map_zero
```

数式では次である。

$$
\operatorname{NontrivialRiemannZetaZero}(s)
\Longrightarrow
\operatorname{offCriticalCFBRC}(d,s.re,\phi(s))=0
$$

この implication は現在の Framework では RH と同値である。

### 10.3 補助 Gap

解析 route によっては、次も必要になる。

```text
Gap B:
  非自明零点から s.im ≠ 0 を無条件に導くこと

Gap C:
  finite eta / paired eta と analytic eta の同定

Gap D:
  moving frame と fixed frame の same-object bridge

Gap E:
  zero-forced と nonzero-forced の同一正規化極限上の衝突

Gap F:
  endpoint closure、energy closure、factorization のいずれかの実現
```

これらの一部は他の module 群で進行中である。個別の状態は後続文書で module ごとに監査する。

## 11. 妥当性監査

### 11.1 CFBRC 零点 theorem 自体は RH を仮定していない

`offCriticalCFBRC_eq_zero_iff_re_eq_half` は CFBRC の代数的性質から証明され、標準ゼータ関数を使用しない。

したがって、CFBRC の零点集合が臨界線であることは独立 Core である。

### 11.2 bridge theorem は条件付き theorem である

`riemannHypothesis_of_standardZeta_map_zero` は正しい theorem であるが、`map_zero` を仮定として受け取る。

よって、これ単独では RH の無条件証明ではない。

### 11.3 universal map-zero の循環性監査

`standardZeta_map_zero_iff_riemannHypothesis` により、universal map-zero は RH と同値である。

したがって、map-zero の証明で次を暗黙に使用してはならない。

```text
- 全非自明零点が臨界線上にあること
- mirror zero が元の zero と一致すること
- centeredSigma s.re = 0
- offCriticalCFBRC d s.re Θ = 0
```

これらを途中仮定として導入すると循環する。

### 11.4 mirror 対称性の限界

関数等式や共役対称性から、零点 orbit が得られる場合がある。

しかし、

```text
s が零点
  → criticalMirror s も零点
```

だけでは、

```text
criticalMirror s = s
```

は導けない。

固定点性を得るには、同じ高さの零点一意性、同一 carrier の衝突、または別の非退化 invariant が必要である。

## 12. 現在の証明地図

現在の最短論理鎖は次である。

```text
CFBRC algebra
  → cfbrcR zero iff X = 0
  → offCriticalCFBRC zero iff re = 1 / 2

standard zeta predicate
  → NontrivialRiemannZetaZero
  → Mathlib RiemannHypothesis と一致

analytic realization
  → universal map_zero
  → standard-zeta-to-CFBRC bridge
  → every nontrivial zero has re = 1 / 2
  → RiemannHypothesis
```

前半と後半の wrapper は完成している。

現在の主研究対象は中央の `analytic realization → universal map_zero` である。

## 13. 今後の文書化順序

後続文書では、次の順序が適切である。

```text
0003:
  OffCriticalExclusionGeneral の詳細証明監査

0004:
  StandardZetaBridge と Mathlib RH 接続監査

0005:
  CriticalMirrorGeometry と零点 orbit の論理的限界

0006:
  FiniteCenteredBridge / EnergyBridge / FactorizationBridge 比較

0007 以降:
  EtaCriticalMirror 系の module 依存順解説
```

## 14. 結論

`DkMath.RH.CFBRC` Framework は、CFBRC の零点集合が臨界線に一致すること、および標準ゼータ零点を CFBRC 零点へ写せれば Mathlib の `RiemannHypothesis` が得られることを、Lean 上で明確に分離している。

現時点での核心は次の一文に集約される。

```text
CFBRC 側の一本線は証明済みである。
未解決なのは、標準ゼータの非自明零点が
その CFBRC 零点集合へ入ることの無条件証明である。
```

この区別を維持することが、以後の形式化妥当性監査において最重要である。

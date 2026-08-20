# Finite centered closure と有限 eta 実現

## 1. この文書の位置

`0003` では、CFBRC 自体の零点幾何として、正次数の standard CFBRC が centered coordinate `0`、すなわち `σ = 1 / 2` でのみ閉じることを記録した。

`0004` では、Mathlib の `RiemannHypothesis` と standard zeta zero predicate を CFBRC へ接続する論理 bridge を記録した。

この文書では、その間にある有限モデル層を記録する。

対象 module は主に次の二つである。

```text
DkMath.RH.CFBRC.FiniteCenteredBridge
DkMath.RH.CFBRC.EtaFiniteClosure
```

この層の目的は、無限級数や解析接続を直接扱うことではない。

有限個の複素ベクトルが endpoint closure を起こしたとき、その閉包を projected mass と normalized center offset に分解し、centered coordinate `σ - 1/2` と同定できるなら `σ = 1/2` を強制できることを固定する。

その一般構造を finite Dirichlet eta vector へ具体化したものが `EtaFiniteClosure` である。

## 2. 一般有限 centered closure

### 2.1 finite endpoint

有限 support `S : Finset ι` と複素ベクトル列 `v : ι → ℂ` を考える。

`finiteEndpoint S v` は、その有限 vector family の合計 endpoint を表す。

この endpoint が閉じる条件は、

```lean
finiteEndpoint S v = 0
```

である。

この時点では `v` がゼータ由来である必要はない。

### 2.2 observation rotation

有限ベクトルをある観測方向から分解するため、非零の複素数 `ω` を observation rotation として用いる。

必要条件は、

```lean
hω : ω ≠ 0
```

である。

この `ω` を用いて、positive / negative projected mass、projected mass total、normalized projected center offset などが構成される。

### 2.3 normalized projected center offset

一般有限モデルで重要なのは、閉包そのものではなく、閉包から得られる中心偏差を `centeredSigma σ` と結ぶことである。

Lean では、

```lean
hCenter :
  centeredSigma σ = normalizedProjectedCenterOffset S v ω
```

という形でその同定を要求する。

`centeredSigma σ` は、

$$
\operatorname{centeredSigma}(σ)=σ-\frac12
$$

である。

したがって、normalized projected center offset が有限 closure により `0` へ固定されれば、`σ - 1/2 = 0` が得られる。

## 3. centeredSigma_eq_zero_of_finiteEndpoint_eq_zero

主要 theorem は、

```lean
theorem centeredSigma_eq_zero_of_finiteEndpoint_eq_zero
    {ι : Type*} (S : Finset ι) (v : ι → ℂ) {ω : ℂ} {σ : ℝ}
    (hω : ω ≠ 0)
    (hClose : finiteEndpoint S v = 0)
    (hTotal : projectedMassTotal S v ω ≠ 0)
    (hCenter :
      centeredSigma σ = normalizedProjectedCenterOffset S v ω) :
    centeredSigma σ = 0
```

である。

論理構造は短い。

```text
finite endpoint closure
  ↓
normalized projected center offset = 0
  ↓
centeredSigma σ = normalized projected center offset
  ↓
centeredSigma σ = 0
```

ここで `hTotal` は重要である。

projected mass total が `0` なら、正規化された中心量そのものが退化する可能性があるため、finite closure だけでは中心情報を読むことができない。

したがって、この theorem は「閉じたから中心」という飛躍をせず、非退化条件を明示している。

## 4. re_eq_half_of_finiteEndpoint_eq_zero

前節の結果と `centeredSigma_eq_zero_iff` を組み合わせて、

```lean
theorem re_eq_half_of_finiteEndpoint_eq_zero ... :
    σ = (1 : ℝ) / 2
```

が得られる。

数学的には、

$$
σ-\frac12=0
\quad\Longrightarrow\quad
σ=\frac12
$$

という最後の変換である。

この theorem もゼータ関数には依存しない。

## 5. finite closure から CFBRC zero への移送

さらに、任意の正次数 `d` について、

```lean
theorem offCriticalCFBRC_eq_zero_of_finiteEndpoint_eq_zero
    {ι : Type*} {d : ℕ} (hd : 0 < d)
    ... :
    offCriticalCFBRC d σ Θ = 0
```

がある。

ここでは finite closure から `σ = 1 / 2` を得た後、既に `0003` で記録した、

```lean
offCriticalCFBRC_eq_zero_iff_re_eq_half
```

を逆向きに使って CFBRC zero locus へ移送する。

したがって依存順は、

```text
finite closure
  ↓
centeredSigma σ = 0
  ↓
σ = 1/2
  ↓
offCriticalCFBRC d σ Θ = 0
```

である。

CFBRC zero を finite closure から直接生成する魔法的な一段 theorem ではない。

## 6. FiniteCenteredZeroBridge

一般有限モデルを selected zero predicate へ接続する抽象構造が、

```lean
structure FiniteCenteredZeroBridge
    (ι : Type*) (Zero : ℂ → Prop)
```

である。

主要 field は次のとおり。

```text
support
vectors
rotation
rotation_ne_zero
projectedMassTotal_ne_zero
endpoint_eq_zero
center_identification
```

意味を通常数学で読むと、selected zero `s` ごとに、

1. 有限 support を選ぶ。
2. 有限 vector family を構成する。
3. 非零 observation rotation を選ぶ。
4. projected mass total が非零であることを示す。
5. finite endpoint が閉じることを示す。
6. normalized projected center offset が `s.re - 1/2` と一致することを示す。

という provider contract である。

このすべてが揃えば、

```lean
theorem re_eq_half_of_finiteCenteredZeroBridge
```

により、

```text
Zero s
  ↓
finite centered realization
  ↓
s.re = 1/2
```

が得られる。

## 7. この bridge の load-bearing field

`FiniteCenteredZeroBridge` は便利な wrapper ではあるが、各 field の重さは同じではない。

特に注意すべきなのは、

```lean
center_identification
```

である。

finite closure が存在するだけなら、任意の有限ベクトル閉包を作ることは可能である。

しかし、その有限モデルで観測した normalized center offset が、本当に元の complex zero の実部偏差

$$
s.re-\frac12
$$

を表していることは別の主張である。

この同定を外部から仮定しただけなら、それが RH の結論を暗黙に含んでいないかを監査する必要がある。

したがって、有限モデルを RH へ用いる場合は少なくとも、

```text
endpoint closure の由来
projected mass noncollapse の由来
center identification の独立性
```

を別々に確認する。

## 8. finite eta への具体化

`EtaFiniteClosure` では、一般有限モデルに genuine alternating Dirichlet eta vector を入れる。

### 8.1 etaUnsignedVector

```lean
noncomputable def etaUnsignedVector (s : ℂ) (m : ℕ) : ℂ :=
  ((m + 1 : ℕ) : ℂ) ^ (-s)
```

自然数 index `m + 1` に対応する unsigned Dirichlet vector である。

数学的には、

$$
(m+1)^{-s}
$$

である。

### 8.2 etaSignedVector

```lean
noncomputable def etaSignedVector (s : ℂ) (m : ℕ) : ℂ :=
  if Even m then etaUnsignedVector s m else -etaUnsignedVector s m
```

zero-based index が偶数なら正、奇数なら負になる。

したがって自然数 index では、

```text
1, 3, 5, ...  positive
2, 4, 6, ...  negative
```

という genuine alternating eta pattern を表す。

### 8.3 etaPartialEndpoint

```lean
noncomputable def etaPartialEndpoint (N : ℕ) (s : ℂ) : ℂ :=
  finiteEndpoint (Finset.range N) (etaSignedVector s)
```

これは最初の `N` 個の eta vector の有限 endpoint である。

ここではまだ `N → ∞` の極限は扱わない。

## 9. positive block と negative block

有限 eta endpoint は二つの genuine parity block に分けられる。

```lean
etaPositivePartial N s
etaNegativePartial N s
```

そして、

```lean
theorem etaPartialEndpoint_eq_positive_sub_negative
```

により、

$$
\operatorname{etaPartialEndpoint}(N,s)
=
\operatorname{etaPositivePartial}(N,s)
-
\operatorname{etaNegativePartial}(N,s)
$$

が exact に成立する。

この恒等式から直ちに、

```lean
theorem etaPartialEndpoint_eq_zero_iff_parity_balance
```

すなわち、

$$
\operatorname{etaPartialEndpoint}(N,s)=0
\iff
\operatorname{etaPositivePartial}(N,s)
=
\operatorname{etaNegativePartial}(N,s)
$$

が得られる。

これは finite eta closure の最初の具体的意味である。

## 10. mass balance と transverse Gap

一般 finite CFBRC decomposition を eta vector に適用すると、非零 observation rotation `ω` の下で、

```lean
theorem etaPartialEndpoint_eq_zero_iff_mass_balance_and_transverseGap
```

が成立する。

内容は、

```text
eta finite endpoint = 0
  ↕
positive projected mass = negative projected mass
and
transverse Gap = 0
```

である。

この段階で finite eta closure は、単なる complex sum `0` から、

```text
projected mass balance
Gap vanishing
```

という二成分条件へ分解される。

ただし、この `transverseGap` はこの module 系の既存実装語彙であり、後の CF2D 正本語彙と同一視する場合は別途 bridge を確認する。

## 11. 1/2–1/2 normalized mass

閉じた有限 eta endpoint が非退化した projected mass total を持つなら、

```lean
theorem etaNormalizedProjectedMass_eq_half_of_endpoint_eq_zero
```

により、

$$
\operatorname{normalizedPositiveProjectedMass}=\frac12
$$

かつ、

$$
\operatorname{normalizedNegativeProjectedMass}=\frac12
$$

が得られる。

これは有限閉包における `1/2` の最初の mass-balance interpretation である。

ただし、ここからただちに

$$
s.re=\frac12
$$

とは言えない。

normalized positive / negative projected mass が `1/2` ずつになることと、`centeredSigma s.re` が normalized projected center offset に一致することは別の命題である。

この区別が `FiniteCenteredZeroBridge.center_identification` の役割である。

## 12. 証明依存関係

この層の依存順をまとめると、次のようになる。

```text
finiteEndpoint
  ↓
finite projected mass decomposition
  ↓
normalizedProjectedCenterOffset
  ↓
finite endpoint closure
  ↓
normalized center offset = 0
  ↓
center_identification
  ↓
centeredSigma σ = 0
  ↓
σ = 1/2
  ↓
offCriticalCFBRC zero
```

eta specialization は、

```text
etaUnsignedVector
  ↓
etaSignedVector
  ↓
etaPartialEndpoint
  ↓
positive / negative parity blocks
  ↓
parity balance
  ↓
projected mass balance + Gap vanishing
  ↓
normalized masses = 1/2, 1/2
```

という別の有限鎖を与える。

この二本は `center_identification` が供給された地点で合流する。

## 13. 妥当性監査

### 13.1 証明済み Core

この文書で扱った次の内容は Lean theorem として固定されている。

```text
finite closure → normalized center offset zero
finite center identification → σ = 1/2
finite center identification → positive-degree CFBRC zero
FiniteCenteredZeroBridge → selected zero has real part 1/2
finite eta endpoint = positive block - negative block
finite eta closure ↔ parity block balance
finite eta closure ↔ projected mass balance + Gap zero
nondegenerate finite eta closure → normalized projected masses 1/2, 1/2
```

### 13.2 この段階では未証明のもの

この module だけでは、次は証明されていない。

```text
standard zeta zero が有限 eta endpoint closure を与えること
標準 zeta zero ごとに有限 support N が存在すること
finite eta の center offset が s.re - 1/2 と一致すること
finite eta closure が無限 eta zero と同値であること
無限 eta と standard riemannZeta の零点同定
```

これらは後続の解析層で別々に確認する必要がある。

## 14. DkMath 状態分類

この文書の範囲では、

```text
Core:
  finite closure algebra
  finite mass normalization
  centered coordinate extraction
  finite eta parity decomposition

Beam:
  finite eta modelを standard zeta zero へ接続する経路

Gap:
  genuine analytic zero から有限 closure / center identification を供給する独立 bridge
```

と整理できる。

ここで finite model 自体が完成していることと、standard zeta zero がその finite model を実際に実現することは分けて扱う。

## 15. 次の文書への接続

次に確認すべき自然な層は、finite eta から infinite eta へ進む前に、有限 projected mass decomposition の内部構造をさらに支えている module 群である。

または、実装依存順を eta 側へ進めるなら、paired eta decomposition、finite-to-infinite convergence、analytic eta との接続を順番に記録する。

いずれの場合も、この文書で固定した原則、

```text
finite closure
≠ analytic zero realization
```

を維持する。
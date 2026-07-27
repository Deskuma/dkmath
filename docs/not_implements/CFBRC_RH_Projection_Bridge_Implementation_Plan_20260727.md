# CFBRC–RH 複素射影橋 Lean 実装計画書

---

title: "CFBRC–RH 複素射影橋 Lean 実装計画書"
author: "D. and Wise Wolf"
date: "2026-07-27"
status: "not implemented"
lang: "ja"

---

## 0. 目的

本書は、DkMath の実代数・整数論側で既に構築されている

- 宇宙式と相対単位 `u`
- `GN` と差冪 core
- CFBRC の実部・虚部再帰
- 円分因子分解
- primitive prime / valuation / boundary API
- RH 側の finite Euler product / HOPC / stationary bridge

を、標準的な Riemann zeta function の非自明零点へ接続するために、今後 CFBRC および RH bridge 側へ実装すべき定理を固定する。

本計画の主眼は、新しい直感を増やすことではない。

既にある代数構造を、次の保存条件を持つ射影として theorem 化することにある。

1. CFBRC 実二成分と複素表現の同値
2. 多単位と総合位相単位の同値
3. 素数ごとの回転寄与と素数集合境界の対応
4. CFBRC closure と zeta zero の零点保存
5. 二つの素数質量の等値と実部 `1 / 2` の同値

最終目標は、定義へ Riemann hypothesis を埋め込まず、次の型を Lean kernel に通すことである。

$$
\operatorname{NontrivialZero}(\rho)
\longrightarrow
\rho.\operatorname{re}=\frac12
$$

---

## 1. 既存実装との関係

### 1.1. CFBRC の代数 core

CFBRC の基礎は、複素数そのものではなく差冪である。

$$
G_d(X,\Theta)
:=(X+i\Theta)^d-(i\Theta)^d
$$

$$
H_d(x,u)
:=\frac{(x+u)^d-u^d}{x}
$$

Lean では除法を避け、幾何和型 core と基本恒等式を主に使用する。

$$
(x+u)^d-u^d
=x\,GN(d,x,u)
$$

また、一般次数では円分因子積へ分解される。

$$
GN(d,x,u)
=
\prod_{\substack{m\mid d\\m>1}}
\Phi_m^{\mathrm h}(x+u,u)
$$

prime exponent では単一の prime cyclotomic core となる。

### 1.2. CFBRC の実二成分再帰

既存 `DkMath.CFBRC.TrigBridge.General` には、次の再帰がある。

$$
\operatorname{cfbrcRe}(d+1,X,\Theta)
=
X\operatorname{cfbrcRe}(d,X,\Theta)
-
\Theta\operatorname{cfbrcIm}(d,X,\Theta)
+
X\Re((i\Theta)^d)
$$

$$
\operatorname{cfbrcIm}(d+1,X,\Theta)
=
X\operatorname{cfbrcIm}(d,X,\Theta)
+
\Theta\operatorname{cfbrcRe}(d,X,\Theta)
+
X\Im((i\Theta)^d)
$$

純位相項は次数の `mod 4` により `0` または `±Θ^d` へ落ちるため、CFBRC の回転機構は複素数を本質的前提とせず、実数二成分と符号周期だけで記述できる。

### 1.3. 既存 RH bridge

`DkMath.RH.CFBRCBridge` には、CFBRC primitive-prime witness を次へ接続する定理群が既にある。

- singleton / finite-set `stationaryAt`
- `nondegenerateStationaryAt`
- `BoundarySide` による左右統一
- provider / provider-family
- eventually stationary
- `hopcPrimeContributionTsum = 0`
- finite contribution sum の `atTop` 極限

したがって、本計画では既存 5,000 行超の bridge に theorem を無制限に追加しない。

既存 bridge は低位 witness・provider API として再利用し、zeta zero への意味保存射影は新規ファイルへ分離する。

### 1.4. 既存計画との差分

`RH_Lean_Implementation_Plan_20260322.md` は、主に次を扱う。

- finite prime-local formation
- eventually finite formation
- infinite lift consequence
- provider-family packaging

`Gap 補正係数 RH 側 Lean 実装計画書.md` は、主に Euler factor の Gap 補正一般化を扱う。

本書が追加で固定する対象は次である。

> CFBRC の代数 closure が、標準 zeta の zero と同一の zero event を表すこと。

> CFBRC の左右素数境界質量が等しいことと、zeta 座標の実部が `1 / 2` であること。

---

## 2. 根底原理

### 2.1. 数学的依存順序

DkMath の依存順序は、通常の教科書と逆である。

$$
\text{unit algebra}
\longrightarrow
q2,q2_\star
\longrightarrow
\text{two-component conservation}
\longrightarrow
\text{rotation-like action}
$$

その後に必要に応じて、次を観測層として導入する。

$$
\mathbb R,
\quad
\theta,
\quad
\sin,\cos,
\quad
\mathbb C
$$

したがって、実数・偏角・虚数は最初から世界を構成する必須素材ではない。

- `ℝ` は連続化・完備化・中間値を与える層
- `θ` は既存軌道上の位置ラベル
- `cfcos`, `cfsin` は二成分保存作用の解析射影
- `ℂ` は実二成分回転の圧縮表現

として後から現れる。

### 2.2. 多単位から総合単位へ

出発点は、多項定理における単位増加である。

$$
(x+u)^d
\longrightarrow
(x+u+v)^d
\longrightarrow
(x+u+v+w)^d
$$

一般に、有限単位族 `U` の総和を `θ` とすれば、

$$
\theta
:=
\sum_{j\in U}u_j
$$

$$
\left(x+\sum_{j\in U}u_j\right)^d
=
(x+\theta)^d
$$

となる。

各単位を回転単位として解釈すると、

$$
u_j
=r_j e^{i\phi_j}
$$

$$
\theta
=
\sum_j r_j e^{i\phi_j}
$$

となる。

ただし、単に `θ` へ潰すだけでは各単位の由来を失う。

したがって Lean 実装では、次を同時に保持する。

1. 総合単位 `θ`
2. 単位族 `u_j`
3. 総和が `θ` に等しい証拠
4. 素数アドレスまたは valuation vector

### 2.3. 半単位中心

二つの正の質量 `x`, `u` に対して、全体を

$$
B:=x+u
$$

とする。

正規化座標を

$$
\lambda_x:=\frac{x}{x+u}
$$

$$
\lambda_u:=\frac{u}{x+u}
$$

と置けば、`x = u` のとき必然的に、

$$
\lambda_x
=
\lambda_u
=
\frac12
$$

となる。

平方展開では四セルが現れ、各セルは全体の `1 / 4` となる。

この `1 / 2` は外部から挿入した座標ではない。

二つの比較対象が同一質量となる条件から生じる唯一の中心である。

### 2.4. 素数境界と比較対象

互いに素性は単項性質ではなく二項関係である。

$$
\operatorname{Coprime}(x,u)
$$

`Nat.Coprime x u` の下で、

$$
\gcd(x,x+u)
=
\gcd(x,u)
=
1
$$

となる。

したがって `x` と `x + u` の素因数支持は交わらない。

`+u` は単なる加算ではなく、既存素数支持から別の素数支持へ切り替わる境界作用である。

非自明零点の CFBRC 解釈では、比較対象となる二つの素数集合または二つの素数質量が必要になる。

片方しか存在しなければ、比較中心・相殺・互いに素境界は非自明には形成できない。

### 2.5. `t` の役割

素数 `p` ごとの位相を、

$$
\vartheta_p(t)
:=
t\log p
$$

とする。

`t` は、全素数の回転を同時に進めるダイヤルである。

整数 `n` の valuation vector により、

$$
 n
 =
 \prod_p p^{v_p(n)}
$$

$$
 e^{-it\log n}
 =
 \prod_p
 \left(e^{-it\log p}\right)^{v_p(n)}
$$

となる。

- 素数は基本回転単位
- valuation は回転回数
- 合成数は素数回転の合成
- `t` は集合分割・符号・境界所属を調整する時間パラメータ

として読む。

---

## 3. 実装上の最重要注意

### 3.1. 循環論法を避ける

`x = u` を最初から `σ = 1 / 2` の場合だけで定義してはならない。

また、`leftMass` と `rightMass` の定義へ `σ = 1 / 2` を埋め込んではならない。

まず任意の臨界帯座標、

$$
0<\sigma<1
$$

と任意の `t` に対して、左右境界・左右素数集合・左右質量を定義する。

その後に独立定理として、

$$
\operatorname{leftMass}(\sigma,t)
=
\operatorname{rightMass}(\sigma,t)
$$

$$
\Longleftrightarrow
$$

$$
\sigma
=
\frac12
$$

を証明する。

### 3.2. stationary と zero を同一視しない

既存 RH bridge は、主として `phaseVel = 0`、すなわち stationary condition を扱う。

しかし、一般に

$$
\operatorname{phaseVel}(f,t)=0
$$

から

$$
 f(t)=0
$$

は従わない。

したがって、次の三概念を明確に分離する。

1. `StationaryEvent`
2. `ClosureEvent`
3. `ZeroEvent`

最終橋では、CFBRC closure と zeta zero の同値を別途証明する必要がある。

### 3.3. `σ > 1` の Euler product bridge と critical strip を分ける

既存 infinite lift の多くは、絶対収束域 `σ > 1` の majorant を利用している。

Riemann hypothesis の対象は、

$$
0<\sigma<1
$$

である。

したがって、次のどちらかを明示する必要がある。

1. `σ > 1` で構築した CFBRC–Euler product bridge を解析接続で critical strip へ輸送する
2. completed zeta または別の有限化表現を用いて critical strip 内で直接 zero-preserving projection を作る

`σ > 1` の theorem を、そのまま critical strip の zero theorem として使用してはならない。

### 3.4. 総合単位へ潰した後も素数アドレスを保存する

`θ = Σ u_p` だけでは、どの素数がどの寄与を持つか復元できない。

そのため、総合射影には少なくとも次の証拠を持たせる。

- prime-indexed component
- finite support または summability
- component sum equality
- left/right boundary membership
- valuation / cyclotomic factor address

---

## 4. 推奨ファイル分割

巨大な既存 `DkMath.RH.CFBRCBridge` へ全て追加しない。

### 4.1. CFBRC 側

```text
DkMath/CFBRC/Projection/RealPair.lean
DkMath/CFBRC/Projection/MultiUnit.lean
DkMath/CFBRC/Projection/PrimePhase.lean
DkMath/CFBRC/Projection/PrimeBoundaryMass.lean
```

役割:

- 複素数を必須としない実二成分モデル
- 多単位族と総合単位の対応
- 素数位相成分
- 左右境界と質量

### 4.2. RH 側

```text
DkMath/RH/CFBRCZeroProjection.lean
DkMath/RH/CFBRCBalanceBridge.lean
DkMath/RH/CFBRCCriticalLine.lean
```

役割:

- 標準 zeta / completed zeta との零点保存
- closure と等質量の橋
- 等質量中心から `re = 1 / 2`
- 最終 theorem package

### 4.3. umbrella import

実装完了後、必要に応じて次へ追加する。

```lean
-- DkMath/CFBRC.lean
import DkMath.CFBRC.Projection.RealPair
import DkMath.CFBRC.Projection.MultiUnit
import DkMath.CFBRC.Projection.PrimePhase
import DkMath.CFBRC.Projection.PrimeBoundaryMass
```

```lean
-- DkMath/RH.lean
import DkMath.RH.CFBRCZeroProjection
import DkMath.RH.CFBRCBalanceBridge
import DkMath.RH.CFBRCCriticalLine
```

---

## 5. Phase A: CFBRC 実二成分の独立化

### A1. 実二成分状態

```lean
structure CFBRCRealState where
  re : ℝ
  im : ℝ
```

複素数との対応を後付けにする。

```lean
def CFBRCRealState.toComplex (z : CFBRCRealState) : ℂ :=
  z.re + Complex.I * z.im
```

```lean
def CFBRCRealState.ofComplex (z : ℂ) : CFBRCRealState :=
  ⟨z.re, z.im⟩
```

### A2. 実再帰作用

```lean
def cfbrcRealStep
    (d : ℕ) (X Θ : ℝ) (z : CFBRCRealState) : CFBRCRealState :=
  {
    re := X * z.re - Θ * z.im + X * purePhaseRe d Θ
    im := X * z.im + Θ * z.re + X * purePhaseIm d Θ
  }
```

ここで `purePhaseRe`, `purePhaseIm` は `d % 4` による実関数として定義する。

### A3. 既存 CFBRC との一致

```lean
theorem cfbrcRealStep_toComplex_eq ... :
    (cfbrcRealStep d X Θ z).toComplex =
      (X + Complex.I * Θ) * z.toComplex + X * (Complex.I * Θ) ^ d
```

```lean
theorem cfbrcRealState_eq_cfbrcReIm ... :
    cfbrcRealState d X Θ =
      ⟨cfbrcRe d X Θ, cfbrcIm d X Θ⟩
```

```lean
theorem cfbrcRealState_toComplex_eq_cfbrcR ... :
    (cfbrcRealState d X Θ).toComplex = cfbrcR d X Θ
```

### A4. 複素表現が圧縮記法であること

```lean
theorem cfbrc_complex_representation_injective :
    Function.Injective CFBRCRealState.toComplex
```

```lean
theorem cfbrc_complex_representation_equiv :
    CFBRCRealState ≃+ ℂ
```

目的は、虚数を使わずに CFBRC の状態遷移を定義でき、複素数はその faithful representation であることを固定すること。

---

## 6. Phase B: 多単位と総合単位

### B1. 有限多単位族

```lean
structure MultiUnitData (ι : Type*) [Fintype ι] where
  unit : ι → ℂ
  total : ℂ
  total_eq_sum : total = ∑ i, unit i
```

実代数版を先に作る場合は、`CFBRCRealState` 値の単位族とする。

### B2. 多項式側の集約

```lean
theorem add_multiUnit_pow_eq_total_pow
    (x : R) (U : ι → R) :
    (x + ∑ i, U i) ^ d = (x + multiUnitTotal U) ^ d
```

これは単なる `rfl` / `simp` に近いが、後段の意味保存 interface として名前を固定する。

### B3. CFBRC 差冪への集約

```lean
theorem cfbrc_multiUnit_diffPow_eq_total ... :
    (x + ∑ i, U i) ^ d - (∑ i, U i) ^ d =
      (x + θ) ^ d - θ ^ d
```

### B4. 成分情報の保存 package

```lean
structure MultiUnitProjectionData (ι : Type*) [Fintype ι] where
  component : ι → ℂ
  total : ℂ
  total_eq_sum : total = ∑ i, component i
  address : ι → PrimeAddress
```

`PrimeAddress` は prime subtype、valuation support、cyclotomic factor address のいずれを採るか実装調査後に決定する。

---

## 7. Phase C: 素数位相射影

### C1. 素数回転単位

```lean
noncomputable def primePhaseUnit
    (p : {q // Nat.Prime q}) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t * Real.log p.1))
```

### C2. 基本性質

```lean
theorem norm_primePhaseUnit ... :
    ‖primePhaseUnit p t‖ = 1
```

```lean
theorem primePhaseUnit_mul ... :
    primePhaseUnit p (t₁ + t₂) =
      primePhaseUnit p t₁ * primePhaseUnit p t₂
```

### C3. valuation vector との一致

```lean
theorem phaseUnit_nat_eq_prod_primePhaseUnit_pow_val ... :
    Complex.exp (-Complex.I * (t * Real.log n)) =
      ∏ p in n.factorization.support,
        (primePhaseUnit ⟨p, ...⟩ t) ^ n.factorization p
```

これは「合成数回転は素数回転の合成」を固定する中心定理である。

### C4. CFBRC 位相との対応

```lean
structure CFBRCPrimePhaseProjection where
  X : ℝ
  Θ : ℝ
  t : ℝ
  primeComponent : {p // Nat.Prime p} → ℂ
  totalPhase : ℂ
  total_eq : totalPhase = ∑' p, primeComponent p
  cfbrc_eq : cfbrcR d X Θ = X * totalPhase
```

実際の等式形は、finite support / `tsum` / completed zeta 表現の選択後に修正する。

---

## 8. Phase D: 素数境界分割と質量

### D1. 境界側

既存 `DkMath.CFBRC.BoundarySide` を再利用する。

必要なら、解析上の左右所属を別 structure として定義する。

```lean
inductive PrimeRotationSide
  | left
  | right
  | boundary
```

### D2. 所属判定

```lean
noncomputable def primeRotationSide
    (σ t : ℝ) (p : {q // Nat.Prime q}) : PrimeRotationSide :=
  ...
```

所属判定は、次のいずれかを候補とする。

1. CFBRC 実部射影の符号
2. completed zeta の局所寄与の符号
3. phase interval / branch sector
4. cyclotomic factor の実軸交差側

ここは数値観測で候補を比較し、zero-preserving theorem が最も短くなる定義を採る。

### D3. 左右素数集合

```lean
noncomputable def leftPrimeSet (σ t : ℝ) : Set {p // Nat.Prime p} :=
  {p | primeRotationSide σ t p = .left}
```

```lean
noncomputable def rightPrimeSet (σ t : ℝ) : Set {p // Nat.Prime p} :=
  {p | primeRotationSide σ t p = .right}
```

### D4. 素数質量

```lean
noncomputable def primeMassWeight
    (σ t : ℝ) (p : {q // Nat.Prime q}) : ℝ :=
  ...
```

候補:

- `p ^ (-σ)` を基礎振幅とする
- CFBRC component norm を使う
- Euler local contribution の絶対値を使う
- completed zeta 対称化後の正値重みを使う

左右質量を定義する。

```lean
noncomputable def leftPrimeMass (σ t : ℝ) : ℝ :=
  ∑' p, if p ∈ leftPrimeSet σ t then primeMassWeight σ t p else 0
```

```lean
noncomputable def rightPrimeMass (σ t : ℝ) : ℝ :=
  ∑' p, if p ∈ rightPrimeSet σ t then primeMassWeight σ t p else 0
```

### D5. 非空条件

```lean
def TwoSidedPrimeBoundary (σ t : ℝ) : Prop :=
  (leftPrimeSet σ t).Nonempty ∧
  (rightPrimeSet σ t).Nonempty
```

片側しかない場合に非自明 closure が形成できないことを証明する。

```lean
theorem not_cfbRcClosure_of_leftPrimeSet_empty ...
```

```lean
theorem not_cfbRcClosure_of_rightPrimeSet_empty ...
```

### D6. 全体 Big と中心比

```lean
noncomputable def primeBoundaryBig (σ t : ℝ) : ℝ :=
  leftPrimeMass σ t + rightPrimeMass σ t
```

```lean
noncomputable def primeBoundaryCenterRatio (σ t : ℝ) : ℝ :=
  leftPrimeMass σ t / primeBoundaryBig σ t
```

基本補題:

```lean
theorem centerRatio_eq_half_iff_mass_eq
    (hpos : 0 < primeBoundaryBig σ t) :
    primeBoundaryCenterRatio σ t = 1 / 2 ↔
      leftPrimeMass σ t = rightPrimeMass σ t
```

この theorem は純代数として早期に通す。

---

## 9. Phase E: 反転対称と `1 / 2`

### E1. 反転側質量

任意の `σ` について左右が `σ ↔ 1 - σ` で対応するように定義または証明する。

```lean
theorem leftMass_reflection ... :
    leftPrimeMass σ t = rightPrimeMass (1 - σ) t
```

```lean
theorem rightMass_reflection ... :
    rightPrimeMass σ t = leftPrimeMass (1 - σ) t
```

### E2. 厳密単調性または一意性

等質量から `σ = 1 / 2` を得るには、反転対称だけでは不足する場合がある。

次のいずれかを証明する。

1. mass difference の厳密単調性
2. sign separation
3. injectivity
4. convexity と唯一零点

質量差を定義する。

```lean
noncomputable def primeMassGap (σ t : ℝ) : ℝ :=
  leftPrimeMass σ t - rightPrimeMass σ t
```

必要な中心定理候補:

```lean
theorem primeMassGap_reflection ... :
    primeMassGap (1 - σ) t = -primeMassGap σ t
```

```lean
theorem primeMassGap_strictMono_on_criticalStrip ... :
    StrictMonoOn (fun σ => primeMassGap σ t) (Set.Ioo 0 1)
```

または向きに応じて `StrictAntiOn` を使用する。

### E3. 等質量中心の一意性

```lean
theorem leftPrimeMass_eq_rightPrimeMass_iff_re_eq_half
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1)
    (htwo : TwoSidedPrimeBoundary σ t)
    ... :
    leftPrimeMass σ t = rightPrimeMass σ t ↔
      σ = 1 / 2
```

これは RH 最終橋の直前に置く最重要定理である。

---

## 10. Phase F: CFBRC closure

### F1. closure の定義

stationary と zero を分けるため、CFBRC closure を独立に定義する。

```lean
def CFBRCClosure (σ t : ℝ) : Prop :=
  cfbRcProjectedSum σ t = 0
```

実二成分版も用意する。

```lean
def CFBRCRealClosure (σ t : ℝ) : Prop :=
  cfbRcProjectedRe σ t = 0 ∧
  cfbRcProjectedIm σ t = 0
```

### F2. 実二成分と複素 closure の同値

```lean
theorem cfbRcRealClosure_iff_complexClosure ... :
    CFBRCRealClosure σ t ↔ CFBRCClosure σ t
```

### F3. closure から等質量

二つの素数群のベクトル和を、

```lean
leftPrimeVector σ t
rightPrimeVector σ t
```

として定義する。

```lean
theorem cfbRcClosure_iff_left_add_right_eq_zero ... :
    CFBRCClosure σ t ↔
      leftPrimeVector σ t + rightPrimeVector σ t = 0
```

反対位相条件または CFBRC boundary construction を用いて、

```lean
theorem cfbRcClosure_implies_equal_prime_mass ... :
    CFBRCClosure σ t →
      leftPrimeMass σ t = rightPrimeMass σ t
```

を証明する。

逆向きには位相差条件が必要である。

```lean
theorem equal_prime_mass_and_antiphase_implies_cfbRcClosure ...
```

必要なら package 化する。

```lean
structure PrimeBoundaryBalanceData (σ t : ℝ) : Prop where
  twoSided : TwoSidedPrimeBoundary σ t
  equalMass : leftPrimeMass σ t = rightPrimeMass σ t
  antiPhase : PrimeBoundaryAntiPhase σ t
```

```lean
theorem cfbRcClosure_iff_primeBoundaryBalanceData ...
```

---

## 11. Phase G: 標準 zeta との零点保存射影

### G1. 非自明零点 predicate

Mathlib の既存 zeta API を調査し、標準 predicate を再利用する。

必要なら局所 wrapper を置く。

```lean
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
  0 < s.re ∧
  s.re < 1
```

実際の名称・定義域は Mathlib の実装に合わせる。

### G2. zero-preserving projection

```lean
structure CFBRCZetaProjection where
  project : ℂ → ℂ
  zero_iff : ∀ s, IsNontrivialZetaZero s ↔ project s = 0
  project_eq_cfbRc : ∀ σ t, project (vertical σ t) = cfbRcProjectedSum σ t
```

ただし `project` を zeta 自身として定義して同値を自明化してはならない。

CFBRC algebra / prime components / completed zeta representation から構成する。

### G3. zero event の同値

```lean
theorem nontrivialZetaZero_iff_cfbRcClosure
    {σ t : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) 1) :
    IsNontrivialZetaZero (vertical σ t) ↔
      CFBRCClosure σ t
```

これは最終計画の最大の橋である。

### G4. CFBRC closure と balance の同値

```lean
theorem cfbRcClosure_iff_primeBoundaryBalance
    {σ t : ℝ} ... :
    CFBRCClosure σ t ↔
      PrimeBoundaryBalanceData σ t
```

### G5. 最終 critical-line theorem

```lean
theorem re_eq_half_of_nontrivialZetaZero
    {s : ℂ}
    (hs : IsNontrivialZetaZero s) :
    s.re = 1 / 2 := by
  let σ := s.re
  let t := s.im
  have hclosure : CFBRCClosure σ t :=
    (nontrivialZetaZero_iff_cfbRcClosure ...).1 ...
  have hmass : leftPrimeMass σ t = rightPrimeMass σ t :=
    cfbRcClosure_implies_equal_prime_mass hclosure
  exact (leftPrimeMass_eq_rightPrimeMass_iff_re_eq_half ...).1 hmass
```

### G6. RH package theorem

Mathlib 側の Riemann hypothesis predicate が存在する場合は、それへ接続する。

```lean
theorem cfbRc_rh : RiemannHypothesis := by
  intro s hs
  exact re_eq_half_of_nontrivialZetaZero hs
```

predicate がない場合は、DkMath 側で標準定式化と同値な wrapper を作る。

---

## 12. 既存 `CFBRCBridge.lean` から再利用するもの

新実装では、既存 bridge の次を再利用する。

1. primitive prime existence
2. right / left boundary unification
3. singleton / insert finite-set stationary wrapper
4. nondegenerate stationary wrapper
5. provider / provider-family
6. eventually stationary
7. finite → infinite HOPC lift
8. local contribution sum

ただし次は新規に必要である。

1. stationary と zero の橋
2. prime contribution の left/right partition
3. positive mass definition
4. closure による equal mass
5. equal mass による `σ = 1 / 2`
6. critical strip に有効な zero-preserving analytic continuation bridge

---

## 13. 実装順序

### Step 1. 実二成分を複素数から独立化

最初に Phase A を実装する。

理由:

- CFBRC の根底が虚数依存でないことを theorem として固定できる
- 後段の `q2`, `q2_star`, `cfcos`, `cfsin` との橋が明瞭になる
- zero を `re = 0 ∧ im = 0` として扱える

### Step 2. 多単位 package

Phase B を実装し、`θ` へ集約しても prime address を失わない型を作る。

### Step 3. prime phase と valuation bridge

Phase C の `phaseUnit_nat_eq_prod_primePhaseUnit_pow_val` を通す。

これは多項指数と素数回転数を結ぶ中心補題である。

### Step 4. left/right partition の数値実験

Phase D の所属判定候補を Python / existing CFBRC observer で比較する。

確認項目:

- 既知の非自明零点近傍で境界切替が観測されるか
- 左右がともに非空か
- mass gap が `σ = 1 / 2` で零になるか
- `t` の変化で所属集合がどのように組み替わるか
- branch cut に依存しない定義が可能か

### Step 5. half-center の純代数 theorem

`centerRatio_eq_half_iff_mass_eq` を先に通す。

### Step 6. mass gap の反転対称と一意性

Phase E を実装する。

ここが `1 / 2` の必然性を担う。

### Step 7. CFBRC closure

Phase F を実装し、stationary と zero を分離する。

### Step 8. zeta projection

Phase G の zero-preserving projection を実装する。

### Step 9. final theorem

最後に、

```lean
re_eq_half_of_nontrivialZetaZero
```

を通す。

---

## 14. 最小実験補題

本実装を開始するとき、まず次の小補題から入る。

### EXP-1. 等質量比

```lean
example {x u : ℝ} (hx : 0 < x) (hxu : x = u) :
    x / (x + u) = 1 / 2 := by
  rw [hxu]
  field_simp
  ring
```

実際には `u ≠ 0` 条件調整が必要。

### EXP-2. CFBRC 実状態の complex encoding

```lean
example (X Θ R I : ℝ) :
    ((X * R - Θ * I : ℝ) : ℂ) +
        Complex.I * (X * I + Θ * R) =
      (X + Complex.I * Θ) * (R + Complex.I * I) := by
  apply Complex.ext <;> simp <;> ring
```

### EXP-3. 素数回転の valuation 合成

有限素数集合版から始める。

```lean
example (S : Finset {p // Nat.Prime p})
    (v : {p // Nat.Prime p} → ℕ) (t : ℝ) :
    ∏ p in S, Complex.exp (-Complex.I * (t * Real.log p.1)) ^ v p =
      Complex.exp
        (-Complex.I *
          (t * ∑ p in S, v p * Real.log p.1)) := by
  ...
```

### EXP-4. closure なら norm equality

```lean
example {L R : ℂ} (h : L + R = 0) : ‖L‖ = ‖R‖ := by
  have : L = -R := by linear_combination h
  rw [this, norm_neg]
```

これは CFBRC closure から左右質量等値へ進む最小核となる。

### EXP-5. reflection fixed point

```lean
example {σ : ℝ} (h : σ = 1 - σ) : σ = 1 / 2 := by
  linarith
```

---

## 15. Definition of Done

本計画が完了したと言える条件は次である。

1. CFBRC 実二成分再帰が複素数なしで定義されている
2. 既存 `cfbrcR`, `cfbrcRe`, `cfbrcIm` と完全同値である
3. 多単位族から総合単位への射影が prime address を保存する
4. 素数回転と valuation vector の積表示が証明される
5. 左右素数境界が任意の `0 < σ < 1`, `t` で定義される
6. CFBRC closure から左右素数質量等値が従う
7. 左右素数質量等値と `σ = 1 / 2` が同値である
8. 標準 zeta の非自明零点と CFBRC closure が同値である
9. 上記を合成した `re_eq_half_of_nontrivialZetaZero` が仮定なしで通る
10. 使用した解析接続・収束・branch choice の全仮定が明示される

---

## 16. 研究上の中心文

本計画の中心像を、将来読み返すために固定する。

> 非自明零点は素数そのものの点ではない。
>
> CFBRC により分離された二つの素数集合または素数質量が、時間パラメータ `t` による回転で組み替わり、複素射影上で閉路を形成する点である。
>
> 比較対象が二つ存在し、その質量が等しくなると、全体 Big の中心比は必然的に `1 / 2` となる。
>
> CFBRC closure と標準 zeta zero の零点保存射影、および closure と等質量の同値を通せば、非自明零点が臨界線以外へ現れない理由が theorem として露出する。

---

## 17. 次回の Wise Wolf への指示

この文書を読んだら、最初に新しい巨大 bridge を書き始めないこと。

次の順で現物確認する。

1. `DkMath.CFBRC.TrigBridge.General`
2. `DkMath.CFBRC.TrigBridge.ClosedForm`
3. `DkMath.CFBRC.Bridge`
4. `DkMath.RH.CFBRCBridge`
5. `DkMath.RH.EulerZeta*`
6. Mathlib の zeta / completed zeta / analytic continuation API

その後、Phase A の `CFBRCRealState` と EXP-2 を最初の PR とする。

`D. and Wise Wolf` が既に CFBRC の橋脚を構築している。

次に必要なのは、新しい比喩を増やすことではなく、零点保存射影の中央径間を Lean で閉じることである。

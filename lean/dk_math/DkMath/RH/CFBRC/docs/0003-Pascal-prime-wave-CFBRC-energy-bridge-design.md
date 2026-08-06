# Pascal 素数波と CFBRC 観測窓エネルギー橋の設計

## 1. 文書の目的

この文書は、`DkMath.RH.CFBRC` に残る RH-equivalent な研究境界を、Pascal の二項係数、素数ごとの振動 mode、Euler-zeta、Prime Harmony Zeta（PHZ）、critical mirror、CFBRC 観測窓を一本の形式化経路へ統合するための設計書である。

対象となる現在の研究境界は次である。

```lean
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_research_goal :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse := by
  sorry
```

この宣言は、既存 audit により `RiemannHypothesis` と論理的に同値である。したがって、同値な provider を別名で置くこと、既存の局所 endpoint asymptotic を言い換えること、異なる sequence の極限を衝突させることでは閉じない。

本設計の目標は、RH そのものを仮定せず、有限的・代数的・素数座標的な Core から新しい zero-locus energy theorem を構成し、その定理から RH を導いた後、既存の `RH → collapse` 経路によって `sorry` を除去することである。

本書は証明済み事項と研究候補を明確に分離する。ここに記載する全経路が現時点で Lean Green であることを主張しない。

## 2. 現在の到達点

### 2.1 証明済み Core

現在の CFBRC では、次が証明済みである。

1. `offCriticalCFBRC` の零点は実部 `1 / 2` に限られる。
2. Mathlib の `RiemannHypothesis` と、DkMath の `NontrivialRiemannZetaZero` の全零点が実部 `1 / 2` を持つことは同値である。
3. critical mirror は `s.re = 1 / 2` を固定点集合として持つ。
4. eta paired endpoint の局所 dominant carrier は、仮想的 off-critical zero の下で非零実数極限へ収束する。
5. その local carrier から作る ThreeElement flow は pair-whole assimilation と nonzero target を無条件に供給する。
6. 不足している interaction assimilation、または difference whole collapse は RH と同値である。
7. generic same-object collision theorem は既に完成している。

### 2.2 現在の Obstruction

現在の local carrier を `z_k = x_k + i u_k` と読むと、既存 asymptotic は概念的に次を与える。

$$
x_k\longrightarrow L,\qquad u_k\longrightarrow 0,\qquad L\ne0
$$

したがって interaction は零へ収束し、plus whole と minus whole は同じ非零 target `L^2` へ収束する。

現在不足している theorem は、同じ carrier の interaction を同じ非零 target へ収束させること、同値には minus whole を零へ収束させることである。しかし既存局所漸近は minus whole を `L^2` へ送るため、局所 endpoint の精密化だけでは不足する。

新しい経路には、同じ対象の別表示から得られる独立な energy identity が必要である。

## 3. Big 構造

本設計で統合する全体経路は次である。

```text
Pascal の二項係数
  → 素数ごとの p-adic dial
  → 素数・素数冪の有限座標
  → Euler-zeta / PHZ の振動 mode
  → critical mirror による左右 amplitude pair
  → CFBRC 観測窓 residual
  → residual norm-square energy
  → off-critical offset の正値 obstruction
  → RiemannHypothesis
  → 既存 RH-equivalent research goal の閉鎖
```

Big の最終形は、次の二本の命題を同じ Lean object に対して証明することである。

```text
Zero-locus Beam:
  非自明零点なら CFBRC 観測窓 residual energy は 0 へ収束する。

Prime-coordinate Core:
  off-critical offset が非零なら同じ residual energy は正であり、0 へ収束できない。
```

同じ residual、同じ cutoff、同じ重み、同じ正規化を用いることが必須である。

## 4. 中心 offset と mirror prime mode

### 4.1 中心化実部

複素数 `s` に対して、臨界線からの横 offset を次で定義する。

$$
\delta(s):=s.re-\frac12
$$

Lean では既存の `centeredSigma` を優先して再利用する。新しい同義定義を増やさない。

### 4.2 実指数の実装方針

`δ` は実数であるため、Lean 実装では自然数冪 `^` ではなく `Real.rpow` または指数関数表示を使う。

正整数 `n > 1` に対して、mirror pair の amplitude を次で定義する。

$$
a_n(\delta):=\exp(-\delta\log n)
$$

$$
b_n(\delta):=\exp(\delta\log n)
$$

数学的には `a_n(δ) = n^{-δ}`、`b_n(δ) = n^δ` である。

この定義により、次の積は exact に固定される。

$$
a_n(\delta)b_n(\delta)=1
$$

### 4.3 mirror offset Gap

一つの整数 mode に対する横 offset Gap を次で定義する。

$$
G_n(\delta):=\bigl(a_n(\delta)-b_n(\delta)\bigr)^2
$$

`n > 1` なら次を証明対象とする。

$$
G_n(\delta)\ge0
$$

$$
G_n(\delta)=0\iff\delta=0
$$

後者は `Real.log n > 0` と `Real.exp` の単射性から導く。

### 4.4 ThreeElement identity

CF2D state を次で置く。

$$
X_n(\delta):=\bigl(a_n(\delta),b_n(\delta)\bigr)
$$

この state の interaction は固定値になる。

$$
2a_n(\delta)b_n(\delta)=2
$$

square mass と difference whole には次の exact identity が成立する。

$$
a_n(\delta)^2+b_n(\delta)^2
=2+\bigl(a_n(\delta)-b_n(\delta)\bigr)^2
$$

したがって、

```text
interaction Big = 2
mirror offset Gap = (a - b)^2
square mass = interaction Big + mirror offset Gap
```

となる。

臨界線 `δ = 0` では `a = b = 1` となり、Gap は零である。off-critical では Gap は正である。

この純代数層は RH に依存せず、最初に Green 化すべき Core である。

## 5. 素数波の縦方向

### 5.1 周波数

整数または素数 mode の縦方向位相は次である。

$$
\omega_n(t):=\exp(-it\log n)
$$

素数 `p` では周波数が `log p` となる。`t` は波の位相配置、`δ` は左右 mirror amplitude の不均衡を担う。

```text
t:
  干渉点が現れる高さを制御する。

δ:
  同じ周波数集合をどの横線で観測するかを制御する。
```

### 5.2 mirror complex mode

一つの mode の左右差は概念的に次である。

$$
M_n(\delta,t)
:=c_n\bigl(a_n(\delta)-b_n(\delta)\bigr)\omega_n(t)
$$

`c_n` は後述する非負 weight の平方根である。位相因子の norm は `1` なので、

$$
\lVert M_n(\delta,t)\rVert^2
=c_n^2G_n(\delta)
$$

となり、各 mode の energy から `t` が消える。

これは、非自明零点の縦 pattern と臨界線の横 rigidity を分離するための核である。

## 6. Pascal 側の現状と追加設計

### 6.1 既存 Core

既存 module は次である。

```text
DkMath.NumberTheory.PascalPrimeDial
DkMath.NumberTheory.WeightedBinomial
DkMath.NumberTheory.AKSBridge
DkMath.Pascal.WallisCosmicPetalBridge
DkMath.Pascal.WallisLimitBridge
DkMath.Pascal.WallisGrowthBridge
```

`PascalPrimeDial` には次が既にある。

```lean
pascalCoeffMass
pascalRowMass
pascalPrimeDialHeight
UniformPrimeDialHeight
FilteredPrimeDialHeight
prime_uniformPrimeDialHeight_self
below_prime_uniformPrimeDialHeight_zero
pascalPrimeDialHeight_eq_zero_of_row_lt
prime_not_dvd_pascalCoeffMass_of_row_lt
pascalPrimeDialHeight_prime_pow_add_index
pascalPrimeDialHeight_prime_pow
prime_power_unitFilteredPrimeDialHeight
```

これにより、Pascal 行の係数が素数ごとの p-adic dial を持つこと、素数行では自身の素数 dial が内側係数に現れること、行番号より大きい素数はまだ現れないこと、素数冪行では Kummer 型の dial 高さが得られることは既に形式化されている。

### 6.2 未実装 Beam

次の内容は本設計時点では既存 Green theorem として確認されていない。

1. Pascal 一行の係数 LCM と `lcm(1, ..., n + 1)` の exact identity
2. 隣接 Pascal 行から von Mangoldt weight を抽出する theorem
3. その weight と Mathlib の Mangoldt 関数との一致
4. Pascal weight を用いた Dirichlet series と `-ζ'/ζ` の一致

これらは文献確認、Mathlib API 確認、添字監査の後に独立 module として実装する。

### 6.3 最初に採用する安全な prime coordinate

最初の energy Core では、Pascal decoder 完成を待たず、有限素数集合を直接用いてもよい。

```lean
def primeModeIndex := {p : ℕ // Nat.Prime p}
```

その後、Pascal prime dial が同じ finite prime coordinate を生成することを bridge theorem として接続する。

これにより、解析 Gap と Pascal decoder Gap を分離して監査できる。

## 7. Euler-zeta と PHZ の既存入口

既存 module は次である。

```text
DkMath.RH.EulerZeta
DkMath.RH.EulerZetaConvergence
```

主要定義として次が存在する。

```lean
eulerZetaFactor
eulerZeta
eulerZeta_onVertical
eulerZeta_exp_s_log_p_sub_one
eulerZetaFactorMag
eulerZetaMag
eulerZetaPhase
eulerZetaFinite
eulerZetaFinite_onVertical
eulerZetaPhaseVelLocal
eulerZetaPhaseVelFinite
eulerZetaFactorPhaseVelLocal
eulerZetaFactorPhaseVelFinite
hopcPrimeLocalContribution
hopcPrimeContributionSum
```

これらは素数ごとの有限 Euler 因子、magnitude、phase、phase velocity を既に提供する。

PHZ は新しい特殊関数を無条件に導入する名称ではなく、次の有限観測層の研究名として扱う。

```text
有限素数 mode の complex sum
有限 Euler 因子の phase velocity sum
平滑化された Mangoldt-weighted sum
```

無限級数、解析接続、標準 `riemannZeta` との一致は、それぞれ独立 theorem として証明されるまで仮定しない。

## 8. `(N, N+1)` 観測窓と偶奇ペア

### 8.1 単一総和の情報喪失

有限 prime mode の総和を `S_N` とする。

$$
S_N(s):=\sum_{j<N}V_j(s)
$$

一つの総和が零でも、各座標が零とは限らない。複数の非零 mode が打ち消し合うためである。

### 8.2 隣接差分による座標復元

隣接する二つの cutoff を同時に保持すると、

$$
S_{N+1}(s)-S_N(s)=V_N(s)
$$

となる。

この exact identity が、宇宙式の `N + 1`、Pascal の隣接行、観測窓の始点・終点、偶奇ペアを共通化する。

```text
単一 N:
  総和への射影で prime coordinate が失われる。

(N, N+1):
  隣接差分で新しく追加された mode を復元できる。
```

本設計では、観測値だけでなく隣接差分履歴を first-class object とする。

### 8.3 真の ZERO の三点組

正規化された一つの窓は、

$$
(-\mathrm{succ},\mathrm{zero},\mathrm{succ})
$$

という三点組として読む。

負側窓 `(-succ, zero)` と正側窓 `(zero, succ)` は中心 `zero` を共有する。集合として貼り合わせれば三点組となり、重複度を保持すれば Pascal の `1, 2, 1` に対応する。

この意味論は、形式化では次の二層へ分ける。

1. index window の pushout または共有中心を持つ pair 構造
2. 重みの加法または convolution による `1, 2, 1` 係数

比喩だけで終わらせず、どの型のどの等式で表すかを個別に固定する。

## 9. Prime-coordinate vector

### 9.1 有限 vector

有限 index `ι_N` 上で、各 prime mode を座標として保持する vector を定義する。

概念型は次である。

```lean
noncomputable def primeMirrorCoordinate
    (δ t : ℝ) (p : {p : ℕ // Nat.Prime p}) : ℂ :=
  Complex.ofReal (Real.sqrt (primeWeight p)) *
    Complex.ofReal
      (Real.exp (-δ * Real.log p) - Real.exp (δ * Real.log p)) *
    Complex.exp (-(Complex.I * (t * Real.log p)))
```

実際の Lean 定義では coercion と複素指数の符号を module 内で一度固定する。

### 9.2 energy

有限集合 `S` に対する energy を座標 norm-square の和として定義する。

$$
E_S(\delta,t)
:=\sum_{p\in S}w_p
\bigl(a_p(\delta)-b_p(\delta)\bigr)^2
$$

全 weight が非負なら、

$$
E_S(\delta,t)\ge0
$$

さらに `S` に少なくとも一つの素数が正 weight で含まれるなら、

$$
E_S(\delta,t)=0\iff\delta=0
$$

を目標 theorem とする。

energy は各座標の norm-square の和であり、総和の norm-squareではない。この区別を厳守する。

$$
\left\lVert\sum_pV_p\right\rVert^2
\ne
\sum_p\lVert V_p\rVert^2
$$

一般には交差項が存在するためである。

## 10. CFBRC 観測窓 residual

### 10.1 必要な同一対象

本設計で最も重要な新定義は、標準ゼータまたは eta endpoint の一つの値ではなく、有限 prime coordinate 履歴を保持する `CFBRCWindowResidual` である。

概念的には次の情報を持つ。

```text
cutoff N
横 offset δ
高さ t
prime coordinate vector
隣接差分 (N, N+1)
critical-mirror pair
CFBRC local/global frame decoder
```

### 10.2 目標 energy identity

load-bearing theorem 候補は次である。

$$
\left\|\operatorname{CFBRCWindowResidual}_N(s)\right\|^2
=
\sum_{p\in S_N}w_{N,p}
\bigl(a_p(\delta(s))-b_p(\delta(s))\bigr)^2
$$

ここで左辺の norm は、複素総和への射影後の norm ではなく、prime coordinate vector の Hilbert norm または有限 Euclidean norm である。

この identity により、同じ residual の zero-locus collapse と off-critical positive Gap を比較できる。

### 10.3 current eta carrier との接続

既存の `etaCriticalMirrorDominantLocalThreeElementFlow` は、局所 endpoint を一つの complex number へ射影した flow である。

新しい prime-coordinate residual は、その上流に置く。

```text
prime coordinate residual
  → finite sum / endpoint decoder
  → existing eta local carrier
  → existing ThreeElement flow
```

最初から両者を定義上同一視しない。必要なのは、有限 sum、重み、normalization、limit を明記した bridge theorem である。

## 11. Zero-locus Beam

### 11.1 本当の研究 theorem

本設計で RH を担う theorem は、次の形である。

```lean
theorem pascalPrimeCFBRCWindowResidual_tendsto_zero_of_nontrivialZero
    {s : ℂ}
    (hs : NontrivialRiemannZetaZero s) :
    Tendsto
      (fun N => pascalPrimeCFBRCWindowResidualEnergy N s)
      atTop
      (nhds 0)
```

この theorem は現時点で未証明であり、単なる structure field として置けば RH-equivalent な Gap を名前変更しただけになる可能性が高い。

### 11.2 許容される証明入力

この theorem は次の既知構造から導く必要がある。

1. finite eta paired endpoint と complete tail の exact identity
2. Euler half-endpoint と remainder の exact split
3. critical mirror の exact involution
4. finite Euler factor または Mangoldt sum の exact prime decomposition
5. `(N, N+1)` の隣接差分 decoder
6. zero-locus での endpoint closure
7. residual energy identity

### 11.3 禁止される循環

次を仮定として使用してはならない。

1. `s.re = 1 / 2`
2. `RiemannHypothesis`
3. 現在の RH-equivalent dominant-half transverse collapse
4. RH-equivalent interaction assimilation provider
5. RH-equivalent difference whole collapse provider
6. 「off-critical では干渉和が零にならない」という未証明の一般原理

## 12. Off-critical Core

Zero-locus Beam と独立に、次を純代数・順序論から証明する。

```lean
theorem primeMirrorEnergy_pos_of_centeredSigma_ne_zero
    (hS : S.Nonempty)
    (hweight : ∀ p ∈ S, 0 < weight p)
    (hδ : centeredSigma s ≠ 0) :
    0 < primeMirrorEnergy S weight s
```

または極限 route では、ある固定素数 `p` の項だけを下界に用いる。

$$
0<w_pG_p(\delta)\le E_S(\delta,t)
$$

これにより energy が零へ収束することと `δ ≠ 0` が衝突する。

有限 cutoff の全段階で同じ固定素数を含める設計にすれば、一様正下界を作りやすい。

## 13. RH への最終接続

energy route から得る最終 theorem 候補は次である。

```lean
theorem riemannHypothesis_of_pascalPrimeCFBRCWindowEnergy :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivialZero_re_eq_half]
  intro s hs
  by_contra hre
  have hδ : centeredSigma s ≠ 0 := by
    -- `hre` と centeredSigma の既存補題から導出
    ...
  have hzero :=
    pascalPrimeCFBRCWindowResidual_tendsto_zero_of_nontrivialZero hs
  have hpositive :=
    primeMirrorEnergy_uniform_positive_of_centeredSigma_ne_zero hδ
  exact tendsto_zero_not_of_eventually_ge_positive hzero hpositive
```

RH が独立 route で Green になった後、現在の research goal を次で閉じる。

```lean
theorem etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_research_goal :
    EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse :=
  etaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse_of_riemannHypothesis
    riemannHypothesis_of_pascalPrimeCFBRCWindowEnergy
```

実際の theorem 名は既存 API に合わせる。

## 14. module 設計

次の順序で新規 module を作成する。

### Phase A: 純代数 mirror Core

```text
DkMath.RH.CFBRC.PrimeMirrorOffsetCore
```

候補識別子は次である。

```lean
primeMirrorLeftAmplitude
primeMirrorRightAmplitude
primeMirrorOffsetGap
primeMirrorOffsetState
primeMirrorOffsetGap_nonneg
primeMirrorOffsetGap_eq_zero_iff_centeredSigma_eq_zero
primeMirrorOffsetState_interaction_eq_two
primeMirrorOffsetState_squareMass_eq_two_add_gap
```

### Phase B: 有限 prime-coordinate energy

```text
DkMath.RH.CFBRC.PrimeMirrorFiniteEnergy
```

候補識別子は次である。

```lean
primeMirrorCoordinate
primeMirrorEnergy
primeMirrorEnergy_nonneg
primeMirrorEnergy_eq_zero_iff_centeredSigma_eq_zero
primeMirrorEnergy_pos_of_offCritical
```

### Phase C: Pascal prime decoder

```text
DkMath.NumberTheory.PascalPrimeCoordinateDecoder
```

既存 `PascalPrimeDial` を再利用し、row transition がどの prime coordinate を追加するかを形式化する。

row LCM、Mangoldt、AKS、Fermat little theorem との接続は、一つの大 theorem にまとめず段階的に置く。

### Phase D: PHZ / Euler finite window

```text
DkMath.RH.CFBRC.PascalPrimeEulerWindow
```

既存 `DkMath.RH.EulerZeta` の有限素数集合 API を使い、Pascal 由来 finite set と Euler finite observation を接続する。

### Phase E: `(N, N+1)` residual decoder

```text
DkMath.RH.CFBRC.PascalPrimeWindowResidual
```

候補識別子は次である。

```lean
pascalPrimePartialState
pascalPrimeWindowIncrement
pascalPrimeWindowIncrement_eq_coordinate
pascalPrimeWindowResidual
pascalPrimeWindowResidualEnergy
```

### Phase F: eta / completed-zeta bridge

```text
DkMath.RH.CFBRC.PascalPrimeEtaWindowEnergyBridge
```

ここで初めて既存 eta paired endpoint、completed-zeta slope、dominant half endpoint と接続する。

### Phase G: RH closure

```text
DkMath.RH.CFBRC.PascalPrimeWindowRHClosure
```

この module は研究境界 theorem が Green になるまで `DkMath.RH` の stable export へ追加しない。

## 15. 実装順序と checkpoint

### Checkpoint 1: mirror amplitude Core

次を `sorry` なしで Green にする。

```text
a * b = 1
interaction = 2
squareMass = 2 + differenceWhole
differenceWhole = 0 ↔ centeredSigma = 0
```

### Checkpoint 2: finite energy Core

有限素数集合と正 weight に対して、非負性、零点一意性、off-critical 正値を Green にする。

### Checkpoint 3: `(N, N+1)` decoder

有限部分和の隣接差分が追加座標と一致することを Green にする。ここではゼータ零点を使わない。

### Checkpoint 4: Pascal bridge

既存 prime dial から有限 prime coordinate set または weight を供給する。row LCM/Mangoldt route を採用する場合は、独立に数値例と theorem statement を監査する。

### Checkpoint 5: Euler/PHZ bridge

Pascal 由来 finite coordinate と既存 `eulerZetaFinite`、phase velocity、または平滑 finite sum を接続する。

### Checkpoint 6: residual energy identity

同じ residual の norm-square が prime mirror energy と exact に一致することを Green にする。

### Checkpoint 7: zero-locus collapse

非自明零点条件から residual energy が零へ収束することを証明する。ここが主要 Gap である。

### Checkpoint 8: RH と既存 `sorry` の閉鎖

新 route から RH を導き、既存 RH-equivalent theorem をその帰結として埋める。

## 16. 妥当性監査

### 16.1 Core と仮説の区別

次は Core 候補であり、通常の実解析と有限和で証明可能と見込まれる。

1. mirror amplitude の積が `1`
2. interaction が `2`
3. square mass identity
4. Gap の非負性
5. `n > 1` における Gap zero と `δ = 0` の同値
6. 有限正 weight energy の非負性と零点一意性
7. `(N, N+1)` の隣接差分 identity

次は Beam または Gap である。

1. Pascal row transition から標準 Mangoldt weight を exact に得ること
2. Pascal/PHZ finite observation と standard zeta zero-locus の exact bridge
3. CFBRC window residual energy identity
4. 非自明零点から residual energy collapse を得ること

### 16.2 解析接続の範囲

Euler product と Dirichlet series の直接恒等式は通常 `re s > 1` に制限される。非自明零点は critical strip にあるため、有限和、eta 表現、completed zeta、解析接続を区別する。

収束領域の恒等式を critical strip へ無条件に移送しない。

### 16.3 素数座標と複素総和の区別

複素総和の零は、各 prime coordinate の零を意味しない。したがって、prime-coordinate vector から複素総和へ射影した後に情報を復元するには `(N, N+1)` 履歴または別の injective decoder が必要である。

### 16.4 数値グラフの位置づけ

`2 * arctan(Im ζ / Re ζ)` の束交点、PHZ 波形、Euler 位相速度の spike は、定義候補と window index を発見する Beam である。これらは exact theorem へ翻訳されるまで Core ではない。

### 16.5 現在の research goal を直接弱めない

既存 `EtaCriticalMirrorDominantEulerHalfEndpointCarrierTransverseCollapse` は RH と同値である。新 route はその statement を弱めたり、別 sequence の類似極限で置換したりせず、独立に RH を証明した後で供給する。

## 17. 最終目標との関係

本設計は最終目標そのものではなく、その途中にある RH closure の設計である。

最終目標は、Pascal の二項係数から生じる素数因子と素数冪の mode が、どのように非自明零点 pattern を形成するかを一本の構成式として記述することである。

その最終経路は次である。

```text
Pascal / binomial coefficients
  → prime factor coordinates
  → prime interference spectrum
  → nontrivial-zero window formation law
  → critical-line rigidity
```

RH は、このより大きな形成則の Core 側に現れる rigidity lemma と位置づける。

CFBRC は、素数座標、mirror pair、観測窓、zero/nonzero collision を同じ形式化対象へ運ぶ橋である。

## 18. 現在の結論

現時点で `sorry` を正当な proof term に置換できる状態ではない。しかし、必要な Core、Beam、Gap は次の形まで具体化した。

```text
Core:
  mirror prime amplitude pair と positive offset energy

Decoder:
  Pascal prime dial と (N, N+1) 隣接差分

Beam:
  Euler-zeta / PHZ finite window

Gap:
  非自明零点から同じ CFBRC residual energy の collapse を導く theorem

Big:
  residual energy の zero/nonzero collision から RH を導き、既存 sorry を閉じる
```

次の実装開始点は `PrimeMirrorOffsetCore` である。ここを RH、eta、無限級数から独立した純代数 module として Green 化し、その後に有限 prime energy と `(N, N+1)` decoder を積み上げる。

# RH-CFBRC off-critical exclusion 引き継ぎ資料

作成日: 2026-08-04  
対象リポジトリ: `Deskuma/dkmath`  
作業ブランチ: `wip/RH-CFBRC-off-critical-exclusion-260802-v2`  
Lean: 4.26.0 以降  
現在の mathlib / toolchain 前提: Lean 4.32.2 系

---

## 0. 次の会話で最初に読む場所

次の新規会話では、この文書を添付して、以下の一文から再開する。

```text
RH-CFBRC off-critical exclusion の続きを行う。
添付 handoff を正本として読み、GitHub branch
wip/RH-CFBRC-off-critical-exclusion-260802-v2
の最新 head と最新ファイルを確認する。

まず最新層の local build / test 状態を確認し、エラーがあればその差分だけ直す。
Green なら normalized constant audit へ進む。
PR はまだ作られていないため CI は存在しない。CI を探さない。
```

作業再開時の優先ファイルは次の二つ。

```text
lean/dk_math/DkMath/RH/CFBRC/
  EtaCriticalMirrorPairedFramePositiveDensityBlock.lean

lean/dk_math/DkMath/RH/CFBRC/
  EtaCriticalMirrorDefectPairMarginPowerLowerBound.lean
```

その前段として、以下も同時に参照する。

```text
EtaCriticalMirrorPairedFrameAbelTailIdentity.lean
EtaCriticalMirrorPairedFrameAbelCorrectionTailBound.lean
EtaCriticalMirrorPairedFrameMovingProjectionTailMargin.lean
```

---

## 1. Git / build の現在状況

### Branch

```text
wip/RH-CFBRC-off-critical-exclusion-260802-v2
```

PR はまだ作成されていない。

したがって GitHub Actions の CI は走っておらず、確認対象も存在しない。  
この開発中は、ユーザー環境での local build / test を正本とする。

使用コマンド:

```bash
cd lean/dk_math
./lean-build.sh && ./lean-test.sh
```

過去の確認では、build と test build の両方が Green になっている。  
既存の別研究モジュールにある `sorry` warning は、この RH-CFBRC 実装とは別件。

### 最新 checkpoint

直近の既知 checkpoint:

```text
efb646939b994acecdce23f626e92f313baca6ed
chore(RH): export defect margin power regression
```

その後、ユーザー側で `EtaCriticalMirrorDefectPairMarginPowerLowerBound.lean` に小さな互換修正が一件入っている。

比較状態:

```text
base:
  efb646939b994acecdce23f626e92f313baca6ed

branch:
  1 commit ahead

changed file:
  EtaCriticalMirrorDefectPairMarginPowerLowerBound.lean

stats:
  +3 / -2
```

この handoff 作成時点では、直近の Layer 20 全体について、会話内で明示的な `build succeeded` 報告はまだ受け取っていない。  
新規会話では、最初に local build / test の結果を確認すること。

---

## 2. 最終目標

対象は非自明なリーマンゼータ零点 $s=\sigma+it$。

目標は、off-critical 仮定、

$$
\sigma\ne\frac12
$$

から、Lean 上で矛盾を導き、

$$
\sigma=\frac12
$$

へ戻すこと。

CFBRC 側の最終出口は既にある。

```lean
re_eq_half_of_nontrivialRiemannZetaZero_of_...

offCriticalCFBRC_eq_zero_of_nontrivialRiemannZetaZero_of_...
```

したがって現在の主戦場は、off-critical point に対して十分強い phase / pressure certificate を構成すること。

---

## 3. 中心となる数学的対象

### Critical mirror

$s=\sigma+it$ の critical mirror は、実部だけを $1/2$ の反対側へ移す。

$$
m=\operatorname{criticalMirror}(s)
$$

実部は、

$$
m.re=1-\sigma
$$

非自明零点なら、

$$
0<\sigma<1
$$

かつ、

$$
0<m.re<1
$$

が使える。

### Paired defect

自然な eta pair の差を mirror と original で比較する。

```lean
etaCriticalMirrorDefectPairTerm s k
```

正確には、

$$
D_k(s)
=
\operatorname{etaPairTerm}(m,k)
-
\operatorname{etaPairTerm}(s,k)
$$

である。

pair interval は、

$$
[2k+1,2k+2]
$$

で固定される。

### Pair-left rotating frame

pair の左端 $2k+1$ の対数位相を消す unit rotation:

```lean
etaPairBaseRotation s k
```

これを $B_k(s)$ と書く。

moving-frame pair:

$$
B_kD_k
$$

signed vertical projection:

```lean
etaCriticalMirrorSignedVerticalProjection s z
```

定義は、

$$
P_s(z)=s.im\cdot z.im
$$

である。

上半平面と下半平面を同じ符号規則で扱うため、$s.im$ を掛けている。

---

## 4. 既に完成している証明鎖

以下は大きく五層に分かれる。

---

## 4.1 Local pair sign

continuous defect coefficient と pair-local residual rotation を分離した。

```text
EtaCriticalMirrorDefectKernelFactorization
EtaCriticalMirrorContinuousWeightPressure
EtaCriticalMirrorDefectCoefficientProjection
EtaCriticalMirrorDefectCoefficientMargin
EtaCriticalMirrorDefectKernelQuantitativeMargin
EtaCriticalMirrorDefectPairQuantitativeMargin
```

continuous transport weight:

$$
W_s(x)=x^{2\sigma-1}
$$

radial decay:

$$
R_s(x)=x^{-\sigma-1}
$$

右側 $\frac12<\sigma$ では weight が増大し、pair-local projection は eventually positive。

左側 $\sigma<\frac12$ では weight が減少し、pair-local projection は eventually negative。

Lean の主要結果:

```lean
eventually_etaCriticalMirrorRightPairMargin_le_rotatedDefectPairProjection

eventually_etaCriticalMirrorLeftPairMargin_le_neg_rotatedDefectPairProjection
```

---

## 4.2 Common-frame finite / growing block

各 pair の local frame を block 始端 frame $B_K$ へ移した。

主要モジュール:

```text
EtaCriticalMirrorPairedFrameBlockAlignment
EtaCriticalMirrorPairedFrameBlockChord
EtaCriticalMirrorPairedFrameBlockProjection
EtaCriticalMirrorPairedFrameBlockMarginDomination
EtaCriticalMirrorPairedFrameFiniteBlockCertificate
EtaCriticalMirrorPairedFrameGrowingBlockGeometry
EtaCriticalMirrorPairedFrameGrowingBlockCertificate
EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate
```

固定有限長 $N$ について、十分大きい $K$ では、

右側:

$$
\forall j<N,\quad 0<P_s(B_KD_{K+j})
$$

左側:

$$
\forall j<N,\quad P_s(B_KD_{K+j})<0
$$

まで完成。

さらに sublinear growing schedule、

$$
N(K)\longrightarrow\infty
$$

かつ、

$$
\frac{N(K)}{2K+1}\longrightarrow0
$$

に対しても、全 offset を一様に common frame へ移す層が完成している。

重要な論理補助:

```lean
eventually_all_nat_add_growingBlock
```

これは、

```text
∀ j, eventually P(K,j)
```

から growing finite intersection を誤って作るのではなく、eventual threshold より先の全自然数 offset を一括で覆う。

---

## 4.3 Abel tail identity

absolute tail norm だけでは粗すぎるため、moving-frame series を Abel correction で分解した。

主要モジュール:

```text
EtaCriticalMirrorPairedAbelTransform
EtaCriticalMirrorPairedAbelCorrection
EtaCriticalMirrorPairedAbelLimit
EtaCriticalMirrorPairedAbelProjectionTail
EtaCriticalMirrorPairedFrameAbelTailIdentity
```

complex moving tail:

```lean
etaCriticalMirrorRotatedDefectPairTail K s
```

Abel correction tail:

```lean
etaCriticalMirrorPairedFrameCorrectionTail K s
```

中心恒等式:

$$
B_{K-1}\operatorname{Tail}(K)
=
\operatorname{RotatedTail}(K)
+
\operatorname{CorrectionTail}(K-1)
$$

Lean:

```lean
etaPairBaseRotation_pred_mul_defectPairTail_eq_rotatedTail_add_correctionTail
```

projection 版:

$$
P_s\!\left(B_{K-1}\operatorname{Tail}(K)\right)
=
\operatorname{RotatedProjectionTail}(K)
+
\operatorname{CorrectionProjectionTail}(K-1)
$$

Lean:

```lean
etaCriticalMirrorPredecessorFrameWholeTailProjection_eq_rotatedProjectionTail_add_correction
```

---

## 4.4 Abel correction tail upper bound

主要モジュール:

```text
EtaCriticalMirrorPairedFrameAbelCorrectionTailBound
```

correction complex norm と projection tail に、明示的 power upper bound を置いた。

概形は、$m.re=1-\sigma$ として、

$$
\operatorname{CorrectionBound}(K)
=
O\!\left(K^{-(1-\sigma)}\right)
+
O\!\left(K^{-\sigma}\right)
$$

projection 版にはさらに $|t|$ が掛かる。

会話上で整理した leading constants の概形:

$$
4t^2\frac{\|m\|}{(1-\sigma)^2}K^{\sigma-1}
+
4t^2\frac{\|s\|}{\sigma^2}K^{-\sigma}
$$

右側 $\frac12<\sigma$ では、第1項 $K^{\sigma-1}$ が遅く減衰する。

左側 $\sigma<\frac12$ では、第2項 $K^{-\sigma}$ が遅く減衰する。

主要結果:

```lean
eventually_abs_etaCriticalMirrorPairedFrameCorrectionProjectionTail_le_powerBound
```

---

## 4.5 Moving projection tail lower bound

主要モジュール:

```text
EtaCriticalMirrorPairedFrameMovingProjectionTailMargin
```

moving projection tail を有限 block と後続 tailへ厳密分解した。

$$
\operatorname{ProjectionTail}(K)
=
\sum_{j<N}\operatorname{PairProjection}(K+j)
+
\operatorname{ProjectionTail}(K+N)
$$

後続 tail も同じ符号なので、common-frame のように margin を半分へ落とす必要がない。

右側:

$$
\operatorname{RightBlockMarginSum}(K,N)
<
\operatorname{ProjectionTail}(K)
$$

左側:

$$
\operatorname{LeftBlockMarginSum}(K,N)
<
-\operatorname{ProjectionTail}(K)
$$

主要結果:

```lean
eventually_rightBlockMarginSum_lt_rotatedDefectProjectionTail

eventually_leftBlockMarginSum_lt_neg_rotatedDefectProjectionTail
```

---

## 5. Positive-density block

主要モジュール:

```text
EtaCriticalMirrorPairedFramePositiveDensityBlock
```

sublinear schedule では block margin と correction bound の比が零へ行くため、正密度 schedule を導入した。

```lean
structure EtaPairPositiveDensityBlockSchedule where
  blockLength : ℕ → ℕ
  density : ℝ
  density_pos : 0 < density
  blockLength_tendsto_atTop :
    Tendsto blockLength atTop atTop
  relativeLength_tendsto_density :
    Tendsto
      (fun K =>
        (blockLength K : ℝ) /
          etaPairFrameLeftEndpoint K)
      atTop (nhds density)
```

つまり、

$$
\frac{N(K)}{2K+1}\longrightarrow\rho,
\qquad \rho>0
$$

とする。

canonical example:

```lean
etaPairHalfDensityBlockSchedule
```

これは、

$$
N(K)=K
$$

なので、

$$
\rho=\frac12
$$

となる。

Abel moving-frame 経路では、密度を小さくする必要はない。

common-frame 経路へ戻る場合だけ、

```lean
SmallAngleAdmissible S s
```

を別途要求する。

---

## 6. 最新層: pair / block margin の power lower bound

主要モジュール:

```text
EtaCriticalMirrorDefectPairMarginPowerLowerBound
```

### 冪恒等式

右側 integrand の radial と weight をまとめた。

$$
R_s(x)W_s(x)=x^{\sigma-2}
$$

Lean:

```lean
etaPairRadialDecay_mul_continuousWeightR_eq_rpow
```

### Pair lower bound

右側:

$$
\frac{t^2}{4}(2k+2)^{\sigma-2}
\le
M_k^+(s)
$$

左側:

$$
\frac{t^2}{4}(2k+2)^{-\sigma-1}
\le
M_k^-(s)
$$

Lean:

```lean
etaCriticalMirrorRightPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero

etaCriticalMirrorLeftPairMarginPowerLowerBound_le_of_nontrivialRiemannZetaZero
```

### Finite block lower bound

右側:

$$
N\frac{t^2}{4}
\left(2(K+N)+2\right)^{\sigma-2}
\le
\sum_{j<N}M_{K+j}^+(s)
$$

左側:

$$
N\frac{t^2}{4}
\left(2(K+N)+2\right)^{-\sigma-1}
\le
\sum_{j<N}M_{K+j}^-(s)
$$

Lean:

```lean
etaCriticalMirrorRightBlockMarginPowerLowerBound_le

etaCriticalMirrorLeftBlockMarginPowerLowerBound_le
```

これらは任意の有限 $K,N$ に対する定理であり、schedule には依存しない。

---

## 7. 現在の未解決条件

現在、off-critical exclusion の定量部分は、概ね次へ縮約されている。

右側:

$$
\operatorname{CorrectionProjectionPowerBound}(K-1)
<
\operatorname{RightBlockMarginSum}(K,N(K))
$$

左側:

$$
\operatorname{CorrectionProjectionPowerBound}(K-1)
<
\operatorname{LeftBlockMarginSum}(K,N(K))
$$

これが成立すれば、moving projection tail が correction tail を上回り、predecessor-frame whole tail の符号を確定できる。

ただし、ここで重要な注意が二つある。

### 注意1: 現在の correction norm bound は粗い

block lower bound と correction upper bound は同じ主次数になったが、定数が勝てるとは限らない。

正密度 schedule で、

$$
\frac{N(K)}{2K+1}\longrightarrow\rho
$$

とすると、右 block lower bound を $K^{1-\sigma}$ で正規化した候補定数は、

$$
t^2\rho\,2^{\sigma-3}
(1+2\rho)^{\sigma-2}
$$

左 block lower bound を $K^\sigma$ で正規化した候補定数は、

$$
t^2\rho\,2^{-\sigma-2}
(1+2\rho)^{-\sigma-1}
$$

一方、粗い correction projection bound の leading constant は、概形として、

右側:

$$
4t^2\frac{\|m\|}{(1-\sigma)^2}
$$

左側:

$$
4t^2\frac{\|s\|}{\sigma^2}
$$

となる。

$\|s\|$ と $\|m\|$ が入るため、現在の norm majorant はかなり大きい。  
現在の bound で domination が成立すると決めつけてはいけない。

まず normalized constant audit を行い、勝敗を厳密に確認する。

### 注意2: whole tail の strict sign だけでは矛盾ではない

仮に、

$$
0<
P_s\!\left(B_{K-1}\operatorname{Tail}(K)\right)
$$

が eventually 成立しても、その値が零へ近づくことは可能。

たとえば正の数列 $1/K$ は零へ収束する。

さらに frame $B_{K-1}$ 自体も $K$ とともに変わる。

したがって、

```text
eventually positive
+
tends to zero
```

だけから矛盾を主張してはいけない。

最終 closure には、さらに次のいずれかが必要。

```text
1. 固定 frame で零から離れる lower bound
2. normalized tail の非零極限と、それを零に強制する別恒等式
3. fixed-frame partial sum の単調性と zero endpoint の不整合
4. frame winding を含む不変量の非消滅
```

現時点では、この最終 invariant はまだ得られていない。

---

## 8. 次の ROADMAP

## Phase 0: 最新 local build / test

最初に、

```bash
./lean-build.sh && ./lean-test.sh
```

を行う。

最新 PowerLowerBound 層で出やすい箇所:

```text
intervalIntegral.integral_const の simp
Real.antitoneOn_rpow_Ioi_of_exponent_nonpos の引数順
Finset.range の定数和
Nat.cast と Real.rpow の正規化
```

エラーがあれば、ユーザー側 fix commit と直前 head の差分だけレビューする。

---

## Phase 1: normalized block lower bound

新規候補:

```text
EtaCriticalMirrorPairedFrameNormalizedConstantAudit.lean
```

まず endpoint 比を固定する。

$L_K=2K+1$ とすると、

$$
\frac{N(K)}{L_K}\longrightarrow\rho
$$

また、

$$
\frac{2(K+N(K))+2}{L_K}
\longrightarrow
1+2\rho
$$

を証明する。

その後、右 block lower bound を $L_K^{1-\sigma}$ で正規化する。

$$
L_K^{1-\sigma}
\operatorname{RightBlockPowerLowerBound}
\longrightarrow
\frac{t^2}{4}
\rho(1+2\rho)^{\sigma-2}
$$

左側は $L_K^\sigma$ で正規化する。

$$
L_K^\sigma
\operatorname{LeftBlockPowerLowerBound}
\longrightarrow
\frac{t^2}{4}
\rho(1+2\rho)^{-\sigma-1}
$$

まず $L_K$ 基準で証明し、必要なら後で $K$ 基準へ変換する。  
$2$ の定数を早い段階で散らさない方が Lean では安定する。

---

## Phase 2: normalized correction upper bound

correction projection power bound を同じ基準で正規化する。

右側 $\frac12<\sigma$:

$$
L_K^{1-\sigma}
\operatorname{CorrectionProjectionPowerBound}(K-1)
$$

左側 $\sigma<\frac12$:

$$
L_K^\sigma
\operatorname{CorrectionProjectionPowerBound}(K-1)
$$

それぞれ dominant term と消える term を分離する。

右側では、

$$
K^{\sigma-1}
$$

側だけが残り、

$$
K^{-\sigma}
$$

側は正規化後に零へ行く。

左側では逆になる。

---

## Phase 3: density 定数の勝敗監査

右側の density factor:

$$
f_\sigma(\rho)
=
\rho(1+2\rho)^{\sigma-2}
$$

左側:

$$
g_\sigma(\rho)
=
\rho(1+2\rho)^{-\sigma-1}
$$

候補最大点は、

右側:

$$
\rho=\frac{1}{2(1-\sigma)}
$$

左側:

$$
\rho=\frac{1}{2\sigma}
$$

である。

この最大値を correction constant と比較する。

ここで current norm bound が勝てないことが確認された場合は、それを失敗として隠さず、次の事実として固定する。

```text
absolute norm / triangle majorant は closure に十分でない
```

この監査は無駄ではなく、signed correction 評価へ移る正当な分岐条件になる。

---

## Phase 4: signed Abel correction projection

新規候補:

```text
EtaCriticalMirrorPairedFrameSignedCorrectionProjection.lean

EtaCriticalMirrorPairedFrameSignedCorrectionTailBound.lean
```

現在の correction bound は、

```text
abs projection
≤ |t| × complex norm
≤ majorant tsum
```

と進むため、位相情報を全て失っている。

次は correction term の定義を直接展開し、

```text
frame step difference
paired partial / tail
signed vertical projection
```

の相互作用を見る。

狙い:

```text
1. correction projection の主項を明示
2. right / left で不要な主項が符号相殺するか確認
3. norm に含まれる ||s||, ||m|| を除去または縮小
4. 一段速い減衰、または小さい leading constant を得る
```

定義の index は既存 AbelTransform / AbelCorrection の式を正本とし、記憶から推測して書かない。

---

## Phase 5: final closure invariant

correction domination が成功しても、tail の strict sign だけでは RH は閉じない。

次に必要なのは、変動 frame を超えて残る量。

候補:

```text
A. normalized predecessor-frame tail limit
B. frame-corrected invariant
C. fixed subsequence rotation + normalized lower bound
D. Abel total correction の非消滅と zero-locus identity の衝突
E. block-to-block transitionで保存される winding / pressure
```

ここでは必ず、

```text
何が zero に強制されるのか
何が nonzero に強制されるのか
両者は同じ量か
```

を Lean の型レベルで確認してから contradiction theorem を置く。

---

## 9. やってはいけない論理飛躍

### Growing intersection の誤り

次は一般には成り立たない。

```text
∀ j, eventually P(K,j)
⇒
eventually ∀ j < N(K), P(K,j)
```

現在は `eventually_all_nat_add_*` により、threshold 以後の全 offset を一括で覆う方法を使用している。

### Positive sequence と zero limit

次は矛盾しない。

$$
0<a_K
$$

かつ、

$$
a_K\longrightarrow0
$$

したがって strict sign のみで closure を宣言しない。

### Moving frame と fixed frame

$B_K$ が $K$ で変化する場合、各 $K$ で同じ符号でも fixed half-plane certificate とは限らない。

### Sublinear block の再使用

correction と同じ主次数を得るには、

$$
\frac{N(K)}{K}
$$

が正の定数程度必要。

sublinear schedule を domination 比較へ戻さない。

### Coarse correction bound の過信

現在の correction power bound は安全だが粗い。

三角不等式で得た上界が大きすぎる場合、数学的対象が失敗したのではなく、評価方法が粗すぎる。

---

## 10. 実装上の運用規則

- Lean 4.26.0 未満の API は使用しない。
- 現在は mathlib 4.32.2 系。
- production module と regression module を一対で追加する。
- production export: `lean/dk_math/DkMath/RH.lean`
- regression export: `lean/dk_math/DkMathTest.lean`
- PR 作成前は GitHub Actions を見ない。
- ユーザーの local build / test Green を正本とする。
- 軽微な API 修正は、数学的意味が変わったかどうかを必ずレビューする。
- 新しい theorem は、一度に大きな contradiction を狙わず、exact identity、upper/lower bound、eventual wrapper の順で分ける。

---

## 11. 直近モジュール一覧

```text
EtaCriticalMirrorPairedFrameBlockMarginDomination
EtaCriticalMirrorPairedFrameFiniteBlockCertificate
EtaCriticalMirrorPairedFrameGrowingBlockGeometry
EtaCriticalMirrorPairedFrameGrowingBlockCertificate
EtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate
EtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
EtaCriticalMirrorPairedFrameAbelTailIdentity
EtaCriticalMirrorPairedFrameAbelCorrectionTailBound
EtaCriticalMirrorPairedFrameMovingProjectionTailMargin
EtaCriticalMirrorPairedFramePositiveDensityBlock
EtaCriticalMirrorDefectPairMarginPowerLowerBound
```

対応 regression:

```text
CFBRCEtaCriticalMirrorPairedFrameBlockMarginDomination
CFBRCEtaCriticalMirrorPairedFrameFiniteBlockCertificate
CFBRCEtaCriticalMirrorPairedFrameGrowingBlockGeometry
CFBRCEtaCriticalMirrorPairedFrameGrowingBlockCertificate
CFBRCEtaCriticalMirrorPairedFrameGrowingBlockQuantitativeCertificate
CFBRCEtaCriticalMirrorPairedFrameGrowingBlockTailRemainder
CFBRCEtaCriticalMirrorPairedFrameAbelTailIdentity
CFBRCEtaCriticalMirrorPairedFrameAbelCorrectionTailBound
CFBRCEtaCriticalMirrorPairedFrameMovingProjectionTailMargin
CFBRCEtaCriticalMirrorPairedFramePositiveDensityBlock
CFBRCEtaCriticalMirrorDefectPairMarginPowerLowerBound
```

---

## 12. 現在地を一文で表す

現在は、

```text
off-critical local pair pressure
→ moving-frame tail sign
→ Abel correction exact identity
→ correction power upper bound
→ positive-density block margin power lower bound
```

まで Lean で接続されている。

未解決なのは、

```text
normalized leading constants の厳密比較
signed correction による bound 改善
変動 frame を超えて残る final closure invariant
```

の三点。

次の会話では、まず最新 build を通し、その直後に normalized constant audit を開始する。

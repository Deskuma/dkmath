# RH-CFBRC off-critical exclusion — Phase 5 引き継ぎ

作成日: 2026-08-05  
Repository: `Deskuma/dkmath`  
Branch: `wip/RH-CFBRC-off-critical-exclusion-260802-v2`  
Lean / mathlib: Lean 4.32.2 系  
Green head: `06db1f443e2ae923a6df3b7f9c82cd88db6605e9` (`fix: error`)

---

## 0. 新しい会話の開始文

```text
RH-CFBRC off-critical exclusion Phase 5 を続行する。
この handoff を正本とし、GitHub repository Deskuma/dkmath の branch
wip/RH-CFBRC-off-critical-exclusion-260802-v2
の最新 head と対象ファイルを最初に確認する。

PowerTailAbelian 層までユーザー環境で Green 済み。
既存 Green 層を再設計せず、Gate 2 の normalized sine-transport tail limit から始める。
local ./lean-build.sh && ./lean-test.sh を正本とする。
PR は未作成なので GitHub Actions CI を探さない。

DkMath の Core / Beam / Gap / Big とトロミノ論法を守る。
失敗経路も named obstruction / audit として残す。
同じ Lean term 上の zero/nonzero collision が得られるまで RH を主張しない。
```

最短の羅針盤:

```text
一項定数
→ tail 定数
→ correction projection 定数
→ exact Abel balance
→ same-object audit
→ closure または obstruction
```

---

## 1. Git / build checkpoint

```text
head:
  06db1f443e2ae923a6df3b7f9c82cd88db6605e9

previous checkpoint:
  b1a7e5066b64da2d60f3b6630a1450a9d4d625b7

changed file:
  lean/dk_math/DkMath/RH/CFBRC/
    EtaCriticalMirrorPairedFramePowerTailAbelian.lean
```

最新 commit は Lean 4.32.2 用の proof engineering 修正で、一般 Abelian theorem の数学的主張は不変。

```text
Nat.cast / Real.rpow の正規化
Tendsto の convert / funext
residual cancellation の ring_nf
暗黙引数 D の明示
tsum_mul_left の明示
norm / abs の乗算方向調整
```

ユーザー環境で次が成功済み。

```bash
cd lean/dk_math
./lean-build.sh && ./lean-test.sh
```

PR は未作成。CI は存在しない。local build / test が正本。

---

## 2. DkMath 設計哲学を Phase 5 へ適用する

### Core / Beam / Gap / Big

```text
Core:
  Lean Green で確定した定義、恒等式、極限、反証

Beam:
  Core から final closure へ伸ばす候補経路

Gap:
  zero-forced と nonzero-forced を同じ対象へ接続する未完成部分

Big:
  off-critical exclusion の完全な Lean 証明
```

$$
\mathrm{Big}=\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}
$$

Gap を証明済み Core と偽って埋めない。

### トロミノ論法

```text
Core theorem:
  動かない exact fact を固定

Beam theorem:
  closure 候補へ進む

Obstruction theorem:
  閉じない条件を False / audit として固定

Gap theorem:
  本当に不足している橋を抽出

Big theorem:
  Core + Beam + Gap を合成
```

粗い norm route は既に、

```text
EtaCriticalMirrorPairedFrameNormalizedCoarseCorrectionObstruction
```

として Core 化済み。`absolute norm + triangle inequality` だけの経路へ戻らない。

### 禁止事項

```text
- eventually positive と tends to zero だけで矛盾を作らない
- moving frame と fixed frame を同一視しない
- K、K+1、K-1 の shift を省略しない
- zero-forced と nonzero-forced の same-object bridge を省略しない
- 過去の可視化や会話着想を Lean Core と扱わない
- Green 層を理由なく大改造しない
```

---

## 3. 記号と index discipline

非自明零点を $s=\sigma+it$、critical mirror を $m=\operatorname{criticalMirror}(s)$ とする。

$$
m.re=1-\sigma
$$

主要対象:

```lean
etaPairBaseRotation s k
etaCriticalMirrorDefectPairTerm s k
etaCriticalMirrorPairFrameRotatedDefectTail s k
etaCriticalMirrorSignedVerticalProjection s z
```

signed projection は $P_s(z)=s.im\cdot z.im$。

index:

```text
frame k left endpoint:
  2k + 1

etaPairTail (k + 1) leading unsigned-vector index:
  2(k + 1)

その自然数 base:
  2k + 3
```

base rotation は $2k+1$、leading endpoint は $2k+3$。有限段階では residual one-step phase が残り、極限で零へ行く。

---

## 4. Phase 1〜4 の状態

```text
Phase 1 normalized block lower bound:
  完了

Phase 2 normalized correction upper bound:
  完了

Phase 3 density constant audit:
  完了。粗い norm route は obstruction

Phase 4 signed correction main term:
  完了。PowerTailAbelian まで Green
```

Phase 4 の証明鎖:

```text
signed correction exact split
→ sine transport + cosine loss
→ normalized cosine-loss vanishing
→ rotated defect-tail exact split
→ eta-tail Euler half decomposition
→ normalized rotated eta-tail constant
→ right / left rotated defect-tail constants
→ scaled sine coefficient limit
→ right / left sine-transport term constants
→ general power-tail Abelian theorem
```

主要モジュール:

```text
EtaCriticalMirrorPairedFrameSignedCorrectionDecomposition
EtaCriticalMirrorPairedFrameCosineLossBound
EtaCriticalMirrorPairedFrameNormalizedCosineLossAudit
EtaCriticalMirrorPairedFrameSineTransportReduction
EtaCriticalMirrorPairedFrameSineTransportSignAudit
EtaCriticalMirrorPairedFrameRotatedDefectTailSplit
EtaCriticalMirrorPairedFrameRotatedTailIntegral
EtaCriticalMirrorPairedFrameEtaTailEulerHalf
EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit
EtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit
EtaCriticalMirrorPairedFramePowerTailAbelian
```

---

## 5. 確定した数学的 Core

### Eta tail Euler half

```lean
etaPairTail_eq_half_endpoint_add_eulerRemainderTail
```

$$
\operatorname{etaPairTail}(K,z)=\frac12\operatorname{etaUnsignedVector}(z,2K)+\operatorname{EulerRemainderTail}(K,z)
$$

$$
\|\operatorname{EulerRemainderTail}(K,z)\|=O\!\left(K^{-z.re-1}\right)
$$

### Normalized eta-tail constant

```lean
etaPairIndexNormalizedTailConstantReal z
```

$$
C_{\mathbb R}(z)=\frac12\left(\frac12\right)^{z.re}>0
$$

右側 $\frac12<s.re$:

$$
(k+1)^{m.re}\operatorname{RotDefectTail}_k(s)\longrightarrow C(m)
$$

左側 $s.re<\frac12$:

$$
(k+1)^{s.re}\operatorname{RotDefectTail}_k(s)\longrightarrow-C(s)
$$

実部版:

```lean
etaCriticalMirrorRightIndexNormalizedRotatedDefectTail_re_tendsto_constant
etaCriticalMirrorLeftIndexNormalizedRotatedDefectTail_re_tendsto_neg_constant
```

### Scaled sine coefficient

$$
(k+1)\phi_k\longrightarrow s.im
$$

$$
(k+1)c_k\longrightarrow(s.im)^2
$$

```lean
etaCriticalMirrorPairedFrameScaledSineTransportCoefficient_tendsto_sq
```

### Sine-transport term

右側:

$$
(k+1)^{m.re+1}\operatorname{SineTerm}_k(s)\longrightarrow-(s.im)^2C_{\mathbb R}(m)
$$

左側:

$$
(k+1)^{s.re+1}\operatorname{SineTerm}_k(s)\longrightarrow(s.im)^2C_{\mathbb R}(s)
$$

```lean
etaCriticalMirrorRightNormalizedSineTransportTerm_tendsto_constant
etaCriticalMirrorLeftNormalizedSineTransportTerm_tendsto_constant
```

### General power-tail Abelian theorem

$a$ が summable、$\alpha>0$、

$$
(n+1)^{\alpha+1}a_n\longrightarrow D
$$

ならば、

$$
K^\alpha\sum_{n=0}^{\infty}a_{n+K}\longrightarrow\frac{D}{\alpha}
$$

```lean
normalized_realSequenceTail_tendsto
```

monotonicity と eventual sign は不要。

---

## 6. Phase 5 ROADMAP

### Gate 1 — PowerTailAbelian

状態: **完了・Green**。再実装しない。

### Gate 2 — Normalized sine-transport tail limit

候補:

```text
EtaCriticalMirrorPairedFrameNormalizedSineTransportTailLimit.lean
```

右側:

$$
D_R=-(s.im)^2C_{\mathbb R}(m),\qquad \alpha_R=m.re
$$

$$
K^{\alpha_R}\operatorname{SineTransportTail}(K,s)\longrightarrow\frac{D_R}{\alpha_R}<0
$$

左側:

$$
D_L=(s.im)^2C_{\mathbb R}(s),\qquad \alpha_L=s.re
$$

$$
K^{\alpha_L}\operatorname{SineTransportTail}(K,s)\longrightarrow\frac{D_L}{\alpha_L}>0
$$

最初に既存コードを検索する。

```text
- sine-transport term sequence の定義名
- sine-transport tail の定義名
- sequence の Summable theorem
- tail index が K か K+1 か
- correction projection exact split theorem
```

実装順:

```text
1. term sequence と realSequenceTail の exact identification
2. right / left summability
3. normalized_realSequenceTail_tendsto の right / left 適用
4. explicit constants の strict sign
5. regression test
6. DkMath.RH / DkMathTest export
```

### Gate 3 — Correction projection tail constant

候補:

```text
EtaCriticalMirrorPairedFrameNormalizedCorrectionProjectionTailLimit.lean
```

既存構造:

```text
CorrectionProjectionTail
  = SineTransportTail
  + CosineLossTail
```

normalized cosine-loss tail は零へ行く。よって correction projection tail は sine tail と同じ主定数を持つはず。

右側:

$$
K^{m.re}\operatorname{CorrectionProjectionTail}(K,s)\longrightarrow\frac{D_R}{m.re}<0
$$

左側:

$$
K^{s.re}\operatorname{CorrectionProjectionTail}(K,s)\longrightarrow\frac{D_L}{s.re}>0
$$

`K-1` を使う Abel identity へ接続するとき、eventually $K\ge1$ と shift ratio を明示する。

### Gate 4 — Normalized Abel balance audit

候補:

```text
EtaCriticalMirrorPairedFrameNormalizedAbelBalanceAudit.lean
```

exact identity:

$$
P_s\!\left(B_{K-1}\operatorname{Tail}(K)\right)=\operatorname{RotatedProjectionTail}(K)+\operatorname{CorrectionProjectionTail}(K-1)
$$

同じ normalization で監査する。

```text
A. predecessor-frame whole-tail projection
B. moving-frame rotated projection tail
C. correction projection tail
```

結果を先に決めない。

```text
Case A:
  constants collide
  → zero/nonzero collision の候補

Case B:
  constants agree with exact Abel identity
  → current route は closure しない
  → balance / obstruction theorem として Core 化
```

必ず分離する theorem:

```text
1. zero-forced
2. nonzero-forced
3. same-object identification
4. constant ≠ 0
5. final contradiction
```

### Gate 5 — Closure decision

Gate 4 が衝突を与える場合のみ候補:

```text
EtaCriticalMirrorPairedFrameOffCriticalContradiction.lean
```

単に各項が正負を保ちながら零へ収束する場合は contradiction ではない。

Gate 4 が整合する場合の次 Gap:

```text
fixed-frame invariant
fixed-limit subsequence rotation
winding / pressure conservation
zero-locus identity との直接接続
finite endpoint identity との衝突
phase drift / π-jump invariant の Lean 再構成
```

---

## 7. 優先ファイル

```text
1. EtaCriticalMirrorPairedFramePowerTailAbelian.lean
2. EtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit.lean
3. EtaCriticalMirrorPairedFrameSineTransportReduction.lean
4. EtaCriticalMirrorPairedFrameSignedCorrectionDecomposition.lean
5. EtaCriticalMirrorPairedFrameNormalizedCosineLossAudit.lean
6. EtaCriticalMirrorPairedFrameAbelTailIdentity.lean
7. EtaCriticalMirrorPairedFrameRotatedDefectTailSplit.lean
8. EtaCriticalMirrorPairedFrameNormalizedDominantTailLimit.lean
```

Tests:

```text
DkMathTest/RH/CFBRCEtaCriticalMirrorPairedFramePowerTailAbelian.lean
DkMathTest/RH/CFBRCEtaCriticalMirrorPairedFrameNormalizedSineTransportTermLimit.lean
DkMathTest/RH/CFBRCEtaCriticalMirrorPairedFrameNormalizedDominantTailLimit.lean
```

---

## 8. Build / write 規則

```bash
cd lean/dk_math
lake build DkMath.RH.CFBRC.<ModuleName>
lake build DkMathTest.RH.<TestModuleName>
./lean-build.sh && ./lean-test.sh
```

```text
- update 前に最新 blob SHA を取得
- 同じ path への write は逐次実行
- production → test → DkMath.RH → DkMathTest の順
- ユーザーの local Green まで Green と主張しない
- compatibility fix は数学的意味の差分監査を行う
```

---

## 9. 情報源

### Core — Green source code

```text
repository:
  https://github.com/Deskuma/dkmath

branch:
  wip/RH-CFBRC-off-critical-exclusion-260802-v2

head:
  06db1f443e2ae923a6df3b7f9c82cd88db6605e9

commit:
  https://github.com/Deskuma/dkmath/commit/06db1f443e2ae923a6df3b7f9c82cd88db6605e9
```

旧 handoff:

```text
lean/dk_math/DkMath/RH/CFBRC/docs/
  RH_CFBRC_off_critical_exclusion_handoff_2026-08-04.md
```

### Design — DkMath philosophy

```text
https://github.com/Deskuma/dkmath/blob/main/lean/dk_math/docs/dev/
petal-obstruction-260615/DkMath-Tromino-%E8%AB%96%E6%B3%95.md

https://github.com/Deskuma/dkmath/blob/main/docs/
cosmic-formula-incompleteness-theorem.md
```

### Conversation source

ChatGPT project `Riemann Hypothsis` の本会話を、2026-08-03〜2026-08-05 の Phase 4→5 作業ログとして参照する。

検索語:

```text
EtaTailEulerHalf
NormalizedDominantTailLimit
NormalizedSineTransportTermLimit
PowerTailAbelian
ROADMAP
Phase 5
```

repository snapshot:

```text
lean/dk_math/DkMath/RH/CFBRC/docs/sources/
  RH_CFBRC_phase4_to_phase5_conversation_digest_2026-08-05.txt
```

snapshot は Phase 4→5 の checkpoint / ROADMAP 抜粋。完全な会話文脈は ChatGPT project conversation を正本とする。

### Historical / conceptual Beam

次は着想源であり Green Lean theorem の代替ではない。

```text
step-all-v2-ja.md
OOL_KND_RH_supplement_v4_2_r1.pdf
OOL_KND_RH_SCT_Prime_Counting_via_Phase_Displacement-pub-v1-r0.pdf
RH-ool-main-proof-pub-v3.5-en-ai-viXra.pdf
RH-ool-supplement-pub-v4.2.pdf
CF2Dとゼータ関数.txt
数学の新成果.txt
リーマン予想解決法 conversation log
論文とリーマン予想考察 conversation log
```

中心語彙:

```text
phase drift
π-jump
mirror symmetry
non-periodic prime phase
C/S two-component balance
fixed invariant
zero-locus alignment
```

必ず現在の Lean 型へ翻訳し、証明してから Core に入れる。

source snapshot:

```text
__snapshot-dk_math-lean-code-260804-2149.tar.gz
__snapshot-dk_math-lean-code-260804-2149.tar.gz.sha256
```

snapshot は最新 branch より古い。実装判断では GitHub branch を優先する。

---

## 10. Phase 5 の完了条件

```text
Outcome A — Closure:
  同一の Lean term または normalized limit が
  zero と nonzero の双方に強制され、
  off-critical contradiction が Green。

Outcome B — Exact obstruction:
  Abel balance の constants が整合し、
  current Beam では closure しないことが named theorem として Green。
  次の Gap が明示される。
```

どちらも正しい Core の増加である。

最後の問い:

```text
零点条件が zero に強制する対象と、
漸近解析が nonzero に強制する対象は、
Lean 上で本当に同じものか。
```

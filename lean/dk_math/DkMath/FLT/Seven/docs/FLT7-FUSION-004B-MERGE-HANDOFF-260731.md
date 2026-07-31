# FLT7-FUSION-004B 合流・再開指示書

作成日: 2026-07-31
Repository: `Deskuma/dkmath`
Work dir. : `lean/dk_math/DkMath/FLT/Seven`

---

## 0. この文書の目的

本書は、FLT7-FUSION-004B / ULTRA U1.1–U1.6 の成果を `develop` へ合流し、次回の再構成遠征を迷わず開始するための自己用指示書である。

この文書を読む時点では、まず GitHub current source を正とする。古い snapshot、会話ログ、生成済みサマリーは補助資料として扱う。

---

## 1. 現在の GitHub 状態

```text
Pull request:
  #74

Title:
  feat(FLT7): begin 004B conjugate-prime fibre reconstruction

Base:
  develop

Head:
  wip/FLT7-fusion-004b-conjugate-fiber-260730

Head commit:
  550b3f1c4503126b6db65fc79d9066bda9a1d43f

State:
  open
  draft
  mergeable

Branch relation:
  ahead of develop by 13 commits
  behind develop by 0 commits

Diff:
  29 changed files
  +9105
  -21

Latest Lean CI:
  run 445
  success
```

作業ツリーと index は空であり、U1.5 と U1.6 は独立コミットとして push 済みである。

---

## 2. マージ判断

### 判定

```text
MERGE RECOMMENDED
```

PR #74 は `develop` へ合流してよい。

理由:

1. U1.1–U1.6 が意味のあるイベント境界で完了している。
2. focused build、公開 facade build、プロジェクト全体 build が成功している。
3. Lean CI が成功している。
4. branch は `develop` より 13 commits ahead / 0 behind である。
5. 新規 Lean 実装に `sorry`、`admit`、明示的 `axiom`、`native_decide` はない。
6. 公理依存は標準的な `propext`、`Classical.choice`、`Quot.sound` のみ。
7. 未完成部分は theorem の欠落ではなく、明示的な obligation として分離されている。
8. 次の研究は新しい再構成イベントであり、この PR へ継ぎ足すべきではない。

### マージ前に必要な文書操作

現在の PR title / body は「共役素理想 fibre equality を開始する」という初期状態のままであり、最終成果を表していない。

コード上の blocker ではないが、研究履歴としては更新必須。

推奨タイトル:

```text
feat(FLT7): extract oriented seventh powers and isolate reconstruction boundary
```

推奨 summary:

```text
FLT7-FUSION-004B closes the conjugate-prime fibre, global oriented
factorization, exact carrier valuation ownership, seventh-power residual
ideal extraction, and element-level oriented power equations.

The final U1.5/U1.6 checkpoints formally isolate the nontrivial mu_7 gauge,
exclude naive additive-chart projections, prove the internal seven-adic
depth drop 5 -> 4, and identify counterexample reconstruction plus an
indexed recursive state bridge as the exact remaining obligations.

This PR does not claim a reconstructed primitive FLT7 counterexample,
recursive descent, terminal contradiction, or FLT7.
```

### マージ方式

```text
Use:
  merge commit

Do not use:
  squash merge
```

理由:

- U1.1–U1.6 は独立した数学イベントである。
- U1.5 の不可能境界と U1.6 の下降責務を別履歴として保存する価値が高い。
- 後の bisect、引用、研究日誌、定理来歴で checkpoint commit が必要になる。

---

## 3. マージ手順

GitHub UI を使う場合:

```text
1. PR #74 の title と body を最終成果へ更新
2. Draft を Ready for review へ変更
3. Lean CI success を再確認
4. Create a merge commit で develop へ merge
5. develop の head と公開 CI を確認
6. 次 branch を作成してから旧 branch を削除
```

CLI を使う場合の概念手順:

```bash
git fetch origin

gh pr ready 74
gh pr merge 74 --merge

git switch develop
git pull --ff-only origin develop
```

旧 branch は、次 branch を merge 後の `develop` から作成したことを確認してから削除する。

---

## 4. PR #74 の数学的到達点

### 4.1 共役素理想 fibre

初期義務だった reverse containment を閉じ、実三次素理想の degree-six extension が oriented / conjugate の二つの degree-one prime の積として正確に復元される。

```text
map(ofReal, realPrime)
  =
orientedPrime * conjugatePrime
```

ここから先の global oriented factorization の局所基盤が完成した。

### 4.2 U1.1 — global oriented factorization

三つの real rotations と quadratic star を組み合わせた六つの prime address を固定した。

```text
3 real phases
  x
2 quadratic orientations
  =
6 Galois/star addresses
```

各 rational prime support に対して:

- oriented prime
- conjugate prime
- rotation coherence
- star coherence
- pairwise comaximality
- finite ideal product reconstruction

を保持する global factorization が完成した。

### 4.3 U1.2 — exact oriented carrier valuation ownership

Checkpoint:

```text
88b27e1035ca4fc6431284ddc7aed391fc991745
feat(FLT7): close oriented carrier valuation ownership
```

完成内容:

- ramified prime above seven は各 carrier に exact multiplicity one
- quotient-root support の各 prime は選択された orientation に exact `padicValNat` exponent で入る
- competing orientation への混入を排除
- 予測 factor ideal と carrier principal ideal の exact equality

この時点で carrier の prime ownership は完全に確定した。

### 4.4 U1.3 — seventh-power residual ideal extraction

Checkpoint:

```text
675a57469fd780e54a2353d8f47c3024f06de46b
feat(FLT7): extract oriented seventh-power residual ideals
```

完成内容:

```text
carrier ideal
  =
ramified ideal
  *
loaded ideal
  *
residual ideal ^ 7
```

- full quotient support へ load exponent を zero-extension
- residual exponent を各 prime で exact に定義
- oriented / conjugate ideal equation
- star coherence
- residual seventh-power provenance

U1.3 は ideal-level event として独立固定された。

### 4.5 U1.4 — concrete PID と element-level power

Checkpoint:

```text
de1848ee4ed62aca1c02c6031cbf01b705267bee
```

完成内容:

- abstract seventh cyclotomic ring of integers から concrete carrier への全射
- full ring-of-integers 同型を作らず principal ideal property を移送
- loaded ideal と residual ideal の principal generators を取得
- associated unit を load generator へ吸収
- 一般の unit を seventh power と仮定しない

正確な元レベル式:

```text
carrier
  =
loadElement * residualRoot ^ 7
```

provenance:

```text
span {loadElement}
  =
loadedIdeal

span {residualRoot}
  =
residualIdeal
```

conjugate witnesses は独立選択せず、oriented witnesses の literal star として構成された。

### 4.6 U1.5 — cyclotomic additive-chart boundary

Checkpoint:

```text
2dc8423e632077c43c6d363f07a736316c59705b
feat(FLT7): isolate cyclotomic additive-chart boundary
```

Lean が確定したこと:

1. 六 Galois phase の積は additive chart ではなく integral norm に潰れる。
2. integral coordinates は乗法的でない。
3. concrete carrier から `ℤ` への unital ring homomorphism は存在しない。
4. visible signed endpoints は `SignedFermatSevenChart` を作らない。
5. residual root は非自明な `mu_7` gauge を持つ。

```text
r != zeta * r

r ^ 7
  =
(zeta * r) ^ 7

span {r}
  =
span {zeta * r}

coordinates r
  !=
coordinates (zeta * r)
```

したがって、ideal と seventh power の情報だけでは additive integer coordinates を復元できない。

Outcome C:

```text
mu_7-invariant extractor
or
canonical phase normalization

plus

independent additive seventh-power identity
```

が必要である。

### 4.7 U1.6 — strict descent failure boundary

Checkpoint:

```text
550b3f1c4503126b6db65fc79d9066bda9a1d43f
feat(FLT7): isolate strict descent failure boundary
```

既存 ramified extraction 内の二 carrier:

```text
internalDepthFourCarrier
outerDepthFiveCarrier
```

Lean が証明:

```text
padicValNat 7 internalDepthFourCarrier
  =
4

padicValNat 7 outerDepthFiveCarrier
  =
5

padicValNat 7 internalDepthFourCarrier
  <
padicValNat 7 outerDepthFiveCarrier
```

重要:

```text
strict inequality は完成済み
```

不足しているのは、depth-four coordinate を新しい正の原始 FLT7 counterexample の exceptional carrier として再構成すること。

正確な receiver:

```lean
InternalDepthFourCounterexampleReconstructionObligation p :=
  ∃ (x y z : ℕ) (route : AwayValuationTransferPacket x y z),
    route.carrier = internalDepthFourCarrier p
```

Lean は次を証明済み:

```text
reconstruction obligation
  iff
strict descent candidate
```

つまり、再構成が得られれば strict depth drop は自動で付く。

---

## 5. 現在証明していないもの

次は未証明であり、今回の PR は主張しない。

```text
- residual root の canonical integer phase
- mu_7-invariant additive extractor
- 新しい三整数の Fermat identity
- 新三整数の nonzero / positivity
- primitive coprimality
- signed-to-natural normalization
- original terminal provenance
- InternalDepthFourCounterexampleReconstructionObligation の inhabitant
- generic away-to-away reconstruction
- common indexed well-founded state transition
- recursive descent closure
- terminal contradiction
- FLT7
```

この境界を弱めたり、provider、axiom、typeclass inhabitant として埋めてはならない。

---

## 6. FLT7 の現在地を一行で

```text
乗法的七乗抽出と七進深さ減少は完成した。

未完成なのは、
位相情報を失わずに代数的七乗根から
新しい加法的・正・原始な FLT7 反例へ戻す再構成である。
```

---

## 7. 次回の主戦場

次の研究対象は degree-six ideal theory の追加ではない。

最優先魔核:

```text
seventhPowerSndCore
```

既存恒等式:

```text
seventhPowerSnd(u, v)
  =
7 * v * seventhPowerSndCore(u, v)
```

away packet では:

```text
7 ∤ seventhPowerSndCore(u, v)
```

endpoint product:

```text
y * z * (y + z)
  =
7 * |v| * |seventhPowerSndCore(u, v)|
```

読み:

```text
current exceptional carrier
  -> old root second coordinate |v|
  -> next exceptional carrier candidate
```

FLT7 版 Golden lift が存在するなら、`seventhPowerSndCore` の自己相似分解に現れる可能性が高い。

---

## 8. 次回 branch

PR #74 の merge 後、最新 `develop` から新 branch を作る。

推奨名:

```text
wip/FLT7-fusion-004c-away-reconstruction-260731
```

概念手順:

```bash
git switch develop
git pull --ff-only origin develop
git switch -c wip/FLT7-fusion-004c-away-reconstruction-260731
git push -u origin wip/FLT7-fusion-004c-away-reconstruction-260731
```

新 branch は PR #74 の branch を直接継続しない。必ず merge 済み `develop` を起点とする。

---

## 9. 次回 checkpoint

### R1 — explicit away receiver constructors

目的:

`AwayValuationTransferPacket` の三 sector を `Classical.choice` の外へ明示する。

```text
right
left
sum
```

候補 API:

```lean
awayTransferPacketOfRight
awayTransferPacketOfLeft
awayTransferPacketOfSum
```

成功条件:

- 既存 theorem の薄い明示 constructor
- carrier provenance を definitionally 保持
- 新しい数学主張は行わない
- 一つの module / commit で停止

禁止:

```text
- additive reconstruction
- service provider
- recursive descent
- FLT7 closure
```

### R2 — `seventhPowerSndCore` reconnaissance

調査対象:

```text
- integer factorization
- TraceOne norm representation
- Galois conjugate product
- sign sectors
- gcd / coprimality
- prime support
- endpoint triple factorization
- self-similar seventh-power packet
```

Outcome:

```text
A:
  explicit self-similar lift found

B:
  norm / ideal power representation found

C:
  finite candidate sectors isolated

D:
  this core route cannot provide additive reconstruction
```

Outcome A/B/C/D のいずれかを確定した時点で停止する。

### R3 — phase-indexed candidates

R2 で具体式が出た場合だけ開始する。

```text
r_k = zeta^k * r
k : Fin 7
```

七位相を先に全部構成し、加法 Fermat identity、primitivity、provenance を満たす位相を選別する。

抽象的な lexicographic minimum を canonical phase として採用しない。

### R4 — `AwayCoordinateNormalForm` construction

既存 constructor に必要な事実を供給する。

証明順:

```text
1. Fermat identity
2. positivity / nonzero
3. primitivity
4. 7 ∤ z' - y'
5. coordinate equation
6. exceptional sector
7. new carrier = |old root.snd|
```

### R5 — generic away return

最重要 summit:

```lean
theorem awayRootCounterexampleReconstruction
    {x y z : ℕ}
    (p : AwayValuationTransferPacket x y z) :
    ∃ (x' y' z' : ℕ)
        (q : AwayValuationTransferPacket x' y' z'),
      q.carrier = Int.natAbs p.normal.root.snd
```

特定の depth `5 -> 4` だけで止めず、任意の away state に一般化する。

### R6 — recursive closure

状態:

```lean
structure AwayDescentState where
  x y z : ℕ
  route : AwayValuationTransferPacket x y z
```

measure:

```lean
padicValNat 7 route.carrier
```

generic reconstruction により:

```text
measure(next state)
  <
measure(current state)
```

を得て、`Nat` の well-foundedness と衝突させる。

最後に `ValuationCounterexampleRoute` の ramified / away 両 branch へ接続する。

---

## 10. 次回に避ける道

現時点で主線にしない。

```text
- concrete carrier と full ring of integers の同型
- class group の再計算
- PID の再証明
- さらに巨大な ideal factorization
- norm だけからの integer reconstruction
- integral coordinate を ring hom のように扱う
- 六位相積から additive chart を読む
- arbitrary lexicographic phase normalization
- unit は seventh power と仮定する
- U1.6 obligation を provider / axiom で埋める
```

これらは U1.4–U1.6 の結果により、不要または不十分と判明している。

---

## 11. Codex 停止契約

Codex 自身は利用枠残量を観測できない前提で運用する。

利用率を停止条件に書かない。

次の観測可能な契約を使う。

```text
EXECUTION CONTRACT

- この run は指定された一 Event のみを実行する。
- 最大 new commit 数は 2。
- Outcome A/B/C/D のいずれかを確定したら停止する。
- 次 Event の実装を開始しない。
- 次 Event の先行調査は read-only reconnaissance と候補命題まで。
- 現 Event の focused build、facade build、report、audit、commit 後に停止する。
- 続行にはユーザーの明示的な CONTINUE 指示が必要。
```

推奨 hard gate:

```text
STOP_GATE_REQUIRED
```

ユーザーが次を与えるまで次 Event を開始しない。

```text
CONTINUE_FLT7
```

緊急停止:

```text
EMERGENCY_STOP
```

受信時:

```text
- 新規編集を停止
- index を監査
- current Event 以外を unstage
- focused build
- report / handoff
- 意味のある単独 commit
- push は明示指示がある場合のみ
```

---

## 12. 次回会話の開始プロンプト

```text
賢狼よ、FLT7-FUSION-004B を develop へ統合した地点から、
FLT7-FUSION-004C away reconstruction の設計を再開する。

最初に README.md、AGENT.md、SUMMARY.md を読み、
GitHub current develop と PR #74 の merge commit を確認せよ。
古い snapshot より GitHub current source を優先する。

前 checkpoint:
  PR #74
  final head 550b3f1c
  U1.1–U1.6 complete

Lean が確定したこと:
  - exact conjugate-prime fibre
  - six-address Galois/star coherence
  - exact oriented carrier valuation ownership
  - ramified * loaded * residual^7 ideal factorization
  - carrier = loadElement * residualRoot^7
  - nontrivial mu_7 residual-root gauge
  - naive norm / coordinate additive charts are impossible
  - internal seven-adic depth 5 -> 4
  - strict inequality is complete
  - exact missing receiver is
    InternalDepthFourCounterexampleReconstructionObligation

現在の本質:
  代数的 seventh-power data から、
  位相情報を失わずに新しい正・原始な additive FLT7 packet を
  再構成すること。

次は直ちに ULTRA 実装へ入らず、NORMAL で二段階行う。

R1:
  AwayValuationTransferPacket の right / left / sum 明示 constructor を
  小 checkpoint として切り出す。

R2:
  seventhPowerSndCore(u,v) の factorization / norm / gcd / support /
  self-similar endpoint decomposition を read-only reconnaissance する。

R2 の Outcome A/B/C/D を確定した時点で停止し、
R3 phase-indexed reconstruction へ進むかを再判断する。

禁止:
  full ring-of-integers 同型の追加
  PID / class group の再解析
  norm だけからの整数復元
  arbitrary phase normalization
  obligation の axiom/provider 化
  次 Event の自動開始

停止契約:
  一 run 一 Event
  最大2 commits
  STOP_GATE_REQUIRED
```

---

## 13. 最終記録

```text
PR #74:
  merge recommended

Merge mode:
  merge commit

Checkpoint chain:
  U1.1–U1.6 complete

Final head:
  550b3f1c

Exact remaining boss:
  additive counterexample reconstruction
  plus indexed recursive state/measure bridge

Next first action:
  merge PR #74 into develop
  then create FLT7-FUSION-004C branch
```

この文書を、FLT7-FUSION-004B の正式な合流・再開しおりとする。

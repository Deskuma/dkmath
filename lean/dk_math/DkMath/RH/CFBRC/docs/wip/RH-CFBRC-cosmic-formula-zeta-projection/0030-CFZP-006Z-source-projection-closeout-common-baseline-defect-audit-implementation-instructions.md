# CFZP-0030 — CFZP-006Z source-projection closeout / common-baseline defect audit 実装指示

## 0. Status

- Repository: `Deskuma/dkmath`
- Working branch: `wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`
- Parent implementation: CFZP-006Y
- Expected parent commit: `e54883e5e0a82d9735404244aa84dbfead10d5cf`
- 日本語を正本とする。

006Y までの局所 phase-cell 解析は Green-A とみなす。

ただし CFZP-006 全体の original ROADMAP exit condition はまだ閉じていない。

006Z は **新しい局所枝を増やす段階ではない**。

目的は 006A〜Y を source projection の大局へ戻し、

1. 何が exact に閉じたか、
2. rectangle completion remainder を genuine nonnegative Gap と呼ぶために何が不足しているか、
3. 007 が次に攻めるべき一穴は何か、

を Lean theorem として固定して CFZP-006 を終了することである。

---

# 1. 006 original ROADMAP の exit condition を再確認する

`0000-CFZP-roadmap.md` の CFZP-006 は、同じ source projection の下で概念的に

```text
Π(Big_cosmic)  -> SourceBig
Π(Body_cosmic) -> SourceBody
Π(Gap_cosmic)  -> SourceGap
```

を得て、

```text
SourceBig = SourceBody + SourceGap
```

を閉じることを要求していた。

さらに rectangle ledger と比較して

```text
SourceBig  = RectangleBackground
SourceBody = TopZetaMismatchScalar
```

が exact に出る場合だけ

```text
SourceGap = RectangleBackground - TopZetaMismatchScalar
```

を genuine completion Gap と解釈する設計だった。

006A〜Y では rectangle remainder / interaction / phase event の内部構造は非常に深く exact 化されたが、

```text
nonnegative quadratic Gap
  -> source-side nonnegative minus whole
  -> rectangle completion remainder
```

の same-observable identification は未確定のままである。

006Z はこの点を曖昧にしない。

---

# 2. 006Z の中心発見 — interaction ではなく common baseline が残っている

CS25 には既に exact に

```text
G_X = G_0 - I_X
```

がある。

ここで

```text
G_X := pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
G_0 := pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0
I_X := pascalCenteredXiPrimeSideAggregateRayInteractionEnergy ε W X
```

である。

同じ CS25 には minus whole energy について

```text
Eminus_X = C_X - I_X
```

がある。

ここで

```text
Eminus_X := pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X
C_X      := pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X
```

である。

したがって algebraically

```text
G_X = Eminus_X + (G_0 - C_X)
```

となる。

この最後の差

```text
D_X := G_0 - C_X
```

を 006Z の first-class obstruction とする。

この `D_X` は prime-power event interaction `I_X` の内部符号問題とは別である。

006R〜Y は主に `I_X` を

```text
prime power
-> kernel
-> phase primitive
-> branch-free trig event
-> centered profile
-> derivative core
-> phase cell
```

へ exact 分解した。

しかし `G_X` を nonnegative minus whole と同一視する最後の差では `I_X` が cancellation し、`G_0 - C_X` だけが残る。

**これを006の大局的 closeout とする。**

---

# 3. 推奨 module

新規 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSourceProjectionCloseoutAudit
```

path:

```text
lean/dk_math/DkMath/RH/CFBRC/CosmicFormulaZetaSourceProjectionCloseoutAudit.lean
```

推奨 imports:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaPrimePowerCenteredPhaseCellCoverageAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
import DkMath.RH.CFBRC.CosmicFormulaZetaFinitePolarizationProjection
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideCommonCarrierInteractionCancellationAudit
import Mathlib.Tactic
```

必要なら import を最小化してよいが、依存の意味は上記を保つ。

`DkMath/RH.lean` に public import を追加する。

---

# 4. Gate A — common-baseline defect を first-class 化

推奨 definition:

```lean
noncomputable def cfzp006CommonBaselineDefect
    (ε : ℝ)
    (W : PascalCenteredXiResidueTransportWindow)
    (X : ℕ) : ℝ :=
  pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W 0 -
    pascalCenteredXiPrimeSideAggregateRayCommonEnergy ε W X
```

これは signed quantity である。

非負とも非正とも仮定しない。

---

# 5. Gate B — radial deficit = minus whole + common-baseline defect

006Z の中心 theorem 1。

推奨 theorem:

```lean
cfzp006RadialContactDeficit_eq_rayMinusEnergy_add_commonBaselineDefect
```

hypothesis は最低限

```text
hε : 0 < ε
```

とする。

目標:

```text
pascalCenteredXiPrimeSideFiniteRadialContactDeficit ε W X
  = pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X
    + cfzp006CommonBaselineDefect ε W X
```

proof route:

```text
1. CS25:
   G_X = G_0 - I_X

2. CS25:
   Eminus_X = C_X - I_X

3. unfold D_X = G_0 - C_X

4. ring
```

さらに差分形も公開する。

```lean
cfzp006RadialContactDeficit_sub_rayMinusEnergy_eq_commonBaselineDefect
```

目標:

```text
G_X - Eminus_X = D_X
```

これにより

```text
G_X = Eminus_X
  <-> D_X = 0
```

を exact に公開する。

推奨 theorem:

```lean
cfzp006RadialContactDeficit_eq_rayMinusEnergy_iff_commonBaselineDefect_eq_zero
```

---

# 6. Gate C — rectangle completion remainder の最終形

`CosmicFormulaZetaSourceCompletionGeometryAudit` から既に

```text
G_X = pi * CompletionRemainder_X
```

がある。

したがって heavy rectangle/source hypotheses の下で 006Z の中心 theorem 2 を閉じる。

推奨 theorem:

```lean
cfzp006PiMulCompletionRemainder_eq_rayMinusEnergy_add_commonBaselineDefect
```

目標:

```text
Real.pi * cfzpFiniteRectangleCompletionRemainder ε W X
  = pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X
    + cfzp006CommonBaselineDefect ε W X
```

必要 hypotheses は既存

```text
hε
hSafe
hZeta
hArch
hElem
```

をそのまま使う。

新しい top/Mellin assumptions を追加しない。

続いて normalized form:

```lean
cfzp006CompletionRemainder_eq_rayMinusEnergy_div_pi_add_defect_div_pi
```

目標:

```text
CompletionRemainder_X
  = Eminus_X / pi + D_X / pi
```

を exact に公開する。

---

# 7. Gate D — genuine source minus-whole identification の iff

Gate C から exact に

```text
CompletionRemainder_X = Eminus_X / pi
  <-> D_X = 0
```

を証明する。

推奨 theorem:

```lean
cfzp006CompletionRemainder_eq_normalizedRayMinusEnergy_iff_commonBaselineDefect_eq_zero
```

これは 006Z の **original ROADMAP exit gate** の source-side half である。

重要:

- `Eminus_X` は既存 theorem により nonnegative。
- `CompletionRemainder_X` は現時点では signed。
- `D_X = 0` が証明された場合に限り、rectangle remainder はこの source-side nonnegative minus whole と一致する。

したがって conditional に次を公開する。

```lean
cfzp006CompletionRemainder_nonneg_of_commonBaselineDefect_eq_zero
```

目標:

```text
D_X = 0 -> 0 <= CompletionRemainder_X
```

さらに

```lean
cfzp006RadialContactDeficit_eq_zero_iff_rayMinusEnergy_eq_zero_of_commonBaselineDefect_eq_zero
```

および可能なら

```lean
cfzp006CompletionRemainder_eq_zero_iff_rayMinusEnergy_eq_zero_of_commonBaselineDefect_eq_zero
```

を公開する。

ここで `Eminus_X = 0` から pointwise zero / zeta zero / RH へ進まない。

---

# 8. Gate E — 004 amplitude Gap と CS25 ray minus whole を混同しない

CFZP-004 には exact に

```text
cfzpAggregateMirrorMinusWholeUpTo X δ
  = cfzpAggregateMirrorGapUpTo X δ
```

および

```text
0 <= cfzpAggregateMirrorGapUpTo X δ
```

がある。

CS25 には別 object として

```text
0 <= pascalCenteredXiPrimeSideAggregateRayMinusEnergy ε W X
```

がある。

006Z ではこの二つを勝手に同一視しない。

ただし closeout で

```text
amplitude-side minusWhole/Gap is nonnegative
source-ray minusWhole is nonnegative
```

という両側 fact を並べて記録してよい。

推奨 frontier marker:

```lean
inductive Cfzp006AmplitudeGapToRayMinusWholeProjectionGap : Prop
  | noExactAmplitudeGapToRayMinusWholeProjectionProvider
```

これは original ROADMAP の

```text
Π(Gap_cosmic) = SourceGap
```

に残るもう一つの穴である。

---

# 9. Gate F — current algebra だけでは baseline alignment は出ない countermodel

006Z では「なぜ `D_X = 0` を algebraic rearrangement だけで勝手に得られないか」を pure-real countermodel で固定する。

例えば次の型でよい。

```lean
cfzp006CommonBaselineAlignment_not_forced_by_commonInteractionAlgebra
```

目標例:

```text
∃ G0 C I G Eminus : ℝ,
  G = G0 - I ∧
  Eminus = C - I ∧
  0 <= Eminus ∧
  G ≠ Eminus
```

具体値は単純でよい。

必要なら plus whole も追加して

```text
Eplus = C + I
0 <= Eplus
```

まで満たす countermodel にしてよい。

意味は

> 既存の common/interation/minus-whole algebra だけでは `G0 = C` は論理的に出ない。

という audit である。

これは actual RH object に対する反例ではない。

generic algebraic insufficiency certificate であることを doc comment に明記する。

---

# 10. Gate G — 006 closeout theorem

006Z の最後に、今回の大局を一 theorem surface にまとめる。

推奨 theorem 名:

```lean
cfzp006SourceProjection_closeout
```

heavy rectangle hypotheses の下で最低限次の三項を conjunction 等でまとめる。

```text
pi * CompletionRemainder_X
  = Eminus_X + D_X

CompletionRemainder_X = Eminus_X / pi
  <-> D_X = 0

D_X = 0
  -> 0 <= CompletionRemainder_X
```

proof は既存 Gate theorem の組合せだけにする。

この theorem は RH conclusion ではない。

意味は

> 006A〜Y で複雑化した source remainder problem を、
> nonnegative source minus whole と一個の common-baseline defect に exact に圧縮した。

という 006 stage の closeout である。

---

# 11. 006 stage の判定

006Z 自体は上記 theorem が exact に閉じれば Green-A audit implementation としてよい。

しかし **CFZP-006 stage 全体**は original ROADMAP の基準では Green-B と記録する。

理由:

1. `RectangleBackground = TopMismatch + CompletionRemainder` は exact。
2. TopMismatch の linear / polarized / interaction / prime-power / phase-cell projection は exact。
3. CompletionRemainder は `Eminus/pi + D/pi` まで exact。
4. source-side nonnegative minus whole `Eminus` は存在する。
5. しかし `D = 0` は未証明。
6. さらに CFZP-004 amplitude Gap と CS25 ray minus whole の exact projection bridge は未証明。

したがって CompletionRemainder を無条件に `SourceGap` と rename しない。

---

# 12. 007 への舵取り変更

006Z Green 後、元 ROADMAP の 007

```text
finite completion -> limit closure
```

へ直ちに入らない。

まず 007 の入口を次へ再定義する。

```text
CFZP-007 — source minus-whole / common-baseline closure gate
```

007 の最初の二つの research target は次だけに絞る。

### 007 target A — common-baseline alignment

```text
G_0 ?= C_X
```

すなわち

```text
cfzp006CommonBaselineDefect ε W X ?= 0
```

がどの finite/canonical surface で成立し得るかを監査する。

最初から universal `∀ X` を狙わない。

まず exact dependency / possible no-go / special cutoff / normalization を調べる。

### 007 target B — amplitude Gap -> ray minus-whole projection

CFZP-004 の

```text
AggregateMirrorMinusWhole = AggregateMirrorGap
```

と CS25 の

```text
AggregateRayMinusEnergy
```

が同じ source projection chain 上の object であることを示す exact bridge を探す。

これが無い限り `Eminus` を cosmic Gap の射影像と断定しない。

### 007 exit condition

次の二つが閉じた場合だけ original 007 の finite nonnegative completion / limit closure を再開する。

```text
A. D_X = 0
B. amplitude Gap -> ray minus-whole exact projection
```

どちらかが不可能と判明した場合は、limit に進まず SourceBig / projection definition を再設計する。

---

# 13. ROADMAP status note

006Z 実装時に `0000-CFZP-roadmap.md` の historical sections を書き換えすぎない。

ただし先頭 Status 付近または末尾に compact な `006Z closeout / 007 re-steering note` を追加し、次を記録する。

```text
006 closeout:
- interaction chain: exact
- phase-cell localization: exact conditional
- rectangle remainder: signed
- source minus whole: nonnegative
- exact relation: pi*R = Eminus + D
- D = G0 - C
- stage status: Green-B against original 006 exit condition

007 re-entry:
- solve/common-audit D
- bridge amplitude Gap to ray minus whole
- only then finite/limit closure
```

これは今後の A〜Z runaway を防ぐための navigation beacon とする。

---

# 14. Dependency / firewall

006Z は closeout / structural audit である。

禁止:

- 新しい phase-cell branch の追加
- 006Y の phase arithmetic をさらに局所展開すること
- unconditional `D_X = 0`
- unconditional CompletionRemainder nonnegativity
- `Eminus` と CFZP-004 amplitude Gap の無証明同一視
- ledger monotonicity
- baseline reach existence
- convergence
- new `X -> infinity` argument
- infinite Euler product
- `Complex.arg`
- new global `Complex.log` branch
- zeta-zero conclusion
- RH conclusion
- `sorry`
- `admit`
- `axiom`
- `native_decide`

006Z は新しい解析を発明せず、既存 exact facts を正しい大局へ再編成する。

---

# 15. 実装順序

推奨:

```text
1. new closeout module / imports
2. cfzp006CommonBaselineDefect definition
3. G = Eminus + D
4. G - Eminus = D
5. G = Eminus iff D = 0
6. pi*CompletionRemainder = Eminus + D
7. normalized CompletionRemainder formula
8. CompletionRemainder = Eminus/pi iff D = 0
9. D=0 -> remainder nonnegative / zero iff minus energy zero
10. amplitude Gap and ray minus-whole separation marker
11. pure-real algebraic insufficiency countermodel
12. cfzp006SourceProjection_closeout theorem
13. DkMath/RH.lean public import
14. ROADMAP 006Z/007 re-steering status note
15. local Green suite
```

---

# 16. 成功条件

006Z Green 条件:

1. `CosmicFormulaZetaSourceProjectionCloseoutAudit.lean` を追加。
2. `DkMath/RH.lean` に public import。
3. common-baseline defect `D_X = G_0 - C_X` を first-class 定義。
4. `G_X = Eminus_X + D_X` を exact に証明。
5. `G_X = Eminus_X <-> D_X = 0` を exact に証明。
6. `pi * CompletionRemainder_X = Eminus_X + D_X` を exact に証明。
7. `CompletionRemainder_X = Eminus_X/pi <-> D_X = 0` を exact に証明。
8. `D_X = 0` の下で CompletionRemainder nonnegative を証明。
9. `D_X = 0` の下で radial/contact zero と ray-minus zero の iff を少なくとも一つ公開。
10. amplitude Gap と ray minus whole を無条件同一視しない。
11. current common/interaction algebraだけでは alignment が出ない generic countermodel を記録。
12. 006 closeout theorem surface を公開。
13. ROADMAP に 006 stage Green-B / 007 re-steering note を追加。
14. target module build Green。
15. `lake build DkMath.RH` Green。
16. `./lean-build.sh` Green。
17. `./lean-test.sh` Green。
18. `git diff --check` Green。
19. new module に `sorry`, `admit`, `axiom`, `native_decide` なし。
20. new module に新規 `Complex.arg` / global `Complex.log` branch なし。
21. zeta-zero / RH conclusion を追加しない。

---

# 17. 006Z の位置づけ

```text
006A〜Q  source / polarization / threshold / baseline
006R〜Y  interaction event の arithmetic / phase / derivative localization
006Z     source remainder を minus whole + common-baseline defect へ戻して closeout
```

最終的な 006Z の絵は次である。

```text
Cosmic / amplitude side
  AggregateMirrorMinusWhole
  = AggregateMirrorGap >= 0
              |
              |  exact projection bridge is still open
              v
Source ray side
  Eminus_X = C_X - I_X >= 0
              |
              |  common-baseline alignment D_X = G_0 - C_X
              v
Radial / rectangle side
  G_X = Eminus_X + D_X
  pi * CompletionRemainder_X = Eminus_X + D_X
```

したがって 007 で攻めるべき穴は無制限な phase-cell refinement ではない。

```text
1. amplitude Gap -> ray minus whole
2. G_0 -> common mass C_X
```

という **二つの source-object alignment** に限定する。

ここが閉じた時点で初めて original ROADMAP の genuine SourceGap / finite completion / limit closure へ戻る。
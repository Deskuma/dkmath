# CFZP-0007 — CFZP-006C functional quadratic companion audit 実装指示書

## 0. 作業対象

Repository:

```text
Deskuma/dkmath
```

Working branch:

```text
wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0
```

この指示書作成直前に確認した Green checkpoint:

```text
79880fb67aab860e3b711d6cab45d0b6b8bbf5c3
Add: CFZP-0006: CFZP-006B source interaction classification
```

CFZP-006B 実装 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
```

CFZP-006B は次を exact に閉じている。

```text
CompletionRemainder
  = SourceZeroCutoffBaseline - SourceInteraction

SourceInteraction
  = SourcePlusMass - SourceMinusMass

CompletionRemainder
  = SourceZeroCutoffBaseline + SourceMinusMass - SourcePlusMass

0 ≤ SourcePlusMass
0 ≤ SourceMinusMass
```

また、CS24 / CS25 ray energy と CFZP-004 amplitude ledger を同一視せず、quadratic nonnegative source Gap provider は未提供のまま明示されている。

今回の CFZP-006C では、この Green API を壊さない。

---

# 1. 今回の目的 — linear source から induced quadratic companion を exact に監査する

CFZP-005 / 006 までに得た actual source projection は線形である。

概念的には finite canonical source

```text
L_X(s) = Σ_q w_q D_q(s)
```

を使う。

ここで

```text
w_q = canonicalPrimePowerShadowCost q
D_q(s) = functional-reflection mode difference
```

である。

一方、CFZP-003 / 004 の Big / Gap は二次 observable である。

したがって

```text
linear source projection Π
```

をそのまま Big / Gap に適用したと見なしてはならない。

必要なのは `Π` から誘導される quadratic companion の exact algebra を先に露出することである。

今回の目的は三段階。

```text
A. mode 内 quadraticization
B. linear-weight finite diagonal ledger
C. finite linear source 全体の normSq と cross-mode interference
```

これにより、CFZP-004 の positive carrier-weighted mirror Gap が quadratic companion のどこに exact に現れるかを固定する。

---

# 2. 新規 module

推奨 filename:

```text
lean/dk_math/DkMath/RH/CFBRC/
  CosmicFormulaZetaFunctionalQuadraticCompanionAudit.lean
```

推奨 module:

```text
DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalQuadraticCompanionAudit
```

推奨 import:

```lean
import DkMath.RH.CFBRC.CosmicFormulaZetaSourceInteractionClassificationAudit
import Mathlib.Tactic
```

CFZP-004 / 005 / 006 の API は transitively 使用してよい。

今回 `MellinQuadraticGramKernel` を import する必要はない。まず finite prime-power source 自体の quadratic algebra を閉じる。

---

# 3. A — mode 内 quadratic companion

CFZP-006 には

```lean
cfzpFunctionalReflectionModeDifference
cfzpFunctionalVsSameHeightCycleDisplacementMode
cfzpSameHeightMirrorModeDifference
```

があり、exact に

```text
FunctionalDifference = CycleDisplacement + SameHeightDifference
```

がある。

これを `Complex.normSq` で二次化する。

## 3.1 推奨 definitions

概念名:

```text
cfzpFunctionalReflectionModeQuadraticMass q s
cfzpCycleDisplacementModeQuadraticMass q s
cfzpSameHeightMirrorModeQuadraticMass q s
cfzpCycleSameHeightModeCrossTerm q s
```

推奨内容:

```text
FunctionalMass = normSq FunctionalDifference
CycleMass      = normSq CycleDisplacement
SameHeightMass = normSq SameHeightDifference
```

cross term は実数で、例えば

```text
2 * Re(CycleDisplacement * conj SameHeightDifference)
```

または同値な conjugation orientation を使う。

orientation は Lean の簡約が最も自然な方を採用してよい。

## 3.2 必須 exact theorem

概念的に

```text
FunctionalMass
  = CycleMass
    + SameHeightMass
    + CrossTerm
```

を証明する。

`Complex.normSq` の一般恒等式を再利用してよい。必要なら `Complex.normSq_eq_conj_mul_self` と ring で閉じる。

## 3.3 same-height mass と CFZP-004 Gap

既存 theorem

```lean
normSq_cfzpSameHeightMirrorModeDifference
```

を再利用し、

```text
SameHeightMass
  = normSq(SameHeightCommonCarrier)
    * primeMirrorOffsetGap
```

を wrapper theorem として得る。

これは今回の load-bearing bridge である。

## 3.4 zero-height / critical-line audits

既存 CFZP-006 API を使い、少なくとも次を閉じる。

`Im(s) = 0` なら cycle displacement は zero なので

```text
FunctionalMass = SameHeightMass
```

さらに CFZP-004 の theorem から carrier-weighted mirror Gap へ落とせる。

`Re(s) = 1/2` なら same-height difference は zero なので

```text
FunctionalMass = CycleMass
```

となる。

両方

```text
Re(s) = 1/2
Im(s) = 0
```

なら

```text
FunctionalMass = 0
```

まで閉じてよい。

重要:

critical line 上で functional mass が一般に zero とは主張しない。`Im(s) ≠ 0` では cycle displacement が残る。

## 3.5 非負性

次を証明する。

```text
0 ≤ FunctionalMass
0 ≤ CycleMass
0 ≤ SameHeightMass
```

cross term の符号は主張しない。

---

# 4. B — linear-weight finite diagonal quadratic ledger

次に canonical prime-power support 上で、PHZ と同じ一次 weight `w_q` を保持した mode-wise quadratic ledger を作る。

## 4.1 推奨 definitions

```text
cfzpAggregateFunctionalReflectionQuadraticLedgerUpTo X s
cfzpAggregateCycleDisplacementQuadraticLedgerUpTo X s
cfzpAggregateCycleSameHeightCrossLedgerUpTo X s
```

概念的には

```text
FunctionalLedger
  = Σ_q w_q * FunctionalMass_q

CycleLedger
  = Σ_q w_q * CycleMass_q

CrossLedger
  = Σ_q w_q * CrossTerm_q
```

same-height ledger は新規定義せず、既存

```lean
cfzpAggregateCarrierWeightedMirrorGapUpTo
```

を正本として使うことを推奨する。

## 4.2 必須 exact decomposition

次を証明する。

```text
FunctionalLedger
  = CycleLedger
    + cfzpAggregateCarrierWeightedMirrorGapUpTo X s
    + CrossLedger
```

ここで `cfzpAggregateCarrierWeightedMirrorGapUpTo` が CFZP-004 positive Gap component として exact に再登場することが重要。

## 4.3 aggregate boundary theorems

`Im(s) = 0` なら

```text
FunctionalLedger
  = cfzpAggregateCarrierWeightedMirrorGapUpTo X s
```

を証明する。

`Re(s) = 1/2` なら

```text
FunctionalLedger = CycleLedger
```

を証明する。

両条件なら functional ledger は zero。

## 4.4 aggregate positivity

少なくとも

```text
0 ≤ FunctionalLedger
0 ≤ CycleLedger
0 ≤ cfzpAggregateCarrierWeightedMirrorGapUpTo X s
```

を public theorem として揃える。

三つ目は既存 theorem を再利用する。

CrossLedger の符号は主張しない。

---

# 5. C — finite linear source 全体の quadraticization

ここが今回の第二 load-bearing point。

既存 linear source は

```lean
cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s
```

で、概念的に

```text
L_X(s) = Σ_q w_q D_q(s)
```

である。

この全体を `Complex.normSq` すると、mode-wise linear-weight ledger にはならない。

## 5.1 scaled mode

推奨 definition:

```text
cfzpCanonicalFunctionalReflectionScaledMode q s
```

内容:

```text
(w_q : ℂ) * cfzpFunctionalReflectionModeDifference q s
```

support 外でも total definition でよい。

次を証明する。

```text
normSq(ScaledMode_q)
  = w_q^2 * normSq(D_q)
```

weight が一次から二次へ変わることを theorem surface に出す。

## 5.2 squared-weight diagonal ledger

推奨 definition:

```text
cfzpCanonicalFunctionalReflectionSquaredWeightDiagonalUpTo X s
```

概念的に

```text
Σ_q w_q^2 * normSq(D_q)
```

または scaled mode の `normSq` sum として定義してよい。

両表示の equality theorem を持つこと。

非負性も証明する。

## 5.3 total source mass

推奨 definition:

```text
cfzpCanonicalFunctionalReflectionTotalSourceMassUpTo X s
```

内容:

```text
Complex.normSq (cfzpCanonicalFunctionalReflectionLinearSourceUpTo X s)
```

非負性は当然証明する。

## 5.4 cross-mode interference

必ず total mass と squared-weight diagonal の差を明示する。

最小 acceptable definition:

```text
cfzpCanonicalFunctionalReflectionCrossModeInterferenceUpTo X s :=
  TotalSourceMass - SquaredWeightDiagonal
```

そして

```text
TotalSourceMass
  = SquaredWeightDiagonal
    + CrossModeInterference
```

を exact に証明する。

ただし、可能ならさらに off-diagonal pair sum 表示を証明する。

推奨形は canonical support 上で

```text
Σ_q Σ_r, if q = r then 0
  else Re(conj(ScaledMode_q) * ScaledMode_r)
```

または algebraically equivalent な ordered-pair sum。

ordered pair を使う場合、`q,r` と `r,q` の両方を数えるので余分な factor `2` を誤って入れないこと。

pair-sum theorem が Lean 上で大きな実装障害になる場合は、今回は difference definition + exact decomposition までを必須とし、pair-sum は optional でよい。ただしコメントで cross-mode interference が hidden zero ではないことを明示する。

---

# 6. weight-degree mismatch を明示する

今回、次の二つを絶対に同一視しない。

linear-weight quadratic ledger:

```text
Σ_q w_q * normSq(D_q)
```

squared linear source の diagonal:

```text
Σ_q w_q^2 * normSq(D_q)
```

これは一般に別 object である。

`w_q = log p` 型の weight なので、`w_q^2 = w_q` のような冪等性はない。

今回 equality を作るために weight を変更してはならない。

必要なら frontier marker を追加してよい。

推奨例:

```lean
inductive CfzpLinearWeightToSquaredWeightBridgeGap : Prop
  | noExactWeightDegreeIdentificationProvided
```

これは impossibility theorem ではなく「この module では provider を与えない」という marker とする。

---

# 7. CompletionRemainder との関係

今回、次の equality は禁止する。

```text
CompletionRemainder = FunctionalLedger
CompletionRemainder = TotalSourceMass
CompletionRemainder = SquaredWeightDiagonal
CompletionRemainder = carrier-weighted mirror Gap
```

CFZP-006B で `CompletionRemainder` は

```text
baseline - signed interaction
```

という affine signed observable に分類済みである。

今回構成する quadratic companion は非負 quadratic observable であり、型が違う。

exact source theorem が得られるまでは bridge しない。

必要なら frontier marker:

```lean
inductive CfzpCompletionRemainderQuadraticCompanionBridgeGap : Prop
  | noExactRemainderQuadraticIdentificationProvided
```

を置いてよい。

---

# 8. Mellin Gram との関係

既存

```text
DkMath.Analysis.MellinQuadraticGramKernel
```

には finite-family Gram energy とその非負性がある。

また既存

```text
PascalCenteredXiPrimeSideQuadraticizationAudit
```

は source ledger が one-index linear source、Gram が two-index quadratic formであるという arity boundary を既に記録している。

今回の CFZP-006C では、そこへ無理に接続しない。

今回得た

```text
mode cross term
cross-mode interference
weight-degree mismatch
```

を次フェーズの exact input とする。

CFZP-006C Green 後に、必要なら CFZP-006D で actual Mellin box feature / Gram source family への bridge を設計する。

---

# 9. Firewall

禁止事項:

- `CompletionRemainder` を `Gap` と rename しない。
- `normSq (Σ mode)` を `Σ normSq(mode)` としない。
- PHZ linear weight `w_q` と quadratic diagonal weight `w_q^2` を混同しない。
- mode 内の `cycle + sameHeight` に対する cross term を消さない。
- critical line 上で functional-reflection difference が zero と主張しない。
- CFZP-004 amplitude ledger と CS24/25 ray energy を同一視しない。
- generic Mellin Gram positivity から rectangle remainder の符号を結論しない。
- provider structure を仮定して desired equality を作らない。
- `Complex.arg` を導入しない。
- 新しい global `Complex.log` branch を導入しない。
- infinite Euler product を導入しない。
- limit / sum-integral exchangeへ進まない。
- zero-set / RH conclusionへ進まない。
- `sorry` / `admit` / `axiom` を追加しない。
- 同じ実装で CFZP-006D へ進まない。

---

# 10. 成功判定

## Green-A

次が exact に閉じる。

```text
FunctionalModeMass
  = CycleMass + SameHeightMass + ModeCross

SameHeightMass
  = carrier normSq * mirror amplitude Gap

FunctionalAggregateLedger
  = CycleLedger
    + CFZP-004 carrier-weighted Gap
    + ModeCrossLedger

Im(s)=0
  → FunctionalAggregateLedger = carrier-weighted Gap

Re(s)=1/2
  → FunctionalAggregateLedger = CycleLedger

normSq(linear canonical source)
  = squared-weight diagonal
    + cross-mode interference

squared-weight diagonal
  = Σ w_q^2 * normSq(D_q)
```

さらに nonnegative quadratic pieces の非負性が証明される。

## Green-B

mode / finite diagonal decomposition は exact だが、total source mass の off-diagonal pair representationのみ未完成。

この場合も difference-defined cross-mode interference が exact なら次へ進める。

## Yellow

- cross term を無視。
- `Σ w_q normSq(D_q)` と `normSq(Σ w_q D_q)` を rename で同一視。
- weight square を落とす。
- CompletionRemainder を quadratic mass と仮定。

## Red

- RH-equivalent theorem や zero-side theorem を quadratic source provider に使う。
- infinite / limit machineryを未証明で導入。
- `Complex.arg` / global complex-log branch を新たな本質 bridge にする。

---

# 11. 検証

最低限:

```text
lake build DkMath.RH.CFBRC.CosmicFormulaZetaFunctionalQuadraticCompanionAudit
lake build DkMath.RH
./lean-build.sh
./lean-test.sh
git diff --check
```

新規 module に

```text
sorry
admit
axiom
```

が無いことを確認する。

Green 後のみ `DkMath/RH.lean` へ public import を追加する。

---

# 12. 完了時の報告

報告には最低限:

```text
実装 commit SHA
変更 file
主要 public API
mode cross term の exact formula
aggregate decomposition
zero-height / critical-line boundary theorem
squared-weight diagonal theorem
cross-mode interference theorem
検証結果
```

を含める。

実装・push 後は停止し、CFZP-006D へ自動的に進まないこと。

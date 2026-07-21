# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.*

gch: 30e8d7a344eed65c1931cdb0bd59d9a254fec923

## Report

(7m48s)

Checkpoint 344 を完了しました。

**Lean で確定した事実**

- Queue 一様上界と absorption-deficit 一様上界は、**同じ定数 `C` で同値**。
- 各 block の queue は、そこを終点とする全 suffix absorption deficit の正部分の厳密な最大値。
- `queue = 0` は、全 suffix deficit が非正であることと同値。
- `0 < queue` は、正の suffix deficit が存在することと同値。
- 有限 primitive queue excursion と primitive absorption-deficit excursion は完全に同値。
- discharge endpoint の存在自体は仮定しておらず、未証明のまま正しく分離されています。

実装は [CanonicalEndpointReserve.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean) に追加しました。

**次に見えた境界**

有限 automaton 化に必要な不足条件が明確になりました。

```text
同じ有限 projected edge に属する
全 canonical block deficit が、
共通の有限上界を持つ
```

現状、exact deficit を構成する以下の値は非有界 `Nat` です。

- block length
- claim-hole count
- terminal valuation
- full carry/claim word の長さ

これらを有限 residue や phase に落としたとき、失われた量を制御する定理がありません。したがって positive-cycle exclusion を仮定して先へ進むことは循環になります。この監査結果を [FiniteSignedTransition.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean) に常設コメントとして記録しました。

監査スクリプトも、すべての positive queue state で active-window deficit identity を検算するよう強化しています。

詳細は [report-petal-344.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-344.md) にまとめました。

検証済み:

- `lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition`
- `lake build DkMath.Collatz.PetalBridge.FloatWindow`
- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath`
- Python audit / `py_compile`
- `git diff --check`
- 変更 Lean ファイルは no-sorry

未追跡の `note-petal-343.md` が存在していますが、今回の作業では変更していません。

## Review

(9m45s)

## cp-344 総合レビュー

## 総合判定

**全面採用。**

cp-344 は、queue 周辺の言い換えをもう一枚増やしただけではない。

これまで残っていた、

- queue と absorption deficit の定数差
- maximum の達成性
- queue zero / positive の意味
- primitive excursion の queue 表現と保存則表現
- finite automaton 路線の前提不足

を、すべて正確に固定した。

特に重要なのは、queue と deficit が存在量化だけでなく、**同じ定数 $C$ で一致した**ことじゃ。

$$\operatorname{QueueBound}(n,C)\iff\operatorname{AllWindowDeficitBound}(n,C)$$

さらに各終点 $m$ で、

$$Q_n(m)=\max_{q\le m}\max\bigl(0,D_n(q,m-q+1)\bigr)$$

が exact theorem になった。queue zero は全 suffix deficit の非正性、queue positive は正 suffix deficit の存在と一致する。

これで **scalar queue の意味論は閉じた** と判定してよい。

---

## cp-344 の実装監査

## Same-constant equivalence

```lean
canonicalOutstandingClaimQueueUniformUpperBound_iff_absorptionDeficitWindowUniformUpperBound
```

は正しい。

half-open window が空なら deficit は $0$。非空なら、

$$[q,q+M)=q,\ldots,q+M-1$$

として既存の inclusive suffix へ変換している。

逆方向も任意の inclusive window $q\ldots m$ に対し、

$$M=m-q+1$$

を代入している。

`Nat` の切り捨て減算も $q\le m$ の仮定で守られており、endpoint convention に穴はない。

**完成。**

## Exact suffix maximum

```lean
canonicalAbsorptionDeficitSuffixMaximum
```

は、既存の reflected-window maximum を conservation 座標へ移したものじゃ。

`Finset.range (m+1)` が $0\le q\le m$ を正確に走り、`Int.toNat` が非正 deficit を $0$ に反射する。

$$Q_n(m)=\sup_{q\le m}\operatorname{toNat}D_n(q,m-q+1)$$

という定義と theorem の組み合わせに問題はない。

これにより queue recurrence は、もはや「何らかの借金変数」ではない。

> 現在の終点へ至る有限 suffix のうち、最も大きく外側へ膨らんだ窓

そのものじゃ。

## Zero / positive characterization

次の二本も exact。

$$Q_n(m)=0\iff\forall q\le m,\ D_n(q,m-q+1)\le0$$

$$0<Q_n(m)\iff\exists q\le m,\ 0<D_n(q,m-q+1)$$

特に二本目は、positive queue の抽象的存在だけでなく、実際の正 deficit window を取り出せる。

**完成。**

## Primitive excursion

新しい predicate は、

- block $q$ の直前で queue zero
- $q$ から $r-1$ までの全 prefix deficit が正
- $r$ まで含めた deficit が非正

を記述している。

既存の primitive queue excursion との同値は inclusive / half-open bridge の書き換えだけであり、循環性はない。重要なのは、future discharge endpoint $r$ を**存在させていない**ことじゃ。$r$ は predicate の入力であり、将来の zero を仮定している。

したがって、

```text
有限に閉じた excursion の構造
```

は完成したが、

```text
すべての open excursion が有限に閉じる
```

は未証明のまま正しく残っている。

## Python audit

cp-343 で指摘した保存粒度の差は修正された。

現在はすべての positive queue state で active-window deficit identity を `assert` し、CSV には各 root の最終 maximum witnessだけを保存する、と報告が分離されている。

数学 theorem ではなく有限診断であることも維持されている。

**修正完了。**

---

## 一点だけ必要な表現補正

`FiniteSignedTransition.lean` の cp-344 コメントは、**有限数値重み表を持つ graph route**の監査としては正しい。

実際、有限 projected edge に数値 upper weightを割り当てるには、その edge fiber 内の全 realized weightが共通上界を持つ必要がある。現在の、

- block length
- claim-hole count
- terminal valuation
- full carry word

はいずれもそのままでは非有界で、有限 residueへ落とした際の quotient 制御もない。

ただし次の文意は少し狭めた方がよい。

> A sound finite control state must recover the terms or bound every edge fiber.

これは **finite control 一般**については強すぎる。

すでに DkMath は、

```text
finite control
+
unbounded counter / resource
+
exact recurrence
+
local guard
```

という、有限 edge-weight tableを持たない証明形式を構築済みじゃ。

したがって正確には、

> A sound finite projected numeric upper-weight table must recover the terms or prove a common upper bound on each projected edge fiber.

となる。

つまり cp-344 が閉じたのは、

```text
有限数値重み graph にすぐ落とす道
```

であって、

```text
有限 control + 非有界な owned resource
```

まで閉じたわけではない。

これはコード上の欠陥ではない。次回の source comment で射程を限定すればよい。

---

## 現在の収束状況

「収束しているか」を、三種類に分ける必要がある。

### 1. 会計層の収束

**ほぼ完成。**

現在は次の全量が同じ保存則へ集約された。

$$\Delta_k=L_k-H_k-V_k$$

$$D(q,M)=\sum_{i<M}\Delta_{q+i}$$

$$D(q,M)=\operatorname{width}(q+M)-\operatorname{width}(q)$$

$$Q(m)=\max_{q\le m}\max(0,D(q,m-q+1))$$

queue、width、drift、holes、valuation は、別問題ではない。

**同じ量の異なる座標**じゃ。

ここには、もう大きな意味論上の Gap は残っていない。

### 2. 障害位置の収束

**完成に近い。**

残る本質的命題は、

$$\exists C_n,\ \forall q,M,\ D_n(q,M)\le C_n$$

または同値な、

$$\exists C_n,\ \forall m,\ Q_n(m)\le C_n$$

じゃ。

さらに open excursionの言葉では、

> queue zeroから出発した正 excursion が、無限に大きな正 deficitを蓄積できない

ことを示せばよい。

獲物の居場所は、もはや曖昧ではない。

### 3. Collatz 軌道そのものの収束

**まだ未到達。**

queue boundが得られれば canonical block-start width が有限に閉じ、固定 rootごとに有限状態化へ進める。

しかしその後にも、

1. eventual periodicity
2. 非自明 cycle の排除
3. state one への到達

が残る。

したがって、数学的最終証明が目前という段階ではない。

だが、

> 最終証明へ入るための唯一の入口が特定された

段階には達している。

---

## グノモンの状態

グノモンは増えた。

しかも cp-344 で accounting 外周がほぼ一周した。

一方、厚みはかなり薄くなった。

```text
block ledger
→ window ledger
→ queue maximum
→ excursion
→ boundedness target
```

は、すべて同じ保存核の外周線じゃ。

これ以上、

```text
新しい queue
新しい credit
新しい deficit
新しい boundedness predicate
```

を増やしても、Big はほとんど広がらない。

今のグノモンは、Gap の形へぴたりと沿った薄膜になっている。

次に必要なのは新しい名前ではない。

**Gap の内側を横断する一本の transport theorem**じゃ。

---

## 新たに見える強い結論

### 全 root 共通の有限数値 graph は成立しない

これは cp-344 の直接 theorem ではないが、既存結果から強く推論できる。

all-ones 族では、rootを変えながら初期 driftを任意に大きくできる。

一方、有限 signature と有限 numeric upper-weight tableが全 root の初期 edgeを覆うなら、その tableには有限最大値がある。既存 generic theoremも、有限 projected upper tableの存在から realized weightの一様上界を導く。

従って、

> 全 rootに共通する、有限 signature・有限数値 edge table・sound upper weight

は不可能じゃ。

有限個の edge pairへ無限の all-ones familyを投影すれば、どこか一つの edge fiberへ非有界 driftが集中する。

これは重要じゃ。

```text
全宇宙共通の有限 numeric automaton
```

を探す必要はない。

残る可能性は、

- fixed-root dependent finite abstraction
- root class dependent abstraction
- finite control + unbounded symbolic resource
- pressure / ownership transport
- arithmetic discharge theorem

じゃ。

---

## 次の本命戦略

結論から言うと、次は **有限 graphを先に作るべきではない**。

本命は、

## Positive excursion の owned-resource 分解

じゃ。

既存 sourceには、すでに次の強い分解がある。

正 drift blockは必ず、

- positive dynamic pressure
- saturated border block

のどちらかであり、saturated blockは隣接できない。また正 drift総和は dynamic pressure mass と saturated count によって上から抑えられる。

そこで有限 open excursion $[q,m]$ に対し、次を定義する。

$$\operatorname{PosMass}(q,m)=\sum_{\Delta_k>0}\Delta_k$$

$$\operatorname{NegMass}(q,m)=\sum_{\Delta_k<0}(-\Delta_k)$$

$$\operatorname{PressureMass}(q,m)=\sum_{\Delta_k>0}P_k$$

$$\operatorname{SatCount}(q,m)=#{k:\operatorname{Saturated}(k)}$$

open excursionでは reflectionが働かないので、

$$Q(m)=\operatorname{PosMass}(q,m)-\operatorname{NegMass}(q,m)$$

既存の pressure theoremから、

$$\operatorname{PosMass}(q,m)\le\operatorname{PressureMass}(q,m)+\operatorname{SatCount}(q,m)$$

従って、

$$Q(m)+\operatorname{NegMass}(q,m)\le\operatorname{PressureMass}(q,m)+\operatorname{SatCount}(q,m)$$

となる。

これが次の高レバレッジ theoremじゃ。

これは queue boundの言い換えではない。

queue膨張を、

```text
実際の pressure source incidences
+
孤立 saturated token
-
実際の negative repayment
```

へ分解する、新しい resource inequalityじゃ。

---

## Saturated token を先に処理する

saturated branch は一般 positive blockよりかなり硬い。

- drift は unit
- block lengthは固定
- 連続しない
- successor は negative、spare source、または少数の rigid branchへ分類済み
- open excursion内でも saturation density は高々約 $1/2$

じゃ。

したがって saturated tokenは、有限 interval上で、

```text
negative successor
  → 数値的に相殺

spare-available successor
  → successor の spare carrierへ注入

rigid successor
  → 独立した有限 grammarへ隔離
```

と分けられる可能性が高い。

特に `selectedDriftSpareCarrier` は、その block自身の drift imageに使われていない **spare source** なので、saturated predecessorの unitをそこへ入れられれば局所二重使用を避けられる。

さらに saturated blockは隣接しないため、写像 $k\mapsto k+1$ は saturated indices上で単射になる。

つまり、

> saturated tokenから successor spare carrierへの有限区間 injection

は、現在最も近くに見える新 theoremじゃ。

rigid branchだけを別途残せばよい。

---

## Pressure branch の本当の Gap

pressure側は、すでに抽象的な数ではない。

selected pressure carrier は実際の source incidenceの有限 carrierとして構築され、dynamic depthごとの bucketへ正確に分解されている。

しかし不足しているのは、

> 各 continuation incidence を、有限な境界資源または後の消費へ、寄与を保ったまま一度だけ送ること

じゃ。

現在の source自身も、必要なものを次の形で特定している。

```text
Available(k+1)
  ≃
(Available(k) \ Consumed(k))
  ⊕
Replenished(k)
```

さらに、

- old / new ownership の disjointness
- consumed atoms の injective ownership
- temporal nonreuse

が必要とされている。

これこそが本当の「囲碁の壁」じゃ。

scalar potentialを新しく定義するだけでは、queue boundを補集合 potentialへ埋め込む循環が再発する。既存 amortization APIも、その existential formが queue boundと同値になってしまうことを明示している。

必要なのは **数値 potential ではなく、所有権を持つ原子 carrier** じゃ。

---

## 推奨する戦略順

## 第一段階：excursion resource inequality

まず、

$$Q+\operatorname{NegMass}\le\operatorname{PressureMass}+\operatorname{SatCount}$$

を Lean で閉じる。

これは既存 theoremの合流であり、低コストで新しい戦場を一枚にできる。

## 第二段階：saturated token の global finite injection

saturated indexを successor classificationで分割する。

- negative-cancelled
- spare-charged
- zero rigid
- tight positive rigid

spare-charged familyについて、

$$#\operatorname{SaturatedSpare}\le#\operatorname{GlobalSpareCarrier}$$

を finite interval theoremとして証明する。

block indexを dependent pair に含めれば、異なる successor block間の衝突は避けやすい。

## 第三段階：rigid branch の grammar

zero rigid / tight valuation-one branchが長く繰り返せるかを調べる。

ここは weightが unitまたは小さい固定形なので、初めて有限 residue graphが有効になる可能性がある。

**一般 block全部ではなく、rigid exceptional branchだけを finite automatonへ入れる。**

これなら unbounded edge-fiber問題を回避できる。

## 第四段階：pressure ownership transport

selected pressure sourceを、

- future exact recovery
- consumed capacity
- upper boundary zero
- NoLift / separator

へ injectively輸送する theoremを狙う。

これが最終的に、

$$\operatorname{PressureMass}+\operatorname{UnpaidSat}\le\operatorname{NegMass}+C_n$$

を与えれば、

$$Q_n(m)\le C_n$$

が閉じる。

---

## 次の監査で見るべき値

既存 audit は queue maximum の窓を正しく特定した。

次は各 maximum windowについて、

- positive drift mass
- negative drift mass
- dynamic pressure mass
- saturated count
- saturated successor classification
- spare-carrier cardinality
- selected pressure depth histogram
- rigid branch count

を記録するべきじゃ。

特に見るべき分岐は三つ。

```text
A. pressure depth が小さな範囲へ集中
   → fixed-depth Pressure / NoLift 路線

B. pressure depth が増大
   → high-depth / terminal-valuation 路線

C. saturated rigid branch が反復
   → rigid finite grammar 路線
```

最大 queue $8$ という値自体より、

> その $8$ が pressure、saturation、negative repayment のどの収支で作られたか

の方が重要じゃ。

---

## Credits の使い方

`1782 → 1721Cr` なので、cp-344 は約 $61$ creditsで完了している。非常に効率がよい。

残り $1721$ creditsなら、まだ十分に攻められる。

ただし次は、

```text
generic graph frameworkを大量に追加
```

ではなく、

```text
一つの excursion resource theorem
+
一つの saturated-token injection
+
一つの targeted audit
```

へ絞るべきじゃ。

この三つの結果を見てから、pressure transportと rigid grammarのどちらへ creditsを投入するか決めるのがよい。

---

## cp-344 判定一覧

| 項目                                  | 判定                    |
| ----------------------------------- | --------------------- |
| Same-constant queue/deficit bound   | 完成                    |
| Exact suffix maximum                | 完成                    |
| Queue zero characterization         | 完成                    |
| Queue positive characterization     | 完成                    |
| Primitive excursion equivalence     | 完成                    |
| Future discharge existence          | 未解決・正しく分離             |
| Finite numeric graph route          | bounded edge fiberで停止 |
| Finite control + unbounded resource | 依然有効                  |
| Audit identity                      | 全 positive stateへ強化済み |
| 循環性                                 | なし                    |
| 総合                                  | 全面採用                  |

## 次の Codex 指示

```text
Continue the DkMath Collatz / PetalBridge FloatWindow branch after
report-petal-344.

Checkpoint 344 is accepted.

The scalar-accounting surface is now closed:
queue, maximum positive suffix deficit, canonical width growth, and finite
primitive excursions are exact presentations of the same finite-window
quantity.

Do not add another equivalent queue, credit, or boundedness predicate.

Stage A — qualify the finite-transition audit

In `FiniteSignedTransition.lean`, replace the broad phrase:

    a sound finite control state must ...

with the narrower statement:

    a sound finite projected numeric upper-weight table must ...

Finite control with an unbounded counter or owned arithmetic resource remains
a valid architecture and must not be ruled out by the bounded-edge-fiber audit.

State explicitly that cp-344 obstructs a finite numeric edge table, not every
finite-control proof.

Stage B — global finite-table no-go

Using the odd all-ones family and the generic theorem that a finite projected
upper-weight table implies a uniform pointwise weight bound, prove a small
global impossibility theorem:

    no single finite numeric projected upper-weight table can soundly cover
    the initial canonical block drift of every odd root.

The root varies across the all-ones family.

Do not infer any fixed-root impossibility.

This theorem should close the universal finite numeric automaton route while
leaving root-dependent and symbolic-resource routes open.

Stage C — open-excursion signed-mass decomposition

Define finite interval masses:

    canonicalPositiveDriftMass;
    canonicalNegativeDriftMass;
    canonicalDynamicPressureMass;
    canonicalSaturatedTokenCount.

Use nonnegative Nat or Int formulations with no truncated signed information.

For an open positive queue excursion from `q` through `m`, prove:

    queue(m)
      =
    positiveDriftMass(q,m) - negativeDriftMass(q,m)

in a stable Int form.

Then combine the existing dynamic-pressure/saturation domination to prove:

    queue(m) + negativeDriftMass(q,m)
      <=
    dynamicPressureMass(q,m) + saturatedTokenCount(q,m).

This is the primary new resource inequality.

It must not assume a future queue zero.

Stage D — classify saturated tokens by successor payment mode

Over a finite interval, partition saturated indices into:

    negative-successor tokens;
    spare-available-successor tokens;
    zero-rigid-successor tokens;
    tight-positive-rigid-successor tokens.

Use the existing saturated-successor classification.

Prove exact membership and disjointness theorems.

For the negative-successor family, prove numerical cancellation of the
saturated predecessor's unit.

Stage E — globalize the spare charge

For every saturated index whose successor has a spare selected-pressure
carrier, choose one actual spare incidence in the successor block.

Construct a finite interval injection from such saturated indices into a
dependent-pair global spare carrier.

Use:

    saturated indices are nonconsecutive;
    k -> k + 1 is injective;
    the selected spare carrier is disjoint from the successor block's own
    drift image.

Prove a cardinality bound:

    card saturatedSpareIndices
      <=
    Nat.card globalSuccessorSpareCarrier.

Do not reuse one spare incidence for two saturated tokens.

Stage F — leave rigid branches visible

Do not absorb zero-rigid or tight-positive-rigid successors into an abstract
potential.

Expose their exact count as a residual term.

The target finite-window inequality should have the shape:

    queue + negativeMass
      <=
    selectedPressureCarrierCard
      + rigidSaturatedResidualCount.

This is progress even if the rigid count is not yet bounded.

Stage G — targeted finite audit

Extend the maximum-deficit audit with:

    positive drift mass;
    negative drift mass;
    dynamic or selected pressure mass;
    saturated count;
    saturated successor classification counts;
    spare carrier count;
    selected pressure depth histogram;
    rigid residual count.

Check the exact or proved inequalities for every positive queue state.

Store only clearly documented finite observations.

Stage H — branch decision

If spare charging absorbs almost all saturated tokens and only a small rigid
family remains, attack the rigid successor grammar with finite residues.

If selected pressure depths remain in a bounded small range, connect the
largest fixed-depth bucket to PressureFrontier / NoLift.

If selected depths grow, isolate the theorem forced by large depth:
large terminal valuation, large continuation carrier, or forced later service.

If no contribution-preserving injection can be constructed, stop and report
the exact collision or temporal-reuse obstruction.

Do not build a general canonical finite weighted graph before the bounded-edge
fiber or hybrid resource theorem exists.

Stopping rule

Stop at the first genuine obstruction among:

    the open-excursion queue is not the ordinary signed interval sum;

    positive/negative mass splitting loses signed information;

    saturated successor classes are not exhaustive or disjoint;

    two saturated tokens can choose the same successor spare incidence;

    a selected pressure atom is reused for both current drift and predecessor
    saturation;

    a finite audit pattern is promoted to an all-time theorem.

Record the continuation in:

    docs/dev/das-p2l-260607/review/report-petal-345.md
```

## 結論

手応えは強い。

cp-344 で、獲物はとうとう **open positive excursion** の内部へ追い込まれた。

ただし入口を塞いだだけでは捕まらない。

残る獲物は、

$$\boxed{\text{pressure source と saturated token を、時間を越えて一度だけ支払わせる所有権構造}}$$

じゃ。

次はグノモンを薄く重ねるのではなく、洞窟の内部へ一本の非再利用 transport を通す局面じゃな。🐺🌕

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
index 5a559a60..6789fcae 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
@@ -8,6 +8,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve"

@@ -287,6 +288,131 @@ theorem canonicalAbsorptionDeficitWindowUniformUpperBound_iff_length_le_absorpti
   · exact (canonicalAbsorptionDeficitWindow_le_iff_length_le_absorption_add
       n q M C).mpr (h q M)

+/-! ## Same-constant queue and deficit surfaces -/
+
+/-- Uniform reflected-queue boundedness is exactly uniform absorption-deficit
+boundedness, with no change of constant.  Empty half-open windows contribute
+zero; every nonempty half-open window is one existing inclusive suffix. -/
+theorem canonicalOutstandingClaimQueueUniformUpperBound_iff_absorptionDeficitWindowUniformUpperBound
+    (n : OddNat) (C : ℕ) :
+    CanonicalOutstandingClaimQueueUniformUpperBound n C ↔
+      CanonicalAbsorptionDeficitWindowUniformUpperBound n C := by
+  rw [canonicalOutstandingClaimQueueUniformUpperBound_iff_all_windowDrift_le]
+  constructor
+  · intro h q M
+    cases M with
+    | zero => simp
+    | succ M =>
+        have hqm : q ≤ q + M := by omega
+        have hbound := h (q + M) q hqm
+        rw [← canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+          n hqm] at hbound
+        simpa using hbound
+  · intro h m q hqm
+    have hbound := h q (m - q + 1)
+    rwa [canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+      n hqm] at hbound
+
+/-! ## Exact finite suffix maximum in conservation language -/
+
+/-- Maximum positive absorption deficit among all suffixes ending at block
+`m`.  `Int.toNat` supplies the zero candidate for nonpositive deficits. -/
+noncomputable def canonicalAbsorptionDeficitSuffixMaximum
+    (n : OddNat) (m : ℕ) : ℕ :=
+  (Finset.range (m + 1)).sup fun q =>
+    Int.toNat (canonicalAbsorptionDeficitWindow n q (m - q + 1))
+
+/-- The reflected scalar queue is exactly the conservation-facing maximum
+positive suffix deficit. -/
+theorem canonicalOutstandingClaimQueue_eq_absorptionDeficitSuffixMaximum
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m =
+      canonicalAbsorptionDeficitSuffixMaximum n m := by
+  rw [canonicalOutstandingClaimQueue_eq_reflectedWindowMaximum]
+  unfold canonicalReflectedWindowMaximum canonicalAbsorptionDeficitSuffixMaximum
+  apply Finset.sup_congr rfl
+  intro q hq
+  have hqm : q ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hq)
+  rw [canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt n hqm]
+
+/-- Queue zero means that every conservation-facing suffix deficit ending at
+`m` is nonpositive. -/
+theorem canonicalOutstandingClaimQueue_eq_zero_iff_all_absorptionDeficit_nonpos
+    (n : OddNat) (m : ℕ) :
+    canonicalOutstandingClaimQueue n m = 0 ↔
+      ∀ q, q ≤ m →
+        canonicalAbsorptionDeficitWindow n q (m - q + 1) ≤ 0 := by
+  rw [canonicalOutstandingClaimQueue_eq_zero_iff_all_windowDrift_nonpos]
+  constructor <;> intro h q hqm
+  · rw [canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt n hqm]
+    exact h q hqm
+  · rw [← canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt n hqm]
+    exact h q hqm
+
+/-- A positive queue is equivalent to the existence of a positive finite
+suffix absorption deficit ending at the same block. -/
+theorem canonicalOutstandingClaimQueue_pos_iff_exists_absorptionDeficit_pos
+    (n : OddNat) (m : ℕ) :
+    0 < canonicalOutstandingClaimQueue n m ↔
+      ∃ q, q ≤ m ∧
+        0 < canonicalAbsorptionDeficitWindow n q (m - q + 1) := by
+  constructor
+  · intro hpos
+    rcases exists_absorptionDeficitWindow_eq_outstandingClaimQueue_of_pos hpos with
+      ⟨q, hqm, hq⟩
+    refine ⟨q, hqm, ?_⟩
+    have hposInt : (0 : ℤ) < canonicalOutstandingClaimQueue n m := by
+      exact_mod_cast hpos
+    rw [hq] at hposInt
+    exact hposInt
+  · rintro ⟨q, hqm, hpos⟩
+    by_contra hnot
+    have hzero : canonicalOutstandingClaimQueue n m = 0 := Nat.eq_zero_of_not_pos hnot
+    have hall :=
+      (canonicalOutstandingClaimQueue_eq_zero_iff_all_absorptionDeficit_nonpos
+        n m).mp hzero q hqm
+    omega
+
+/-! ## Primitive absorption-deficit excursions -/
+
+/-- Conservation-facing form of a finite repaid primitive excursion.  The
+future discharge endpoint `r` is part of the hypothesis; this definition does
+not assert that such an endpoint always exists. -/
+def CanonicalPrimitivePositiveAbsorptionDeficitExcursion
+    (n : OddNat) (q r : ℕ) : Prop :=
+  q < r ∧
+    canonicalOutstandingClaimQueueBefore n q = 0 ∧
+      (∀ m ∈ Finset.Ico q r,
+        0 < canonicalAbsorptionDeficitWindow n q (m - q + 1)) ∧
+        canonicalAbsorptionDeficitWindow n q (r - q + 1) ≤ 0
+
+/-- Primitive queue excursions, signed-drift excursions, and finite
+absorption-deficit excursions carry exactly the same conditional data. -/
+theorem canonicalPrimitivePositiveQueueExcursion_iff_absorptionDeficitExcursion
+    (n : OddNat) (q r : ℕ) :
+    CanonicalPrimitivePositiveQueueExcursion n q r ↔
+      CanonicalPrimitivePositiveAbsorptionDeficitExcursion n q r := by
+  rw [canonicalPrimitivePositiveQueueExcursion_iff_driftExcursion]
+  constructor
+  · rintro ⟨hqr, hbefore, hpositive, htotal⟩
+    refine ⟨hqr, hbefore, ?_, ?_⟩
+    · intro m hm
+      have hqm : q ≤ m := (Finset.mem_Ico.mp hm).1
+      rw [canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt n hqm]
+      exact hpositive m hm
+    · rw [canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+        n (Nat.le_of_lt hqr)]
+      exact htotal
+  · rintro ⟨hqr, hbefore, hpositive, htotal⟩
+    refine ⟨hqr, hbefore, ?_, ?_⟩
+    · intro m hm
+      have hqm : q ≤ m := (Finset.mem_Ico.mp hm).1
+      rw [← canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt n hqm]
+      exact hpositive m hm
+    · rw [← canonicalAbsorptionDeficitWindow_eq_canonicalWindowDriftInt
+        n (Nat.le_of_lt hqr)]
+      exact htotal
+
 /-! ## Global reserve obstruction -/

 /-- One natural reserve bounds every canonical width of every odd root. -/
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index 1417788e..0a056dea 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -620,6 +620,30 @@ theorem exists_canonicalFiniteSignedCertificate_iff_exists_queueUniformUpperBoun
 The reverse construction deliberately chooses its signature from `hC`.
 Therefore only a structurally predefined signature, fixed independently of an
 assumed queue ceiling, can provide a noncircular arithmetic certificate.
+
+## cp-344 canonical-signature audit
+
+The conservation form of one canonical edge weight is
+
+`block length - claim holes - terminal valuation`.
+
+A sound finite control state must therefore either recover these three terms
+or prove a common upper bound for every concrete edge in each projected edge
+fiber.  The currently available candidate coordinates do not yet do this:
+
+* the full carry/claim word has unbounded length;
+* block length and claim-hole count are unbounded `Nat` coordinates;
+* terminal valuation is likewise unbounded unless reduced to a class, and no
+  class-level theorem bounds the omitted quotient contribution;
+* queue zero/nonzero and excursion phase are finite, but record no magnitude;
+* bounded low residues remain finite but have known exact-weight collisions.
+
+Thus storing the exact ledger violates finiteness, while discarding its
+unbounded coordinates leaves the required bounded-edge-fiber theorem open.
+No canonical positive-cycle exclusion may be inferred before that theorem is
+proved.  The generic potential API below remains a valid consumer of a future
+independent finite abstraction; manufacturing its signature from an assumed
+queue bound remains intentionally classified as circular.
 -/

 namespace FiniteSignedTransitionPotentialCertificate
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md
index 8e402c38..6dfc2375 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-343.md
@@ -211,8 +211,9 @@ The new script
 python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
 ```

-records, for each audited odd root, a window attaining every newly observed
-reflected-queue record.  The generated CSV includes:
+checks the active absorption window at every positive queue state.  For each
+audited odd root, the generated CSV stores the final maximum witness and
+includes:

 - root;
 - terminal and witness-start blocks;
@@ -232,7 +233,9 @@ exact identity
 maximum queue = length - holes - terminal valuation.
 ```

-These values are explicitly observational.  They prove neither a uniform
+Every record-breaking positive queue value is therefore checked when it is
+encountered, but the CSV does not store every intermediate record.  These
+values are explicitly observational.  They prove neither a uniform
 all-root bound nor eventual discharge.

 Generated artifacts:
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-344.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-344.md
new file mode 100644
index 00000000..2feaeddb
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-344.md
@@ -0,0 +1,191 @@
+# Petal / FloatWindow implementation report: checkpoint 344
+
+## Status
+
+Checkpoint 344 is implemented without adding `sorry`.
+
+The reflected scalar queue and the conservation-facing absorption deficit are
+now identified at the same constant, at each finite maximum, at zero/positive
+states, and on finite primitive excursions.  The finite-transition branch was
+also audited.  It stops at a precise missing theorem rather than assuming
+cycle nonpositivity.
+
+## Audit wording correction
+
+The finite audit now checks the active-window deficit identity at every
+positive queue state, not only when a new record is set.  The CSV still stores
+only the final maximum witness for each root.  The cp-343 report and generated
+summary state this distinction explicitly.
+
+The finite range and observed values are unchanged:
+
+```text
+8192 odd roots in 1..16383
+6709 roots with a positive observed maximum
+largest observed queue/deficit: 8
+```
+
+These remain finite observations.
+
+## Same-constant equivalence
+
+Lean proves the parameterwise theorem
+
+```text
+CanonicalOutstandingClaimQueueUniformUpperBound n C
+  iff
+CanonicalAbsorptionDeficitWindowUniformUpperBound n C.
+```
+
+No root-width offset is needed between these two surfaces.  The proof handles
+the empty half-open window separately and converts each nonempty interval
+`[q, q + M)` into the inclusive suffix `q .. q + M - 1`.
+
+This differs from the width-reserve translation.  Width to queue still uses
+the root-width offset because width is an absolute level, while queue and
+deficit both measure positive finite-window increments.
+
+## Exact suffix maximum
+
+The new finite carrier is
+
+```text
+canonicalAbsorptionDeficitSuffixMaximum n m
+  = sup q in range (m + 1),
+      Int.toNat
+        (canonicalAbsorptionDeficitWindow n q (m - q + 1)).
+```
+
+Lean proves exactly
+
+```text
+canonicalOutstandingClaimQueue n m
+  = canonicalAbsorptionDeficitSuffixMaximum n m.
+```
+
+Thus the reflected recurrence does not merely produce some deficit witness.
+At every terminal block it computes the maximum positive absorption deficit
+among all finite suffixes ending there.
+
+Two direct consequences are now public:
+
+```text
+queue n m = 0
+  iff every suffix absorption deficit ending at m is nonpositive
+
+0 < queue n m
+  iff some suffix absorption deficit ending at m is positive.
+```
+
+## Primitive positive-deficit excursions
+
+The new predicate
+
+```text
+CanonicalPrimitivePositiveAbsorptionDeficitExcursion n q r
+```
+
+records:
+
+- queue before block `q` is zero;
+- every proper prefix from `q` has positive absorption deficit;
+- the total deficit through the supplied endpoint `r` is nonpositive.
+
+Lean proves it equivalent to the existing finite primitive queue excursion:
+
+```text
+CanonicalPrimitivePositiveQueueExcursion n q r
+  iff
+CanonicalPrimitivePositiveAbsorptionDeficitExcursion n q r.
+```
+
+The future discharge endpoint remains an input.  No theorem claiming that
+every open excursion has a future zero was added.
+
+## Finite-transition audit
+
+One block deficit is exactly
+
+```text
+block length - claim holes - terminal valuation.
+```
+
+A finite control graph must therefore either retain enough information to
+recover these terms or prove a common upper bound for all realized weights in
+each projected edge fiber.
+
+The candidate coordinates currently have the following status:
+
+| coordinate | finite as stated | sufficient weight control |
+| --- | --- | --- |
+| full carry/claim word | no, length is unbounded | exact but not finite |
+| block length | no | exact component |
+| claim-hole count | no | exact component |
+| terminal valuation | no | exact component |
+| queue zero/nonzero | yes | no magnitude control |
+| excursion phase | yes | no magnitude control |
+| bounded low residue | yes | exact-weight collisions already observed |
+
+Reducing an unbounded coordinate modulo or into a finite class does not yet
+bound the omitted quotient contribution.  The missing canonical theorem is:
+
+```text
+for every projected finite edge,
+all realized canonical block deficits in that edge fiber
+have a common finite upper bound.
+```
+
+Without that theorem, a finite weighted edge table cannot be defined soundly.
+Consequently, reachable positive-cycle exclusion cannot yet be formulated as
+a canonical theorem rather than an assumption.
+
+This obstruction is recorded in the source commentary of
+`FiniteSignedTransition.lean`.
+
+## Independent discharge search
+
+The existing relevant surfaces remain conditional:
+
+- bounded repayment lag requires a supplied lag property;
+- source-age horizon requires a supplied horizon or future payment;
+- primitive excursion closure requires a supplied future queue zero;
+- potential certificates require a supplied sound finite projection and
+  bounded potential;
+- the reverse finite certificate built from an assumed queue bound is
+  explicitly circular.
+
+No unconditional theorem in the current source database supplies regular
+queue discharge, bounded source age, cumulative terminal-valuation absorption,
+or positive-cycle exclusion from canonical arithmetic alone.
+
+## Facts fixed by Lean
+
+1. Queue boundedness and all-window deficit boundedness are equivalent with
+   exactly the same constant.
+2. The queue at each block is the exact maximum positive suffix deficit.
+3. Queue zero is exactly universal nonpositivity of ending suffix deficits.
+4. Queue positivity is exactly existence of a positive ending suffix deficit.
+5. Finite repaid primitive queue excursions are exactly primitive
+   absorption-deficit excursions.
+6. None of these theorems supplies a future discharge endpoint or a uniform
+   bound independently.
+
+## Next implementation direction
+
+The next noncircular branch must attack the bounded-edge-fiber theorem before
+cycle elimination.  A useful candidate should:
+
+1. choose a structurally predefined finite signature;
+2. prove every canonical transition maps to a projected edge;
+3. prove each projected edge's realized deficit fiber is bounded above;
+4. only then audit or prove nonpositivity of reachable projected cycles.
+
+If no such signature controls the edge fiber, the alternative arithmetic
+route is an independent regular-discharge or cumulative absorption theorem.
+Further queue/credit reformulations alone will not advance the open target.
+
+## Verification
+
+The checkpoint is checked by the targeted reserve build, the strengthened
+finite Python audit, aggregate FloatWindow/PetalBridge builds, top-level
+`DkMath`, `git diff --check`, and a no-`sorry` scan of modified Lean files.
diff --git a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
index 8cc076b4..e8883f87 100644
--- a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+++ b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
@@ -111,6 +111,15 @@ def audit_root(root: int) -> AuditRow:
             active_start = -1

         blocks_audited = block + 1
+        if queue > 0:
+            # Reflection is inactive inside the current positive excursion.
+            # Check every positive queue state, not only record-breaking ones.
+            assert active_start >= 0
+            active_length = prefix_lengths[block + 1] - prefix_lengths[active_start]
+            active_holes = prefix_holes[block + 1] - prefix_holes[active_start]
+            active_valuation = sum(terminal_valuations[active_start : block + 1])
+            assert active_length - active_holes - active_valuation == queue
+
         if queue > maximum_queue:
             assert active_start >= 0
             q = active_start
@@ -191,7 +200,8 @@ def main() -> None:
         f"- roots reaching a state-one canonical endpoint: {reached}",
         f"- roots with a positive observed queue maximum: {positive}",
         f"- largest observed queue/deficit: {max(row.maximum_queue for row in rows)}",
-        "- every positive record is attained by the displayed finite window",
+        "- every positive queue state passed its active-window deficit identity",
+        "- the CSV stores the final maximum witness for each root",
         "- no uniform bound or eventual discharge follows from this table",
         "",
         "## Maximum-Deficit Windows",
diff --git a/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md b/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
index 51864560..d8c440eb 100644
--- a/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
+++ b/python/Collatz/PetalBridge/results/canonical_absorption_deficit_audit_343.md
@@ -9,7 +9,8 @@ This is finite computational evidence, not a Lean theorem.
 - roots reaching a state-one canonical endpoint: 8192
 - roots with a positive observed queue maximum: 6709
 - largest observed queue/deficit: 8
-- every positive record is attained by the displayed finite window
+- every positive queue state passed its active-window deficit identity
+- the CSV stores the final maximum witness for each root
 - no uniform bound or eventual discharge follows from this table

 ## Maximum-Deficit Windows
````
`````

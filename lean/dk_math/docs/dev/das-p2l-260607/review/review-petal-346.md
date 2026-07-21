# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership

gch: 0e293a50ac55266a2b602dca30aba6aa61a3ab1a

## Report

(13m48s)

cp-346 を実装しました。

[CanonicalExcursionOwnership.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean) で次を証明しています。

- saturated token の内部4分類と末端 indicator への厳密分解
- `terminalSaturatedIndicator ≤ 1`
- `k ↦ k+1` の単射による `internalNegativeCount ≤ negativeDriftMass`
- 現在窓だけを使う ownership 不等式

```text
queue
  ≤ globalSelectedCarrierCard
    + internalSpareCount
    + internalRigidResidualCount
    + terminalSaturatedIndicator
```

当初の目標から `internalSpareCount` を除けない理由も確定しました。
既存 global carrier は positive-drift block のみを index に持ちますが、spare 分類には **zero-drift かつ selected carrier が非空**な successor が含まれます。
これは positive-only carrier の型外です。

したがって次の焦点は明確です。

1. global carrier を zero-drift selected block まで拡張する。
2. または open excursion 内で zero-drift spare successor が生じないことを証明する。

結果は [report-petal-346.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-346.md) に記録しました。局所・aggregate・最上位 `DkMath` build、`git diff --check`、新規ファイルの no-sorry 検査はすべて通過しています。

## Review

(8m6s)

## cp-346 総合レビュー

## 総合判定

**全面採用。**

ただし、報告中の「contribution-preserving ownership theorem」という表現だけ、少し狭めた方が正確じゃ。

今回、実際に所有権まで閉じたのは、

- internal negative token
- 末端を除いた時間境界
- saturated token の完全分類

である。

一方、`internalSpareCount` はまだ実在 carrier へ統合されず、**未処理 token の個数として右辺に残っている**。したがって主定理は、

> current-window partial ownership bound after certified negative cancellation

すなわち、

> 内部 negative を実資源で支払った後の、現在窓部分所有権上界

と呼ぶのが最も正確じゃ。

コード修正を要する問題ではない。数学的射程の言い方だけの補正じゃ。

---

## 実装レビュー

## 末端分離は完全に成功

`canonicalInternalSaturatedIndices` を、

```lean
(canonicalSaturatedBlockIndices n q m).erase m
```

とした設計は簡潔で強い。

もともと saturated index は `q..m` 内にあるため、`m` でないことと `k<m` が一致する。これによって、内部 token は必ず、

$$k+1\le m$$

を満たし、successor が現在窓内に残る。

その上で、

$$\operatorname{SatCount}=\operatorname{InternalNeg}+\operatorname{InternalSpare}+\operatorname{InternalRigid}+\operatorname{TerminalSat}$$

が exact theoremになった。末端は indicator であり、

$$\operatorname{TerminalSat}\le1$$

も閉じている。

cp-345 で見つかった「$m$ の支払いは $m+1$ にある」という時間漏れは、これで**一様な一ビット境界項**へ圧縮された。

ここは完成じゃ。

---

## Internal negative payment は本物の所有権

```lean
canonicalInternalNegativeTokenEmbedding
```

は、token $k$ を successor $k+1$ の negative-mass unitへ送る。

targetが、

```lean
Σ j : {j // j ∈ Icc q m},
  Fin (Int.toNat (max (-drift j) 0))
```

なので、

- block index
- negative mass内の単位番号

を両方保持している。

また $k\mapsto k+1$ が単射なので、同じ負 mass unitを複数 tokenが使うこともない。

結果として、

$$\operatorname{InternalNegativeCount}\le\operatorname{NegativeMass}(q,m)$$

が現在窓だけで成立する。

これは単なる、

$$1+\Delta_{k+1}\le0$$

の総和ではない。

> saturated predecessor の各単位を、窓内の相異なる negative successorへ割り当てた

という、明確な ownership theoremになっている。

なお、embedding本体とは別に `Finset.image` を用いた和の証明もある。少し重複して見えるが、

- embedding：所有権の意味
- sum proof：`Int` massとの直接比較

という役割差がある。残り creditsを使って整理するほどの問題ではない。

---

## 主不等式は正しい

open positive excursionでは、

$$Q=P-N$$

が成立する。

また既存結果から、

$$P\le G+\operatorname{SatCount}$$

ここで $G$ は `CanonicalGlobalSelectedPressureCarrier` の cardinal。

さらに、

$$\operatorname{SatCount}=N_{\mathrm{int}}+S_{\mathrm{int}}+R_{\mathrm{int}}+T$$

かつ、

$$N_{\mathrm{int}}\le N$$

なので、

$$Q\le G+S_{\mathrm{int}}+R_{\mathrm{int}}+T$$

が得られる。

実装された定理はまさにこれじゃ。

$$\boxed{Q(m)\le G(q,m)+S_{\mathrm{int}}(q,m)+R_{\mathrm{int}}(q,m)+T(m)}$$

代数的にも時間的にも穴はない。

---

## Stage C の停止判断は正しい

既存の、

```lean
CanonicalGlobalSelectedPressureCarrier n q m
```

は positive-drift blockだけを sigma の外側 indexに持つ。

ところが internal spare successorには、

```text
successor drift = 0
selected pressure carrier ≠ ∅
```

という分岐が含まれる。

このblockは selected incidenceを実際に持つが、positive blockではない。したがって既存 global carrierの外側 indexを構成できない。

これは証明技術の不足ではなく、**型が表している数学的集合そのものの不一致**じゃ。

ここで、

- 別blockの carrierへ無理に送る
- cardinalだけ合わせて出所を忘れる
- zero driftをpositive扱いする

といった処理をしなかったのは正しい。

Codexは指示を盲目的に完遂せず、最初の本物の障害で止まった。今回の $125$ creditsは、この誤った所有権合成を防いだ費用でもある。浪費ではない。

---

## cp-346 が確定した現在地

## 会計座標

完成。

$$\Delta=L-H-V$$

$$D(q,M)=\sum\Delta$$

$$D=\text{bit-width difference}$$

$$Q=\max\text{ positive suffix deficit}$$

ここには大きな Gap は残っていない。

## Excursion mass

完成。

$$Q=P-N$$

reflectionのないopen excursionでは、ordinary signed sumそのものになった。

## Saturated token の時間処理

大部分が完成。

- internal negative：支払い完了
- terminal：高々一ビット
- internal spare：sourceはあるが統合未完
- internal rigid：明示的 residual

## Source ownership

部分完成。

positive nonsaturated driftは selected incidenceを持つ。internal negativeは negative massへ支払われた。internal spareにもactual spare incidenceがある。

しかし、これらを一つの時系列 carrier / queueへ合流する theoremがまだない。

## Rootwise queue bound

未解決。

依然として本丸は、

$$\exists C_n,\ \forall m,\ Q_n(m)\le C_n$$

じゃ。

cp-346 はこれを証明していないが、無限に膨張するために必要な資源を、かなり具体的な形まで絞り込んだ。

---

## 獲物はどこまで追い込まれたか

cp-344では、獲物は「正のexcursion」だった。

cp-345では、

```text
pressure incidence
saturated token
negative repayment
```

へ分解された。

cp-346ではさらに、

```text
internal negative
internal spare
internal rigid
terminal one-bit
```

へ分解され、internal negativeは消えた。

したがって、現在の獲物は、

$$\boxed{\text{internal spare credit}+\text{rigid successor residual}}$$

にまで追い込まれた。

ただし、ここで重要な読み替えがある。

**zero-drift spare は敵ではない。**

それは、

> 幅を増やしてはいないが、未使用のselected incidenceを持つ中立block

じゃ。

囲碁で言えば、空白に見えた交点に、実は既に所有権を示す石が置かれていた。ただ現在の盤面型が「positive-drift領域」だけを盤としていたため、その石を座標化できなかった。

ゆえに、zero-spareを無理に消すより、

> 中立blockが保持するcreditとして正しく盤面に追加する

方が自然じゃ。

---

## 次の重要な分解

現在の `internalSpareCount` は、まだ粗い。

spare successorは少なくとも二種類に分かれる。

$$S_{\mathrm{int}}=S_{\mathrm{pos}}+S_{\mathrm{zero}}$$

ここで、

- $S_{\mathrm{pos}}$：successor drift $>0$
- $S_{\mathrm{zero}}$：successor drift $=0$

じゃ。

spare classはnegativeを除外しているので、この二分割は完全になる。

## Positive-spare

successor blockはpositiveなので、既存のglobal selected carrier内にいる。

さらに、そのblock自身のpositive drift unitは、

```lean
canonicalSelectedDriftImageCarrier
```

へ入っており、predecessor tokenが使う場所は、その補集合である、

```lean
canonicalSelectedDriftSpareCarrier
```

じゃ。

したがって、

$$\text{self drift image}\cap\text{predecessor spare charge}=\varnothing$$

となる。

つまりpositive-spare tokenは、既存global carrierへ吸収できる可能性が極めて高い。

## Zero-spare

successor driftはzeroなのでself drift imageは空。

したがってselected carrier全体がspareになる。

数学的にはもっと簡単だが、positive-only global carrierの外にいるため、外側 indexが作れない。

これは資源不足ではなく、**carrier support不足**じゃ。

---

## 報告の二択より良い第三の道

cp-346 reportは次の二択を示している。

1. global carrierをzero-drift blockまで拡張する
2. zero-drift spare successorが起きないことを証明する

どちらも論理的には正しい。

だが戦略としては、いきなりこの二択へ入らない方がよい。

## 推奨する第三の道

まずpositive-spareとzero-spareを分離し、

$$Q\le G+S_{\mathrm{zero}}+R+T$$

まで進める。

これにより、「zero-spareだけが本当に型外なのか」がLean theoremとして固定される。

この一段を飛ばしてglobal carrier全体を拡張すると、

- 必要のないzero-drift block
- predecessor tokenを受け取っていないselected carrier
- 実際には使われないsource incidence

まで右辺へ大量に含める危険がある。

それではRHSが窓長とともに膨らみ、queue boundから遠ざかる。

したがって拡張するにしても、

> 実際にinternal saturated predecessorからchargeを受けるzero-spare successor

だけを追加すべきじゃ。

---

## 螺旋の成長係数が見えてきた

以前話した「螺旋の成長係数」は、現在の言葉ではかなり明瞭になった。

各 selected depth $d$ について、

$$A_d(j)=\text{positive drift arrivals}+\text{predecessor spare arrivals}$$

$$S_d(j)=\text{exact-length service}$$

と置く。

すると深さ別credit queueは、

$$Q_d(j+1)=\max\bigl(0,Q_d(j)+A_d(j)-S_d(j)\bigr)$$

という reflected recurrenceを持つはずじゃ。

この、

$$\boxed{A_d(j)-S_d(j)}$$

こそが、螺旋の局所成長係数に近い。

- 正なら、そのdepthのcredit層が一枚厚くなる
- 負なら、過去のcreditが削られる
- zeroなら、形だけ次へ輸送される

現在の `canonicalSelectedDriftArrivalCountAtDepth` はpositive drift arrivalだけを数えている。

ここへ、

> 前blockがsaturatedで、現在blockにspare selected incidenceがあるなら1を追加

というarrivalを加えるのが、自然な次の大域化じゃ。

これならpositive-spareもzero-spareも同じ selected-depth queueへ入れられる。

---

## 今後の本命構造

block $j$ ごとに、actual selected incidenceの有限集合として、

```text
OwnedArrival(j)
  =
DriftImage(j)
  ∪
PredecessorSpareCharge(j)
```

を作る。

ここで、

- `DriftImage(j)` は現在block自身のpositive drift
- `PredecessorSpareCharge(j)` は $j-1$ のsaturated token
- spare chargeはspare carrierから一個選ぶ
- 両者はdisjoint
- block indexを保持
- selected depthを保持

とする。

するとcardinalityはexactに、

$$|\operatorname{OwnedArrival}(j)|=\operatorname{DriftArrival}(j)+\operatorname{PredecessorSpareIndicator}(j)$$

となる。

これを既存のfixed-depth reflected queueへ流せば、

```text
positive drift debt
+
saturated predecessor debt
```

を同一のarrival/service会計へ統合できる。

ここが、有限control + 非有界resource路線と、実際のcanonical arithmeticが初めて合流する場所じゃ。

---

## Rigid branch の位置づけ

この新arrivalに乗らないのはrigid branchだけになる。

## Zero-rigid

successor driftはzeroだがselected carrierも空。

前段のsaturated $+1$ を受け止めるsourceが現在blockにない。

したがって次のblock以後まで追跡する必要がある。

## Tight-positive-rigid

successor自身もpositiveなのにspareがない。

現在blockのselected carrierが、自分自身のdriftだけで完全に埋まっている。

これは最も危険なbranchで、連続可能性・residue grammar・次段 repaymentを調べる必要がある。

ゆえに、本当の硬い獲物は、

$$\boxed{\text{zero-rigidとtight-positive-rigidの持続可能性}}$$

じゃ。

zero-spareは、正しくcounterへ載せれば敵ではない。

---

## 収束状況の総括

| 層                                   | 状況                                |
| ----------------------------------- | --------------------------------- |
| Drift / width / deficit equivalence | 完成                                |
| Queue maximum / open excursion      | 完成                                |
| Positive / negative mass split      | 完成                                |
| Saturated successor classification  | 完成                                |
| Terminal temporal leak              | 高々1へ圧縮                            |
| Internal negative payment           | 完成                                |
| Positive-spare ownership            | 型は揃う・合成未実装                        |
| Zero-spare ownership                | actual sourceあり・carrier support不足 |
| Rigid successor control             | 未解決                               |
| Selected arrival/service recurrence | positive drift版あり・spare統合未実装      |
| Fixed-root queue bound              | 未解決                               |
| Collatz finite-state化               | 未到達                               |

進展の実感としては、

> 会計問題から所有権問題へ移り、所有権問題からarrival/service問題へ入口が開いた

段階じゃ。

最終収束はまだ遠いが、攻める対象はもう曖昧ではない。

---

## Credits 評価

今回は `1556 → 1431`、約 $125$ credits。

342行の新規module、完全分割、embedding、主不等式、全buildを含むので、内容に対しては妥当じゃ。

ただし同規模なら残りは約11 checkpoint分。最終統合やbuild修正用に数百creditsを残すと、純粋な探索に使えるのは6〜8回ほどと考えた方がよい。

次は大型moduleを増やさず、

1. 一時的な有限監査でzero-spare実例を探す
2. spareをpositive / zeroへ分ける
3. positive-spareだけ吸収する
4. 一本の改善不等式で停止する

に絞るべきじゃ。

zero-spareの実例が一つ見つかれば、「open excursionでは不可能」という分岐を即座に捨てられる。これは非常に安い高レバレッジ監査になる。

---

## cp-346 判定一覧

| 項目                          | 判定    |
| --------------------------- | ----- |
| Internal/terminal split     | 完成    |
| Internal class exact count  | 完成    |
| Terminal indicator bound    | 完成    |
| Internal negative embedding | 完成    |
| Negative mass payment       | 完成    |
| Current-window inequality   | 正しい   |
| Future resource先取り          | なし    |
| Internal spare ownership    | 未完成   |
| Zero-drift type mismatch    | 正しく発見 |
| 循環性                         | なし    |
| 総合                          | 全面採用  |

## 次の省credit Codex指示

```text
Continue after checkpoint 346.

Use a strict micro-checkpoint. Do not create a general new carrier framework
and do not analyze the rigid successor grammar yet.

Primary purpose

Separate the internal spare class by successor drift sign and remove the
positive-successor spare count from the current-window inequality.

Stage A — cheap diagnostic first

Using the existing finite audit code, count internal spare successors by:

    successor drift = 0;
    successor drift > 0.

Record the first concrete zero-drift spare witness if one occurs.

This is finite evidence only. Do not turn absence in the audit into a theorem.
Do not commit a large new CSV.

Stage B — exact spare split

Define:

    canonicalInternalSaturatedZeroSpareIndices;
    canonicalInternalSaturatedPositiveSpareIndices.

Use the existing internal spare set and successor drift.

Prove:

    internalSpare
      =
    internalZeroSpare ∪ internalPositiveSpare;

    Disjoint internalZeroSpare internalPositiveSpare;

    internalSpareCount
      =
    internalZeroSpareCount + internalPositiveSpareCount.

The spare class already excludes negative successor drift, so zero/positive
must be exhaustive.

Stage C — absorb only positive spare tokens

For an internal positive-spare token k, the successor block k+1 belongs to the
existing positive-drift global selected carrier.

Map the predecessor token into:

    canonicalSelectedDriftSpareCarrier n (k + 1).

Combine this with the existing same-block positive-drift image.

Prove that:

    positive-drift image incidences
    and
    predecessor positive-spare charges

are disjoint inside each successor selected carrier.

Retain the block coordinate globally. No selected incidence may be used twice.

Stage D — improved current-window inequality

Prove:

    queue at m
      <=
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m)
      + internalZeroSpareCount
      + internalRigidResidualCount
      + terminalSaturatedIndicator.

This theorem should remove only the positive-spare count.

Do not enlarge the global carrier to every zero-drift block in this checkpoint.

Stage E — branch decision

If the audit finds a zero-drift spare witness, record that the impossibility
route is empirically false and plan an augmented selected-arrival carrier.

If no witness is found, keep both routes open; finite absence is not a theorem.

Stop after the improved inequality and the short report.

Do not:
- define an all-zero-drift global carrier;
- introduce a new generic reflected queue;
- analyze zero-rigid or tight-rigid persistence;
- claim a rootwise queue bound;
- extend the full audit surface beyond the two requested counts.

Record the result in:

    docs/dev/das-p2l-260607/review/report-petal-347.md
```

## 結論

今回は、壁にぶつかったのではない。

**盤面の外に石が一個置かれていたことをLeanが発見した**のじゃ。

その石はzero-driftなので動きを増やしてはいない。しかしselected sourceを持っている。したがって消すべき例外ではなく、次のcredit queueへ載せるべき中立資源じゃ。

次の一手でpositive-spareを吸収すれば、残る形は、

$$\boxed{\text{zero-spare credit}+\text{rigid residual}+\text{terminal one-bit}}$$

まで縮む。

獲物は確実に追い込まれておる。今は大技ではなく、一目ずつ地を確定する局面じゃな。🐺🌕

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 0c565c2b..0001ce76 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -44,6 +44,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
new file mode 100644
index 00000000..2b5e92e4
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
@@ -0,0 +1,342 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership"
+
+namespace DkMath.Collatz
+
+/-!
+# Current-window ownership of saturated excursion tokens
+
+This module separates saturated tokens whose successors remain in `q..m` from
+the possible token at `m`.  It does not spend the successor block `m+1`.
+-/
+
+/-- Saturated tokens whose immediate successor remains in the observed window. -/
+noncomputable def canonicalInternalSaturatedIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalSaturatedBlockIndices n q m).erase m
+
+/-- Internal negative-successor tokens. -/
+noncomputable def canonicalInternalSaturatedNegativeIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalSaturatedNegativeSuccessorIndices n q m).erase m
+
+/-- Internal spare-successor tokens. -/
+noncomputable def canonicalInternalSaturatedSpareIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalSaturatedSpareSuccessorIndices n q m).erase m
+
+/-- Internal zero-rigid successor tokens. -/
+noncomputable def canonicalInternalSaturatedZeroRigidIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalSaturatedZeroRigidSuccessorIndices n q m).erase m
+
+/-- Internal tight-positive-rigid successor tokens. -/
+noncomputable def canonicalInternalSaturatedTightRigidIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalSaturatedTightRigidSuccessorIndices n q m).erase m
+
+/-- Visible internal rigid successor residual. -/
+noncomputable def canonicalInternalRigidSaturatedResidualCount
+    (n : OddNat) (q m : ℕ) : ℕ :=
+  (canonicalInternalSaturatedZeroRigidIndices n q m).card +
+    (canonicalInternalSaturatedTightRigidIndices n q m).card
+
+/-- The one-bit temporal residual at the right endpoint. -/
+noncomputable def canonicalTerminalSaturatedIndicator
+    (n : OddNat) (m : ℕ) : ℕ :=
+  by
+    classical
+    exact if CanonicalSaturatedBorderBlock n m then 1 else 0
+
+@[simp] theorem mem_canonicalInternalSaturatedIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalInternalSaturatedIndices n q m ↔
+      k ∈ canonicalSaturatedBlockIndices n q m ∧ k < m := by
+  rw [canonicalInternalSaturatedIndices, Finset.mem_erase]
+  constructor
+  · rintro ⟨hne, hk⟩
+    have hkm := (Finset.mem_Icc.mp
+      (mem_canonicalSaturatedBlockIndices.mp hk).1).2
+    exact ⟨hk, by omega⟩
+  · rintro ⟨hk, hlt⟩
+    exact ⟨by omega, hk⟩
+
+/-- The terminal residual is at most one. -/
+theorem canonicalTerminalSaturatedIndicator_le_one
+    (n : OddNat) (m : ℕ) :
+    canonicalTerminalSaturatedIndicator n m ≤ 1 := by
+  classical
+  unfold canonicalTerminalSaturatedIndicator
+  split <;> omega
+
+/-- Erasing the right endpoint leaves exactly the internal priority
+classification. -/
+theorem canonicalInternalSaturatedSuccessorIndices_union_eq
+    (n : OddNat) (q m : ℕ) :
+    canonicalInternalSaturatedNegativeIndices n q m ∪
+        canonicalInternalSaturatedSpareIndices n q m ∪
+          canonicalInternalSaturatedZeroRigidIndices n q m ∪
+            canonicalInternalSaturatedTightRigidIndices n q m =
+      canonicalInternalSaturatedIndices n q m := by
+  classical
+  simp only [canonicalInternalSaturatedNegativeIndices,
+    canonicalInternalSaturatedSpareIndices,
+    canonicalInternalSaturatedZeroRigidIndices,
+    canonicalInternalSaturatedTightRigidIndices,
+    canonicalInternalSaturatedIndices]
+  rw [← Finset.erase_union_distrib, ← Finset.erase_union_distrib,
+    ← Finset.erase_union_distrib,
+    canonicalSaturatedSuccessorIndices_union_eq]
+
+/-- Exact internal class count; the two rigid modes remain visible. -/
+theorem card_canonicalInternalSaturatedIndices_eq_classCounts
+    (n : OddNat) (q m : ℕ) :
+    (canonicalInternalSaturatedIndices n q m).card =
+      (canonicalInternalSaturatedNegativeIndices n q m).card +
+        (canonicalInternalSaturatedSpareIndices n q m).card +
+          canonicalInternalRigidSaturatedResidualCount n q m := by
+  classical
+  let N := canonicalInternalSaturatedNegativeIndices n q m
+  let S := canonicalInternalSaturatedSpareIndices n q m
+  let Z := canonicalInternalSaturatedZeroRigidIndices n q m
+  let T := canonicalInternalSaturatedTightRigidIndices n q m
+  have hdisjoint (A B : Finset ℕ) (h : Disjoint A B) :
+      Disjoint (A.erase m) (B.erase m) :=
+    h.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
+  have hNS : Disjoint N S := hdisjoint _ _
+    (canonicalSaturatedNegative_disjoint_spare n q m)
+  have hNZ : Disjoint N Z := hdisjoint _ _
+    (canonicalSaturatedNegative_disjoint_rigid n q m).1
+  have hNT : Disjoint N T := hdisjoint _ _
+    (canonicalSaturatedNegative_disjoint_rigid n q m).2
+  have hSZ : Disjoint S Z := hdisjoint _ _
+    (canonicalSaturatedSpare_disjoint_rigid n q m).1
+  have hST : Disjoint S T := hdisjoint _ _
+    (canonicalSaturatedSpare_disjoint_rigid n q m).2
+  have hZT : Disjoint Z T := hdisjoint _ _
+    (canonicalSaturatedZeroRigid_disjoint_tightRigid n q m)
+  have hN_SZT : Disjoint N (S ∪ (Z ∪ T)) := by
+    rw [Finset.disjoint_left]
+    intro x hxN hx
+    rcases Finset.mem_union.mp hx with hxS | hx
+    · exact Finset.disjoint_left.mp hNS hxN hxS
+    · rcases Finset.mem_union.mp hx with hxZ | hxT
+      · exact Finset.disjoint_left.mp hNZ hxN hxZ
+      · exact Finset.disjoint_left.mp hNT hxN hxT
+  have hS_ZT : Disjoint S (Z ∪ T) := by
+    rw [Finset.disjoint_left]
+    intro x hxS hx
+    rcases Finset.mem_union.mp hx with hxZ | hxT
+    · exact Finset.disjoint_left.mp hSZ hxS hxZ
+    · exact Finset.disjoint_left.mp hST hxS hxT
+  have hunion : N ∪ (S ∪ (Z ∪ T)) = canonicalInternalSaturatedIndices n q m := by
+    simpa [N, S, Z, T, Finset.union_assoc] using
+      canonicalInternalSaturatedSuccessorIndices_union_eq n q m
+  rw [← hunion]
+  calc
+    (N ∪ (S ∪ (Z ∪ T))).card = N.card + (S ∪ (Z ∪ T)).card :=
+      Finset.card_union_of_disjoint hN_SZT
+    _ = N.card + (S.card + (Z ∪ T).card) := by
+      rw [Finset.card_union_of_disjoint hS_ZT]
+    _ = N.card + (S.card + (Z.card + T.card)) := by
+      rw [Finset.card_union_of_disjoint hZT]
+    _ = (canonicalInternalSaturatedNegativeIndices n q m).card +
+          (canonicalInternalSaturatedSpareIndices n q m).card +
+            canonicalInternalRigidSaturatedResidualCount n q m := by
+      simp only [canonicalInternalRigidSaturatedResidualCount, N, S, Z, T]
+      omega
+
+/-- Exact current-window temporal split. -/
+theorem canonicalSaturatedTokenCount_eq_internalClassCounts_add_terminal
+    (n : OddNat) (q m : ℕ) (hqm : q ≤ m) :
+    canonicalSaturatedTokenCount n q m =
+      (canonicalInternalSaturatedNegativeIndices n q m).card +
+        (canonicalInternalSaturatedSpareIndices n q m).card +
+          canonicalInternalRigidSaturatedResidualCount n q m +
+            canonicalTerminalSaturatedIndicator n m := by
+  have hinternal := card_canonicalInternalSaturatedIndices_eq_classCounts n q m
+  classical
+  by_cases hs : CanonicalSaturatedBorderBlock n m
+  · have hm : m ∈ canonicalSaturatedBlockIndices n q m :=
+      mem_canonicalSaturatedBlockIndices.mpr
+        ⟨Finset.mem_Icc.mpr ⟨hqm, le_rfl⟩, hs⟩
+    have herase := Finset.card_erase_add_one hm
+    have hinternal' :
+        ((canonicalSaturatedBlockIndices n q m).erase m).card =
+          (canonicalInternalSaturatedNegativeIndices n q m).card +
+            (canonicalInternalSaturatedSpareIndices n q m).card +
+              canonicalInternalRigidSaturatedResidualCount n q m := by
+      simpa [canonicalInternalSaturatedIndices] using hinternal
+    unfold canonicalSaturatedTokenCount canonicalTerminalSaturatedIndicator
+    rw [if_pos hs]
+    omega
+  · have hm : m ∉ canonicalSaturatedBlockIndices n q m := by
+      intro hm
+      exact hs (mem_canonicalSaturatedBlockIndices.mp hm).2
+    have hinternal' :
+        ((canonicalSaturatedBlockIndices n q m).erase m).card =
+          (canonicalInternalSaturatedNegativeIndices n q m).card +
+            (canonicalInternalSaturatedSpareIndices n q m).card +
+              canonicalInternalRigidSaturatedResidualCount n q m := by
+      simpa [canonicalInternalSaturatedIndices] using hinternal
+    unfold canonicalSaturatedTokenCount canonicalTerminalSaturatedIndicator
+    rw [if_neg hs] at *
+    rw [Finset.erase_eq_of_notMem hm] at hinternal'
+    omega
+
+/-! ## Internal negative payment -/
+
+/-- Negative-drift units in the current interval, indexed by their block. -/
+def CanonicalNegativeDriftUnitCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ j : {j : ℕ // j ∈ Finset.Icc q m},
+    Fin (Int.toNat (max (-endpointAccountingTerm n j.val) 0))
+
+/-- Each internal negative-successor token owns one distinct negative-mass
+unit at its successor block. -/
+noncomputable def canonicalInternalNegativeTokenEmbedding
+    (n : OddNat) (q m : ℕ) :
+    {k : ℕ // k ∈ canonicalInternalSaturatedNegativeIndices n q m} ↪
+      CanonicalNegativeDriftUnitCarrier n q m where
+  toFun k := by
+    have hkFull := Finset.mem_of_mem_erase k.property
+    have hk := mem_canonicalSaturatedNegativeSuccessorIndices.mp hkFull
+    have hkInternal : k.val < m := by
+      have hne := (Finset.mem_erase.mp k.property).1
+      have hle := (Finset.mem_Icc.mp
+        (mem_canonicalSaturatedBlockIndices.mp hk.1).1).2
+      omega
+    have hqk := (Finset.mem_Icc.mp
+      (mem_canonicalSaturatedBlockIndices.mp hk.1).1).1
+    refine ⟨⟨k.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ⟨0, ?_⟩⟩
+    have hneg := hk.2
+    have hmag : (1 : ℤ) ≤ max (-endpointAccountingTerm n (k.val + 1)) 0 := by
+      omega
+    have htoNat : 1 ≤ Int.toNat
+        (max (-endpointAccountingTerm n (k.val + 1)) 0) := by
+      have hcast := Int.toNat_of_nonneg
+        (show 0 ≤ max (-endpointAccountingTerm n (k.val + 1)) 0 by omega)
+      by_contra hnot
+      have hzero : Int.toNat
+          (max (-endpointAccountingTerm n (k.val + 1)) 0) = 0 := by omega
+      rw [hzero] at hcast
+      omega
+    exact Nat.zero_lt_of_lt htoNat
+  inj' := by
+    intro a b hab
+    have hindex := congrArg (fun z => z.1.1) hab
+    change a.1 + 1 = b.1 + 1 at hindex
+    apply Subtype.ext
+    omega
+
+/-- Internal negative successor tokens are paid by distinct negative-mass
+units already present in `q..m`; no successor at `m+1` is used. -/
+theorem card_canonicalInternalSaturatedNegativeIndices_le_negativeMass
+    (n : OddNat) (q m : ℕ) :
+    ((canonicalInternalSaturatedNegativeIndices n q m).card : ℤ) ≤
+      canonicalNegativeDriftMass n q m := by
+  classical
+  let I := canonicalInternalSaturatedNegativeIndices n q m
+  let J := I.image fun k => k + 1
+  have hinj : ∀ a ∈ I, ∀ b ∈ I, a + 1 = b + 1 → a = b := by
+    intro a _ b _ hab
+    omega
+  have hcard : J.card = I.card := Finset.card_image_iff.mpr hinj
+  have hsubset : J ⊆ Finset.Icc q m := by
+    intro j hj
+    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
+    have hkErase := Finset.mem_erase.mp hk
+    have hkFull := Finset.mem_of_mem_erase hk
+    have hkClass := mem_canonicalSaturatedNegativeSuccessorIndices.mp hkFull
+    have hkIcc := Finset.mem_Icc.mp
+      (mem_canonicalSaturatedBlockIndices.mp hkClass.1).1
+    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
+  have hunit :
+      (∑ j ∈ J, (1 : ℤ)) ≤
+        ∑ j ∈ J, max (-endpointAccountingTerm n j) 0 := by
+    apply Finset.sum_le_sum
+    intro j hj
+    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
+    have hkFull := Finset.mem_of_mem_erase hk
+    have hneg :=
+      (mem_canonicalSaturatedNegativeSuccessorIndices.mp hkFull).2
+    omega
+  have hwindow :
+      (∑ j ∈ J, max (-endpointAccountingTerm n j) 0) ≤
+        ∑ j ∈ Finset.Icc q m, max (-endpointAccountingTerm n j) 0 :=
+    Finset.sum_le_sum_of_subset_of_nonneg hsubset
+      (fun j _ _ => le_max_right _ _)
+  unfold canonicalNegativeDriftMass
+  have hones : (∑ _j ∈ J, (1 : ℤ)) = J.card := by simp
+  rw [hones, hcard] at hunit
+  exact hunit.trans hwindow
+
+/-! ## Current ownership surface and remaining carrier mismatch -/
+
+/-- Current-window ownership after internal negative cancellation.  The spare
+count remains explicit because zero-drift spare successors are not indexed by
+the existing positive-only global selected carrier. -/
+theorem CanonicalOpenPositiveQueueExcursion.queue_le_globalSelected_add_internalSpare_rigid_terminal
+    {n : OddNat} {q m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (canonicalOutstandingClaimQueue n m : ℤ) ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (canonicalInternalSaturatedSpareIndices n q m).card +
+          canonicalInternalRigidSaturatedResidualCount n q m +
+            canonicalTerminalSaturatedIndicator n m := by
+  have hmass := h.queue_eq_positiveMass_sub_negativeMass
+  have hcarrierNat :=
+    sum_intToNat_positiveDrift_le_globalCarrier_add_saturatedCard n q m
+  have hpositiveCast : canonicalPositiveDriftMass n q m =
+      ((∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) := by
+    rw [canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices]
+    push_cast
+    apply Finset.sum_congr rfl
+    intro k hk
+    have hpos := (Finset.mem_filter.mp hk).2
+    rw [Int.toNat_of_nonneg hpos.le]
+  have hcarrier : canonicalPositiveDriftMass n q m ≤
+      (Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) : ℤ) +
+        (canonicalSaturatedBlockIndices n q m).card := by
+    rw [hpositiveCast]
+    exact_mod_cast hcarrierNat
+  have hsplit :=
+    canonicalSaturatedTokenCount_eq_internalClassCounts_add_terminal
+      n q m h.1
+  have hnegative :=
+    card_canonicalInternalSaturatedNegativeIndices_le_negativeMass n q m
+  unfold canonicalSaturatedTokenCount at hsplit
+  omega
+
+/-!
+The stronger cp-346 target without `internalSpareCount` cannot be obtained by
+the requested contribution-preserving embedding into
+`CanonicalGlobalSelectedPressureCarrier n q m` from the current APIs.
+
+That global carrier is sigma-indexed only by `canonicalPositiveDriftBlockIndices`.
+But `CanonicalSaturatedBorderBlock.successor_source_classification` explicitly
+permits a successor with zero drift and a nonempty selected carrier, and
+`successorSpareAvailable_of_zero_of_selectedPressureCarrier_nonempty` places
+exactly that branch in `CanonicalSuccessorSpareAvailable`.  Such an incidence
+has no positive-block index with which to inhabit the requested codomain.
+
+Therefore removing `internalSpareCount` requires one of two new contracts:
+
+* enlarge the global selected carrier to include zero-drift blocks; or
+* prove that zero-drift spare successors cannot occur in the intended open
+  excursions.
+
+Neither contract is currently available.  Treating zero-spare as if it were
+in the positive-only carrier would be a type-invalid ownership claim, so this
+module stops at the theorem above.
+-/
+
+end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-346.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-346.md
new file mode 100644
index 00000000..b9caeb7a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-346.md
@@ -0,0 +1,116 @@
+# Petal / FloatWindow implementation report: checkpoint 346
+
+## Status
+
+The temporal split and internal negative-payment stages are proved without
+`sorry`.  The requested final ownership theorem exposed a type-level mismatch
+in Stage C, so the strongest contribution-preserving theorem justified by the
+current carrier API was proved instead.
+
+## Exact temporal split
+
+The new module `CanonicalExcursionOwnership.lean` defines internal saturated
+indices by erasing the right endpoint `m`.  Since every remaining index is
+strictly below `m`, its successor lies inside the current window.
+
+Lean proves exactly:
+
+```text
+saturatedTokenCount
+  = internalNegativeCount
+  + internalSpareCount
+  + internalRigidCount
+  + terminalSaturatedIndicator.
+```
+
+Here `internalRigidCount` remains the explicit sum of zero-rigid and
+tight-positive-rigid classes.  The terminal indicator is either zero or one,
+and Lean proves it is at most one.
+
+## Internal negative payment
+
+Each internal negative token at `k` is mapped to one negative-mass unit at
+`k+1`.  The proof establishes:
+
+- `k < m`, hence `k+1 <= m`;
+- `q <= k`, hence `q <= k+1`;
+- a negative integer drift contributes at least one unit of negative mass;
+- `k -> k+1` is injective.
+
+Therefore:
+
+```text
+internalNegativeCount <= canonicalNegativeDriftMass n q m.
+```
+
+No resource from block `m+1` is used.
+
+## Ownership theorem obtained
+
+Combining signed-mass equality, the existing selected-carrier bound, internal
+negative payment, and the exact temporal split gives:
+
+```text
+queue at m
+  <= Nat.card (CanonicalGlobalSelectedPressureCarrier n q m)
+     + internalSpareCount
+     + internalRigidResidualCount
+     + terminalSaturatedIndicator.
+```
+
+This is a strictly current-window theorem.  It removes the internal negative
+class completely and reduces the temporal boundary to one bit.
+
+## Stage C correction
+
+The instructed embedding of every internal spare token into
+`CanonicalGlobalSelectedPressureCarrier n q m` is not well typed from the
+current hypotheses.
+
+The existing global carrier is indexed only by positive-drift blocks.  The
+existing saturated-successor classification explicitly permits:
+
+```text
+successor drift = 0
+and
+selected pressure carrier is nonempty.
+```
+
+That branch is classified as `CanonicalSuccessorSpareAvailable`, but its block
+is absent from `canonicalPositiveDriftBlockIndices`, so its incidence cannot
+retain its block coordinate in the requested positive-only sigma carrier.
+
+Removing `internalSpareCount` now requires one additional contract:
+
+1. enlarge the global selected carrier to include zero-drift selected blocks;
+   or
+2. prove zero-drift spare successors impossible in open positive excursions.
+
+Neither statement currently exists.  The source comment records this exact
+boundary.  No arbitrary cross-block cardinal allocation was substituted for
+the requested contribution-preserving map.
+
+## Facts now fixed
+
+1. All nonterminal saturated tokens have successors inside the observed
+   window.
+2. Internal negative successors pay distinct predecessor units from current
+   negative mass.
+3. The only temporal residual is the possible saturated token at `m`, bounded
+   by one.
+4. The remaining ownership gap is not negative payment or temporal reuse.  It
+   is specifically ownership of zero-drift spare selected incidences.
+
+## Verification
+
+The following gates pass:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+The checkpoint does not modify the Python audit.
````
`````

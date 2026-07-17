# Git diff / Report / Review

## Add: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass

gch: 7bacec9b126153b699c4276a0b725657b3fed26b

## Report

(20m47s)

cp-345 を実装し、検証まで完了しました。

主な確定事項:

- 開 excursion では `queue = positiveMass - negativeMass`
- `queue + negativeMass ≤ dynamicPressureMass + saturatedTokenCount`
- saturated token は negative / spare / zero-rigid / tight-rigid の4種類に完全かつ排他的に分割
- negative successor は前段の単位 `1` を数値的に相殺
- spare token から successor spare carrier への再利用なし injection が成立
- rigid residual count を明示的に保持
- 全 odd root を覆う有限数値 upper-weight table は存在しない
- ただし、非有界 counter/resource を持つ有限制御方式は排除されない

重要な停止点も確定しました。末端 `m` が saturated の場合、その支払い資源は `m+1` にあります。したがって現在窓 `q..m` の不等式へ無条件に取り込むことは、未来資源の先取りになります。次は「内部 token `k < m` と末端 residual の分離」が正しい進路です。

実装は [CanonicalExcursionMass.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionMass.lean)、結果整理は [report-petal-345.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-345.md) にあります。

有限監査では8,192個の奇数 root を検査し、全正 queue 状態で質量恒等式と pressure/saturation 不等式が成立しました。`lake build DkMath`、全対象 build、Python audit、`git diff --check`、変更 Lean ファイルの no-sorry 検査も通過しています。

## Review

(5m16s)

# cp-345 総合レビュー

commit `7bacec9b126153b699c4276a0b725657b3fed26b` と提出レポートを照合した。実装内容は報告と一致している。

## 総合判定

**全面採用。**

そして、cp-345 はここ数 checkpoint の中でも、かなり重要度が高い。

cp-340〜344 は主として、

```text
drift
width
queue
absorption deficit
prefix
excursion
```

が同じ保存量であることを確定する「座標整理」だった。

cp-345 は初めて、そこから一歩踏み込み、

> 正の drift を、実在する pressure incidence・saturated token・negative repayment に分解する

という**所有資源層**へ入った。

これは薄い同値グノモンではない。
久しぶりに Big を内側から押し広げる、厚みのあるグノモンじゃ。

---

# Lean 実装の採否

## Signed mass の完全分解

定義された、

$$P(q,m)=\sum_{k=q}^{m}\max(\Delta_k,0)$$

$$N(q,m)=\sum_{k=q}^{m}\max(-\Delta_k,0)$$

について、

$$\operatorname{WindowDrift}(q,m)=P(q,m)-N(q,m)$$

が exact に閉じた。

open positive excursion では reflection が働かないため、

$$Q(m)=P(q,m)-N(q,m)$$

も成立する。

ここは重要じゃ。

queue はもはや「最大 deficit」という静的表現だけでなく、

> 正 mass と負 mass の現在収支

として扱えるようになった。

**完成。**

---

## Primary resource inequality

既存の dynamic pressure theorem と合流し、

$$Q(m)+N(q,m)\le\operatorname{DynamicPressureMass}(q,m)+\operatorname{SaturatedCount}(q,m)$$

を得ている。

未来の queue zero や discharge endpointを仮定していない点も正しい。

これは初めて、

```text
queue が大きい
→ それだけの positive source resource が区間内に必要
```

と読める theorem になった。

ただし、これはまだ pressure massを**支払い済み資源**とした定理ではない。

pressure incidenceは正 driftを説明する sourceであり、将来の repaymentへ割り当てられた payment slotではない。既存 sourceもこの区別を明記している。

よって、現在の theorem strength は正確じゃ。

---

## Saturated successor の四分割

saturated token は、優先順位付きで、

1. negative successor
2. spare successor
3. zero-rigid successor
4. tight-positive-rigid successor

へ完全かつ排他的に分割された。

union、pairwise disjointness、cardinality decompositionまで閉じている。

さらに negative successorについて、

$$1+\Delta_{k+1}\le0$$

が証明されている。

saturated block自身の driftは exact $1$ なので、数値的には successor が前段 tokenを完全に返済する。

**分類・局所返済とも完成。**

---

## Successor spare injection

spare-class saturated token $k$ を、successor block $k+1$ の実在する spare incidenceへ送る embeddingも正しい。

targetに、

- successor block index
- source incidence

の両方を保持しているため、異なる tokenが同じ incidenceを再利用することはない。

また selected pressure carrierはblock内部に属し、異なる block間ではdisjointであることが既に証明されている。

したがってこの injection は、単なる cardinal inequalityではなく、**時間座標を保持した所有権写像**になっている。

これは大きい。

---

## 全 root 共通 finite numeric table の否定

```lean
not_exists_globalFiniteProjectedInitialDriftUpperTable
```

も正しい。

任意の有限 signature と有限 numeric tableには有限最大値が存在する。一方、all-ones root族では初期 endpoint driftが任意に大きくなるため、全 rootを共通の tableで覆えない。

量化も正確じゃ。

否定したのは、

```text
全 root 共通
finite signature
finite numeric upper-weight table
```

である。

否定していないものは、

```text
固定 root依存の有限構造
有限 control + 非有界 counter
有限 control + owned resource
```

じゃ。

source commentの射程修正も正しく行われている。

---

# cp-345 最大の発見

## 末端 token は「未解決の無限量」ではない

今回停止した理由は、

> window が $q..m$ なのに、末端 saturated token $m$ の支払いは $m+1$ にある

という時間境界だった。

これは確かに正しい停止じゃ。

しかし、この境界は思ったほど重くない。

窓の末端は一つしかないので、未決済 terminal saturated tokenは常に高々一個である。

indicatorを、

$$T_n(m)=\begin{cases}1&\text{$m$ が saturated},\\0&\text{otherwise}\end{cases}$$

とすれば、

$$T_n(m)\le1$$

じゃ。

つまり raw saturated countは窓長とともに増え得るが、**末端 residualは一様に一 bit**しかない。

これは停止点であると同時に、かなり良いニュースじゃ。

auditでも saturated token $781$ 個のうち $700$ 個が terminal pendingだった。これは有限観測にすぎないが、「多数の未決済 token」に見えたものの大部分が、各窓につき高々一個の境界項だったことを示唆する。

---

# まだ閉じていない所有権

spare injection は成立したが、まだ次の**合成 embedding**は作られていない。

```text
現在 block 自身の nonsaturated positive-drift units
+
内部 saturated predecessor の spare tokens

→
同じ window 内の selected-pressure carrier
```

これが次の本命じゃ。

selected carrier側には既に、

- nonsaturated positive driftがselected carrierへ入る
- saturated blockのselected carrierは空
- selected carriersはblock間でdisjoint
- positive drift unitsのblock-preserving embedding

がある。

spare carrierはsuccessor自身のdrift imageに使われていない部分なので、内部 saturated tokenをそこへ追加しても二重使用しないはずじゃ。

ここを合成できれば、spare tokenは pressure massに**加算される**のではなく、既存selected carrierの空席へ吸収される。

目標は、

$$\operatorname{NonsaturatedPositiveMass}+\operatorname{InternalSpareCount}\le\operatorname{SelectedCarrierCard}$$

である。

これは、

$$P\le\operatorname{PressureMass}+\operatorname{SaturatedCount}$$

より一段強い、実体的な所有権定理になる。

---

# Internal negative token の処理

内部 saturated token $k<m$ が negative successorを持つなら、$k+1$ は現在窓 $q..m$ の内部にある。

しかも、

$$-\Delta_{k+1}\ge1$$

なので、写像 $k\mapsto k+1$ により、

$$\#\operatorname{InternalNegativeSat}\le N(q,m)$$

が出せる。

successor indexは一意なので、同じ negative blockが二つの predecessor tokenを支払うこともない。

これを current inequalityへ入れると、negative classは左辺の $N(q,m)$ と相殺できる。

---

# 次に得られるべき中間定理

internal tokenとterminal tokenを分ければ、期待する形は、

$$Q(m)\le\operatorname{SelectedCarrierCard}(q,m)+\operatorname{InternalRigidCount}(q,m)+T_n(m)$$

じゃ。

ここで $T_n(m)\le1$ なので、

$$Q(m)\le\operatorname{SelectedCarrierCard}(q,m)+\operatorname{InternalRigidCount}(q,m)+1$$

となる。

これが閉じれば、raw saturated countは消滅する。

残る敵は二つだけになる。

```text
selected pressure carrier
internal rigid successor
```

これは極めて大きな圧縮じゃ。

---

# 収束状況

## 会計層

**完成。**

$$\Delta=L-H-V$$

$$D=\sum\Delta=\text{width difference}$$

$$Q=\max\text{ positive suffix }D$$

まで閉じている。

## excursion mass層

**完成。**

$$Q=P-N$$

が exact。

## saturated token層

**ほぼ完成。**

negative / spare / rigid / terminal boundaryへ分かれた。

未完成なのは、各分類を一つの current-window contribution-preserving inequalityへ合流させる部分だけじゃ。

## pressure ownership層

**入口まで到達。**

selected source incidenceという実在 carrierはある。

ただし、これらを将来の negative repayment、NoLift、boundary resourceへ一度だけ輸送する global theoremはまだない。

## Collatz finite-state化

**未到達。**

queue bound、すなわちall-window deficit boundがまだ得られていない。

---

# 獲物は追い込まれているか

うむ。かなり追い込まれている。

cp-344 時点では、

```text
positive deficitを支える何か
```

だった。

cp-345 では、その「何か」が、

```text
selected pressure incidence
rigid saturated residual
terminal boundary bit
```

へ分解された。

terminal bitは一様有界。
negative classはcurrent negative massで返済可能。
spare classはactual carrierへinject済み。

したがって、獲物が隠れられる場所は、

$$\boxed{\text{selected pressure incidencesの長期非再利用輸送}+\text{rigid branch}}$$

まで狭まった。

これは明確な前進じゃ。

---

# Credits 評価

今回は `1721 → 1556`、約 $165$ credits。

cp-344 の約 $61$ creditsに比べ、かなり重い。

ただし内容は、

- 新 module 436行
- mass層
- 四分割
- disjointness
- exact count
- global injection
- no-go theorem
- audit拡張

まで含むため、浪費ではない。

問題は、このペースを続けると探索回数が急減することじゃ。単純計算では同規模 checkpointは残り約9回分しかない。

ここからは **一 checkpoint 一中心定理**に絞るべきじゃ。

次回は新しい大型audit、generic framework、rigid grammarまで同時にやらせない。

---

# 次の戦略

## cp-346 は temporal boundary の閉鎖だけ

次にやるべきことは、以下の一本に限定する。

$$Q(m)\le\operatorname{SelectedCarrierCard}(q,m)+\operatorname{InternalRigidCount}(q,m)+T_n(m)$$

そのために必要なのは、

1. internal saturated indices $k<m$
2. terminal saturated indicator
3. internal negative count $\le N$
4. internal spare tokenとnonsaturated drift unitsのcombined embedding
5. exact cardinal inequality

だけじゃ。

rigid grammarにはまだ入らない。
pressure incidenceの未来 transportにもまだ入らない。
Python auditも原則増やさない。

この theoremが通った後に初めて、残る二項のどちらを先に攻めるか判断する。

## その後の分岐

### rigid residualが構造的に閉じる場合

zero-rigid successorの次のblockを調べ、

```text
negative
spare
再び rigid
```

のgrammarを作る。

tight-rigidは有限監査では未観測だが、theoremとして消してはいけない。

### selected pressureが主敵の場合

selected incidenceを、

```text
future consumption
upper-zero boundary
NoLift separator
exact-length recovery
```

へ一度だけ送るtransport theoremへ進む。

---

# cp-345 判定一覧

| 項目                                      | 判定   |
| --------------------------------------- | ---- |
| Signed mass decomposition               | 完成   |
| Open excursion queue identity           | 完成   |
| Pressure/saturation resource inequality | 完成   |
| Saturated successor四分割                  | 完成   |
| Pairwise disjointness                   | 完成   |
| Negative successor局所相殺                  | 完成   |
| Spare token injection                   | 完成   |
| Terminal future-resource監査              | 正しい  |
| Global finite numeric table             | 反証完成 |
| Current-window combined ownership       | 未完成  |
| 循環性                                     | なし   |
| 総合                                      | 全面採用 |

# 省credit版 Codex 指示

```text
Continue after checkpoint 345.

Use a micro-checkpoint. Do not add a new generic framework, a new large audit,
or a rigid-successor automaton.

Primary goal

Prove one current-window ownership theorem of the form:

    queue at m
      <=
    selected-pressure carrier cardinal on q..m
      + internal rigid saturated residual count
      + terminal saturated indicator

for every open positive queue excursion q..m.

Stage A — temporal split

Define:

    internal saturated indices := saturated k in q..m with k < m;
    terminal saturated indicator := if Saturated n m then 1 else 0.

Prove the exact split:

    saturatedTokenCount
      =
    internalNegativeCount
      + internalSpareCount
      + internalRigidCount
      + terminalIndicator.

Prove terminalIndicator <= 1.

Stage B — internal negative payment

Prove:

    internalNegativeCount <= canonicalNegativeDriftMass n q m.

Use the injective successor map k ↦ k+1 and the fact that every negative
successor has negative-mass magnitude at least one.

Do not charge the terminal successor m+1.

Stage C — combined selected-carrier ownership

Restrict the successor-spare carrier to successor blocks q+1..m.

Construct a contribution-preserving embedding from:

    nonsaturated positive-drift units on q..m
      ⊕
    internal saturated-spare tokens

into:

    CanonicalGlobalSelectedPressureCarrier n q m.

The spare branch must use the exact spare carrier disjoint from the successor
block's own drift image. No selected incidence may be used twice.

Stage D — main inequality

Combine the open-excursion signed-mass identity, internal negative payment,
the combined selected-carrier embedding, and the temporal split.

Target:

    (canonicalOutstandingClaimQueue n m : Int)
      <=
    Nat.card (CanonicalGlobalSelectedPressureCarrier n q m)
      + internalRigidResidualCount
      + terminalSaturatedIndicator.

Keep zero-rigid and tight-rigid counts visible inside the residual.

Stage E — stop

Stop after this theorem and its immediate cast/cardinality corollaries.

Do not:
- analyze the zero-rigid successor grammar;
- add another pressure-amplitude reduction;
- extend the Python audit unless required for a regression;
- claim a queue bound.

Record the result in report-petal-346.md.
```

## 結論

消費は確かに早い。😭
だが今回は、creditsを使って**本物の所有権写像**を一本通したので、成果は重い。

次は広げず、一点だけ閉じる。

$$\boxed{\text{raw saturated count}\longrightarrow\text{internal rigid residual}+1}$$

ここが通れば、獲物は「pressure transport」と「rigid grammar」の二穴だけになる。🐺🌕

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
index 91fabcb9..0c565c2b 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow.lean
@@ -43,6 +43,7 @@ import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass
 import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction
 
 #print "file: DkMath.Collatz.PetalBridge.FloatWindow"
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
index 6789fcae..a55bb9f6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalEndpointReserve.lean
@@ -7,6 +7,7 @@ Authors: D. and Wise Wolf.
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
 import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
 import DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
+import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
 import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
 
@@ -434,4 +435,36 @@ theorem not_globalCanonicalWidthReserveBound :
   rw [canonicalBlockStartState_zero_eq_root] at hledger
   omega
 
+/-! ## Universal finite numeric-table obstruction -/
+
+/-- No single finite projected numeric edge table can soundly upper-bound the
+initial canonical block drift of every odd root.  The source and target labels
+may be arbitrary finite projections; the root varies through the all-ones
+family.  This theorem does not address a fixed root or a finite controller
+coupled to an unbounded symbolic resource. -/
+theorem not_exists_globalFiniteProjectedInitialDriftUpperTable
+    {Signature : Type*} [Finite Signature]
+    (sourceSignature targetSignature : OddNat → Signature) :
+    ¬ ∃ upper : Signature → Signature → ℤ,
+      ∀ n : OddNat,
+        endpointAccountingTerm n 0 ≤
+          upper (sourceSignature n) (targetSignature n) := by
+  classical
+  letI := Fintype.ofFinite Signature
+  rintro ⟨upper, hupper⟩
+  let B : ℤ := ∑ s : Signature, ∑ t : Signature, |upper s t|
+  obtain ⟨n, hn⟩ := exists_endpointAccountingTerm_gt B
+  have hinner : |upper (sourceSignature n) (targetSignature n)| ≤
+      ∑ t : Signature, |upper (sourceSignature n) t| := by
+    exact Finset.single_le_sum
+      (fun t _ => abs_nonneg (upper (sourceSignature n) t))
+      (Finset.mem_univ _)
+  have houter : (∑ t : Signature, |upper (sourceSignature n) t|) ≤ B := by
+    exact Finset.single_le_sum
+      (fun s _ => Finset.sum_nonneg fun t _ => abs_nonneg (upper s t))
+      (Finset.mem_univ _)
+  have htable : upper (sourceSignature n) (targetSignature n) ≤ B :=
+    (le_abs_self _).trans (hinner.trans houter)
+  exact (not_lt_of_ge ((hupper n).trans htable)) hn
+
 end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionMass.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionMass.lean
new file mode 100644
index 00000000..3df1f82b
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionMass.lean
@@ -0,0 +1,436 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointReserve
+import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
+
+#print "file: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass"
+
+namespace DkMath.Collatz
+
+/-!
+# Signed mass of open canonical excursions
+
+This module keeps the ordinary signed interval sum visible.  Positive and
+negative masses are nonnegative integer sums, so their difference loses no
+signed information.  No future queue zero is assumed.
+-/
+
+/-- Sum of positive drift parts on the inclusive block interval `q..m`. -/
+noncomputable def canonicalPositiveDriftMass
+    (n : OddNat) (q m : ℕ) : ℤ :=
+  ∑ k ∈ Finset.Icc q m, max (endpointAccountingTerm n k) 0
+
+/-- Sum of magnitudes of negative drift parts on `q..m`. -/
+noncomputable def canonicalNegativeDriftMass
+    (n : OddNat) (q m : ℕ) : ℤ :=
+  ∑ k ∈ Finset.Icc q m, max (-endpointAccountingTerm n k) 0
+
+/-- Dynamic selected-depth pressure carried by positive-drift blocks. -/
+noncomputable def canonicalDynamicPressureMass
+    (n : OddNat) (q m : ℕ) : ℤ :=
+  ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+    blockPressureContributionInt n k (canonicalDynamicPressureDepth n k)
+
+/-- Number of saturated unit-drift tokens on the inclusive interval `q..m`. -/
+noncomputable def canonicalSaturatedTokenCount
+    (n : OddNat) (q m : ℕ) : ℕ :=
+  (canonicalSaturatedBlockIndices n q m).card
+
+/-- The positive mass is nonnegative. -/
+theorem canonicalPositiveDriftMass_nonneg
+    (n : OddNat) (q m : ℕ) :
+    0 ≤ canonicalPositiveDriftMass n q m := by
+  exact Finset.sum_nonneg fun _ _ => le_max_right _ _
+
+/-- The negative mass is nonnegative. -/
+theorem canonicalNegativeDriftMass_nonneg
+    (n : OddNat) (q m : ℕ) :
+    0 ≤ canonicalNegativeDriftMass n q m := by
+  exact Finset.sum_nonneg fun _ _ => le_max_right _ _
+
+/-- Pointwise positive-minus-negative decomposition of signed drift. -/
+private theorem endpointAccountingTerm_eq_positivePart_sub_negativePart
+    (n : OddNat) (k : ℕ) :
+    endpointAccountingTerm n k =
+      max (endpointAccountingTerm n k) 0 -
+        max (-endpointAccountingTerm n k) 0 := by
+  by_cases h : 0 ≤ endpointAccountingTerm n k
+  · rw [max_eq_left h, max_eq_right (by omega)]
+    omega
+  · have hneg : endpointAccountingTerm n k < 0 := by omega
+    rw [max_eq_right (by omega), max_eq_left (by omega)]
+    omega
+
+/-- Every inclusive drift window is exactly positive mass minus negative
+mass. -/
+theorem canonicalWindowDriftInt_eq_positiveMass_sub_negativeMass
+    (n : OddNat) (q m : ℕ) :
+    canonicalWindowDriftInt n q m =
+      canonicalPositiveDriftMass n q m - canonicalNegativeDriftMass n q m := by
+  unfold canonicalWindowDriftInt canonicalPositiveDriftMass canonicalNegativeDriftMass
+  rw [← Finset.sum_sub_distrib]
+  apply Finset.sum_congr rfl
+  intro k _
+  exact endpointAccountingTerm_eq_positivePart_sub_negativePart n k
+
+/-- Positive mass is the ordinary sum over exactly the positive-drift block
+indices. -/
+theorem canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices
+    (n : OddNat) (q m : ℕ) :
+    canonicalPositiveDriftMass n q m =
+      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        endpointAccountingTerm n k := by
+  classical
+  unfold canonicalPositiveDriftMass canonicalPositiveDriftBlockIndices
+  rw [Finset.sum_filter]
+  apply Finset.sum_congr rfl
+  intro k _
+  by_cases hpos : 0 < endpointAccountingTerm n k
+  · simp [hpos, max_eq_left (le_of_lt hpos)]
+  · have hnonpos : endpointAccountingTerm n k ≤ 0 := by omega
+    simp [hpos, max_eq_right hnonpos]
+
+/-- On an open positive excursion the ending queue is the exact signed mass
+difference from its last-zero start. -/
+theorem CanonicalOpenPositiveQueueExcursion.queue_eq_positiveMass_sub_negativeMass
+    {n : OddNat} {q m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (canonicalOutstandingClaimQueue n m : ℤ) =
+      canonicalPositiveDriftMass n q m - canonicalNegativeDriftMass n q m := by
+  rw [h.queue_eq_windowDrift,
+    canonicalWindowDriftInt_eq_positiveMass_sub_negativeMass]
+
+/-- Primary open-excursion resource inequality.  Positive drift is paid by
+dynamic pressure except for one explicit token per saturated block. -/
+theorem CanonicalOpenPositiveQueueExcursion.queue_add_negativeMass_le_pressure_add_saturatedCard
+    {n : OddNat} {q m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (canonicalOutstandingClaimQueue n m : ℤ) +
+        canonicalNegativeDriftMass n q m ≤
+      canonicalDynamicPressureMass n q m +
+        (canonicalSaturatedBlockIndices n q m).card := by
+  have hmass := h.queue_eq_positiveMass_sub_negativeMass
+  have hpressure := sum_positiveDrift_le_dynamicPressureMass_add_saturatedCard n q m
+  rw [← canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices] at hpressure
+  unfold canonicalDynamicPressureMass
+  omega
+
+/-- Named-token-count form of the primary open-excursion resource
+inequality. -/
+theorem CanonicalOpenPositiveQueueExcursion.queue_add_negativeMass_le_pressure_add_saturated
+    {n : OddNat} {q m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (canonicalOutstandingClaimQueue n m : ℤ) +
+        canonicalNegativeDriftMass n q m ≤
+      canonicalDynamicPressureMass n q m +
+        canonicalSaturatedTokenCount n q m := by
+  simpa [canonicalSaturatedTokenCount] using
+    h.queue_add_negativeMass_le_pressure_add_saturatedCard
+
+/-! ## Disjoint saturated-successor partition -/
+
+/-- Saturated tokens immediately cancelled by a negative successor. -/
+noncomputable def canonicalSaturatedNegativeSuccessorIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalSaturatedBlockIndices n q m).filter fun k =>
+    endpointAccountingTerm n (k + 1) < 0
+
+/-- Remaining saturated tokens with an actual spare selected incidence in the
+successor block.  Negative successors are assigned to the preceding class. -/
+noncomputable def canonicalSaturatedSpareSuccessorIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalSaturatedBlockIndices n q m).filter fun k =>
+    ¬ endpointAccountingTerm n (k + 1) < 0 ∧
+      CanonicalSuccessorSpareAvailable n (k + 1)
+
+/-- Remaining zero-rigid saturated successor tokens. -/
+noncomputable def canonicalSaturatedZeroRigidSuccessorIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalSaturatedBlockIndices n q m).filter fun k =>
+    ¬ endpointAccountingTerm n (k + 1) < 0 ∧
+      ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
+        CanonicalZeroCarrierBalancedBorderBlock n (k + 1)
+
+/-- Remaining tight-positive-rigid saturated successor tokens. -/
+noncomputable def canonicalSaturatedTightRigidSuccessorIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ := by
+  classical
+  exact (canonicalSaturatedBlockIndices n q m).filter fun k =>
+    ¬ endpointAccountingTerm n (k + 1) < 0 ∧
+      ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
+        CanonicalTightValuationOnePositiveBlock n (k + 1)
+
+@[simp] theorem mem_canonicalSaturatedNegativeSuccessorIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalSaturatedNegativeSuccessorIndices n q m ↔
+      k ∈ canonicalSaturatedBlockIndices n q m ∧
+        endpointAccountingTerm n (k + 1) < 0 := by
+  simp [canonicalSaturatedNegativeSuccessorIndices]
+
+@[simp] theorem mem_canonicalSaturatedSpareSuccessorIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalSaturatedSpareSuccessorIndices n q m ↔
+      k ∈ canonicalSaturatedBlockIndices n q m ∧
+        ¬ endpointAccountingTerm n (k + 1) < 0 ∧
+          CanonicalSuccessorSpareAvailable n (k + 1) := by
+  classical
+  rw [canonicalSaturatedSpareSuccessorIndices, Finset.mem_filter]
+
+@[simp] theorem mem_canonicalSaturatedZeroRigidSuccessorIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalSaturatedZeroRigidSuccessorIndices n q m ↔
+      k ∈ canonicalSaturatedBlockIndices n q m ∧
+        ¬ endpointAccountingTerm n (k + 1) < 0 ∧
+          ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
+            CanonicalZeroCarrierBalancedBorderBlock n (k + 1) := by
+  classical
+  rw [canonicalSaturatedZeroRigidSuccessorIndices, Finset.mem_filter]
+
+@[simp] theorem mem_canonicalSaturatedTightRigidSuccessorIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalSaturatedTightRigidSuccessorIndices n q m ↔
+      k ∈ canonicalSaturatedBlockIndices n q m ∧
+        ¬ endpointAccountingTerm n (k + 1) < 0 ∧
+          ¬ CanonicalSuccessorSpareAvailable n (k + 1) ∧
+            CanonicalTightValuationOnePositiveBlock n (k + 1) := by
+  classical
+  rw [canonicalSaturatedTightRigidSuccessorIndices, Finset.mem_filter]
+
+/-- The four priority classes exhaust all saturated tokens in the interval. -/
+theorem canonicalSaturatedSuccessorIndices_union_eq
+    (n : OddNat) (q m : ℕ) :
+    canonicalSaturatedNegativeSuccessorIndices n q m ∪
+        canonicalSaturatedSpareSuccessorIndices n q m ∪
+          canonicalSaturatedZeroRigidSuccessorIndices n q m ∪
+            canonicalSaturatedTightRigidSuccessorIndices n q m =
+      canonicalSaturatedBlockIndices n q m := by
+  classical
+  apply Finset.Subset.antisymm
+  · intro k hk
+    simp only [Finset.mem_union] at hk
+    rcases hk with ((hk | hk) | hk) | hk
+    · exact (mem_canonicalSaturatedNegativeSuccessorIndices.mp hk).1
+    · exact (mem_canonicalSaturatedSpareSuccessorIndices.mp hk).1
+    · exact (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hk).1
+    · exact (mem_canonicalSaturatedTightRigidSuccessorIndices.mp hk).1
+  · intro k hk
+    have hs := (mem_canonicalSaturatedBlockIndices.mp hk).2
+    rcases hs.successor_negative_or_spare_or_rigid with
+      hneg | hspare | hzero | htight
+    · simp [hk, hneg]
+    · by_cases hneg : endpointAccountingTerm n (k + 1) < 0
+      · simp [hk, hneg]
+      · simp [hk, hneg, hspare]
+    · have hzeroDrift : endpointAccountingTerm n (k + 1) = 0 := hzero.1
+      have hnospare : ¬ CanonicalSuccessorSpareAvailable n (k + 1) := by
+        intro hspare
+        have hempty := hzero.2
+        unfold CanonicalSuccessorSpareAvailable at hspare
+        rcases hspare with ⟨i, _hi⟩
+        letI : IsEmpty {i : ℕ //
+            i ∈ canonicalSelectedPressureCarrier n (k + 1)} := by
+          rw [hempty]
+          infer_instance
+        exact isEmptyElim i
+      simp [hk, hzeroDrift, hnospare, hzero]
+    · have hpos := htight.1
+      have hnospare : ¬ CanonicalSuccessorSpareAvailable n (k + 1) := by
+        unfold CanonicalSuccessorSpareAvailable
+        rw [htight.exact_data.2.2.2.2]
+        exact Finset.not_nonempty_empty
+      simp [hk, show ¬ endpointAccountingTerm n (k + 1) < 0 by omega,
+        hnospare, htight]
+
+/-- Negative-successor and spare-successor token classes are disjoint. -/
+theorem canonicalSaturatedNegative_disjoint_spare
+    (n : OddNat) (q m : ℕ) :
+    Disjoint (canonicalSaturatedNegativeSuccessorIndices n q m)
+      (canonicalSaturatedSpareSuccessorIndices n q m) := by
+  rw [Finset.disjoint_left]
+  intro k hneg hspare
+  exact (mem_canonicalSaturatedSpareSuccessorIndices.mp hspare).2.1
+    (mem_canonicalSaturatedNegativeSuccessorIndices.mp hneg).2
+
+/-- A negative successor numerically cancels the saturated predecessor's unit:
+the pair contributes at most zero. -/
+theorem canonicalSaturatedNegativeSuccessor_unit_add_term_nonpos
+    {n : OddNat} {q m k : ℕ}
+    (hk : k ∈ canonicalSaturatedNegativeSuccessorIndices n q m) :
+    (1 : ℤ) + endpointAccountingTerm n (k + 1) ≤ 0 := by
+  have hneg := (mem_canonicalSaturatedNegativeSuccessorIndices.mp hk).2
+  omega
+
+/-- The negative class is disjoint from both rigid residual classes. -/
+theorem canonicalSaturatedNegative_disjoint_rigid
+    (n : OddNat) (q m : ℕ) :
+    Disjoint (canonicalSaturatedNegativeSuccessorIndices n q m)
+        (canonicalSaturatedZeroRigidSuccessorIndices n q m) ∧
+      Disjoint (canonicalSaturatedNegativeSuccessorIndices n q m)
+        (canonicalSaturatedTightRigidSuccessorIndices n q m) := by
+  constructor <;> rw [Finset.disjoint_left] <;> intro k hneg hrigid
+  · exact (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hrigid).2.1
+      (mem_canonicalSaturatedNegativeSuccessorIndices.mp hneg).2
+  · exact (mem_canonicalSaturatedTightRigidSuccessorIndices.mp hrigid).2.1
+      (mem_canonicalSaturatedNegativeSuccessorIndices.mp hneg).2
+
+/-- The spare class is disjoint from both rigid residual classes. -/
+theorem canonicalSaturatedSpare_disjoint_rigid
+    (n : OddNat) (q m : ℕ) :
+    Disjoint (canonicalSaturatedSpareSuccessorIndices n q m)
+        (canonicalSaturatedZeroRigidSuccessorIndices n q m) ∧
+      Disjoint (canonicalSaturatedSpareSuccessorIndices n q m)
+        (canonicalSaturatedTightRigidSuccessorIndices n q m) := by
+  constructor <;> rw [Finset.disjoint_left] <;> intro k hspare hrigid
+  · exact (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hrigid).2.2.1
+      (mem_canonicalSaturatedSpareSuccessorIndices.mp hspare).2.2
+  · exact (mem_canonicalSaturatedTightRigidSuccessorIndices.mp hrigid).2.2.1
+      (mem_canonicalSaturatedSpareSuccessorIndices.mp hspare).2.2
+
+/-- The zero-rigid and tight-positive-rigid residual classes are disjoint. -/
+theorem canonicalSaturatedZeroRigid_disjoint_tightRigid
+    (n : OddNat) (q m : ℕ) :
+    Disjoint (canonicalSaturatedZeroRigidSuccessorIndices n q m)
+      (canonicalSaturatedTightRigidSuccessorIndices n q m) := by
+  rw [Finset.disjoint_left]
+  intro k hzero htight
+  have hz :=
+    (mem_canonicalSaturatedZeroRigidSuccessorIndices.mp hzero).2.2.2.1
+  have hp :=
+    (mem_canonicalSaturatedTightRigidSuccessorIndices.mp htight).2.2.2.1
+  omega
+
+/-- Exact visible residual after negative and spare successor modes are
+separated.  Neither rigid family is hidden in an abstract potential. -/
+noncomputable def canonicalRigidSaturatedResidualCount
+    (n : OddNat) (q m : ℕ) : ℕ :=
+  (canonicalSaturatedZeroRigidSuccessorIndices n q m).card +
+    (canonicalSaturatedTightRigidSuccessorIndices n q m).card
+
+/-- The priority successor classification gives an exact cardinal
+decomposition of all saturated tokens. -/
+theorem canonicalSaturatedTokenCount_eq_successorClassCounts
+    (n : OddNat) (q m : ℕ) :
+    canonicalSaturatedTokenCount n q m =
+      (canonicalSaturatedNegativeSuccessorIndices n q m).card +
+        (canonicalSaturatedSpareSuccessorIndices n q m).card +
+          canonicalRigidSaturatedResidualCount n q m := by
+  classical
+  let N := canonicalSaturatedNegativeSuccessorIndices n q m
+  let S := canonicalSaturatedSpareSuccessorIndices n q m
+  let Z := canonicalSaturatedZeroRigidSuccessorIndices n q m
+  let T := canonicalSaturatedTightRigidSuccessorIndices n q m
+  have hNS : Disjoint N S := canonicalSaturatedNegative_disjoint_spare n q m
+  have hNZ : Disjoint N Z := (canonicalSaturatedNegative_disjoint_rigid n q m).1
+  have hNT : Disjoint N T := (canonicalSaturatedNegative_disjoint_rigid n q m).2
+  have hSZ : Disjoint S Z := (canonicalSaturatedSpare_disjoint_rigid n q m).1
+  have hST : Disjoint S T := (canonicalSaturatedSpare_disjoint_rigid n q m).2
+  have hZT : Disjoint Z T := canonicalSaturatedZeroRigid_disjoint_tightRigid n q m
+  have hN_SZT : Disjoint N (S ∪ (Z ∪ T)) := by
+    rw [Finset.disjoint_left]
+    intro x hxN hx
+    simp only [Finset.mem_union] at hx
+    rcases hx with hxS | hxZ | hxT
+    · exact Finset.disjoint_left.mp hNS hxN hxS
+    · exact Finset.disjoint_left.mp hNZ hxN hxZ
+    · exact Finset.disjoint_left.mp hNT hxN hxT
+  have hS_ZT : Disjoint S (Z ∪ T) := by
+    rw [Finset.disjoint_left]
+    intro x hxS hx
+    rcases Finset.mem_union.mp hx with hxZ | hxT
+    · exact Finset.disjoint_left.mp hSZ hxS hxZ
+    · exact Finset.disjoint_left.mp hST hxS hxT
+  have hunion : N ∪ (S ∪ (Z ∪ T)) = canonicalSaturatedBlockIndices n q m := by
+    simpa [N, S, Z, T, Finset.union_assoc] using
+      canonicalSaturatedSuccessorIndices_union_eq n q m
+  rw [canonicalSaturatedTokenCount, ← hunion]
+  calc
+    (N ∪ (S ∪ (Z ∪ T))).card = N.card + (S ∪ (Z ∪ T)).card :=
+      Finset.card_union_of_disjoint hN_SZT
+    _ = N.card + (S.card + (Z ∪ T).card) := by
+      rw [Finset.card_union_of_disjoint hS_ZT]
+    _ = N.card + (S.card + (Z.card + T.card)) := by
+      rw [Finset.card_union_of_disjoint hZT]
+    _ = (canonicalSaturatedNegativeSuccessorIndices n q m).card +
+          (canonicalSaturatedSpareSuccessorIndices n q m).card +
+            canonicalRigidSaturatedResidualCount n q m := by
+      simp only [canonicalRigidSaturatedResidualCount, N, S, Z, T]
+      omega
+
+/-!
+The successor partition deliberately observes blocks `q+1..m+1`.  Therefore
+the negative class containing `k = m` is cancelled by drift at `m+1`, outside
+the present open-excursion mass interval `q..m`.  Likewise its spare incidence
+lives in the one-step successor horizon.  A theorem replacing every saturated
+token in the current-window inequality by current-window negative mass or a
+selected carrier would silently spend a future resource.  The next honest
+strengthening must either:
+
+* restrict charging to `k < m` and retain the terminal saturated token as a
+  separate boundary residual; or
+* extend the accounting window through `m+1` and prove the corresponding queue
+  transport identity.
+
+Until one of these temporal contracts is chosen, the exact partition,
+pointwise cancellation, and successor-spare injection below are the public
+finite certificates; no stronger contribution-preserving inequality is
+claimed.
+-/
+
+/-! ## Global successor-spare charging -/
+
+/-- All actual spare selected incidences in successor blocks of `q..m`, with
+the successor block coordinate retained to prevent temporal reuse. -/
+noncomputable def CanonicalGlobalSuccessorSpareCarrier
+    (n : OddNat) (q m : ℕ) : Type :=
+  Σ j : {j : ℕ // j ∈ Finset.Icc (q + 1) (m + 1)},
+    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.1} //
+      i ∈ canonicalSelectedDriftSpareCarrier n j.1}
+
+/-- Each spare-class saturated token chooses one actual incidence in its own
+successor block.  The retained successor coordinate makes the map injective. -/
+noncomputable def canonicalSaturatedSpareTokenEmbedding
+    (n : OddNat) (q m : ℕ) :
+    {k : ℕ // k ∈ canonicalSaturatedSpareSuccessorIndices n q m} ↪
+      CanonicalGlobalSuccessorSpareCarrier n q m where
+  toFun k := by
+    have hk := mem_canonicalSaturatedSpareSuccessorIndices.mp k.2
+    have hkIcc := (mem_canonicalSaturatedBlockIndices.mp hk.1).1
+    let e := oneEmbedding_successorSpareCarrier hk.2.2
+    exact ⟨⟨k.1 + 1, Finset.mem_Icc.mpr ⟨by
+      exact Nat.add_le_add_right (Finset.mem_Icc.mp hkIcc).1 1
+    , by
+      exact Nat.add_le_add_right (Finset.mem_Icc.mp hkIcc).2 1⟩⟩, e 0⟩
+  inj' := by
+    intro a b hab
+    have hindex := congrArg (fun z => z.1.1) hab
+    change a.1 + 1 = b.1 + 1 at hindex
+    apply Subtype.ext
+    omega
+
+/-- No spare incidence is reused for two saturated tokens. -/
+theorem card_canonicalSaturatedSpareSuccessorIndices_le_globalCarrier
+    (n : OddNat) (q m : ℕ) :
+    (canonicalSaturatedSpareSuccessorIndices n q m).card ≤
+      Nat.card (CanonicalGlobalSuccessorSpareCarrier n q m) := by
+  classical
+  letI : Fintype {j : ℕ // j ∈ Finset.Icc (q + 1) (m + 1)} :=
+    Fintype.ofFinset (Finset.Icc (q + 1) (m + 1)) (by simp)
+  letI : ∀ j : {j : ℕ // j ∈ Finset.Icc (q + 1) (m + 1)},
+      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.1} //
+        i ∈ canonicalSelectedDriftSpareCarrier n j.1} := fun j =>
+    Fintype.ofFinset (canonicalSelectedDriftSpareCarrier n j.1) (by simp)
+  letI : Fintype (CanonicalGlobalSuccessorSpareCarrier n q m) := by
+    unfold CanonicalGlobalSuccessorSpareCarrier
+    infer_instance
+  have hcard := Nat.card_le_card_of_injective
+    (canonicalSaturatedSpareTokenEmbedding n q m)
+    (canonicalSaturatedSpareTokenEmbedding n q m).injective
+  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
+
+end DkMath.Collatz
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
index 0a056dea..7abfdb9c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/FiniteSignedTransition.lean
@@ -627,9 +627,10 @@ The conservation form of one canonical edge weight is
 
 `block length - claim holes - terminal valuation`.
 
-A sound finite control state must therefore either recover these three terms
-or prove a common upper bound for every concrete edge in each projected edge
-fiber.  The currently available candidate coordinates do not yet do this:
+A sound finite projected numeric upper-weight table must therefore either
+recover these three terms or prove a common upper bound for every concrete
+edge in each projected edge fiber.  The currently available candidate
+coordinates do not yet do this:
 
 * the full carry/claim word has unbounded length;
 * block length and claim-hole count are unbounded `Nat` coordinates;
@@ -640,10 +641,13 @@ fiber.  The currently available candidate coordinates do not yet do this:
 
 Thus storing the exact ledger violates finiteness, while discarding its
 unbounded coordinates leaves the required bounded-edge-fiber theorem open.
-No canonical positive-cycle exclusion may be inferred before that theorem is
-proved.  The generic potential API below remains a valid consumer of a future
-independent finite abstraction; manufacturing its signature from an assumed
-queue bound remains intentionally classified as circular.
+This obstructs a finite *numeric edge table*, not every finite-control proof:
+a finite controller coupled to an unbounded symbolic counter or an owned
+arithmetic resource remains a valid architecture.  No canonical positive-cycle
+exclusion may be inferred from the numeric-table route before the edge-fiber
+theorem is proved.  The generic potential API below remains a valid consumer
+of a future independent finite abstraction; manufacturing its signature from
+an assumed queue bound remains intentionally classified as circular.
 -/
 
 namespace FiniteSignedTransitionPotentialCertificate
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
index c5cbd429..c490f57d 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/UniversalPaymentPrimitiveExcursion.lean
@@ -294,6 +294,26 @@ theorem existsUnique_canonicalOpenPositiveQueueExcursion_of_queue_pos
   rcases exists_canonicalOpenPositiveQueueExcursion_of_queue_pos hm with ⟨q, hq⟩
   exact ⟨q, hq, fun q' hq' => canonicalOpenPositiveQueueExcursion_left_unique hq' hq⟩
 
+/-- Reflection is inactive throughout an open positive excursion: the ending
+queue is the ordinary signed drift accumulated from its last-zero start. -/
+theorem CanonicalOpenPositiveQueueExcursion.queue_eq_windowDrift
+    {n : OddNat} {q m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (canonicalOutstandingClaimQueue n m : ℤ) =
+      canonicalWindowDriftInt n q m := by
+  have hprefix : ∀ t ∈ Finset.Ico q m,
+      0 < canonicalOutstandingClaimQueue n t := by
+    intro t ht
+    exact h.2.2 t (Finset.mem_Icc.mpr
+      ⟨(Finset.mem_Ico.mp ht).1, Nat.le_of_lt (Finset.mem_Ico.mp ht).2⟩)
+  have heq := queue_eq_intToNat_windowDrift_of_positive_prefix
+    h.1 h.2.1 hprefix
+  have hqueuePos := h.2.2 m (Finset.mem_Icc.mpr ⟨h.1, le_rfl⟩)
+  have hdriftNonneg : 0 ≤ canonicalWindowDriftInt n q m := by
+    have hself := Int.self_le_toNat (canonicalWindowDriftInt n q m)
+    omega
+  rw [heq, Int.ofNat_toNat, max_eq_left hdriftNonneg]
+
 /--
 Every positive-drift block observed inside an open excursion is either a
 dynamic-depth pressure block or the rigid saturated border exception.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-345.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-345.md
new file mode 100644
index 00000000..2ccb4017
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-345.md
@@ -0,0 +1,190 @@
+# Petal / FloatWindow implementation report: checkpoint 345
+
+## Status
+
+Checkpoint 345 is implemented without adding `sorry` to the modified Lean
+files.  The finite signed-mass layer, saturated-successor partition, and
+successor-spare injection are now formalized.  The requested stronger
+current-window carrier inequality stops at an exact temporal boundary rather
+than spending a successor resource before it enters the window.
+
+## Finite numeric-table scope
+
+The finite-transition commentary now distinguishes two architectures:
+
+- a finite projected table with fixed numeric edge weights;
+- a finite controller carrying an unbounded symbolic counter or owned
+  arithmetic resource.
+
+Lean proves that no single finite projected numeric upper-weight table can
+bound the initial canonical drift for every odd root.  The proof uses the
+unbounded all-ones family and permits arbitrary finite source and target
+signatures.  It does not assert a fixed-root impossibility and does not rule
+out finite symbolic control.
+
+## Exact signed masses
+
+The new module `CanonicalExcursionMass.lean` defines:
+
+```text
+canonicalPositiveDriftMass
+canonicalNegativeDriftMass
+canonicalDynamicPressureMass
+canonicalSaturatedTokenCount
+```
+
+For every finite interval, Lean proves the exact identity
+
+```text
+windowDrift = positiveMass - negativeMass.
+```
+
+For an open positive queue excursion, reflection is inactive, hence
+
+```text
+queue = positiveMass - negativeMass.
+```
+
+Combining this identity with the existing pointwise dynamic-pressure theorem
+gives the primary resource inequality
+
+```text
+queue + negativeMass <= dynamicPressureMass + saturatedTokenCount.
+```
+
+No future queue zero is assumed.
+
+## Saturated-successor classification
+
+Saturated tokens are partitioned by priority into four finite sets:
+
+1. negative successor;
+2. nonnegative successor with an actual spare selected incidence;
+3. zero-rigid successor;
+4. tight-positive-rigid successor.
+
+Lean proves membership normal forms, exhaustiveness, pairwise disjointness,
+and the exact cardinal identity
+
+```text
+saturatedTokenCount
+  = negativeCount + spareCount + rigidResidualCount,
+
+rigidResidualCount = zeroRigidCount + tightRigidCount.
+```
+
+A negative successor cancels the predecessor unit pointwise:
+
+```text
+1 + successorDrift <= 0.
+```
+
+The two rigid classes remain explicit.  They are not hidden in a potential.
+
+## Successor-spare injection
+
+For each spare-class saturated token, Lean chooses one actual spare selected
+incidence in its successor block.  The target is a dependent-pair carrier that
+retains both successor block index and source incidence.  Equality of images
+therefore forces equality of successor indices and then predecessor indices.
+
+Consequently:
+
+```text
+card saturatedSpareIndices
+  <= Nat.card globalSuccessorSpareCarrier.
+```
+
+No incidence can be reused by two saturated tokens.
+
+## Exact stopping obstruction
+
+The signed masses for an open excursion through block `m` cover `q..m`, while
+the successor classification covers successor blocks `q+1..m+1`.  If block
+`m` is saturated, its negative cancellation or spare incidence belongs to
+block `m+1`, outside the current mass interval.
+
+Thus the proposed replacement
+
+```text
+queue + negativeMass
+  <= selectedPressureCarrierCard + rigidResidualCount
+```
+
+is not presently contribution-preserving.  It would silently spend a future
+resource for a terminal saturated token.  The source code records two honest
+continuations:
+
+1. restrict successor charging to `k < m` and retain terminal saturation as a
+   boundary residual;
+2. extend the accounting horizon through `m+1` and prove queue transport to
+   that enlarged window.
+
+This is the first genuine cp-345 stopping obstruction.  The exact partition,
+pointwise cancellation, and injection remain valid finite certificates.
+
+## Finite audit
+
+The Python audit was extended and rerun over all 8,192 odd roots in
+`1..16383`, with at most 4,096 blocks per root.  Every root reached a
+state-one canonical endpoint within this finite run.
+
+At every positive queue state the audit checked:
+
+- the active-window absorption-deficit identity;
+- `queue = positiveMass - negativeMass`;
+- `positiveMass <= dynamicPressureMass + saturatedCount`.
+
+The CSV stores the richer data for each root's maximum witness.  Across the
+6,709 positive maximum witnesses it observed:
+
+```text
+largest queue:                     8
+largest positive drift mass:      11
+largest negative drift mass:       5
+total saturated tokens:          781
+internal negative successors:      0
+internal spare successors:        52
+internal zero-rigid successors:   29
+internal tight-rigid successors:   0
+terminal successor pending:      700
+largest spare carrier count:       3
+```
+
+The 700 pending cases are not failures of classification.  Their successor is
+outside the recorded maximum window and is intentionally not charged.  These
+figures are finite observations only; they imply no all-time frequency or
+uniform bound.
+
+## Branch decision
+
+The immediate continuation should make the temporal contract explicit before
+attacking rigid grammar.  The most local route is an internal-token theorem
+for saturated `k < m` plus a one-bit terminal saturation residual.  Only after
+that theorem should the selected carrier and rigid count replace the raw
+saturated count in the open-window inequality.
+
+The audit suggests zero-rigid successors are the observed internal rigid
+branch and tight-rigid successors did not occur among maximum witnesses, but
+this finite pattern must not be promoted to a theorem.
+
+## Verification
+
+The following gates pass:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionMass
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+python3 python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+python3 -m py_compile python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+git diff --check
+```
+
+Generated audit files:
+
+```text
+python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.csv
+python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.md
+```
diff --git a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
index e8883f87..e95a2578 100644
--- a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+++ b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
@@ -70,6 +70,18 @@ class AuditRow:
     witness_claim_holes: int
     witness_terminal_valuation: int
     witness_absorption_deficit: int
+    witness_positive_drift_mass: int
+    witness_negative_drift_mass: int
+    witness_dynamic_pressure_mass: int
+    witness_saturated_count: int
+    witness_negative_successor_count: int
+    witness_spare_successor_count: int
+    witness_zero_rigid_successor_count: int
+    witness_tight_rigid_successor_count: int
+    witness_terminal_successor_pending_count: int
+    witness_spare_carrier_count: int
+    witness_rigid_residual_count: int
+    witness_selected_depth_histogram: str
 
 
 def audit_root(root: int) -> AuditRow:
@@ -79,10 +91,13 @@ def audit_root(root: int) -> AuditRow:
     queue = 0
     active_start = -1
     maximum_queue = 0
-    record = (-1, -1, 0, 0, 0, 0, 0)
+    record = (-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, "")
     prefix_lengths = [0]
     prefix_holes = [0]
     terminal_valuations: list[int] = []
+    drifts: list[int] = []
+    lengths: list[int] = []
+    claims_by_block: list[int] = []
     reached_one = False
 
     blocks_audited = 0
@@ -100,6 +115,9 @@ def audit_root(root: int) -> AuditRow:
         prefix_lengths.append(prefix_lengths[-1] + length)
         prefix_holes.append(prefix_holes[-1] + holes)
         terminal_valuations.append(terminal_valuation)
+        drifts.append(drift)
+        lengths.append(length)
+        claims_by_block.append(claims)
 
         candidate = queue + drift
         if candidate > 0:
@@ -119,6 +137,39 @@ def audit_root(root: int) -> AuditRow:
             active_holes = prefix_holes[block + 1] - prefix_holes[active_start]
             active_valuation = sum(terminal_valuations[active_start : block + 1])
             assert active_length - active_holes - active_valuation == queue
+            active_drifts = drifts[active_start : block + 1]
+            positive_mass = sum(max(value, 0) for value in active_drifts)
+            negative_mass = sum(max(-value, 0) for value in active_drifts)
+            saturated = [
+                index
+                for index in range(active_start, block + 1)
+                if claims_by_block[index] == lengths[index]
+                and drifts[index] > 0
+            ]
+            dynamic_depths = [
+                terminal_valuations[index]
+                if index in saturated
+                else terminal_valuations[index] - 1
+                if terminal_valuations[index] >= 2
+                else 0
+                for index in range(active_start, block + 1)
+                if drifts[index] > 0
+            ]
+            dynamic_pressure = sum(
+                max(lengths[index] - depth, 0)
+                - int(1 <= depth <= lengths[index])
+                for index, depth in zip(
+                    [
+                        index
+                        for index in range(active_start, block + 1)
+                        if drifts[index] > 0
+                    ],
+                    dynamic_depths,
+                    strict=True,
+                )
+            )
+            assert queue == positive_mass - negative_mass
+            assert positive_mass <= dynamic_pressure + len(saturated)
 
         if queue > maximum_queue:
             assert active_start >= 0
@@ -128,6 +179,84 @@ def audit_root(root: int) -> AuditRow:
             window_valuation = sum(terminal_valuations[q : block + 1])
             deficit = window_length - window_holes - window_valuation
             assert deficit == queue
+            window_indices = range(q, block + 1)
+            positive_mass = sum(max(drifts[index], 0) for index in window_indices)
+            negative_mass = sum(max(-drifts[index], 0) for index in window_indices)
+            saturated = [
+                index
+                for index in window_indices
+                if claims_by_block[index] == lengths[index] and drifts[index] > 0
+            ]
+            positive_indices = [index for index in window_indices if drifts[index] > 0]
+            dynamic_depth_by_index = {
+                index: terminal_valuations[index]
+                if index in saturated
+                else terminal_valuations[index] - 1
+                if terminal_valuations[index] >= 2
+                else 0
+                for index in positive_indices
+            }
+            dynamic_pressure = sum(
+                max(lengths[index] - depth, 0)
+                - int(1 <= depth <= lengths[index])
+                for index, depth in dynamic_depth_by_index.items()
+            )
+            depth_counts: dict[int, int] = {}
+            for depth in dynamic_depth_by_index.values():
+                depth_counts[depth] = depth_counts.get(depth, 0) + 1
+
+            negative_successors = 0
+            spare_successors = 0
+            zero_rigid_successors = 0
+            tight_rigid_successors = 0
+            spare_carrier_count = 0
+            pending = 0
+            for index in saturated:
+                if index == block:
+                    # The successor lies outside the observed window.  Keep
+                    # this temporal boundary explicit rather than fabricating
+                    # a current-window payment.
+                    pending += 1
+                    continue
+                successor = index + 1
+                successor_drift = drifts[successor]
+                selected_depth = (
+                    1
+                    if terminal_valuations[successor] == 1
+                    else terminal_valuations[successor] - 1
+                )
+                selected_card = max(lengths[successor] - (selected_depth + 1), 0)
+                successor_saturated = (
+                    claims_by_block[successor] == lengths[successor]
+                    and successor_drift > 0
+                )
+                drift_image_card = (
+                    successor_drift
+                    if successor_drift > 0 and not successor_saturated
+                    else 0
+                )
+                spare_card = selected_card - drift_image_card
+                assert spare_card >= 0
+                if successor_drift < 0:
+                    negative_successors += 1
+                elif spare_card > 0:
+                    spare_successors += 1
+                    spare_carrier_count += spare_card
+                elif successor_drift == 0 and selected_card == 0:
+                    zero_rigid_successors += 1
+                else:
+                    assert successor_drift > 0
+                    assert terminal_valuations[successor] == 1
+                    assert claims_by_block[successor] == lengths[successor] - 1
+                    tight_rigid_successors += 1
+            assert (
+                negative_successors
+                + spare_successors
+                + zero_rigid_successors
+                + tight_rigid_successors
+                + pending
+                == len(saturated)
+            )
             maximum_queue = queue
             record = (
                 block,
@@ -137,6 +266,18 @@ def audit_root(root: int) -> AuditRow:
                 window_holes,
                 window_valuation,
                 deficit,
+                positive_mass,
+                negative_mass,
+                dynamic_pressure,
+                len(saturated),
+                negative_successors,
+                spare_successors,
+                zero_rigid_successors,
+                tight_rigid_successors,
+                pending,
+                spare_carrier_count,
+                zero_rigid_successors + tight_rigid_successors,
+                ";".join(f"{depth}:{count}" for depth, count in sorted(depth_counts.items())),
             )
 
         if orbit.state(endpoint) == 1:
@@ -158,6 +299,18 @@ def audit_root(root: int) -> AuditRow:
         witness_claim_holes=record[4],
         witness_terminal_valuation=record[5],
         witness_absorption_deficit=record[6],
+        witness_positive_drift_mass=record[7],
+        witness_negative_drift_mass=record[8],
+        witness_dynamic_pressure_mass=record[9],
+        witness_saturated_count=record[10],
+        witness_negative_successor_count=record[11],
+        witness_spare_successor_count=record[12],
+        witness_zero_rigid_successor_count=record[13],
+        witness_tight_rigid_successor_count=record[14],
+        witness_terminal_successor_pending_count=record[15],
+        witness_spare_carrier_count=record[16],
+        witness_rigid_residual_count=record[17],
+        witness_selected_depth_histogram=record[18],
     )
 
 
@@ -177,8 +330,8 @@ def main() -> None:
 
     output_dir = Path(__file__).with_name("results")
     output_dir.mkdir(parents=True, exist_ok=True)
-    csv_path = output_dir / "canonical_absorption_deficit_audit_343.csv"
-    md_path = output_dir / "canonical_absorption_deficit_audit_343.md"
+    csv_path = output_dir / "canonical_excursion_mass_audit_345.csv"
+    md_path = output_dir / "canonical_excursion_mass_audit_345.md"
 
     with csv_path.open("w", newline="", encoding="utf-8") as stream:
         writer = csv.DictWriter(stream, fieldnames=list(asdict(rows[0])))
@@ -189,7 +342,7 @@ def main() -> None:
     reached = sum(row.reached_state_one_endpoint for row in rows)
     positive = sum(row.maximum_queue > 0 for row in rows)
     lines = [
-        "# Canonical Absorption-Deficit Audit (cp-343)",
+        "# Canonical Excursion-Mass Audit (cp-345)",
         "",
         f"Odd roots: `1..{ROOT_MAX}`. Block limit: `{BLOCK_LIMIT}`.",
         "This is finite computational evidence, not a Lean theorem.",
@@ -201,6 +354,10 @@ def main() -> None:
         f"- roots with a positive observed queue maximum: {positive}",
         f"- largest observed queue/deficit: {max(row.maximum_queue for row in rows)}",
         "- every positive queue state passed its active-window deficit identity",
+        "- every positive queue state passed signed-mass decomposition",
+        "- every positive queue state passed dynamic-pressure plus saturation domination",
+        "- successor classifications cover only observed internal successors",
+        "- a saturated terminal block is recorded as pending, not spent from the current window",
         "- the CSV stores the final maximum witness for each root",
         "- no uniform bound or eventual discharge follows from this table",
         "",
diff --git a/python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.md b/python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.md
new file mode 100644
index 00000000..20b92508
--- /dev/null
+++ b/python/Collatz/PetalBridge/results/canonical_excursion_mass_audit_345.md
@@ -0,0 +1,43 @@
+# Canonical Excursion-Mass Audit (cp-345)
+
+Odd roots: `1..16383`. Block limit: `4096`.
+This is finite computational evidence, not a Lean theorem.
+
+## Summary
+
+- roots audited: 8192
+- roots reaching a state-one canonical endpoint: 8192
+- roots with a positive observed queue maximum: 6709
+- largest observed queue/deficit: 8
+- every positive queue state passed its active-window deficit identity
+- every positive queue state passed signed-mass decomposition
+- every positive queue state passed dynamic-pressure plus saturation domination
+- successor classifications cover only observed internal successors
+- a saturated terminal block is recorded as pending, not spent from the current window
+- the CSV stores the final maximum witness for each root
+- no uniform bound or eventual discharge follows from this table
+
+## Maximum-Deficit Windows
+
+| root | queue | terminal | start | blocks | length | holes | valuation | deficit |
+| --- | --- | --- | --- | --- | --- | --- | --- | --- |
+| 4255 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 4591 | 8 | 6 | 0 | 7 | 27 | 12 | 7 | 8 |
+| 5673 | 8 | 9 | 7 | 3 | 18 | 7 | 3 | 8 |
+| 6121 | 8 | 7 | 1 | 7 | 27 | 12 | 7 | 8 |
+| 6383 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 6471 | 8 | 4 | 2 | 3 | 18 | 7 | 3 | 8 |
+| 6887 | 8 | 6 | 0 | 7 | 26 | 11 | 7 | 8 |
+| 8161 | 8 | 8 | 2 | 7 | 27 | 12 | 7 | 8 |
+| 8191 | 8 | 2 | 0 | 3 | 18 | 7 | 3 | 8 |
+| 8511 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 9575 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 9663 | 8 | 3 | 0 | 4 | 23 | 10 | 5 | 8 |
+| 9707 | 8 | 4 | 2 | 3 | 18 | 7 | 3 | 8 |
+| 10881 | 8 | 9 | 3 | 7 | 27 | 12 | 7 | 8 |
+| 10921 | 8 | 3 | 1 | 3 | 18 | 7 | 3 | 8 |
+| 11347 | 8 | 9 | 7 | 3 | 18 | 7 | 3 | 8 |
+| 12243 | 8 | 7 | 1 | 7 | 26 | 11 | 7 | 8 |
+| 12591 | 8 | 14 | 12 | 3 | 18 | 7 | 3 | 8 |
+| 12767 | 8 | 8 | 6 | 3 | 18 | 7 | 3 | 8 |
+| 12943 | 8 | 3 | 1 | 3 | 18 | 7 | 3 | 8 |
````
`````

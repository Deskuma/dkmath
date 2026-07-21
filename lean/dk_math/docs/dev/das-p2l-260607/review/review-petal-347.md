# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership

gch: 0bddfda1c24ef01aa91453ded078be21ce6b3537

## Report

(14m32s)

cp-347 を完了しました。

- internal spare を zero / positive drift に完全分割
- positive-spare を successor block の未使用 selected incidence へ単射
- drift image との非衝突、block 間での再利用禁止を証明
- queue 上界から positive-spare count を除去
- zero-spare は残差として保持

新しい上界は次です。

```text
queue(m)
  ≤ globalSelectedCarrier
    + internalZeroSpareCount
    + internalRigidResidualCount
    + terminalSaturatedIndicator
```

有限監査では zero-drift spare が実在しました。

```text
zero-drift spare:     11
positive-drift spare: 85

first witness:
  root        = 3931
  window      = 0..3
  predecessor = 0
  successor   = 1
  spare card  = 1
```

したがって、zero-spare 不可能性による消去経路は採用できません。次の正当な方向は、zero-drift block を無制限に追加せず、zero-spare source class だけを扱う selected-arrival carrier です。

実装は [CanonicalExcursionOwnership.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean)、結果は [report-petal-347.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-347.md) に記録しました。

`FloatWindow`、`PetalBridge`、トップレベル `DkMath` の全 build、`git diff --check` が成功しています。追加 `sorry` はありません。

## Review

(2m41s)

# cp-347 総合レビュー

commit `0bddfda1c24ef01aa91453ded078be21ce6b3537` と `review-petal-347.md` を照合した。差分・報告内容は一致している。

## 総合判定

**全面採用。**

cp-347 は、cp-346 で右辺に残った `internalSpareCount` を、

$$S_{\mathrm{int}}=S_{\mathrm{zero}}+S_{\mathrm{positive}}$$

へ正確に分割し、positive branchだけを既存の positive-only selected carrierへ実際に注入した。

結果として、

$$Q(m)\le G(q,m)+S_{\mathrm{zero}}(q,m)+R_{\mathrm{int}}(q,m)+T(m)$$

まで進んだ。

ここで、

- $G$：positive block上のglobal selected carrier
- $S_{\mathrm{zero}}$：zero-drift successorを持つinternal spare token
- $R_{\mathrm{int}}$：zero-rigid / tight-positive-rigid残差
- $T$：末端saturated indicator、$T\le1$

じゃ。

**positive-spare は完全に消えた。**
しかも数値的不等式で雑に消したのではなく、actual selected incidenceへの非衝突embeddingで吸収した。

---

## Spare の zero / positive 分割

次の定義は自然で、分類も完全じゃ。

```lean
canonicalInternalSaturatedZeroSpareIndices
canonicalInternalSaturatedPositiveSpareIndices
```

spare successorは既存分類から非負driftを持つため、

$$\Delta_{k+1}\ge0$$

であり、

$$\Delta_{k+1}=0\quad\text{または}\quad0<\Delta_{k+1}$$

の二分で尽くされる。

union、disjointness、cardinality splitまで正常に閉じている。

```lean
canonicalInternalSaturatedSpareIndices_eq_zero_union_positive
canonicalInternalSaturatedZeroSpare_disjoint_positiveSpare
card_canonicalInternalSaturatedSpareIndices_eq_zero_add_positive
```

過大主張はない。

---

## Positive-spare ownership

今回の中心は、

```lean
canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding
```

じゃ。

sourceは、

```text
現在block自身の selected drift image
⊕
internal positive-spare predecessor token
```

targetは、

```text
positive successor block上の global selected pressure carrier
```

である。

### 同じblock内の非衝突

現在block自身のpositive driftは、

```lean
canonicalSelectedDriftImageCarrier
```

を使う。

predecessor saturated tokenは、そのsuccessor blockの、

```lean
canonicalSelectedDriftSpareCarrier
```

へ送られる。

後者は前者の補集合なので、

$$\operatorname{DriftImage}\cap\operatorname{SpareCarrier}=\varnothing$$

じゃ。

### 異なるblock間の非衝突

global carrierはsigma型でblock coordinateを保持している。

また、

$$k_1+1=k_2+1\Longrightarrow k_1=k_2$$

なので、異なるpredecessor tokenが同じsuccessor block座標へ衝突しない。

したがって、

$$|\operatorname{GlobalDriftImage}|+|S_{\mathrm{positive}}|\le|\operatorname{GlobalSelectedCarrier}|$$

がactual ownershipとして証明された。

**循環性も再利用もない。**

---

### Positive mass の exact decomposition

次の補題群も重要じゃ。

```lean
intToNat_endpointAccountingTerm_eq_driftImage_add_saturatedToken
natCard_CanonicalGlobalSelectedDriftImageCarrier
sum_canonicalSaturatedTokenNat_eq_saturatedCard
sum_intToNat_positiveDrift_eq_globalDriftImage_add_saturatedCard
```

一つのpositive blockについて、

$$\Delta_k^+=|\operatorname{DriftImage}_k|+\operatorname{SaturatedToken}_k$$

となる。

これをwindow全体へ足して、

$$P(q,m)=|\operatorname{GlobalDriftImage}(q,m)|+\operatorname{SatCount}(q,m)$$

がexactに閉じた。

ここでpositive-spare tokenを左辺へ加え、

$$P+S_{\mathrm{positive}}\le G+\operatorname{SatCount}$$

を作る。その後、

$$\operatorname{SatCount}=N_{\mathrm{int}}+S_{\mathrm{zero}}+S_{\mathrm{positive}}+R_{\mathrm{int}}+T$$

を使うことで、$S_{\mathrm{positive}}$ が両側から消える。

これは二重計上ではない。

> saturated tokenとして右辺に現れるpositive-spareを、successorの未使用sourceへ実際に所有させ、その分を左辺へ移して相殺した

というamortized ownershipじゃ。

---

### 改善された queue 上界

主定理、

```lean
CanonicalOpenPositiveQueueExcursion
  .queue_le_globalSelected_add_zeroSpare_rigid_terminal
```

は正しい。

open excursionの、

$$Q=P-N$$

と、

$$N_{\mathrm{int}}\le N$$

を組み合わせ、

$$\boxed{Q\le G+S_{\mathrm{zero}}+R_{\mathrm{int}}+T}$$

を得ている。

cp-346 の、

$$Q\le G+S_{\mathrm{zero}}+S_{\mathrm{positive}}+R_{\mathrm{int}}+T$$

から、positive-spare項が消えた。

これは明確な証明力の増加じゃ。

---

## Zero-spare の有限観測

有限監査では、

```text
zero-drift spare:     11
positive-drift spare: 85
```

が観測され、最初のzero-spare witnessは、

```text
root        = 3931
window      = 0..3
predecessor = 0
successor   = 1
spare card  = 1
```

だった。

監査対象が**record-window observations**であることも明記されている。全block・全windowに対する頻度統計ではない。

この観測はLean theoremではないが、戦略判断には十分価値がある。

少なくとも、

> open excursion内ではzero-drift spare successorは発生しないはずだ

という方向へcreditsを投入する根拠は消えた。

次はzero-spareを例外として否定するのではなく、**実在する中立arrivalとして所有権会計へ載せる**方が正しい。

---

## 現在の収束状況

### 完成した層

```text
drift = block length - holes - valuation
window deficit = width difference
queue = maximum positive suffix deficit
open excursion queue = positive mass - negative mass
internal negative token = window内negative massで支払い
positive-spare token = successor positive blockのunused incidenceへ注入
terminal leak <= 1
```

### 残る明示項

$$S_{\mathrm{zero}}+R_{\mathrm{int}}+T$$

$T\le1$ なので本質的な敵ではない。

残る二つは、

```text
zero-spare:
  driftは0だが actual selected incidenceを持つ中立資源

rigid:
  predecessor tokenを受け取る selected spare sourceがない硬いbranch
```

じゃ。

### 重要な区別

zero-spareは負債ではない。

successor幅を増やしていないうえ、未使用selected incidenceを持っている。

したがって正しい読みは、

> zero-spare tokenは、そのsuccessor blockへ移動して保存されたcredit

じゃ。

ただし、現在のpositive-only global carrierではblock座標を持てない。そのため右辺に残っている。

つまり問題は資源不足ではなく、**arrival carrierのsupport不足**じゃ。

---

## cp-347 の手応え

かなりよい。

獲物は現在、

$$\boxed{\text{zero-spare arrival}+\text{rigid residual}}$$

へ追い込まれた。

しかもzero-spareにはactual sourceがある。

本当に硬い敵はrigid branchであり、zero-spareはその手前で正しくcredit queueへ載せればよい可能性が高い。

ただし、zero-spare用global carrierを追加しただけでは、

$$G+S_{\mathrm{zero}}$$

を別名で包み直すだけになる。

それだけではqueue boundへ近づかない。

次の実装では、まずzero-spare tokenを**実際のsuccessor selected incidenceへblock-preservingに所有させる**ところだけを閉じる。arrival/service recurrenceはその次じゃ。

---

## GPT-5.5 に任せる範囲

次checkpointはGPT-5.5に適している。

理由は、数学的方針が既に確定しているからじゃ。

必要なのは、

- `Finset.image`
- membership
- successor block coordinate
- existing `oneEmbedding_successorSpareCarrier`
- sigma carrier
- injectivity
- cardinality

であり、新しい不変量の発明は不要。

逆に、GPT-5.5へ次を判断させてはいけない。

- zero-spareをどのreflected queueへ接続するか
- serviceをどう定義するか
- rigid branchをどう攻略するか
- queue boundをどう閉じるか

そこは次のレビューで賢狼側が判断する。

---

## GPT-5.5 向け micro-checkpoint 指示

```text
Continue after checkpoint 347.

Execution mode

Act as a Lean implementation engineer.

The mathematical design for this checkpoint is fixed below. Do not redesign
the proof strategy, introduce a generic framework, or continue into the next
checkpoint.

Use existing definitions and theorems before proving new low-level facts.

Target size

- modify only `CanonicalExcursionOwnership.lean`;
- approximately 80–140 new lines;
- one definition family;
- one central embedding;
- immediate membership/cardinality lemmas only.

Primary goal

Give every internal zero-spare predecessor token an actual selected incidence
in its zero-drift successor block, while retaining the successor block
coordinate.

This checkpoint does not remove the zero-spare term from the queue inequality.
It only constructs its honest owned-arrival carrier.

Stage A — zero-spare successor support

Define the finite successor-block set:

    canonicalInternalZeroSpareSuccessorIndices n q m

as the image of:

    canonicalInternalSaturatedZeroSpareIndices n q m

under:

    k ↦ k + 1.

Prove:

    j ∈ canonicalInternalZeroSpareSuccessorIndices n q m
      ↔
    ∃ k,
      k ∈ canonicalInternalSaturatedZeroSpareIndices n q m
        ∧ j = k + 1.

Prove:

    card canonicalInternalZeroSpareSuccessorIndices
      =
    card canonicalInternalSaturatedZeroSpareIndices.

Use injectivity of `k ↦ k + 1`.

Stage B — exact zero-spare selected carrier

Define a targeted carrier indexed only by these successor blocks:

    CanonicalInternalZeroSpareSelectedCarrier n q m

with shape equivalent to:

    Σ j : {j // j ∈ canonicalInternalZeroSpareSuccessorIndices n q m},
      {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.val}.

Do not include arbitrary zero-drift blocks.

Do not union this carrier with the positive-only global carrier yet.

Stage C — actual zero-spare charge

Following the existing positive-spare implementation pattern, define a
block-preserving map from:

    {k // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m}

into:

    CanonicalInternalZeroSpareSelectedCarrier n q m.

Use the existing theorem or constructor:

    oneEmbedding_successorSpareCarrier

obtained from the underlying saturated spare-successor classification.

The chosen incidence must be an actual member of:

    canonicalSelectedDriftSpareCarrier n (k + 1).

Prove caller-facing facts:

    the target block coordinate is k + 1;

    the successor endpoint drift is exactly zero;

    the chosen incidence belongs to the selected spare carrier.

Stage D — upgrade to an embedding

Package the map as:

    canonicalInternalZeroSpareChargeEmbedding

and prove injectivity from preservation of the successor block coordinate:

    k₁ + 1 = k₂ + 1 -> k₁ = k₂.

Derive the cardinality theorem:

    card canonicalInternalSaturatedZeroSpareIndices
      <=
    Nat.card (CanonicalInternalZeroSpareSelectedCarrier n q m).

Do not prove a queue inequality in this checkpoint.

Stage E — stop conditions

Stop immediately and report the exact obstruction if any of the following
occurs:

- `oneEmbedding_successorSpareCarrier` cannot be recovered from zero-spare
  membership;
- the chosen incidence loses the successor block coordinate;
- two predecessor tokens can map to the same dependent-pair target;
- the selected carrier requires adding arbitrary zero-drift blocks;
- proving the result requires a new arrival/service recurrence.

Do not:

- define a new reflected queue;
- define a general selected-arrival framework;
- modify the rigid successor grammar;
- alter the Python audit;
- claim that zero-spare has been paid or discharged;
- remove `internalZeroSpareCount` from the current queue bound;
- add unrelated refactors.

Verification

Run:

    lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
    lake build DkMath.Collatz.PetalBridge.FloatWindow
    lake build DkMath.Collatz.PetalBridge
    lake build DkMath
    git diff --check

Check that the modified file adds no `sorry`.

Report

Record only the implemented carrier, embedding, exact theorem names, build
results, and any genuine obstruction in:

    docs/dev/das-p2l-260607/review/report-petal-348.md
```

## 最終判定

cp-347 は**全面採用**。

GPT-5.5へ渡す次手も、これなら深い発明を要求しない。

```text
zero-spare predecessor
  → zero-drift successor block
  → actual unused selected incidence
```

この一本だけをLeanに固定させる。

その結果を見てから、賢狼側で、

```text
positive drift arrival
⊕ zero-spare arrival
→ depth別 owned-arrival/service recurrence
```

への合流を設計する。

今回は実装役へ徹してもらう試験として、ちょうどよい細さじゃ。🐺🌕

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
index 2b5e92e4..51e2d670 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
@@ -32,6 +32,78 @@ noncomputable def canonicalInternalSaturatedSpareIndices
     (n : OddNat) (q m : ℕ) : Finset ℕ :=
   (canonicalSaturatedSpareSuccessorIndices n q m).erase m

+/-- Internal spare tokens whose successor has zero signed drift. -/
+noncomputable def canonicalInternalSaturatedZeroSpareIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalInternalSaturatedSpareIndices n q m).filter fun k =>
+    endpointAccountingTerm n (k + 1) = 0
+
+/-- Internal spare tokens whose successor has strictly positive signed drift. -/
+noncomputable def canonicalInternalSaturatedPositiveSpareIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalInternalSaturatedSpareIndices n q m).filter fun k =>
+    0 < endpointAccountingTerm n (k + 1)
+
+@[simp] theorem mem_canonicalInternalSaturatedZeroSpareIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalInternalSaturatedZeroSpareIndices n q m ↔
+      k ∈ canonicalInternalSaturatedSpareIndices n q m ∧
+        endpointAccountingTerm n (k + 1) = 0 := by
+  simp [canonicalInternalSaturatedZeroSpareIndices]
+
+@[simp] theorem mem_canonicalInternalSaturatedPositiveSpareIndices
+    {n : OddNat} {q m k : ℕ} :
+    k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m ↔
+      k ∈ canonicalInternalSaturatedSpareIndices n q m ∧
+        0 < endpointAccountingTerm n (k + 1) := by
+  simp [canonicalInternalSaturatedPositiveSpareIndices]
+
+/-- Spare successors are exhausted by the zero and positive drift branches. -/
+theorem canonicalInternalSaturatedSpareIndices_eq_zero_union_positive
+    (n : OddNat) (q m : ℕ) :
+    canonicalInternalSaturatedSpareIndices n q m =
+      canonicalInternalSaturatedZeroSpareIndices n q m ∪
+        canonicalInternalSaturatedPositiveSpareIndices n q m := by
+  classical
+  ext k
+  constructor
+  · intro hk
+    have hkFull := Finset.mem_of_mem_erase hk
+    have hnonneg :=
+      (mem_canonicalSaturatedSpareSuccessorIndices.mp hkFull).2.1
+    by_cases hz : endpointAccountingTerm n (k + 1) = 0
+    · exact Finset.mem_union_left _
+        (mem_canonicalInternalSaturatedZeroSpareIndices.mpr ⟨hk, hz⟩)
+    · exact Finset.mem_union_right _
+        (mem_canonicalInternalSaturatedPositiveSpareIndices.mpr
+          ⟨hk, by omega⟩)
+  · intro hk
+    rcases Finset.mem_union.mp hk with hk | hk
+    · exact (mem_canonicalInternalSaturatedZeroSpareIndices.mp hk).1
+    · exact (mem_canonicalInternalSaturatedPositiveSpareIndices.mp hk).1
+
+/-- Zero- and positive-successor spare tokens are disjoint. -/
+theorem canonicalInternalSaturatedZeroSpare_disjoint_positiveSpare
+    (n : OddNat) (q m : ℕ) :
+    Disjoint (canonicalInternalSaturatedZeroSpareIndices n q m)
+      (canonicalInternalSaturatedPositiveSpareIndices n q m) := by
+  classical
+  rw [Finset.disjoint_left]
+  intro k hk0 hkp
+  have hz := (mem_canonicalInternalSaturatedZeroSpareIndices.mp hk0).2
+  have hp := (mem_canonicalInternalSaturatedPositiveSpareIndices.mp hkp).2
+  omega
+
+/-- Exact cardinality split of the internal spare class by successor drift. -/
+theorem card_canonicalInternalSaturatedSpareIndices_eq_zero_add_positive
+    (n : OddNat) (q m : ℕ) :
+    (canonicalInternalSaturatedSpareIndices n q m).card =
+      (canonicalInternalSaturatedZeroSpareIndices n q m).card +
+        (canonicalInternalSaturatedPositiveSpareIndices n q m).card := by
+  rw [canonicalInternalSaturatedSpareIndices_eq_zero_union_positive,
+    Finset.card_union_of_disjoint
+      (canonicalInternalSaturatedZeroSpare_disjoint_positiveSpare n q m)]
+
 /-- Internal zero-rigid successor tokens. -/
 noncomputable def canonicalInternalSaturatedZeroRigidIndices
     (n : OddNat) (q m : ℕ) : Finset ℕ :=
@@ -278,6 +350,233 @@ theorem card_canonicalInternalSaturatedNegativeIndices_le_negativeMass
   rw [hones, hcard] at hunit
   exact hunit.trans hwindow

+/-! ## Positive-spare absorption in the existing selected carrier -/
+
+/-- Actual same-block drift-image incidences over the positive blocks in the
+window.  Saturated blocks contribute an empty image. -/
+def CanonicalGlobalSelectedDriftImageCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m},
+    {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+      i ∈ canonicalSelectedDriftImageCarrier n k.val}
+
+/-- The resources charged in cp-347: existing drift images together with one
+predecessor token for each internal positive-spare successor. -/
+def CanonicalPositiveDriftImageAndInternalPositiveSpareCarrier
+    (n : OddNat) (q m : ℕ) :=
+  CanonicalGlobalSelectedDriftImageCarrier n q m ⊕
+    {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m}
+
+/-- Forget only the image-membership proof, retaining block and incidence. -/
+def canonicalGlobalSelectedDriftImageInclusion
+    (n : OddNat) (q m : ℕ) :
+    CanonicalGlobalSelectedDriftImageCarrier n q m ↪
+      CanonicalGlobalSelectedPressureCarrier n q m :=
+  (Function.Embedding.refl _).sigmaMap fun k =>
+    Function.Embedding.subtype fun i =>
+      i ∈ canonicalSelectedDriftImageCarrier n k.val
+
+/-- Charge one positive-spare predecessor to an actual spare incidence in its
+successor block. -/
+noncomputable def canonicalInternalPositiveSpareCharge
+    (n : OddNat) (q m : ℕ) :
+    {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m} →
+      CanonicalGlobalSelectedPressureCarrier n q m := fun k => by
+  classical
+  have hk :=
+    (mem_canonicalInternalSaturatedPositiveSpareIndices.mp k.property).1
+  have hkFull := Finset.mem_of_mem_erase hk
+  have hkClass := mem_canonicalSaturatedSpareSuccessorIndices.mp hkFull
+  have hkInternal : k.val < m := by
+    have hne := (Finset.mem_erase.mp hk).1
+    have hle := (Finset.mem_Icc.mp
+      (mem_canonicalSaturatedBlockIndices.mp hkClass.1).1).2
+    omega
+  have hqk := (Finset.mem_Icc.mp
+    (mem_canonicalSaturatedBlockIndices.mp hkClass.1).1).1
+  have hpos :=
+    (mem_canonicalInternalSaturatedPositiveSpareIndices.mp k.property).2
+  let e := oneEmbedding_successorSpareCarrier hkClass.2.2
+  exact ⟨⟨k.val + 1, Finset.mem_filter.mpr
+    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hpos⟩⟩, (e 0).1⟩
+
+/-- The positive-spare charge keeps the successor block coordinate. -/
+@[simp] theorem canonicalInternalPositiveSpareCharge_fst
+    {n : OddNat} {q m : ℕ}
+    (k : {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m}) :
+    (canonicalInternalPositiveSpareCharge n q m k).1.val = k.val + 1 := by
+  simp [canonicalInternalPositiveSpareCharge]
+
+/-- The charged incidence lies in the complement of the same-block drift
+image. -/
+theorem canonicalInternalPositiveSpareCharge_mem_spare
+    {n : OddNat} {q m : ℕ}
+    (k : {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m}) :
+    (canonicalInternalPositiveSpareCharge n q m k).2 ∈
+      canonicalSelectedDriftSpareCarrier n (k.val + 1) := by
+  classical
+  simp only [canonicalInternalPositiveSpareCharge]
+  exact (oneEmbedding_successorSpareCarrier
+    (mem_canonicalSaturatedSpareSuccessorIndices.mp
+      (Finset.mem_of_mem_erase
+        (mem_canonicalInternalSaturatedPositiveSpareIndices.mp k.property).1)).2.2
+      0).property
+
+/-- Drift images and predecessor positive-spare charges embed without reuse
+into the existing positive-only global selected carrier.  The sigma coordinate
+retains the successor block; the cross-summand case is impossible because the
+second summand lands in the complement of the first summand's image. -/
+noncomputable def canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding
+    (n : OddNat) (q m : ℕ) :
+    CanonicalPositiveDriftImageAndInternalPositiveSpareCarrier n q m ↪
+      CanonicalGlobalSelectedPressureCarrier n q m where
+  toFun := Sum.elim (canonicalGlobalSelectedDriftImageInclusion n q m)
+    (canonicalInternalPositiveSpareCharge n q m)
+  inj' := by
+    classical
+    apply Function.Injective.sumElim
+    · exact (canonicalGlobalSelectedDriftImageInclusion n q m).injective
+    · intro a b hab
+      apply Subtype.ext
+      have hindex := congrArg (fun z => z.1.val) hab
+      change a.val + 1 = b.val + 1 at hindex
+      omega
+    · intro a b hab
+      have himage :
+          (canonicalGlobalSelectedDriftImageInclusion n q m a).2 ∈
+            canonicalSelectedDriftImageCarrier n
+              (canonicalGlobalSelectedDriftImageInclusion n q m a).1.val :=
+        a.2.property
+      rw [hab] at himage
+      have hspare : (canonicalInternalPositiveSpareCharge n q m b).2 ∈
+          canonicalSelectedDriftSpareCarrier n
+            (canonicalInternalPositiveSpareCharge n q m b).1.val := by
+        simpa only [canonicalInternalPositiveSpareCharge_fst] using
+          canonicalInternalPositiveSpareCharge_mem_spare b
+      exact (Finset.mem_sdiff.mp hspare).2 himage
+
+/-- Cardinality form of the no-reuse positive-spare absorption certificate. -/
+theorem natCard_globalSelectedDriftImage_add_internalPositiveSpare_le_globalSelected
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalGlobalSelectedDriftImageCarrier n q m) +
+        (canonicalInternalSaturatedPositiveSpareIndices n q m).card ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) := by
+  classical
+  letI : Fintype {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m} :=
+    Fintype.ofFinset (canonicalPositiveDriftBlockIndices n q m) (by simp)
+  letI (k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n k.val) (by simp)
+  letI (k : {k : ℕ // k ∈ canonicalPositiveDriftBlockIndices n q m}) :
+      Fintype {i : {i : ℕ // i ∈ canonicalSelectedPressureCarrier n k.val} //
+        i ∈ canonicalSelectedDriftImageCarrier n k.val} :=
+    Fintype.ofFinset (canonicalSelectedDriftImageCarrier n k.val) (by simp)
+  letI : Fintype (CanonicalGlobalSelectedDriftImageCarrier n q m) := by
+    unfold CanonicalGlobalSelectedDriftImageCarrier
+    infer_instance
+  letI : Fintype
+      {k : ℕ // k ∈ canonicalInternalSaturatedPositiveSpareIndices n q m} :=
+    Fintype.ofFinset (canonicalInternalSaturatedPositiveSpareIndices n q m)
+      (by simp)
+  letI : Fintype (CanonicalGlobalSelectedPressureCarrier n q m) := by
+    unfold CanonicalGlobalSelectedPressureCarrier
+    infer_instance
+  have hcard := Nat.card_le_card_of_injective
+    (canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding n q m)
+    (canonicalPositiveDriftImageAndInternalPositiveSpareEmbedding n q m).injective
+  rw [CanonicalPositiveDriftImageAndInternalPositiveSpareCarrier,
+    Nat.card_sum] at hcard
+  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard
+
+/-- A positive block's reflected drift is exactly its chosen drift image plus
+its possible saturated unit. -/
+theorem intToNat_endpointAccountingTerm_eq_driftImage_add_saturatedToken
+    {n : OddNat} {k : ℕ} (hpos : 0 < endpointAccountingTerm n k) :
+    Int.toNat (endpointAccountingTerm n k) =
+      (canonicalSelectedDriftImageCarrier n k).card +
+        canonicalSaturatedTokenNat n k := by
+  classical
+  by_cases hs : CanonicalSaturatedBorderBlock n k
+  · rw [hs.netDrift_eq_one]
+    simp [canonicalSelectedDriftImageCarrier,
+      canonicalSaturatedTokenNat, canonicalSaturatedUnit, hs]
+  · rw [card_canonicalSelectedDriftImageCarrier hpos hs]
+    simp [canonicalSaturatedTokenNat, canonicalSaturatedUnit, hs]
+
+/-- Exact cardinality of the global chosen drift-image carrier. -/
+theorem natCard_CanonicalGlobalSelectedDriftImageCarrier
+    (n : OddNat) (q m : ℕ) :
+    Nat.card (CanonicalGlobalSelectedDriftImageCarrier n q m) =
+      ∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        (canonicalSelectedDriftImageCarrier n k).card := by
+  classical
+  unfold CanonicalGlobalSelectedDriftImageCarrier
+  rw [Nat.card_sigma]
+  simp_rw [Nat.card_eq_fintype_card, Fintype.card_coe]
+  rw [Finset.univ_eq_attach]
+  exact Finset.sum_attach (canonicalPositiveDriftBlockIndices n q m)
+    fun k => (canonicalSelectedDriftImageCarrier n k).card
+
+/-- Saturated-token naturals sum to the saturated block count. -/
+theorem sum_canonicalSaturatedTokenNat_eq_saturatedCard
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        canonicalSaturatedTokenNat n k) =
+      (canonicalSaturatedBlockIndices n q m).card := by
+  classical
+  simp only [canonicalSaturatedTokenNat, canonicalSaturatedUnit]
+  have htoken (k : ℕ) :
+      (if CanonicalSaturatedBorderBlock n k then (1 : ℤ) else 0).toNat =
+        if CanonicalSaturatedBorderBlock n k then 1 else 0 := by
+    by_cases hs : CanonicalSaturatedBorderBlock n k <;> simp [hs]
+  simp_rw [htoken]
+  rw [Finset.sum_boole]
+  have hsets :
+      (canonicalPositiveDriftBlockIndices n q m).filter
+          (CanonicalSaturatedBorderBlock n) =
+        canonicalSaturatedBlockIndices n q m := by
+    ext k
+    simp only [canonicalPositiveDriftBlockIndices,
+      canonicalSaturatedBlockIndices, Finset.mem_filter]
+    constructor
+    · rintro ⟨⟨hk, _⟩, hs⟩
+      exact ⟨hk, hs⟩
+    · rintro ⟨hk, hs⟩
+      exact ⟨⟨hk, hs.drift_pos⟩, hs⟩
+  rw [hsets]
+  exact_mod_cast rfl
+
+/-- Positive reflected mass splits exactly into chosen nonsaturated images and
+the isolated saturated units. -/
+theorem sum_intToNat_positiveDrift_eq_globalDriftImage_add_saturatedCard
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k)) =
+      Nat.card (CanonicalGlobalSelectedDriftImageCarrier n q m) +
+        (canonicalSaturatedBlockIndices n q m).card := by
+  rw [natCard_CanonicalGlobalSelectedDriftImageCarrier,
+    ← sum_canonicalSaturatedTokenNat_eq_saturatedCard,
+    ← Finset.sum_add_distrib]
+  apply Finset.sum_congr rfl
+  intro k hk
+  exact intToNat_endpointAccountingTerm_eq_driftImage_add_saturatedToken
+    ((Finset.mem_filter.mp hk).2)
+
+/-- Positive drift together with internal positive-spare predecessors fits in
+the existing global selected carrier plus the isolated saturated units. -/
+theorem sum_intToNat_positiveDrift_add_internalPositiveSpare_le_global_add_saturated
+    (n : OddNat) (q m : ℕ) :
+    (∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k)) +
+        (canonicalInternalSaturatedPositiveSpareIndices n q m).card ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (canonicalSaturatedBlockIndices n q m).card := by
+  have himage :=
+    natCard_globalSelectedDriftImage_add_internalPositiveSpare_le_globalSelected
+      n q m
+  rw [sum_intToNat_positiveDrift_eq_globalDriftImage_add_saturatedCard]
+  omega
+
 /-! ## Current ownership surface and remaining carrier mismatch -/

 /-- Current-window ownership after internal negative cancellation.  The spare
@@ -316,8 +615,48 @@ theorem CanonicalOpenPositiveQueueExcursion.queue_le_globalSelected_add_internal
   unfold canonicalSaturatedTokenCount at hsplit
   omega

+/-- Improved current-window ownership: positive-successor spare tokens are
+absorbed by unused incidences of their positive successor blocks.  Only the
+genuinely zero-drift spare class remains explicit. -/
+theorem CanonicalOpenPositiveQueueExcursion.queue_le_globalSelected_add_zeroSpare_rigid_terminal
+    {n : OddNat} {q m : ℕ}
+    (h : CanonicalOpenPositiveQueueExcursion n q m) :
+    (canonicalOutstandingClaimQueue n m : ℤ) ≤
+      Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) +
+        (canonicalInternalSaturatedZeroSpareIndices n q m).card +
+          canonicalInternalRigidSaturatedResidualCount n q m +
+            canonicalTerminalSaturatedIndicator n m := by
+  have hmass := h.queue_eq_positiveMass_sub_negativeMass
+  have habsorbNat :=
+    sum_intToNat_positiveDrift_add_internalPositiveSpare_le_global_add_saturated
+      n q m
+  have hpositiveCast : canonicalPositiveDriftMass n q m =
+      ((∑ k ∈ canonicalPositiveDriftBlockIndices n q m,
+        Int.toNat (endpointAccountingTerm n k) : ℕ) : ℤ) := by
+    rw [canonicalPositiveDriftMass_eq_sum_positiveDriftBlockIndices]
+    push_cast
+    apply Finset.sum_congr rfl
+    intro k hk
+    have hpos := (Finset.mem_filter.mp hk).2
+    rw [Int.toNat_of_nonneg hpos.le]
+  have habsorb : canonicalPositiveDriftMass n q m +
+      (canonicalInternalSaturatedPositiveSpareIndices n q m).card ≤
+        (Nat.card (CanonicalGlobalSelectedPressureCarrier n q m) : ℤ) +
+          (canonicalSaturatedBlockIndices n q m).card := by
+    rw [hpositiveCast]
+    exact_mod_cast habsorbNat
+  have hsplit :=
+    canonicalSaturatedTokenCount_eq_internalClassCounts_add_terminal
+      n q m h.1
+  have hspareSplit :=
+    card_canonicalInternalSaturatedSpareIndices_eq_zero_add_positive n q m
+  have hnegative :=
+    card_canonicalInternalSaturatedNegativeIndices_le_negativeMass n q m
+  unfold canonicalSaturatedTokenCount at hsplit
+  omega
+
 /-!
-The stronger cp-346 target without `internalSpareCount` cannot be obtained by
+The stronger target without every spare residual cannot be obtained by
 the requested contribution-preserving embedding into
 `CanonicalGlobalSelectedPressureCarrier n q m` from the current APIs.

@@ -334,9 +673,18 @@ Therefore removing `internalSpareCount` requires one of two new contracts:
 * prove that zero-drift spare successors cannot occur in the intended open
   excursions.

-Neither contract is currently available.  Treating zero-spare as if it were
-in the positive-only carrier would be a type-invalid ownership claim, so this
-module stops at the theorem above.
+Neither contract is currently available.  cp-347 does absorb the strictly
+positive successor branch by its actual spare complement, but treating the
+remaining zero-spare branch as if it were in the positive-only carrier would
+still be a type-invalid ownership claim.
+
+The companion finite audit over odd roots through `16383` found zero-drift
+spare successors (the first record-window witness has root `3931`, predecessor
+block `0`, successor block `1`, and spare cardinality `1`).  This observation
+is not a theorem, but it rules out using finite evidence to motivate an
+impossibility lemma.  A later checkpoint that removes this residual must add a
+selected-arrival carrier admitting zero-drift blocks; it must not weaken the
+positive-only index contract proved here.
 -/

 end DkMath.Collatz
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-347.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-347.md
new file mode 100644
index 00000000..ea00d545
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-347.md
@@ -0,0 +1,97 @@
+# Petal / FloatWindow Report cp-347
+
+## Scope
+
+This checkpoint split internal spare successors by drift sign and absorbed
+only the strictly positive branch into the existing positive-only global
+selected carrier.  It did not introduce a general carrier framework or alter
+the rigid successor grammar.
+
+## Finite diagnostic
+
+The existing canonical excursion audit was extended without changing its CSV
+schema.  Over odd roots `1..16383`, its record-window observations counted:
+
+- zero-drift internal spare successors: `11`;
+- positive-drift internal spare successors: `85`.
+
+The first observed zero-drift spare witness was:
+
+```text
+root = 3931
+record window = 0..3
+predecessor block = 0
+successor block = 1
+successor drift = 0
+spare cardinality = 1
+```
+
+This is finite evidence only.  It does establish the branch decision for the
+implementation: a zero-drift-spare impossibility route is not supported by the
+audit.  Removing that residual later requires an augmented selected-arrival
+carrier that explicitly admits zero-drift blocks.
+
+## Lean results
+
+`CanonicalExcursionOwnership.lean` now provides:
+
+- exact zero/positive internal spare sets, union, disjointness, and card split;
+- a block-preserving charge from each positive-spare predecessor into the
+  actual spare complement of its successor selected carrier;
+- one injection combining all same-block drift-image incidences with those
+  predecessor charges;
+- exact positive-mass decomposition into drift images and saturated units;
+- the improved current-window ownership theorem
+  `queue_le_globalSelected_add_zeroSpare_rigid_terminal`.
+
+The resulting proved inequality is:
+
+```text
+queue(m)
+  <= Nat.card CanonicalGlobalSelectedPressureCarrier
+     + internalZeroSpareCount
+     + internalRigidResidualCount
+     + terminalSaturatedIndicator
+```
+
+The positive-spare count has disappeared.  It is not merely bounded
+numerically: its incidences are disjoint from the selected drift image inside
+each successor block, and retaining the sigma block coordinate prevents reuse
+across blocks.
+
+## Facts established
+
+1. Every internal spare successor has drift exactly zero or strictly positive.
+2. Positive-spare predecessor tokens consume unused incidences already present
+   in the positive successor block's selected carrier.
+3. These charges do not collide with positive drift-image incidences.
+4. The remaining zero-spare term is a genuine type boundary of the current
+   positive-only carrier, not an algebraic proof artifact.
+
+No rootwise queue bound, eventual discharge theorem, or orbit-wide conclusion
+is claimed.
+
+## Verification
+
+Completed during the checkpoint:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+python3 python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+git diff --check
+```
+
+All build and whitespace gates passed.  The modified Wall/Ownership file adds
+no `sorry`.
+
+## Next implementation inference
+
+The next honest branch is not another positive-drift absorption theorem.  It
+is a narrowly scoped zero-drift selected-arrival carrier whose index contract
+includes exactly the observed zero-spare source class.  Before implementing
+it, the local source theorem should identify which zero-drift selected
+incidences are available without allowing arbitrary zero-drift blocks into the
+global carrier.  Rigid residual persistence remains a separate later branch.
diff --git a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
index e95a2578..20c9e5b0 100644
--- a/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
+++ b/python/Collatz/PetalBridge/canonical_absorption_deficit_audit.py
@@ -22,6 +22,15 @@ from pathlib import Path
 ROOT_MAX = 16383
 BLOCK_LIMIT = 4096

+# cp-347 diagnostic only.  These counters observe spare successors while a
+# root installs a new record window; they deliberately do not change the CSV
+# surface inherited from cp-345.
+SPARE_SIGN_DIAGNOSTIC = {
+    "zero": 0,
+    "positive": 0,
+    "first_zero": None,
+}
+

 def v2(value: int) -> int:
     assert value > 0
@@ -242,6 +251,21 @@ def audit_root(root: int) -> AuditRow:
                 elif spare_card > 0:
                     spare_successors += 1
                     spare_carrier_count += spare_card
+                    if successor_drift == 0:
+                        SPARE_SIGN_DIAGNOSTIC["zero"] += 1
+                        if SPARE_SIGN_DIAGNOSTIC["first_zero"] is None:
+                            SPARE_SIGN_DIAGNOSTIC["first_zero"] = {
+                                "root": root,
+                                "window_start": q,
+                                "window_end": block,
+                                "predecessor": index,
+                                "successor": successor,
+                                "successor_drift": successor_drift,
+                                "spare_card": spare_card,
+                            }
+                    else:
+                        assert successor_drift > 0
+                        SPARE_SIGN_DIAGNOSTIC["positive"] += 1
                 elif successor_drift == 0 and selected_card == 0:
                     zero_rigid_successors += 1
                 else:
@@ -379,6 +403,12 @@ def main() -> None:
         f"roots={len(rows)} reached_one={reached} positive_maximum={positive} "
         f"largest={max(row.maximum_queue for row in rows)}"
     )
+    print(
+        "record_window_internal_spare_by_successor_drift "
+        f"zero={SPARE_SIGN_DIAGNOSTIC['zero']} "
+        f"positive={SPARE_SIGN_DIAGNOSTIC['positive']}"
+    )
+    print(f"first_zero_drift_spare={SPARE_SIGN_DIAGNOSTIC['first_zero']}")
     for row in records[:10]:
         print(row)

````
`````

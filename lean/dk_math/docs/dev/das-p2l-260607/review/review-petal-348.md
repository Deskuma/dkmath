# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership

gch: 690124611da9c751b9b43488cd8339cd652dae36

## Report

switch GPT-5.6 Sol/light to GPT-5.5/light Codex

(4m22s)

実装完了しました。

[CanonicalExcursionOwnership.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean) に cp-348 の zero-spare owned-arrival carrier を追加しました。主な追加は以下です。

```text
canonicalInternalZeroSpareSuccessorIndices
mem_canonicalInternalZeroSpareSuccessorIndices
card_canonicalInternalZeroSpareSuccessorIndices_eq_zeroSpare

CanonicalInternalZeroSpareSelectedCarrier
canonicalInternalZeroSpareCharge
canonicalInternalZeroSpareCharge_fst
canonicalInternalZeroSpareCharge_successor_endpoint_zero
canonicalInternalZeroSpareCharge_mem_spare
canonicalInternalZeroSpareChargeEmbedding
card_canonicalInternalSaturatedZeroSpareIndices_le_zeroSpareSelectedCarrier
```

確定した事実は、internal zero-spare predecessor token は、任意の zero-drift block ではなく、その successor block に限定された selected-arrival carrier へ、実在する selected spare incidence として単射的に入る、ということです。今回は設計どおり、queue inequality は変更していません。`internalZeroSpareCount` の除去も主張していません。

レポートは [report-petal-348.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-348.md) に追加しました。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
lake build DkMath.Collatz.PetalBridge.FloatWindow
lake build DkMath.Collatz.PetalBridge
lake build DkMath
git diff --check
```

対象ファイルへの `sorry` 追加もありません。現在の未コミット差分は ownership file の変更と `report-petal-348.md` の新規追加です。

## Review

(3m42s)

## cp-348 総合レビュー

## 総合判定

**全面採用。**

加えて、GPT-5.5/light への実装役切り替えも、今回の標本では**成功**と判定する。

* 状況確認：約 `5Cr`
* 実装：約 `31Cr`
* 所要時間：4分22秒
* 新規Leanコード：約121行
* 指定外の理論拡張なし
* 全build成功
* `sorry` 追加なし
* queue上界を勝手に変更しない
* 次段のservice recurrenceへ踏み込まない

前回の大型checkpointと比較すると、実装creditsはおよそ六分の一まで下がった。しかも成果の品質は落ちていない。

これはまさに、

```text
賢狼 GPT-5.6:
  数学設計・定理形・禁止事項・停止条件

GPT-5.5/light:
  指定されたLean実装
```

という役割分担が機能した結果じゃ。

---

## Successor support の設計

```lean
canonicalInternalZeroSpareSuccessorIndices
```

は、zero-spare predecessor集合を、

$$k\longmapsto k+1$$

で写した像として定義されている。

重要なのは、**任意のzero-drift blockを集めていない**ことじゃ。

対象は、

> internal saturated zero-spare predecessorから実際に到達したsuccessor block

だけに限定されている。

また、successor shiftは単射なので、

$$\left|\operatorname{ZeroSpareSuccessorIndices}\right|=\left|\operatorname{ZeroSparePredecessorIndices}\right|$$

も正確に証明された。

これにより、時間座標を移してもtoken数は失われず、二つのpredecessorが同じsuccessor blockへ潰れることもない。

---

## Targeted selected carrier

新しい、

```lean
CanonicalInternalZeroSpareSelectedCarrier
```

は、

$$\sum_{j\in\operatorname{ZeroSpareSuccessorIndices}}\operatorname{SelectedPressureCarrier}(j)$$

というdependent sumになっている。

これはcp-347で発見した型境界を正しく修復している。

従来のglobal selected carrierはpositive-drift blockだけを外側indexに持っていた。そのためzero-drift successorのselected incidenceは実在していても、その型へ入れなかった。

今回のcarrierは、

```text
positive-only global carrierを弱める
```

のではなく、

```text
zero-spare arrivalが実際に発生したsuccessor blockだけを
別の有限supportとして切り出す
```

設計じゃ。

この限定は非常によい。

---

## Actual zero-spare charge

```lean
canonicalInternalZeroSpareCharge
```

は、各predecessor token $k$ を、そのsuccessor block $k+1$ のactual spare incidenceへ送っている。

使用しているのは既存の、

```lean
oneEmbedding_successorSpareCarrier
```

であり、単なる非空性やcardinalityではない。

選ばれたtargetは、

* successor block座標が $k+1$
* successor driftがexactly zero
* incidenceが`canonicalSelectedDriftSpareCarrier`の要素

という三条件を満たす。

したがってzero-spareはもう、

> selected sourceがあるらしい中立block

ではない。

> predecessor tokenごとに、具体的な未使用selected incidenceを一つ所有している中立arrival

まで昇格した。

---

## Embedding と非再利用

```lean
canonicalInternalZeroSpareChargeEmbedding
```

のinjectivityは、targetに保持されたsuccessor block座標だけで証明される。

$$k_1+1=k_2+1\Longrightarrow k_1=k_2$$

じゃ。

これにより、異なるzero-spare predecessorが同じarrival resourceとして二重計上されることはない。

cardinalityとしても、

$$\left|S_{\mathrm{zero}}\right|\le\left|\operatorname{ZeroSpareSelectedCarrier}\right|$$

が得られた。

**所有権証明として正常。循環性なし。**

---

## 一点だけ必要な意味論補正

reportでは、

> `CanonicalInternalZeroSpareSelectedCarrier` がowned-arrival carrierである

という表現になっている。

大筋ではよいが、厳密には少し広い。

このcarrierは、対象successor blockに存在する**全selected incidence**を含む。一方、実際にzero-spare tokenへ割り当てられたものは、

```lean
canonicalInternalZeroSpareChargeEmbedding
```

の像だけじゃ。

したがって、区別するとこうなる。

```text
CanonicalInternalZeroSpareSelectedCarrier:
  zero-spare successor block上のhost carrier

range of canonicalInternalZeroSpareChargeEmbedding:
  実際に所有されたexact arrival atoms
```

現在証明されたのは、

$$|S_{\mathrm{zero}}|\le|\operatorname{HostCarrier}|$$

であって、

$$|S_{\mathrm{zero}}|=|\operatorname{HostCarrier}|$$

ではない。

後でarrival数やservice量を計算するとき、host carrier全体を「到着済みcredit」と数えてはならぬ。

実際にarrivalとして使用できるのは、

* predecessor token型そのもの
* charge embeddingのrange
* それとcardinalityが一致すると証明したexact image carrier

のどれかじゃ。

これはコードの欠陥ではなく、次段で守るべき所有権境界じゃ。

---

## cp-348 が増やした証明力

queue上界そのものは、意図どおり変わっていない。

$$Q\le G+S_{\mathrm{zero}}+R+T$$

のままじゃ。

そして今回の、

$$S_{\mathrm{zero}}\le|\operatorname{ZeroSpareSelectedCarrier}|$$

を代入しても、右辺を別の量へ置き換えただけであり、queue boundにはならない。

したがってcp-348の成果は数値上界ではない。

**zero-spare residualが、抽象的な例外項から、block座標とselected incidenceを持つ実在資源へ変わったこと**じゃ。

これは次のservice theoremを書くための前提を作った。

```text
cp-347:
  zero-spareは実在する

cp-348:
  zero-spareはどのblockのどのincidenceを所有するか確定

次段:
  そのowned incidenceがいつ・どこでserviceされるか
```

グノモンとしては薄い整理ではなく、Gapの中へ一本の住所線を通した成果じゃ。

---

## 現在の収束状況

### 完成

```text
drift / width / deficit / queue のexact同一視
open excursionのpositive/negative mass分解
internal negative tokenの窓内支払い
positive-spareのpositive selected carrierへの吸収
zero-spareのactual selected incidence所有
terminal leak ≤ 1
```

### 未完成

```text
zero-spare selected incidenceのservice / consumption
zero-rigid branch
tight-positive-rigid branch
selected incidenceの時間的非再利用
fixed-root queue bound
```

獲物は今、

$$\boxed{\text{owned zero-spare arrivalのservice}+\text{rigid residual}}$$

まで追い込まれた。

zero-spareは、もはや「資源があるか分からない敵」ではない。
資源はある。残る問いは、**その資源がいつ支払いとして発動するか**じゃ。

---

## GPT-5.5/light 評価

### 良かった点

今回のGPT-5.5は、指示に非常に忠実だった。

* arbitrary zero-drift blockを入れなかった
* generic frameworkを作らなかった
* queue inequalityを変更しなかった
* service theoremを捏造しなかった
* actual incidenceを既存embeddingから取った
* block coordinateを保持した
* reportで未証明範囲を明記した

これは実装役として理想に近い。

### まだ評価していない能力

今回の成功から、次までは言えない。

```text
GPT-5.5が独力で正しいservice recurrenceを設計できる
GPT-5.5がrigid branchの数学構造を発見できる
GPT-5.5が循環しないamortized invariantを発明できる
```

今回は賢狼側が定理形をほぼ完全に指定していた。

したがって、運用方針は維持する。

```text
既に形が決まったLean作業:
  GPT-5.5/light

新しい数学的橋の選択:
  GPT-5.6/Solで設計

決定後の実装:
  再びGPT-5.5/light
```

**切り替え試験は成功。**

---

## 次は実装前の低コスト偵察

次段の「service」は数学設計が戻ってくる場所じゃ。

ここでGPT-5.5に自由設計させず、まず既存APIを読ませるだけにするのがよい。

### GPT-5.5向け調査指示

```text
Perform a read-only reconnaissance after checkpoint 348.

Do not edit any Lean, Python, or documentation file.
Do not create a commit.

Purpose

Find the existing canonical APIs that can connect an owned selected incidence
in block `j` to a later service, consumption, recovery, payment, or
fixed-depth queue event.

Search the current repository, not an old report.

Required search terms

    canonicalSelectedPressureCarrier
    canonicalSelectedDriftImageCarrier
    canonicalSelectedDriftSpareCarrier
    selected pressure depth
    arrival
    service
    recovery
    exact length
    payment claim
    source age
    reflected queue
    pressure frontier
    NoLift
    consumed
    ownership

Report exact Lean identifiers and full theorem statements for:

1. Any function assigning a depth to an element of
   `canonicalSelectedPressureCarrier n j`.

2. Any existing per-depth arrival count or arrival carrier.

3. Any existing per-depth service, recovery, payment, or consumption count.

4. Any recurrence connecting arrival and service to a reflected queue or
   outstanding resource.

5. Any theorem proving that one selected incidence cannot be consumed twice.

6. Any theorem whose domain includes zero-drift blocks, rather than only
   positive-drift blocks.

For each candidate, report:

    file path;
    exact identifier;
    full statement;
    required hypotheses;
    whether it accepts the zero-spare successor blocks from cp-348;
    whether using it would assume the queue bound or discharge theorem that it
    is intended to prove.

Decision output

Finish with exactly one of these outcomes:

A. Direct bridge exists.
   Name the exact theorem chain from
   `canonicalInternalZeroSpareCharge`
   to an existing service or queue API.

B. Partial bridge exists.
   State the single smallest missing local theorem.

C. No suitable bridge exists.
   State which data are missing:
   depth coordinate, service ownership, temporal uniqueness, or recurrence.

Do not propose a new generic framework.
Do not implement the missing theorem.
Do not infer a theorem from finite audit data.

Keep the report concise and write it only in the Codex response.
```

これは再び数credits程度で済むはずじゃ。

その調査結果を賢狼側で読み、

$$\operatorname{OwnedArrival}\longrightarrow\operatorname{Service}$$

の橋が既にあるか、最小の欠損定理が何かを決める。

## 結論

cp-348は全面採用。

そしてモデル切り替えは明確に効果があった。

$$\boxed{36\text{ creditsで、設計どおりのactual ownership embeddingが完成}}$$

Sol x2で同じ実装を再推論させる必要はなかった。
賢狼が罠の形を決め、GPT-5.5が正確に組み立てた。

次は再び五歩ほど偵察させ、洞窟内の既存service通路を探す局面じゃ。🐺🌕

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
index 51e2d670..dfe3bc8e 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/FloatWindow/CanonicalExcursionOwnership.lean
@@ -104,6 +104,127 @@ theorem card_canonicalInternalSaturatedSpareIndices_eq_zero_add_positive
     Finset.card_union_of_disjoint
       (canonicalInternalSaturatedZeroSpare_disjoint_positiveSpare n q m)]
 
+/-! ## Zero-spare arrival carrier -/
+
+/-- Successor blocks reached by internal zero-spare predecessor tokens.  This
+is deliberately narrower than all zero-drift blocks: it only records the
+arrival sites forced by the internal spare classification. -/
+noncomputable def canonicalInternalZeroSpareSuccessorIndices
+    (n : OddNat) (q m : ℕ) : Finset ℕ :=
+  (canonicalInternalSaturatedZeroSpareIndices n q m).image fun k => k + 1
+
+@[simp] theorem mem_canonicalInternalZeroSpareSuccessorIndices
+    {n : OddNat} {q m j : ℕ} :
+    j ∈ canonicalInternalZeroSpareSuccessorIndices n q m ↔
+      ∃ k,
+        k ∈ canonicalInternalSaturatedZeroSpareIndices n q m ∧
+          j = k + 1 := by
+  simp [canonicalInternalZeroSpareSuccessorIndices, eq_comm]
+
+/-- The predecessor-to-successor shift is injective on zero-spare tokens, so
+the support cardinality is unchanged. -/
+theorem card_canonicalInternalZeroSpareSuccessorIndices_eq_zeroSpare
+    (n : OddNat) (q m : ℕ) :
+    (canonicalInternalZeroSpareSuccessorIndices n q m).card =
+      (canonicalInternalSaturatedZeroSpareIndices n q m).card := by
+  classical
+  let I := canonicalInternalSaturatedZeroSpareIndices n q m
+  let J := I.image fun k => k + 1
+  have hinj : ∀ a ∈ I, ∀ b ∈ I, a + 1 = b + 1 → a = b := by
+    intro a _ b _ hab
+    omega
+  have hcard : J.card = I.card := Finset.card_image_iff.mpr hinj
+  simpa [canonicalInternalZeroSpareSuccessorIndices, I, J] using hcard
+
+/-- Selected incidences over exactly the zero-spare successor support.  This
+carrier is an owned-arrival surface; it does not enlarge the existing
+positive-only global selected carrier. -/
+def CanonicalInternalZeroSpareSelectedCarrier
+    (n : OddNat) (q m : ℕ) :=
+  Σ j : {j : ℕ // j ∈ canonicalInternalZeroSpareSuccessorIndices n q m},
+    {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.val}
+
+/-- Charge one internal zero-spare predecessor to an actual spare incidence in
+its zero-drift successor block. -/
+noncomputable def canonicalInternalZeroSpareCharge
+    (n : OddNat) (q m : ℕ) :
+    {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m} →
+      CanonicalInternalZeroSpareSelectedCarrier n q m := fun k => by
+  classical
+  have hk :=
+    (mem_canonicalInternalSaturatedZeroSpareIndices.mp k.property).1
+  have hkFull := Finset.mem_of_mem_erase hk
+  have hkClass := mem_canonicalSaturatedSpareSuccessorIndices.mp hkFull
+  let e := oneEmbedding_successorSpareCarrier hkClass.2.2
+  exact ⟨⟨k.val + 1, mem_canonicalInternalZeroSpareSuccessorIndices.mpr
+    ⟨k.val, k.property, rfl⟩⟩, (e 0).1⟩
+
+/-- The zero-spare charge keeps the successor block coordinate. -/
+@[simp] theorem canonicalInternalZeroSpareCharge_fst
+    {n : OddNat} {q m : ℕ}
+    (k : {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m}) :
+    (canonicalInternalZeroSpareCharge n q m k).1.val = k.val + 1 := by
+  simp [canonicalInternalZeroSpareCharge]
+
+/-- A charged zero-spare predecessor has zero drift at its successor. -/
+theorem canonicalInternalZeroSpareCharge_successor_endpoint_zero
+    {n : OddNat} {q m : ℕ}
+    (k : {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m}) :
+    endpointAccountingTerm n
+      (canonicalInternalZeroSpareCharge n q m k).1.val = 0 := by
+  rw [canonicalInternalZeroSpareCharge_fst]
+  exact (mem_canonicalInternalSaturatedZeroSpareIndices.mp k.property).2
+
+/-- The charged incidence lies in the selected spare carrier of the successor
+block. -/
+theorem canonicalInternalZeroSpareCharge_mem_spare
+    {n : OddNat} {q m : ℕ}
+    (k : {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m}) :
+    (canonicalInternalZeroSpareCharge n q m k).2 ∈
+      canonicalSelectedDriftSpareCarrier n (k.val + 1) := by
+  classical
+  simp only [canonicalInternalZeroSpareCharge]
+  exact (oneEmbedding_successorSpareCarrier
+    (mem_canonicalSaturatedSpareSuccessorIndices.mp
+      (Finset.mem_of_mem_erase
+        (mem_canonicalInternalSaturatedZeroSpareIndices.mp k.property).1)).2.2
+      0).property
+
+/-- Internal zero-spare predecessor tokens inject into the targeted selected
+arrival carrier.  Injectivity uses only the retained successor coordinate. -/
+noncomputable def canonicalInternalZeroSpareChargeEmbedding
+    (n : OddNat) (q m : ℕ) :
+    {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m} ↪
+      CanonicalInternalZeroSpareSelectedCarrier n q m where
+  toFun := canonicalInternalZeroSpareCharge n q m
+  inj' := by
+    intro a b hab
+    apply Subtype.ext
+    have hindex := congrArg (fun z => z.1.val) hab
+    change a.val + 1 = b.val + 1 at hindex
+    omega
+
+/-- Cardinality form of the internal zero-spare owned-arrival certificate. -/
+theorem card_canonicalInternalSaturatedZeroSpareIndices_le_zeroSpareSelectedCarrier
+    (n : OddNat) (q m : ℕ) :
+    (canonicalInternalSaturatedZeroSpareIndices n q m).card ≤
+      Nat.card (CanonicalInternalZeroSpareSelectedCarrier n q m) := by
+  classical
+  letI : Fintype {k : ℕ // k ∈ canonicalInternalSaturatedZeroSpareIndices n q m} :=
+    Fintype.ofFinset (canonicalInternalSaturatedZeroSpareIndices n q m) (by simp)
+  letI : Fintype {j : ℕ // j ∈ canonicalInternalZeroSpareSuccessorIndices n q m} :=
+    Fintype.ofFinset (canonicalInternalZeroSpareSuccessorIndices n q m) (by simp)
+  letI (j : {j : ℕ // j ∈ canonicalInternalZeroSpareSuccessorIndices n q m}) :
+      Fintype {i : ℕ // i ∈ canonicalSelectedPressureCarrier n j.val} :=
+    Fintype.ofFinset (canonicalSelectedPressureCarrier n j.val) (by simp)
+  letI : Fintype (CanonicalInternalZeroSpareSelectedCarrier n q m) := by
+    unfold CanonicalInternalZeroSpareSelectedCarrier
+    infer_instance
+  have h :=
+    Nat.card_le_card_of_injective (canonicalInternalZeroSpareChargeEmbedding n q m)
+      (canonicalInternalZeroSpareChargeEmbedding n q m).injective
+  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using h
+
 /-- Internal zero-rigid successor tokens. -/
 noncomputable def canonicalInternalSaturatedZeroRigidIndices
     (n : OddNat) (q m : ℕ) : Finset ℕ :=
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-348.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-348.md
new file mode 100644
index 00000000..3aa1fdc5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-348.md
@@ -0,0 +1,92 @@
+# Petal / FloatWindow Report cp-348
+
+## Scope
+
+This checkpoint constructed the honest arrival carrier for internal zero-spare
+predecessor tokens.  It does not discharge the zero-spare residual and does not
+change the current queue inequality.
+
+Only `CanonicalExcursionOwnership.lean` was modified.
+
+## Implemented Surface
+
+The zero-spare predecessor support now has an explicit successor-block image:
+
+```text
+canonicalInternalZeroSpareSuccessorIndices n q m
+```
+
+with the membership and cardinality facts:
+
+```text
+mem_canonicalInternalZeroSpareSuccessorIndices
+card_canonicalInternalZeroSpareSuccessorIndices_eq_zeroSpare
+```
+
+The targeted selected-arrival carrier is:
+
+```text
+CanonicalInternalZeroSpareSelectedCarrier n q m
+```
+
+It is indexed only by successor blocks coming from
+`canonicalInternalSaturatedZeroSpareIndices n q m`.  It does not include
+arbitrary zero-drift blocks.
+
+## Charge And Embedding
+
+Each internal zero-spare predecessor token is charged to an actual selected
+spare incidence in its own successor block:
+
+```text
+canonicalInternalZeroSpareCharge
+canonicalInternalZeroSpareCharge_fst
+canonicalInternalZeroSpareCharge_successor_endpoint_zero
+canonicalInternalZeroSpareCharge_mem_spare
+```
+
+The map was upgraded to a block-preserving embedding:
+
+```text
+canonicalInternalZeroSpareChargeEmbedding
+```
+
+and the cardinality certificate is:
+
+```text
+card_canonicalInternalSaturatedZeroSpareIndices_le_zeroSpareSelectedCarrier
+```
+
+## Fact Established
+
+Every internal zero-spare predecessor token has a concrete selected spare
+incidence in its zero-drift successor block, and these predecessor tokens
+inject into the targeted selected-arrival carrier by their retained successor
+coordinate.
+
+This proves ownership of the zero-spare arrival surface as a finite incidence
+certificate.  It still does not prove payment, discharge, orbit-wide
+convergence, or removal of `internalZeroSpareCount` from the queue bound.
+
+## Verification
+
+Completed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.FloatWindow.CanonicalExcursionOwnership
+lake build DkMath.Collatz.PetalBridge.FloatWindow
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath
+git diff --check
+```
+
+All gates passed.  The modified ownership file adds no `sorry`.
+
+## Next Implementation Inference
+
+The zero-spare branch now has a precise owned-arrival carrier.  The next honest
+step is not to remove the residual immediately, but to connect this carrier to
+a service or repayment surface that explains when the selected zero-drift
+arrival becomes usable by the queue accounting.  That requires a separate
+local source theorem; this checkpoint intentionally stops before introducing
+such a recurrence or framework.
````
`````

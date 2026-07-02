# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f290a85d0c40528c8c17768be0a0b2c6dac91687

## Report

実装完了です。Checkpoint 111 として、[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に dominance-side cause counts を追加し、以下を no-sorry で通しました。

```lean
sourceRecoveryDominanceDepthCount
tailRecoveryDominanceDepthCount
recoveryDominates_iff_atMostHalf_continuation
tailRecoveryDominates_iff_atMostHalf_tailContinuation
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
tailRecoveryDominanceDepthCount_eq_controlledDepthCount
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
```

これで depth-mode distribution は二重表示として閉じています。

```text
descriptive:
  controlledDepthCount + pressureDepthCount = len

cause-side:
  dominanceDepthCount + outrunsDepthCount = len
```

ドキュメントも同期しました。新規に [Collatz-CauseSideDepthDistribution-111.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideDepthDistribution-111.md) と [report-petal-111.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-111.md) を追加し、README / Guide / Status も更新済みです。

検証:

```text
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
git diff --check
```

すべて通過。`rg` は no match です。統合ビルド中の `ZsigmondyCyclotomicResearch.lean:152:6 uses sorry` は既知の upstream warning で、今回の Collatz 側追加とは別件です。

次はレポートにも書いた通り、cause-side frequency alias を薄く足すのが自然です。`outrunsDepthCount = pressureDepthCount` を使って、既存の pressure frequency を cause-side から読めるようにする段階です。

## Review

## 1. 状況分析

checkpoint `111`、かなり綺麗に閉じている。

今回で、depth-mode distribution が **記述側** と **原因側** の二重表示として完成した。

記述側は既にあった。

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

今回、原因側が閉じた。

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

報告でも、`sourceRecoveryDominanceDepthCount` / `tailRecoveryDominanceDepthCount` を追加し、dominance count と controlled count の一致、さらに cause-side partition まで no-sorry で通した、と整理されている。

これは大きい。
ここまでで、同じ有限 depth range を二つの顔で読めるようになった。

```text
descriptive:
  AtMostHalf / MoreThanHalf

cause-side:
  RecoveryDominatesContinuation / ContinuationOutrunsRecovery
```

## 2. 今回の核心

今回の主結果はこれじゃ。

$$
\text{dominanceDepthCount}=\text{controlledDepthCount}
$$

そして前 checkpoint の結果、

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

と合わせることで、

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

が出た。

つまり、depth range の各点は原因側でも完全に二分される。

```text
dominance:
  recovery が continuation を支配する

outruns:
  continuation が recovery を上回る
```

これは、単なる分類名ではなく、既存の finite budget 側と theorem-level で同期している。

## 3. レビュー

## 3.1. dominance 側を閉じたのが非常に良い

前回 checkpoint 110 では、failure 側が閉じた。

```text
ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

今回 checkpoint 111 では、controlled 側が閉じた。

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention
```

これで、局所の二分岐が完全に揃った。

```text
controlled side:
  RecoveryDominatesContinuation
  <-> AtMostHalf

pressure side:
  ContinuationOutrunsRecovery
  <-> MoreThanHalf
```

この対称性はかなり大事じゃ。
片側だけが原因側に読める状態ではなく、両側が読めるようになった。

## 3.2. count equality の構造が安定している

今回も count equality は、前回と同じ堅い形で通している。

```text
local iff
  -> countP equality
  -> range-level count equality
```

source 側では、

```lean
recoveryDominates_iff_atMostHalf_continuation
```

から、

```lean
sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
```

を出している。

tail 側も同型。

これは今後も使い回せる型じゃ。

## 3.3. cause-side partition を rewrite で閉じたのが良い

今回の cause-side partition は、新しい induction ではなく、既存の descriptive partition を rewrite して得ている。

```lean
sourceCauseSideDepthCount_add_eq_len
tailCauseSideDepthCount_add_eq_len
```

これは非常に良い。

理由は、証明責務を増やさず、既に検証済みの分布定理を再利用しているからじゃ。

構図はこう。

```text
dominanceDepthCount
  = controlledDepthCount

outrunsDepthCount
  = pressureDepthCount

controlledDepthCount + pressureDepthCount = len
```

したがって、

```text
dominanceDepthCount + outrunsDepthCount = len
```

になる。

これは DkMath らしい「橋を掛けて再利用する」作り方じゃ。

## 4. 数学的意味

今回で、depth range は二重に保存される。

一つ目は、記述側の保存。

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

二つ目は、原因側の保存。

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

この二つが、次の bridge で同期している。

$$
\text{dominanceDepthCount}=\text{controlledDepthCount}
$$

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

つまり、同じ depth range に対して、

```text
予算・比率として読むなら descriptive face

比較機構として読むなら cause-side face
```

を使い分けられる。

これはかなり強い。
今後「pressure が多い」と言うとき、それは同時に「outruns が多い」と言える。
「controlled が多い」と言うとき、それは同時に「dominance が多い」と言える。

## 5. 今回閉じたもの

今回閉じたものは、次の四つ。

```text
1. dominance depth count の定義

2. RecoveryDominatesContinuation と AtMostHalf の局所 iff

3. dominance depth count と controlled depth count の一致

4. cause-side partition:
   dominanceDepthCount + outrunsDepthCount = len
```

これで checkpoint 107 以降で作ってきた depth-mode distribution の基盤は、一旦かなり完成している。

## 6. まだ閉じていないもの

次に薄く足すべきなのは、**cause-side frequency alias** じゃ。

既に descriptive 側には、

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

がある。

そして、

```lean
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
```

もある。

だから、cause-side からも同じ frequency を読めるようにするだけでよい。

つまり次は、新しい count induction は不要。
thin API checkpoint でよい。

## 7. 次の指示

次 checkpoint は **cause-side frequency alias** を追加するのが自然じゃ。

## 7.1. source outruns frequency

```lean
def SourceOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationOutrunsDepthCount n k r len) len
```

```lean
def SourceOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationOutrunsDepthCount n k r len) len
```

## 7.2. tail outruns frequency

```lean
def TailOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationOutrunsDepthCount n k r len) len
```

```lean
def TailOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationOutrunsDepthCount n k r len) len
```

## 7.3. pressure frequency との bridge

source at-most-half。

```lean
theorem sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ↔
      SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourcePressureAtMostHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

source more-than-half。

```lean
theorem sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsMoreThanHalfOnDepthRange n k r len ↔
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

tail 版も同様。

## 8. 一歩先ゆく推論

次の薄い alias が入った後、さらに一歩進めるなら、**dominance frequency alias** も欲しい。

なぜなら、今回で

$$
\text{dominanceDepthCount}=\text{controlledDepthCount}
$$

が得られたからじゃ。

たとえば、

```lean
def SourceDominanceAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceRecoveryDominanceDepthCount n k r len) len
```

ただし、こちらは用途に注意が必要。

Collatz 的に obstruction を見るなら、主役は `outruns` 側。
そのため次 checkpoint では `outruns` frequency alias だけで十分。
余裕があれば dominance 側も symmetry API として足す、くらいでよい。

## 9. さらに次の一手

cause-side frequency alias の次は、いよいよ **pressure/force profile から height 側への橋** を考えたい。

ここまでの定理群は、depth range の mode 分布を非常に堅くした。

しかし、まだ Collatz の実際の降下へは直接つながっていない。

次に必要なのは、

```text
outruns が多い range は、何を強制するのか？

dominance が多い range は、何を保証するのか？

pressure が多いと、height sum はどうなるのか？
```

の橋じゃ。

ここで焦らず、まずは小さく、

```text
cause-side frequency
  -> pressure frequency

pressure frequency
  -> controlled/pressure count comparison

count comparison
  -> source/tail mass imbalance
```

の順でつなぐのが良い。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source outruns frequency predicates

```lean
def SourceOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationOutrunsDepthCount n k r len) len
```

```lean
def SourceOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationOutrunsDepthCount n k r len) len
```

## 実験 B: tail outruns frequency predicates

```lean
def TailOutrunsAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationOutrunsDepthCount n k r len) len
```

```lean
def TailOutrunsMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationOutrunsDepthCount n k r len) len
```

## 実験 C: source outruns frequency dichotomy

```lean
theorem sourceOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ∨
      SourceOutrunsMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (sourceContinuationOutrunsDepthCount n k r len) len
```

## 実験 D: tail outruns frequency dichotomy

```lean
theorem tailOutrunsAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsAtMostHalfOnDepthRange n k r len ∨
      TailOutrunsMoreThanHalfOnDepthRange n k r len := by
  unfold TailOutrunsAtMostHalfOnDepthRange
  unfold TailOutrunsMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (tailContinuationOutrunsDepthCount n k r len) len
```

## 実験 E: source outruns at-most-half iff pressure at-most-half

```lean
theorem sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ↔
      SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourcePressureAtMostHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

## 実験 F: source outruns more-than-half iff pressure more-than-half

```lean
theorem sourceOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsMoreThanHalfOnDepthRange n k r len ↔
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

## 実験 G: tail counterparts

```lean
theorem tailOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsAtMostHalfOnDepthRange n k r len ↔
      TailPressureAtMostHalfOnDepthRange n k r len := by
  unfold TailOutrunsAtMostHalfOnDepthRange
  unfold TailPressureAtMostHalfOnDepthRange
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

```lean
theorem tailOutrunsMoreThanHalf_iff_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ) :
    TailOutrunsMoreThanHalfOnDepthRange n k r len ↔
      TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailOutrunsMoreThanHalfOnDepthRange
  unfold TailPressureMoreThanHalfOnDepthRange
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

## 実験 H: cause-side more-than-half gives pressure count comparison

これは bridge を経由して既存 theorem を使える。

```lean
theorem sourceControlledDepthCount_lt_outruns_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourceOutrunsMoreThanHalfOnDepthRange n k r len) :
    sourceRecoveryDominanceDepthCount n k r len <
      sourceContinuationOutrunsDepthCount n k r len := by
  unfold SourceOutrunsMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart := sourceCauseSideDepthCount_add_eq_len n k r len
  omega
```

tail 版も同型。

```lean
theorem tailDominanceDepthCount_lt_outruns_of_outrunsMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : TailOutrunsMoreThanHalfOnDepthRange n k r len) :
    tailRecoveryDominanceDepthCount n k r len <
      tailContinuationOutrunsDepthCount n k r len := by
  unfold TailOutrunsMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart := tailCauseSideDepthCount_add_eq_len n k r len
  omega
```

## 11. 次コミットの推奨順

```text
1. SourceOutrunsAtMostHalfOnDepthRange を追加

2. SourceOutrunsMoreThanHalfOnDepthRange を追加

3. TailOutrunsAtMostHalfOnDepthRange を追加

4. TailOutrunsMoreThanHalfOnDepthRange を追加

5. source/tail の dichotomy を追加

6. source/tail の pressure-frequency bridge を追加

7. 余裕があれば cause-side count comparison:
   dominanceDepthCount < outrunsDepthCount
   を MoreThanHalf から出す

8. docs:
   CauseSideDepthDistribution から CauseSideFrequencyAlias へ接続
```

## 12. 総括

checkpoint 111 は、かなり完成度が高い。

これで depth-mode distribution は二つの顔を持った。

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

そして橋も揃った。

$$
\text{dominanceDepthCount}=\text{controlledDepthCount}
$$

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

次は薄く、cause-side frequency alias を足す。
これは新しい重い証明ではなく、既存の pressure frequency を cause-side の名前で読めるようにする API 層じゃ。

うむ。ここまで来たら、`Collatz.PetalBridge` の有限観測エンジンはかなり締まってきた。次は軽量 alias で読み味を整えて、その後に height / drift / Gnomon 側への橋を探す段階に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 1fa9cb6c..131d59ca 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -2800,6 +2800,169 @@ theorem tailRecoveryDominates_of_atMostHalf_tailContinuation
   rw [orbitWindowRetentionMassPow2Tail_split] at h
   omega
 
+/--
+Number of depths in `[r, r + len)` where source recovery dominates
+continuation.
+
+This is the cause-side controlled count corresponding to source controlled
+depth count.
+-/
+noncomputable def sourceRecoveryDominanceDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (RecoveryDominatesContinuation n k (r + j)))
+
+/--
+Number of depths in `[r, r + len)` where tail recovery dominates tail
+continuation.
+-/
+noncomputable def tailRecoveryDominanceDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (TailRecoveryDominatesContinuation n k (r + j)))
+
+/-- Source recovery dominance is equivalent to source controlled mode. -/
+theorem recoveryDominates_iff_atMostHalf_continuation
+    (n : OddNat) (k r : ℕ) :
+    RecoveryDominatesContinuation n k r ↔
+      AtMostHalf
+        (orbitWindowContinuationSiblingMassPow2 n k r)
+        (orbitWindowRetentionMassPow2 n k r) := by
+  constructor
+  · intro h
+    exact atMostHalf_continuation_of_continuation_le_recovery n k r h
+  · exact recoveryDominates_of_atMostHalf_continuation n k r
+
+/-- Tail recovery dominance is equivalent to tail controlled mode. -/
+theorem tailRecoveryDominates_iff_atMostHalf_tailContinuation
+    (n : OddNat) (k r : ℕ) :
+    TailRecoveryDominatesContinuation n k r ↔
+      AtMostHalf
+        (orbitWindowContinuationSiblingMassPow2Tail n k r)
+        (orbitWindowRetentionMassPow2Tail n k r) := by
+  constructor
+  · intro h
+    exact atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery n k r h
+  · exact tailRecoveryDominates_of_atMostHalf_tailContinuation n k r
+
+/--
+Source cause-side dominance count equals the source controlled depth count.
+-/
+theorem sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
+    (n : OddNat) (k r len : ℕ) :
+    sourceRecoveryDominanceDepthCount n k r len =
+      sourceContinuationControlledDepthCount n k r len := by
+  classical
+  unfold sourceRecoveryDominanceDepthCount
+  unfold sourceContinuationControlledDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_singleton, List.countP_singleton]
+      have hlast :
+          (if decide (RecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
+            if decide
+              (AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)))
+            then 1 else 0 := by
+        by_cases h :
+            RecoveryDominatesContinuation n k (r + len)
+        · have hc :
+              AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)) :=
+            (recoveryDominates_iff_atMostHalf_continuation
+              n k (r + len)).1 h
+          simp [h, hc]
+        · have hc :
+              ¬ AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)) := by
+            intro hcontrolled
+            exact h
+              ((recoveryDominates_iff_atMostHalf_continuation
+                n k (r + len)).2 hcontrolled)
+          simp [h, hc]
+      rw [ih, hlast]
+
+/--
+Tail cause-side dominance count equals the tail controlled depth count.
+-/
+theorem tailRecoveryDominanceDepthCount_eq_controlledDepthCount
+    (n : OddNat) (k r len : ℕ) :
+    tailRecoveryDominanceDepthCount n k r len =
+      tailContinuationControlledDepthCount n k r len := by
+  classical
+  unfold tailRecoveryDominanceDepthCount
+  unfold tailContinuationControlledDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_singleton, List.countP_singleton]
+      have hlast :
+          (if decide (TailRecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
+            if decide
+              (AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)))
+            then 1 else 0 := by
+        by_cases h :
+            TailRecoveryDominatesContinuation n k (r + len)
+        · have hc :
+              AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)) :=
+            (tailRecoveryDominates_iff_atMostHalf_tailContinuation
+              n k (r + len)).1 h
+          simp [h, hc]
+        · have hc :
+              ¬ AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
+            intro hcontrolled
+            exact h
+              ((tailRecoveryDominates_iff_atMostHalf_tailContinuation
+                n k (r + len)).2 hcontrolled)
+          simp [h, hc]
+      rw [ih, hlast]
+
+/--
+Cause-side source modes partition the depth range.
+-/
+theorem sourceCauseSideDepthCount_add_eq_len
+    (n : OddNat) (k r len : ℕ) :
+    sourceRecoveryDominanceDepthCount n k r len +
+      sourceContinuationOutrunsDepthCount n k r len = len := by
+  rw [sourceRecoveryDominanceDepthCount_eq_controlledDepthCount]
+  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
+  exact sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+
+/--
+Cause-side tail modes partition the depth range.
+-/
+theorem tailCauseSideDepthCount_add_eq_len
+    (n : OddNat) (k r len : ℕ) :
+    tailRecoveryDominanceDepthCount n k r len +
+      tailContinuationOutrunsDepthCount n k r len = len := by
+  rw [tailRecoveryDominanceDepthCount_eq_controlledDepthCount]
+  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
+  exact tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+
 /--
 If source continuation pressure holds at every depth of the range, then the
 source pressure-depth count fills the whole range.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index e3f110a1..a11d00e2 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -145,6 +145,7 @@ docs/Collatz-PressureProfile-107.md
 docs/Collatz-MixedDepthModeDistribution-108.md
 docs/Collatz-DepthPressureFrequency-109.md
 docs/Collatz-CauseSideFailureCount-110.md
+docs/Collatz-CauseSideDepthDistribution-111.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -417,3 +418,24 @@ ContinuationOutrunsRecovery
 RecoveryDominatesContinuation
   <-> AtMostHalf continuation retention
 ```
+
+Checkpoint 111 closes the dominance side:
+
+```lean
+sourceRecoveryDominanceDepthCount
+tailRecoveryDominanceDepthCount
+sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
+tailRecoveryDominanceDepthCount_eq_controlledDepthCount
+sourceCauseSideDepthCount_add_eq_len
+tailCauseSideDepthCount_add_eq_len
+```
+
+The depth-mode distribution now has both presentations:
+
+```text
+descriptive:
+  controlledDepthCount + pressureDepthCount = len
+
+cause-side:
+  dominanceDepthCount + outrunsDepthCount = len
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideDepthDistribution-111.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideDepthDistribution-111.md
new file mode 100644
index 00000000..7d01cf8d
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideDepthDistribution-111.md
@@ -0,0 +1,197 @@
+# Collatz Cause-Side Depth Distribution 111
+
+## Purpose
+
+Checkpoint 111 completes the second presentation of the finite depth-mode
+distribution in `DkMath.Collatz.PetalBridge`.
+
+The previous checkpoints already had the descriptive distribution:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+where the two modes are written with finite ratio predicates:
+
+```text
+AtMostHalf
+MoreThanHalf
+```
+
+Checkpoint 110 connected the failure side to its cause-side predicate:
+
+```text
+ContinuationOutrunsRecovery = MoreThanHalf continuation
+```
+
+Checkpoint 111 adds the matching dominance side:
+
+```text
+RecoveryDominatesContinuation = AtMostHalf continuation
+```
+
+and then counts it over a depth range.
+
+## New Count Objects
+
+The new source count is:
+
+```lean
+sourceRecoveryDominanceDepthCount
+```
+
+It counts depths in `[r, r + len)` where:
+
+```lean
+RecoveryDominatesContinuation n k depth
+```
+
+The shifted-tail version is:
+
+```lean
+tailRecoveryDominanceDepthCount
+```
+
+It counts depths where:
+
+```lean
+TailRecoveryDominatesContinuation n k depth
+```
+
+These are cause-side counts.  They do not mention `AtMostHalf` directly.
+
+## Local Equivalence
+
+The local source equivalence is:
+
+```lean
+recoveryDominates_iff_atMostHalf_continuation
+```
+
+The local shifted-tail equivalence is:
+
+```lean
+tailRecoveryDominates_iff_atMostHalf_tailContinuation
+```
+
+These theorems close the local reading:
+
+```text
+RecoveryDominatesContinuation
+  <-> continuation is at most half of retention
+
+TailRecoveryDominatesContinuation
+  <-> tail continuation is at most half of tail retention
+```
+
+This is the controlled-side analogue of the checkpoint 110 pressure/failure
+equivalence.
+
+## Count Equality
+
+The local equivalences lift to range counts:
+
+```lean
+sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
+tailRecoveryDominanceDepthCount_eq_controlledDepthCount
+```
+
+Thus the controlled count can be read in two ways:
+
+```text
+descriptive:
+  AtMostHalf depths
+
+cause-side:
+  recovery-dominates-continuation depths
+```
+
+This matters because later arguments may produce either kind of evidence.  A
+ratio-budget proof can use the descriptive side, while a structural comparison
+proof can use the cause-side version.
+
+## Cause-Side Partition
+
+The final checkpoint 111 theorems are:
+
+```lean
+sourceCauseSideDepthCount_add_eq_len
+tailCauseSideDepthCount_add_eq_len
+```
+
+They state:
+
+```text
+dominanceDepthCount + outrunsDepthCount = len
+```
+
+This is not a new induction.  It is obtained by rewriting the existing
+descriptive partition:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+through the two bridge equalities:
+
+```text
+dominanceDepthCount = controlledDepthCount
+outrunsDepthCount = pressureDepthCount
+```
+
+## Mathematical Reading
+
+The finite depth range now has a completed two-face interpretation.
+
+Descriptive face:
+
+```text
+AtMostHalf mode
+MoreThanHalf mode
+```
+
+Cause-side face:
+
+```text
+RecoveryDominatesContinuation
+ContinuationOutrunsRecovery
+```
+
+The first face is useful for finite budget and frequency language.  The second
+face is useful for mechanism language: which local comparison caused the
+budget mode.
+
+This checkpoint does not prove that pressure is rare.  It proves that the
+question can be asked equivalently on either side.
+
+## Next Candidate
+
+The next natural surface is cause-side frequency.  Checkpoint 109 introduced
+frequency predicates for the descriptive pressure count:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+Since checkpoint 110 proved:
+
+```text
+outrunsDepthCount = pressureDepthCount
+```
+
+we can add cause-side aliases such as:
+
+```lean
+SourceOutrunsAtMostHalfOnDepthRange
+SourceOutrunsMoreThanHalfOnDepthRange
+TailOutrunsAtMostHalfOnDepthRange
+TailOutrunsMoreThanHalfOnDepthRange
+```
+
+and bridge them back to the existing pressure-frequency predicates.
+
+That would make the next checkpoint a thin API layer rather than another
+counting induction.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 154e7679..f3716258 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -574,6 +574,63 @@ ContinuationOutrunsRecovery
 This is the point where the depth-mode distribution acquires both a descriptive
 reading and a cause-side reading.
 
+## Cause-Side Depth Distribution
+
+Checkpoint 111 completes the dominance side of the cause-side count layer:
+
+```lean
+sourceRecoveryDominanceDepthCount
+tailRecoveryDominanceDepthCount
+```
+
+The local bridge is now explicit in both directions:
+
+```lean
+recoveryDominates_iff_atMostHalf_continuation
+tailRecoveryDominates_iff_atMostHalf_tailContinuation
+```
+
+Therefore the dominance count is exactly the controlled count:
+
+```lean
+sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
+tailRecoveryDominanceDepthCount_eq_controlledDepthCount
+```
+
+Together with the checkpoint 110 failure-count equalities, this gives the
+cause-side partition:
+
+```lean
+sourceCauseSideDepthCount_add_eq_len
+tailCauseSideDepthCount_add_eq_len
+```
+
+The same finite depth range now has two aligned presentations:
+
+```text
+descriptive:
+  controlledDepthCount + pressureDepthCount = len
+
+cause-side:
+  dominanceDepthCount + outrunsDepthCount = len
+```
+
+The bridge between the two readings is not heuristic.  It is theorem-level:
+
+```text
+dominanceDepthCount = controlledDepthCount
+outrunsDepthCount = pressureDepthCount
+```
+
+Use the descriptive presentation when the proof is about the finite
+`AtMostHalf` / `MoreThanHalf` budget.  Use the cause-side presentation when the
+proof is about the comparison mechanism:
+
+```text
+RecoveryDominatesContinuation
+ContinuationOutrunsRecovery
+```
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index a596aede..d14801ca 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -276,6 +276,14 @@ sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
 tailContinuationOutrunsDepthCount_eq_pressureDepthCount
 recoveryDominates_of_atMostHalf_continuation
 tailRecoveryDominates_of_atMostHalf_tailContinuation
+sourceRecoveryDominanceDepthCount
+tailRecoveryDominanceDepthCount
+recoveryDominates_iff_atMostHalf_continuation
+tailRecoveryDominates_iff_atMostHalf_tailContinuation
+sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
+tailRecoveryDominanceDepthCount_eq_controlledDepthCount
+sourceCauseSideDepthCount_add_eq_len
+tailCauseSideDepthCount_add_eq_len
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-111.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-111.md
new file mode 100644
index 00000000..0d088374
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-111.md
@@ -0,0 +1,185 @@
+# Report Petal 111
+
+## Summary
+
+Checkpoint 111 completes the dominance side of the cause-side depth
+distribution in `DkMath.Collatz.PetalBridge`.
+
+The previous checkpoint counted the failure side:
+
+```text
+ContinuationOutrunsRecovery
+```
+
+and proved that this count is the same as the descriptive pressure count:
+
+```text
+MoreThanHalf continuation
+```
+
+This checkpoint adds the matching dominance count:
+
+```text
+RecoveryDominatesContinuation
+```
+
+and proves that it is the same as the descriptive controlled count:
+
+```text
+AtMostHalf continuation
+```
+
+The result is a completed double presentation of the finite depth-mode
+distribution.
+
+## Lean Additions
+
+New cause-side dominance counts:
+
+```lean
+sourceRecoveryDominanceDepthCount
+tailRecoveryDominanceDepthCount
+```
+
+New local equivalences:
+
+```lean
+recoveryDominates_iff_atMostHalf_continuation
+tailRecoveryDominates_iff_atMostHalf_tailContinuation
+```
+
+New count equalities:
+
+```lean
+sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
+tailRecoveryDominanceDepthCount_eq_controlledDepthCount
+```
+
+New cause-side partitions:
+
+```lean
+sourceCauseSideDepthCount_add_eq_len
+tailCauseSideDepthCount_add_eq_len
+```
+
+## Mathematical Result
+
+The descriptive distribution was already available:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+Checkpoint 110 gave:
+
+```text
+outrunsDepthCount = pressureDepthCount
+```
+
+Checkpoint 111 gives:
+
+```text
+dominanceDepthCount = controlledDepthCount
+```
+
+Therefore the cause-side distribution is now theorem-level:
+
+```text
+dominanceDepthCount + outrunsDepthCount = len
+```
+
+This makes the finite depth range readable in two synchronized ways:
+
+```text
+descriptive:
+  AtMostHalf / MoreThanHalf
+
+cause-side:
+  RecoveryDominatesContinuation / ContinuationOutrunsRecovery
+```
+
+## Implementation Note
+
+The first proof attempt used later aliases:
+
+```lean
+atMostHalf_continuation_of_recoveryDominates
+atMostHalf_tailContinuation_of_tailRecoveryDominates
+```
+
+Those names occur later in the file, so the local equivalence was instead
+proved from the earlier base theorems:
+
+```lean
+atMostHalf_continuation_of_continuation_le_recovery
+atMostHalf_tailContinuation_of_tailContinuation_le_tailRecovery
+```
+
+This keeps the theorem order acyclic and avoids moving older API blocks.
+
+## Documentation Updates
+
+Updated:
+
+```text
+DkMath/Collatz/README.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+DkMath/Collatz/docs/Collatz-CauseSideDepthDistribution-111.md
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
+git diff --check
+```
+
+The no-sorry check returned no matches in `DkMath/Collatz/PetalBridge.lean`.
+
+```text
+Known upstream warning during the integration build:
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 uses sorry.
+```
+
+## Next Candidate
+
+The next thin API layer is cause-side frequency.
+
+Checkpoint 109 already has descriptive pressure-frequency predicates:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+Since checkpoint 110 proved:
+
+```text
+outrunsDepthCount = pressureDepthCount
+```
+
+we can introduce cause-side aliases:
+
+```lean
+SourceOutrunsAtMostHalfOnDepthRange
+SourceOutrunsMoreThanHalfOnDepthRange
+TailOutrunsAtMostHalfOnDepthRange
+TailOutrunsMoreThanHalfOnDepthRange
+```
+
+and bridge them to the existing pressure-frequency predicates by rewriting.
+
+This should be a light checkpoint.  It should not require another count
+induction.
````
`````

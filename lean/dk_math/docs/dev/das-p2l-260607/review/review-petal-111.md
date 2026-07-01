# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: b14f95bb037b183284b0ee1e3113d2756ccd5170

## Report

110 チェックポイント完了です。

`DkMath.Collatz.PetalBridge` に cause-side failure count 層を追加しました。主な追加は以下です。

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
continuationOutruns_iff_moreThanHalf_continuation
tailContinuationOutruns_iff_moreThanHalf_tailContinuation
sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
tailContinuationOutrunsDepthCount_eq_pressureDepthCount
recoveryDominates_of_atMostHalf_continuation
tailRecoveryDominates_of_atMostHalf_tailContinuation
```

これで、

```text
pressure depth count = continuation outruns depth count
```

が source/tail ともに no-sorry で閉じました。pressure count は単なる記述側の `MoreThanHalf` count ではなく、原因側の `ContinuationOutrunsRecovery` count として読めます。

さらに追加実験として、controlled 側の逆向きも通りました。

```text
AtMostHalf continuation retention -> RecoveryDominatesContinuation
```

既存の forward と合わせて、局所的には source/tail ともに次が揃いました。

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

文書も同期済みです。

- [Collatz-CauseSideFailureCount-110.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFailureCount-110.md)
- [report-petal-110.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-110.md)
- README / Guide / Status も 110 の theorem 名と解説を反映済み

検証結果:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

次は dominance-side count です。`sourceRecoveryDominanceDepthCount = sourceContinuationControlledDepthCount` と tail 版を閉じれば、原因側分布と記述側分布の二重表示が完成します。

## Review

## 1. 状況分析

よし、作業本線に戻る。今回の `review-petal-111.md` は、内容としては **checkpoint 110: cause-side failure count** の完了報告じゃ。

今回の到達点はかなり大きい。

$$
\text{sourceContinuationOutrunsDepthCount}=\text{sourceContinuationPressureDepthCount}
$$

および tail 版が no-sorry で閉じた。つまり、これまで「記述側」の `MoreThanHalf` pressure として数えていた depth count が、原因側の `ContinuationOutrunsRecovery` count と一致した。報告でも、pressure count は単なる記述側の `MoreThanHalf` count ではなく、原因側の `ContinuationOutrunsRecovery` count として読める、と明確に整理されている。

さらに、controlled 側の逆向きも通った。

```lean
recoveryDominates_of_atMostHalf_continuation
tailRecoveryDominates_of_atMostHalf_tailContinuation
```

これで局所的には source / tail ともに、

$$
\text{RecoveryDominatesContinuation}\leftrightarrow\text{AtMostHalf continuation retention}
$$

$$
\text{ContinuationOutrunsRecovery}\leftrightarrow\text{MoreThanHalf continuation retention}
$$

が読める状態になった。これは、depth-mode distribution が「記述側」と「原因側」の二重表示を持ち始めた、ということじゃ。

## 2. 今回の核心

checkpoint 110 の本質は、次の橋を閉じたこと。

```text
記述側:
  MoreThanHalf continuation retention

原因側:
  ContinuationOutrunsRecovery
```

これまでは pressure は観測された状態だった。

```text
continuation が retention の半分超え
```

しかし今回、その状態は単に見えているだけではなく、

```text
continuation が recovery を上回っている
```

という原因側 predicate と一致することが確認された。

つまり、pressure は「見た目」ではなく「原因」になった。

これが大きい。

## 3. レビュー

## 3.1. cause-side count を入れた判断は正しい

追加された count はこれ。

```lean
sourceContinuationOutrunsDepthCount
tailContinuationOutrunsDepthCount
```

これは、depth range \([r,r+\text{len}\)) の中で、

```lean
ContinuationOutrunsRecovery n k (r + j)
```

が成立する depth を数える。

既存の pressure count は、

```lean
MoreThanHalf
  (orbitWindowContinuationSiblingMassPow2 n k (r + j))
  (orbitWindowRetentionMassPow2 n k (r + j))
```

を数えていた。

今回、この二つが一致した。

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

これにより、pressure count は「半分超えの記録」だけでなく、「recovery を上回った原因側 failure の記録」として読める。

## 3.2. 局所 iff を先に整えたのが良い

今回、

```lean
continuationOutruns_iff_moreThanHalf_continuation
tailContinuationOutruns_iff_moreThanHalf_tailContinuation
```

が入っている。

これは count equality の土台として非常に良い。
`countP` の equality は、最終的には各 \(j\) で predicate が一致することに依存する。

局所 iff を先に置くことで、range count の証明が意味的にも実装的にも読みやすくなった。

## 3.3. `by_cases` で singleton を処理したのも堅い

実装は `len` induction で、successor step の最後の singleton を `by_cases` で処理している。

これは checkpoint 108 と同じ安定パターンじゃ。
`decide` や `countP` の indicator を theorem statement に露出させず、proof body の中で `classical` を有効にして処理する。

今後も `countP` equality 系はこの型で進めるのがよい。

```text
unfold count definitions
induction len
successor step:
  List.range_succ
  List.countP_append
  List.countP_singleton
  by_cases local predicate
```

これは DkMath Collatz count 層の定石になってきた。

## 4. 数学的意味

今回で、depth-mode distribution には二つの読みができた。

まず、記述側。

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

ここでは、

```text
controlled:
  AtMostHalf continuation retention

pressure:
  MoreThanHalf continuation retention
```

と読む。

次に、原因側。

```text
dominance:
  RecoveryDominatesContinuation

failure:
  ContinuationOutrunsRecovery
```

今回閉じたのは、failure 側の一致。

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

つまり、

```text
pressure depth
  =
continuation outruns recovery depth
```

である。

これはかなり重要じゃ。
なぜなら今後、

```text
pressure が多い
```

と言ったとき、それは同時に、

```text
continuation が recovery を上回る depth が多い
```

という意味になるからじゃ。

## 5. 今回閉じたもの

今回閉じたものは、はっきり次の三つ。

```text
1. cause-side failure count の定義

2. local failure mode と pressure mode の iff

3. cause-side failure count と pressure depth count の equality
```

さらに controlled 側についても、局所逆向きが入った。

```lean
AtMostHalf continuation retention
  -> RecoveryDominatesContinuation
```

これにより、次 checkpoint で dominance count equality を閉じる準備が整った。

## 6. まだ閉じていないもの

残っている自然な穴は controlled / dominance 側の range count equality じゃ。

今はまだ、

$$
\text{sourceRecoveryDominanceDepthCount}
$$

が未定義。

これを定義し、

$$
\text{sourceRecoveryDominanceDepthCount}=\text{sourceContinuationControlledDepthCount}
$$

tail 版も同様に閉じる。

これが通ると、完全な二重表示になる。

```text
記述側:
  controlledDepthCount + pressureDepthCount = len

原因側:
  dominanceDepthCount + outrunsDepthCount = len

橋:
  dominanceDepthCount = controlledDepthCount
  outrunsDepthCount = pressureDepthCount
```

ここまで行けば、depth-mode 分布はかなり完成度が高くなる。

## 7. 次の指示

次は **dominance-side cause counts** を実装するのが筋じゃ。

## 7.1. source dominance count

```lean
noncomputable def sourceRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (RecoveryDominatesContinuation n k (r + j)))
```

## 7.2. tail dominance count

```lean
noncomputable def tailRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailRecoveryDominatesContinuation n k (r + j)))
```

## 7.3. local controlled iff

まず source。

```lean
theorem recoveryDominates_iff_atMostHalf_continuation
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · exact atMostHalf_continuation_of_recoveryDominates n k r
  · exact recoveryDominates_of_atMostHalf_continuation n k r
```

tail。

```lean
theorem tailRecoveryDominates_iff_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · exact atMostHalf_tailContinuation_of_tailRecoveryDominates n k r
  · exact tailRecoveryDominates_of_atMostHalf_tailContinuation n k r
```

## 7.4. dominance count equals controlled count

source。

```lean
theorem sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len =
      sourceContinuationControlledDepthCount n k r len := by
  classical
  unfold sourceRecoveryDominanceDepthCount
  unfold sourceContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (RecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
            if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            RecoveryDominatesContinuation n k (r + len)
        · have hc :
              AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) :=
            (recoveryDominates_iff_atMostHalf_continuation
              n k (r + len)).1 h
          simp [h, hc]
        · have hc :
              ¬ AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hcontrolled
            exact h
              ((recoveryDominates_iff_atMostHalf_continuation
                n k (r + len)).2 hcontrolled)
          simp [h, hc]
      rw [ih, hlast]
```

tail 版も同型じゃ。

## 8. 一歩先ゆく推論

dominance equality が通ったら、次は cause-side partition を閉じる。

ただし、これは直接 induction するより、既存定理を使って短く閉じる方が良い。

既存：

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

今回済み：

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

次で得る：

$$
\text{dominanceDepthCount}=\text{controlledDepthCount}
$$

なら、原因側分布は rewrite で出る。

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

source 版の theorem はこう。

```lean
theorem sourceCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len +
      sourceContinuationOutrunsDepthCount n k r len = len := by
  rw [sourceRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
```

tail 版も同様。

これが通ると、cause-side distribution が完成する。

## 9. さらに次の一手

cause-side partition まで閉じたら、次は **cause-side frequency** へ進める。

No.109 では pressure frequency を作った。

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
```

しかし、outruns count と pressure count が一致したので、同じ頻度を cause-side でも読める。

候補：

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

そして、

```lean
theorem sourceOutrunsAtMostHalf_iff_pressureAtMostHalf
    (n : OddNat) (k r len : ℕ) :
    SourceOutrunsAtMostHalfOnDepthRange n k r len ↔
      SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourceOutrunsAtMostHalfOnDepthRange
  unfold SourcePressureAtMostHalfOnDepthRange
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
```

これで、

```text
pressure が多い
```

を、

```text
cause-side failure が多い
```

としてそのまま言える。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source dominance count

```lean
noncomputable def sourceRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (RecoveryDominatesContinuation n k (r + j)))
```

## 実験 B: tail dominance count

```lean
noncomputable def tailRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailRecoveryDominatesContinuation n k (r + j)))
```

## 実験 C: local source controlled iff

```lean
theorem recoveryDominates_iff_atMostHalf_continuation
    (n : OddNat) (k r : ℕ) :
    RecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · exact atMostHalf_continuation_of_recoveryDominates n k r
  · exact recoveryDominates_of_atMostHalf_continuation n k r
```

## 実験 D: local tail controlled iff

```lean
theorem tailRecoveryDominates_iff_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailRecoveryDominatesContinuation n k r ↔
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · exact atMostHalf_tailContinuation_of_tailRecoveryDominates n k r
  · exact tailRecoveryDominates_of_atMostHalf_tailContinuation n k r
```

## 実験 E: source dominance count equals controlled count

```lean
theorem sourceRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len =
      sourceContinuationControlledDepthCount n k r len := by
  classical
  unfold sourceRecoveryDominanceDepthCount
  unfold sourceContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          (if decide (RecoveryDominatesContinuation n k (r + len)) then 1 else 0) =
            if decide
              (AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)))
            then 1 else 0 := by
        by_cases h :
            RecoveryDominatesContinuation n k (r + len)
        · have hc :
              AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) :=
            (recoveryDominates_iff_atMostHalf_continuation
              n k (r + len)).1 h
          simp [h, hc]
        · have hc :
              ¬ AtMostHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len)) := by
            intro hcontrolled
            exact h
              ((recoveryDominates_iff_atMostHalf_continuation
                n k (r + len)).2 hcontrolled)
          simp [h, hc]
      rw [ih, hlast]
```

## 実験 F: tail dominance count equals controlled count

source 版が通ったら tail は同型。

```lean
theorem tailRecoveryDominanceDepthCount_eq_controlledDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailRecoveryDominanceDepthCount n k r len =
      tailContinuationControlledDepthCount n k r len := by
  classical
  unfold tailRecoveryDominanceDepthCount
  unfold tailContinuationControlledDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      -- source と同じ形で local iff を使う
      sorry
```

## 実験 G: source cause-side partition

```lean
theorem sourceCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceRecoveryDominanceDepthCount n k r len +
      sourceContinuationOutrunsDepthCount n k r len = len := by
  rw [sourceRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [sourceContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
```

## 実験 H: tail cause-side partition

```lean
theorem tailCauseSideDepthCount_add_eq_len
    (n : OddNat) (k r len : ℕ) :
    tailRecoveryDominanceDepthCount n k r len +
      tailContinuationOutrunsDepthCount n k r len = len := by
  rw [tailRecoveryDominanceDepthCount_eq_controlledDepthCount]
  rw [tailContinuationOutrunsDepthCount_eq_pressureDepthCount]
  exact tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
```

## 11. 次コミットの推奨順

```text
1. sourceRecoveryDominanceDepthCount を追加

2. tailRecoveryDominanceDepthCount を追加

3. recoveryDominates_iff_atMostHalf_continuation を追加

4. tailRecoveryDominates_iff_atMostHalf_tailContinuation を追加

5. sourceRecoveryDominanceDepthCount_eq_controlledDepthCount を証明

6. tailRecoveryDominanceDepthCount_eq_controlledDepthCount を証明

7. sourceCauseSideDepthCount_add_eq_len を rewrite で証明

8. tailCauseSideDepthCount_add_eq_len を rewrite で証明

9. docs:
   CauseSideFailureCount から CauseSideDepthDistribution へ接続
```

## 12. 総括

checkpoint 110 はかなり良い。
pressure count が、ついに原因側 failure count と一致した。

$$
\text{outrunsDepthCount}=\text{pressureDepthCount}
$$

これで、pressure はただの記述的ラベルではなくなった。
`ContinuationOutrunsRecovery` という原因側の構造そのものになった。

次は controlled 側。

$$
\text{dominanceDepthCount}=\text{controlledDepthCount}
$$

を閉じる。

そのうえで、

$$
\text{dominanceDepthCount}+\text{outrunsDepthCount}=\text{len}
$$

を得れば、depth-mode distribution は完全な二重表示を持つ。

```text
記述側:
  controlled / pressure

原因側:
  dominance / outruns
```

うむ。
ここまで来ると、Collatz.PetalBridge はかなり堅い有限観測エンジンになってきた。次は cause-side distribution を閉じよう。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index d4172051..1fa9cb6c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -2636,6 +2636,170 @@ theorem tailContinuationOutruns_of_moreThanHalf_tailContinuation
   rw [orbitWindowRetentionMassPow2Tail_split] at h
   omega
 
+/--
+Number of depths in `[r, r + len)` where source continuation outruns recovery.
+
+This is the cause-side failure count corresponding to source pressure depth
+count.
+-/
+noncomputable def sourceContinuationOutrunsDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (ContinuationOutrunsRecovery n k (r + j)))
+
+/--
+Number of depths in `[r, r + len)` where tail continuation outruns tail
+recovery.
+-/
+noncomputable def tailContinuationOutrunsDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (TailContinuationOutrunsRecovery n k (r + j)))
+
+/-- Source outruns mode is equivalent to source more-than-half pressure. -/
+theorem continuationOutruns_iff_moreThanHalf_continuation
+    (n : OddNat) (k r : ℕ) :
+    ContinuationOutrunsRecovery n k r ↔
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k r)
+        (orbitWindowRetentionMassPow2 n k r) := by
+  constructor
+  · exact moreThanHalf_continuation_of_continuationOutruns n k r
+  · exact continuationOutruns_of_moreThanHalf_continuation n k r
+
+/-- Tail outruns mode is equivalent to tail more-than-half pressure. -/
+theorem tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+    (n : OddNat) (k r : ℕ) :
+    TailContinuationOutrunsRecovery n k r ↔
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2Tail n k r)
+        (orbitWindowRetentionMassPow2Tail n k r) := by
+  constructor
+  · exact moreThanHalf_tailContinuation_of_tailContinuationOutruns n k r
+  · exact tailContinuationOutruns_of_moreThanHalf_tailContinuation n k r
+
+/--
+Source cause-side outruns count equals the source pressure depth count.
+-/
+theorem sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+    (n : OddNat) (k r len : ℕ) :
+    sourceContinuationOutrunsDepthCount n k r len =
+      sourceContinuationPressureDepthCount n k r len := by
+  classical
+  unfold sourceContinuationOutrunsDepthCount
+  unfold sourceContinuationPressureDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_singleton, List.countP_singleton]
+      have hlast :
+          (if decide (ContinuationOutrunsRecovery n k (r + len)) then 1 else 0) =
+            if decide
+              (MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)))
+            then 1 else 0 := by
+        by_cases h :
+            ContinuationOutrunsRecovery n k (r + len)
+        · have hp :
+              MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)) :=
+            (continuationOutruns_iff_moreThanHalf_continuation
+              n k (r + len)).1 h
+          simp [h, hp]
+        · have hp :
+              ¬ MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)) := by
+            intro hpressure
+            exact h
+              ((continuationOutruns_iff_moreThanHalf_continuation
+                n k (r + len)).2 hpressure)
+          simp [h, hp]
+      rw [ih, hlast]
+
+/--
+Tail cause-side outruns count equals the tail pressure depth count.
+-/
+theorem tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+    (n : OddNat) (k r len : ℕ) :
+    tailContinuationOutrunsDepthCount n k r len =
+      tailContinuationPressureDepthCount n k r len := by
+  classical
+  unfold tailContinuationOutrunsDepthCount
+  unfold tailContinuationPressureDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_singleton, List.countP_singleton]
+      have hlast :
+          (if decide (TailContinuationOutrunsRecovery n k (r + len)) then 1 else 0) =
+            if decide
+              (MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)))
+            then 1 else 0 := by
+        by_cases h :
+            TailContinuationOutrunsRecovery n k (r + len)
+        · have hp :
+              MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)) :=
+            (tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+              n k (r + len)).1 h
+          simp [h, hp]
+        · have hp :
+              ¬ MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
+            intro hpressure
+            exact h
+              ((tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+                n k (r + len)).2 hpressure)
+          simp [h, hp]
+      rw [ih, hlast]
+
+/-- Source controlled mode implies source recovery dominance. -/
+theorem recoveryDominates_of_atMostHalf_continuation
+    (n : OddNat) (k r : ℕ)
+    (h :
+      AtMostHalf
+        (orbitWindowContinuationSiblingMassPow2 n k r)
+        (orbitWindowRetentionMassPow2 n k r)) :
+    RecoveryDominatesContinuation n k r := by
+  unfold AtMostHalf at h
+  unfold RecoveryDominatesContinuation
+  rw [orbitWindowRetentionMass_split] at h
+  omega
+
+/-- Tail controlled mode implies tail recovery dominance. -/
+theorem tailRecoveryDominates_of_atMostHalf_tailContinuation
+    (n : OddNat) (k r : ℕ)
+    (h :
+      AtMostHalf
+        (orbitWindowContinuationSiblingMassPow2Tail n k r)
+        (orbitWindowRetentionMassPow2Tail n k r)) :
+    TailRecoveryDominatesContinuation n k r := by
+  unfold AtMostHalf at h
+  unfold TailRecoveryDominatesContinuation
+  rw [orbitWindowRetentionMassPow2Tail_split] at h
+  omega
+
 /--
 If source continuation pressure holds at every depth of the range, then the
 source pressure-depth count fills the whole range.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 28b88203..e3f110a1 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -144,6 +144,7 @@ docs/Collatz-MoreThanHalfPressure-106.md
 docs/Collatz-PressureProfile-107.md
 docs/Collatz-MixedDepthModeDistribution-108.md
 docs/Collatz-DepthPressureFrequency-109.md
+docs/Collatz-CauseSideFailureCount-110.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -396,3 +397,23 @@ The checkpoint also closes the reverse local direction:
 continuationOutruns_of_moreThanHalf_continuation
 tailContinuationOutruns_of_moreThanHalf_tailContinuation
 ```
+
+Checkpoint 110 connects descriptive pressure counts to cause-side failure
+counts:
+
+```lean
+sourceContinuationOutrunsDepthCount
+tailContinuationOutrunsDepthCount
+sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+```
+
+It also records local equivalences:
+
+```text
+ContinuationOutrunsRecovery
+  <-> MoreThanHalf continuation retention
+
+RecoveryDominatesContinuation
+  <-> AtMostHalf continuation retention
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFailureCount-110.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFailureCount-110.md
new file mode 100644
index 00000000..b1add591
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFailureCount-110.md
@@ -0,0 +1,161 @@
+# Collatz Cause-Side Failure Count 110
+
+## Purpose
+
+Checkpoint 109 made pressure frequency a finite `Nat` statement:
+
+```text
+pressureDepthCount is at most half or more than half of len
+```
+
+Checkpoint 110 connects that descriptive pressure count to the cause-side
+failure predicate:
+
+```text
+ContinuationOutrunsRecovery
+```
+
+The point is to read a pressure count in two ways:
+
+```text
+descriptive side:
+  MoreThanHalf continuation retention
+
+cause side:
+  continuation outruns recovery
+```
+
+## Cause-Side Counts
+
+Source failure count:
+
+```lean
+sourceContinuationOutrunsDepthCount
+```
+
+Tail failure count:
+
+```lean
+tailContinuationOutrunsDepthCount
+```
+
+These count depths in `[r, r + len)` where the cause-side failure predicate
+holds.
+
+## Local Equivalence
+
+Checkpoint 110 records the local equivalences:
+
+```lean
+continuationOutruns_iff_moreThanHalf_continuation
+tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+```
+
+The forward direction was already available from checkpoint 106:
+
+```lean
+moreThanHalf_continuation_of_continuationOutruns
+moreThanHalf_tailContinuation_of_tailContinuationOutruns
+```
+
+The reverse direction was added at checkpoint 109:
+
+```lean
+continuationOutruns_of_moreThanHalf_continuation
+tailContinuationOutruns_of_moreThanHalf_tailContinuation
+```
+
+## Count Equality
+
+The main checkpoint theorem is:
+
+```lean
+sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+```
+
+and the shifted-tail counterpart:
+
+```lean
+tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+```
+
+These say:
+
+```text
+cause-side failure count = descriptive pressure count
+```
+
+for the same finite depth range.
+
+## Controlled-Side Reverse Direction
+
+Checkpoint 110 also adds:
+
+```lean
+recoveryDominates_of_atMostHalf_continuation
+tailRecoveryDominates_of_atMostHalf_tailContinuation
+```
+
+Together with the existing predicate-facing half criteria, the local controlled
+mode is also interderivable:
+
+```text
+RecoveryDominatesContinuation
+  <-> AtMostHalf continuation retention
+```
+
+Thus both branches now have aligned readings:
+
+```text
+controlled:
+  RecoveryDominatesContinuation
+  <-> AtMostHalf continuation retention
+
+pressure:
+  ContinuationOutrunsRecovery
+  <-> MoreThanHalf continuation retention
+```
+
+## Mathematical Reading
+
+The depth-mode distribution now has two synchronized presentations:
+
+```text
+descriptive distribution:
+  controlledDepthCount + pressureDepthCount = len
+
+cause-side distribution:
+  dominanceDepthCount + outrunsDepthCount = len
+```
+
+Checkpoint 110 closes the pressure/outruns side of the bridge:
+
+```text
+outrunsDepthCount = pressureDepthCount
+```
+
+The dominance/controlled count equality is the natural next target.
+
+## Next Candidate
+
+Define dominance depth counts:
+
+```lean
+sourceRecoveryDominanceDepthCount
+tailRecoveryDominanceDepthCount
+```
+
+Then prove:
+
+```text
+sourceRecoveryDominanceDepthCount = sourceContinuationControlledDepthCount
+tailRecoveryDominanceDepthCount = tailContinuationControlledDepthCount
+```
+
+After that, prove the cause-side partition:
+
+```text
+dominanceDepthCount + outrunsDepthCount = len
+```
+
+This would complete the double presentation of the depth-mode distribution.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 0aad1bb9..154e7679 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -528,6 +528,52 @@ Together with the checkpoint 106 forward direction, this means the local
 `MoreThanHalf` pressure mode and the continuation-outruns-recovery mode are now
 interderivable.
 
+## Cause-Side Failure Counts
+
+Checkpoint 110 counts the cause-side failure predicate directly:
+
+```lean
+sourceContinuationOutrunsDepthCount
+tailContinuationOutrunsDepthCount
+```
+
+The bridge to the descriptive pressure count is:
+
+```lean
+sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+```
+
+Thus a pressure depth count can be read as:
+
+```text
+descriptive mode:
+  MoreThanHalf continuation retention
+
+cause-side mode:
+  ContinuationOutrunsRecovery
+```
+
+Checkpoint 110 also adds the controlled-side reverse direction:
+
+```lean
+recoveryDominates_of_atMostHalf_continuation
+tailRecoveryDominates_of_atMostHalf_tailContinuation
+```
+
+Together with the existing forward direction, the local modes now align:
+
+```text
+RecoveryDominatesContinuation
+  <-> AtMostHalf continuation retention
+
+ContinuationOutrunsRecovery
+  <-> MoreThanHalf continuation retention
+```
+
+This is the point where the depth-mode distribution acquires both a descriptive
+reading and a cause-side reading.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index f314b17a..a596aede 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -268,6 +268,14 @@ tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
 tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
 continuationOutruns_of_moreThanHalf_continuation
 tailContinuationOutruns_of_moreThanHalf_tailContinuation
+sourceContinuationOutrunsDepthCount
+tailContinuationOutrunsDepthCount
+continuationOutruns_iff_moreThanHalf_continuation
+tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+recoveryDominates_of_atMostHalf_continuation
+tailRecoveryDominates_of_atMostHalf_tailContinuation
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-110.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-110.md
new file mode 100644
index 00000000..5e4ceb5b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-110.md
@@ -0,0 +1,213 @@
+# Report Petal 110: Cause-Side Failure Count
+
+## Summary
+
+Checkpoint 110 implements cause-side failure counts and proves that they equal
+the descriptive pressure depth counts.
+
+The key result is:
+
+```text
+sourceContinuationOutrunsDepthCount
+  = sourceContinuationPressureDepthCount
+```
+
+and the shifted-tail counterpart.
+
+## Lean Additions
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Cause-side failure counts:
+
+```lean
+sourceContinuationOutrunsDepthCount
+tailContinuationOutrunsDepthCount
+```
+
+Local equivalence between cause-side failure and descriptive pressure:
+
+```lean
+continuationOutruns_iff_moreThanHalf_continuation
+tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+```
+
+Count equality:
+
+```lean
+sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
+tailContinuationOutrunsDepthCount_eq_pressureDepthCount
+```
+
+Additional controlled-side reverse bridge:
+
+```lean
+recoveryDominates_of_atMostHalf_continuation
+tailRecoveryDominates_of_atMostHalf_tailContinuation
+```
+
+All additions passed without `sorry`.
+
+## Mathematical Result
+
+Before this checkpoint, pressure depth count was a descriptive count:
+
+```text
+MoreThanHalf continuation retention
+```
+
+Checkpoint 110 proves it is also a cause-side failure count:
+
+```text
+ContinuationOutrunsRecovery
+```
+
+Thus pressure is no longer merely an observed mode.  It is synchronized with
+the underlying comparison failure:
+
+```text
+continuation outruns recovery
+```
+
+Locally, both branches are now aligned:
+
+```text
+RecoveryDominatesContinuation
+  <-> AtMostHalf continuation retention
+
+ContinuationOutrunsRecovery
+  <-> MoreThanHalf continuation retention
+```
+
+The source/tail pressure count equality then lifts the local equivalence to a
+finite depth range.
+
+## Implementation Note
+
+The count equality was proved by induction on `len`.
+
+At the successor step, the final singleton was handled by `by_cases` on the
+cause-side predicate and then converted through:
+
+```lean
+continuationOutruns_iff_moreThanHalf_continuation
+tailContinuationOutruns_iff_moreThanHalf_tailContinuation
+```
+
+This follows the same reliable pattern as checkpoint 108: keep `decide` and
+`countP` indicator reasoning inside the proof body where `classical` is
+available.
+
+## Documentation Updates
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/README.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+Added:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-CauseSideFailureCount-110.md
+```
+
+## Additional Inference
+
+The next natural target is the controlled-side cause count.
+
+The new controlled reverse bridge:
+
+```lean
+recoveryDominates_of_atMostHalf_continuation
+```
+
+and the existing forward bridge:
+
+```lean
+atMostHalf_continuation_of_recoveryDominates
+```
+
+show local equivalence between:
+
+```text
+RecoveryDominatesContinuation
+```
+
+and:
+
+```text
+AtMostHalf continuation retention
+```
+
+Therefore a dominance depth count should equal the controlled depth count.
+
+Expected next surface:
+
+```lean
+sourceRecoveryDominanceDepthCount =
+  sourceContinuationControlledDepthCount
+
+tailRecoveryDominanceDepthCount =
+  tailContinuationControlledDepthCount
+```
+
+After that, a cause-side partition should follow:
+
+```text
+dominanceDepthCount + outrunsDepthCount = len
+```
+
+## Verification
+
+Commands run for this checkpoint:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+rg -n "\bsorry\b" DkMath/Collatz/PetalBridge.lean
+git diff --check -- <touched files>
+```
+
+Results:
+
+```text
+lake build DkMath.Collatz.PetalBridge: passed
+lake build DkMath.Collatz.Collatz2K26: passed
+rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
+git diff --check on touched files: passed
+```
+
+The targeted `DkMath.Collatz.PetalBridge` build passed before documentation
+sync, and the integration build passed after documentation sync.
+
+Known upstream warning:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean declares a theorem using sorry
+```
+
+This warning is outside the Collatz `PetalBridge` checkpoint.
+
+## Next Implementation Candidate
+
+Proceed to dominance-side cause counts.
+
+Minimal API:
+
+```lean
+noncomputable def sourceRecoveryDominanceDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ := ...
+
+noncomputable def tailRecoveryDominanceDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ := ...
+```
+
+Then prove equality with the controlled counts and close the cause-side
+partition.
````
`````

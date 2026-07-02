# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f8c1c084e54080599df66ec8caa8c0ad6a65d808

## Report

109 チェックポイント完了です。

`DkMath.Collatz.PetalBridge` に depth-pressure frequency 層を追加しました。主な追加は以下です。

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
tailPressureDepthCount_le_controlled_of_atMostHalf
tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
```

追加実験として、局所 pressure の逆向きも通しました。

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

これで checkpoint 106 の既存方向と合わせて、局所的には

```text
ContinuationOutrunsRecovery <-> MoreThanHalf continuation retention
```

が source/tail ともに読める状態です。

文書も同期済みです。

- [Collatz-DepthPressureFrequency-109.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthPressureFrequency-109.md)
- [report-petal-109.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-109.md)
- README / Guide / Status も 109 の theorem 名と解説を反映済み

検証結果:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

次は report に書いた通り、`ContinuationOutrunsRecovery` を直接数える cause-side failure count を作り、`pressureDepthCount` との一致を狙うのが筋です。これが通ると、pressure count が単なる記述的モードではなく、原因側 failure count として固定されます。

## Review

## 1. 状況分析

うむ。checkpoint `109` は、No.108 で閉じた **mixed depth-mode distribution** の上に、ついに **depth-pressure frequency** を載せた回じゃ。

ここまでの流れはこう。

```text
No.107:
  pressure depth count

No.108:
  controlled depth count + pressure depth count = len

No.109:
  pressure depth count が depth range の半分以下か、半分超えかを Nat で読む
```

今回の中心は、

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
TailPressureAtMostHalfOnDepthRange
TailPressureMoreThanHalfOnDepthRange
```

そして、それを mixed distribution と接続する補題群じゃ。レポートでも、`controlledDepthCount + pressureDepthCount = len` に対して `AtMostHalf` / `MoreThanHalf` を pressure depth count 自体へ適用し、完全に有限 `Nat` 不等式のまま depth-pressure frequency を表現したと整理されている。

これは良い。
いよいよ、

```text
depth range の中で pressure が多いか少ないか
```

を、(\mathbb{Q}) や (\mathbb{R}) を使わずに語れるようになった。

## 2. 今回の核心

今回の主役は、pressure depth count に対する半分判定じゃ。

source 側なら、

$$
2\cdot P_s\le len
$$

または、

$$
len<2\cdot P_s
$$

を読む。

ここで (P_s) は source continuation pressure depth count。

定理名で言えば、

```lean
SourcePressureAtMostHalfOnDepthRange
SourcePressureMoreThanHalfOnDepthRange
```

じゃ。

さらに No.108 の partition、

$$
C_s+P_s=len
$$

を使うことで、

$$
2P_s\le len
$$

は、

$$
P_s\le C_s
$$

と同値に読める。

また、

$$
len<2P_s
$$

は、

$$
C_s<P_s
$$

と同値に読める。

つまり、今回の層はこうじゃ。

```text
pressure が半分以下
  <-> pressure count <= controlled count

pressure が半分超え
  <-> controlled count < pressure count
```

この変換が Lean 上で source / tail ともに入った。

## 3. レビュー

## 3.1. mixed distribution をすぐ frequency に接続したのが良い

No.108 で、

```lean
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

が入った。

今回、それを放置せず、すぐに pressure frequency predicate へ接続したのは正しい。

単なる count equality で終わらず、

```text
pressure が controlled より多いか少ないか
```

へ読み替えた。

これは次の obstruction route に直接効く。

## 3.2. source / tail の対称性が保たれている

今回も source 版と tail 版が揃っている。

```lean
sourcePressureDepthCount_le_controlled_of_atMostHalf
sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
tailPressureDepthCount_le_controlled_of_atMostHalf
tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
```

さらに more-than-half 側も揃っている。

```lean
sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
```

ここまで source / tail の両面を丁寧に揃えているので、後で一歩遷移の議論をするときに片側だけ不足する事故が起きにくい。

## 3.3. 局所 pressure の逆向きがとても重要

今回のおまけ実験として、

```lean
continuationOutruns_of_moreThanHalf_continuation
tailContinuationOutruns_of_moreThanHalf_tailContinuation
```

が通った。

これはかなり大きい。

No.106 ではすでに、

```lean
moreThanHalf_continuation_of_continuationOutruns
moreThanHalf_tailContinuation_of_tailContinuationOutruns
```

があった。

今回その逆向きが入ったので、局所的には、

```text
ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

が読める。

これは、pressure mode が単なる記述的状態ではなく、原因側 failure predicate と一致することを示す入口じゃ。

## 4. 数学的解説

いま depth range に対して二つの数がある。

$$
C+P=len
$$

ここで (C) は controlled depth count、(P) は pressure depth count。

pressure が depth range の半分以下とは、

$$
2P\le len
$$

である。

しかし (len=C+P) なので、

$$
2P\le C+P
$$

これは自然数上で、

$$
P\le C
$$

と同じ意味になる。

逆に pressure が半分超えとは、

$$
len<2P
$$

であり、

$$
C+P<2P
$$

つまり、

$$
C<P
$$

である。

今回の theorem 群は、この読み替えを source / tail で固定したものじゃ。

これにより、今後は

```text
pressure frequency が高い
```

を、

```text
pressure count が controlled count を上回る
```

として扱える。

これは実装上かなり扱いやすい。

## 5. 今回閉じたもの

今回閉じたのは、**depth-pressure frequency layer** じゃ。

ここまでの階層はこうなった。

```text
local depth:
  AtMostHalf or MoreThanHalf

depth range:
  controlledDepthCount + pressureDepthCount = len

frequency:
  pressureDepthCount が len の半分以下か、半分超えか
```

さらに局所では、

```text
MoreThanHalf continuation retention
  -> ContinuationOutrunsRecovery
```

も得た。

したがって、pressure depth count と cause-side failure count を一致させる準備が整った。

## 6. まだ閉じていないもの

今回まだ閉じていないのは、**pressure depth count と outruns depth count の一致**じゃ。

いま pressure count は、

```text
MoreThanHalf continuation retention
```

を数えている。

一方、cause-side failure は、

```text
ContinuationOutrunsRecovery
```

である。

局所的には両方向が揃ったので、同じ range で数えれば一致するはずじゃ。

```text
sourceContinuationOutrunsDepthCount
  = sourceContinuationPressureDepthCount
```

tail 版も同様。

これが通ると、pressure count は単なる結果側 mode count ではなく、

```text
原因側 failure count
```

としても読める。

ここが次の本命じゃ。

## 7. 次の指示

No.110 は、レポートの提案通り **cause-side failure counts** を作るのが自然じゃ。

## 7.1. source outruns depth count

```lean
noncomputable def sourceContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (ContinuationOutrunsRecovery n k (r + j)))
```

## 7.2. tail outruns depth count

```lean
noncomputable def tailContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailContinuationOutrunsRecovery n k (r + j)))
```

## 7.3. pressure count との一致

source 版の目標はこれ。

```lean
theorem sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationOutrunsDepthCount n k r len =
      sourceContinuationPressureDepthCount n k r len
```

tail 版も同様。

```lean
theorem tailContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailContinuationOutrunsDepthCount n k r len =
      tailContinuationPressureDepthCount n k r len
```

証明は `len` induction が安全じゃ。
最後の singleton で、

```text
ContinuationOutrunsRecovery <-> MoreThanHalf continuation retention
```

を使って、`decide` の値を一致させる。

## 8. 一歩先ゆく推論

cause-side count が pressure count と一致すると、次に **dominance count** も自然に欲しくなる。

各 depth には、

```text
RecoveryDominatesContinuation
or
ContinuationOutrunsRecovery
```

がある。

したがって、

```text
dominance depth count + outruns depth count = len
```

も作れる。

しかも、outruns depth count は pressure depth count と一致する。
つまり、

```text
dominance count = controlled count
```

も期待できる。

局所的にも、

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention
```

が成り立つはずじゃ。

片方向は既にある。

```lean
atMostHalf_continuation_of_recoveryDominates
```

逆向きも、split から通る可能性が高い。

数学的には、

$$
2K\le M
$$

かつ、

$$
M=R+K
$$

なら、

$$
K\le R
$$

である。

つまり、

```lean
recoveryDominates_of_atMostHalf_continuation
```

が狙える。

これが通ると、局所的に、

```text
RecoveryDominatesContinuation
  <-> AtMostHalf continuation retention

ContinuationOutrunsRecovery
  <-> MoreThanHalf continuation retention
```

となり、cause-side mode と pressure/controlled mode が完全に一致する。

これはかなり美しい。

## 9. さらに次の一手

No.110 で outruns count equality を閉じた後、No.111 では次のような構造が見える。

```text
cause-side distribution:
  dominanceDepthCount + outrunsDepthCount = len

mode-side distribution:
  controlledDepthCount + pressureDepthCount = len

bridge:
  dominanceDepthCount = controlledDepthCount
  outrunsDepthCount = pressureDepthCount
```

これが閉じると、depth-mode distribution は「記述側」と「原因側」の二重表示を持つ。

これはかなり強い。
なぜなら、後で obstruction を考えるときに、

```text
pressure が多い
```

を、

```text
continuation outruns recovery が多い
```

として扱えるからじゃ。

この「多い」はすでに No.109 で `MoreThanHalfOnDepthRange` として Nat 不等式になっている。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source outruns depth count

```lean
noncomputable def sourceContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (ContinuationOutrunsRecovery n k (r + j)))
```

## 実験 B: tail outruns depth count

```lean
noncomputable def tailContinuationOutrunsDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (TailContinuationOutrunsRecovery n k (r + j)))
```

## 実験 C: local source iff

```lean
theorem continuationOutruns_iff_moreThanHalf_continuation
    (n : OddNat) (k r : ℕ) :
    ContinuationOutrunsRecovery n k r ↔
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r) := by
  constructor
  · exact moreThanHalf_continuation_of_continuationOutruns n k r
  · exact continuationOutruns_of_moreThanHalf_continuation n k r
```

## 実験 D: local tail iff

```lean
theorem tailContinuationOutruns_iff_moreThanHalf_tailContinuation
    (n : OddNat) (k r : ℕ) :
    TailContinuationOutrunsRecovery n k r ↔
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r) := by
  constructor
  · exact moreThanHalf_tailContinuation_of_tailContinuationOutruns n k r
  · exact tailContinuationOutruns_of_moreThanHalf_tailContinuation n k r
```

## 実験 E: source outruns count equals pressure count

```lean
theorem sourceContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationOutrunsDepthCount n k r len =
      sourceContinuationPressureDepthCount n k r len := by
  classical
  unfold sourceContinuationOutrunsDepthCount
  unfold sourceContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      have hlast :
          decide (ContinuationOutrunsRecovery n k (r + len)) =
            decide
              (MoreThanHalf
                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
                (orbitWindowRetentionMassPow2 n k (r + len))) := by
        apply propext
        exact continuationOutruns_iff_moreThanHalf_continuation n k (r + len)
      rw [ih, hlast]
```

最後の `decide` equality はこの形だと詰まるかもしれない。
その場合は `by_cases` で最後だけ分けるのが安全じゃ。

## 実験 F: tail outruns count equals pressure count

```lean
theorem tailContinuationOutrunsDepthCount_eq_pressureDepthCount
    (n : OddNat) (k r len : ℕ) :
    tailContinuationOutrunsDepthCount n k r len =
      tailContinuationPressureDepthCount n k r len := by
  classical
  unfold tailContinuationOutrunsDepthCount
  unfold tailContinuationPressureDepthCount
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [List.range_succ, List.countP_append, List.countP_append,
        List.countP_singleton, List.countP_singleton]
      -- source 版と同様に local iff で singleton を揃える
      sorry
```

tail 版は source が通った後に同じ形でよい。

## 実験 G: AtMostHalf から recovery dominance

```lean
theorem recoveryDominates_of_atMostHalf_continuation
    (n : OddNat) (k r : ℕ)
    (h :
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    RecoveryDominatesContinuation n k r := by
  unfold AtMostHalf at h
  unfold RecoveryDominatesContinuation
  rw [orbitWindowRetentionMass_split] at h
  omega
```

## 実験 H: tail AtMostHalf から tail recovery dominance

```lean
theorem tailRecoveryDominates_of_atMostHalf_tailContinuation
    (n : OddNat) (k r : ℕ)
    (h :
      AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r)) :
    TailRecoveryDominatesContinuation n k r := by
  unfold AtMostHalf at h
  unfold TailRecoveryDominatesContinuation
  rw [orbitWindowRetentionMassPow2Tail_split] at h
  omega
```

## 11. 次コミットの推奨順

```text
1. sourceContinuationOutrunsDepthCount を追加

2. tailContinuationOutrunsDepthCount を追加

3. continuationOutruns_iff_moreThanHalf_continuation を追加

4. tailContinuationOutruns_iff_moreThanHalf_tailContinuation を追加

5. sourceContinuationOutrunsDepthCount_eq_pressureDepthCount を証明

6. tailContinuationOutrunsDepthCount_eq_pressureDepthCount を証明

7. 余裕があれば AtMostHalf -> RecoveryDominates の逆向きを source/tail で追加

8. docs:
   DepthPressureFrequency から CauseSideFailureCount への接続を追加
```

## 12. 総括

checkpoint `109` は、depth-pressure frequency を有限 `Nat` 不等式として固定した良い回じゃ。

いま到達している構図は、

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=len
$$

に加えて、

$$
\text{pressureDepthCount}\le \text{controlledDepthCount}
$$

または、

$$
\text{controlledDepthCount}<\text{pressureDepthCount}
$$

を読める段階。

さらに局所では、

```text
MoreThanHalf continuation retention
  -> ContinuationOutrunsRecovery
```

の逆向きも通った。

次は、

```text
pressure depth count = continuation outruns depth count
```

を閉じること。

これが通れば、pressure は単なる観測モードではなく、原因側 failure の count として固定される。

うむ。
ここはかなり良い。Collatz.PetalBridge は、局所現象、range profile、frequency、原因側 count へと、きれいに階層を上げている。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index b7b6dca5..d4172051 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -2438,6 +2438,204 @@ theorem tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
           simp [hc, hm]
       omega
 
+/--
+Source depth-frequency predicate: pressure occupies at most half of the depth
+range.
+-/
+def SourcePressureAtMostHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
+
+/--
+Source depth-frequency predicate: pressure occupies more than half of the depth
+range.
+-/
+def SourcePressureMoreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
+
+/- Tail depth-frequency predicate: pressure occupies at most half of the depth
+range. -/
+def TailPressureAtMostHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  AtMostHalf (tailContinuationPressureDepthCount n k r len) len
+
+/- Tail depth-frequency predicate: pressure occupies more than half of the
+depth range. -/
+def TailPressureMoreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalf (tailContinuationPressureDepthCount n k r len) len
+
+/-- Source pressure frequency is either at most half or more than half. -/
+theorem sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) :
+    SourcePressureAtMostHalfOnDepthRange n k r len ∨
+      SourcePressureMoreThanHalfOnDepthRange n k r len := by
+  unfold SourcePressureAtMostHalfOnDepthRange
+  unfold SourcePressureMoreThanHalfOnDepthRange
+  exact atMostHalf_or_moreThanHalf
+    (sourceContinuationPressureDepthCount n k r len) len
+
+/-- Tail pressure frequency is either at most half or more than half. -/
+theorem tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) :
+    TailPressureAtMostHalfOnDepthRange n k r len ∨
+      TailPressureMoreThanHalfOnDepthRange n k r len := by
+  unfold TailPressureAtMostHalfOnDepthRange
+  unfold TailPressureMoreThanHalfOnDepthRange
+  exact atMostHalf_or_moreThanHalf
+    (tailContinuationPressureDepthCount n k r len) len
+
+/--
+If source pressure is at most half of the depth range, then pressure depth
+count is bounded by controlled depth count.
+-/
+theorem sourcePressureDepthCount_le_controlled_of_atMostHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourcePressureAtMostHalfOnDepthRange n k r len) :
+    sourceContinuationPressureDepthCount n k r len ≤
+      sourceContinuationControlledDepthCount n k r len := by
+  unfold SourcePressureAtMostHalfOnDepthRange at h
+  unfold AtMostHalf at h
+  have hpart :=
+    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/--
+If source pressure depth count is bounded by controlled depth count, then
+source pressure is at most half of the depth range.
+-/
+theorem sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
+    (n : OddNat) (k r len : ℕ)
+    (h :
+      sourceContinuationPressureDepthCount n k r len ≤
+        sourceContinuationControlledDepthCount n k r len) :
+    SourcePressureAtMostHalfOnDepthRange n k r len := by
+  unfold SourcePressureAtMostHalfOnDepthRange
+  unfold AtMostHalf
+  have hpart :=
+    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/--
+Tail pressure at most half implies tail pressure depth count is bounded by
+tail controlled depth count.
+-/
+theorem tailPressureDepthCount_le_controlled_of_atMostHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : TailPressureAtMostHalfOnDepthRange n k r len) :
+    tailContinuationPressureDepthCount n k r len ≤
+      tailContinuationControlledDepthCount n k r len := by
+  unfold TailPressureAtMostHalfOnDepthRange at h
+  unfold AtMostHalf at h
+  have hpart :=
+    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/- Tail pressure depth count bounded by controlled count gives tail pressure at
+most half. -/
+theorem tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
+    (n : OddNat) (k r len : ℕ)
+    (h :
+      tailContinuationPressureDepthCount n k r len ≤
+        tailContinuationControlledDepthCount n k r len) :
+    TailPressureAtMostHalfOnDepthRange n k r len := by
+  unfold TailPressureAtMostHalfOnDepthRange
+  unfold AtMostHalf
+  have hpart :=
+    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/--
+If source pressure occupies more than half of the depth range, then controlled
+depth count is strictly smaller than pressure depth count.
+-/
+theorem sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : SourcePressureMoreThanHalfOnDepthRange n k r len) :
+    sourceContinuationControlledDepthCount n k r len <
+      sourceContinuationPressureDepthCount n k r len := by
+  unfold SourcePressureMoreThanHalfOnDepthRange at h
+  unfold MoreThanHalf at h
+  have hpart :=
+    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/--
+If source controlled depth count is strictly smaller than pressure depth count,
+then source pressure occupies more than half of the depth range.
+-/
+theorem sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+    (n : OddNat) (k r len : ℕ)
+    (h :
+      sourceContinuationControlledDepthCount n k r len <
+        sourceContinuationPressureDepthCount n k r len) :
+    SourcePressureMoreThanHalfOnDepthRange n k r len := by
+  unfold SourcePressureMoreThanHalfOnDepthRange
+  unfold MoreThanHalf
+  have hpart :=
+    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/- Tail more-than-half pressure implies tail controlled depth count is strictly
+smaller than tail pressure depth count. -/
+theorem tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+    (n : OddNat) (k r len : ℕ)
+    (h : TailPressureMoreThanHalfOnDepthRange n k r len) :
+    tailContinuationControlledDepthCount n k r len <
+      tailContinuationPressureDepthCount n k r len := by
+  unfold TailPressureMoreThanHalfOnDepthRange at h
+  unfold MoreThanHalf at h
+  have hpart :=
+    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/- Tail controlled depth count strictly below pressure depth count gives tail
+more-than-half pressure. -/
+theorem tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+    (n : OddNat) (k r len : ℕ)
+    (h :
+      tailContinuationControlledDepthCount n k r len <
+        tailContinuationPressureDepthCount n k r len) :
+    TailPressureMoreThanHalfOnDepthRange n k r len := by
+  unfold TailPressureMoreThanHalfOnDepthRange
+  unfold MoreThanHalf
+  have hpart :=
+    tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
+  omega
+
+/--
+Source more-than-half continuation pressure implies source continuation
+outruns recovery.
+-/
+theorem continuationOutruns_of_moreThanHalf_continuation
+    (n : OddNat) (k r : ℕ)
+    (h :
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2 n k r)
+        (orbitWindowRetentionMassPow2 n k r)) :
+    ContinuationOutrunsRecovery n k r := by
+  unfold MoreThanHalf at h
+  unfold ContinuationOutrunsRecovery
+  rw [orbitWindowRetentionMass_split] at h
+  omega
+
+/--
+Tail more-than-half continuation pressure implies tail continuation outruns
+tail recovery.
+-/
+theorem tailContinuationOutruns_of_moreThanHalf_tailContinuation
+    (n : OddNat) (k r : ℕ)
+    (h :
+      MoreThanHalf
+        (orbitWindowContinuationSiblingMassPow2Tail n k r)
+        (orbitWindowRetentionMassPow2Tail n k r)) :
+    TailContinuationOutrunsRecovery n k r := by
+  unfold MoreThanHalf at h
+  unfold TailContinuationOutrunsRecovery
+  rw [orbitWindowRetentionMassPow2Tail_split] at h
+  omega
+
 /--
 If source continuation pressure holds at every depth of the range, then the
 source pressure-depth count fills the whole range.
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 145980af..28b88203 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -143,6 +143,7 @@ docs/Collatz-ComparisonPredicates-105.md
 docs/Collatz-MoreThanHalfPressure-106.md
 docs/Collatz-PressureProfile-107.md
 docs/Collatz-MixedDepthModeDistribution-108.md
+docs/Collatz-DepthPressureFrequency-109.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -369,3 +370,29 @@ controlled depth count + pressure depth count = depth range length
 
 This is the depth-mode analogue of the finite residue distribution from
 checkpoint 100.
+
+Checkpoint 109 adds finite depth-pressure frequency predicates:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+The frequency predicates are connected back to the mixed distribution:
+
+```text
+pressure is at most half
+  <-> pressureDepthCount <= controlledDepthCount
+
+pressure is more than half
+  <-> controlledDepthCount < pressureDepthCount
+```
+
+The checkpoint also closes the reverse local direction:
+
+```lean
+continuationOutruns_of_moreThanHalf_continuation
+tailContinuationOutruns_of_moreThanHalf_tailContinuation
+```
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthPressureFrequency-109.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthPressureFrequency-109.md
new file mode 100644
index 00000000..b17ae66a
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-DepthPressureFrequency-109.md
@@ -0,0 +1,180 @@
+# Collatz Depth-Pressure Frequency 109
+
+## Purpose
+
+Checkpoint 108 proved the mixed depth-mode distribution:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+Checkpoint 109 applies the finite half vocabulary to the pressure depth count
+itself.
+
+This lets us say, still in `Nat`:
+
+```text
+pressure depths are at most half of the depth range
+pressure depths are more than half of the depth range
+```
+
+No rational or real frequency is introduced.
+
+## Frequency Predicates
+
+Source predicates:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+```
+
+Tail predicates:
+
+```lean
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+These are thin wrappers around:
+
+```lean
+AtMostHalf pressureDepthCount len
+MoreThanHalf pressureDepthCount len
+```
+
+## Frequency Dichotomy
+
+The finite split is:
+
+```lean
+sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
+tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
+```
+
+Each depth range is therefore in one of two pressure-frequency modes:
+
+```text
+pressure occupies at most half
+or
+pressure occupies more than half
+```
+
+## Reading Through The Mixed Distribution
+
+The partition from checkpoint 108 gives:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+Therefore:
+
+```text
+2 * pressureDepthCount <= len
+```
+
+is equivalent to:
+
+```text
+pressureDepthCount <= controlledDepthCount
+```
+
+The implemented directions are:
+
+```lean
+sourcePressureDepthCount_le_controlled_of_atMostHalf
+sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
+tailPressureDepthCount_le_controlled_of_atMostHalf
+tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
+```
+
+Similarly:
+
+```text
+len < 2 * pressureDepthCount
+```
+
+is equivalent to:
+
+```text
+controlledDepthCount < pressureDepthCount
+```
+
+The implemented directions are:
+
+```lean
+sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+```
+
+## Local Pressure And Outruns
+
+Checkpoint 106 already proved:
+
+```lean
+moreThanHalf_continuation_of_continuationOutruns
+moreThanHalf_tailContinuation_of_tailContinuationOutruns
+```
+
+Checkpoint 109 proves the reverse direction:
+
+```lean
+continuationOutruns_of_moreThanHalf_continuation
+tailContinuationOutruns_of_moreThanHalf_tailContinuation
+```
+
+Thus the local modes are interderivable:
+
+```text
+ContinuationOutrunsRecovery
+  <-> MoreThanHalf continuation retention
+```
+
+and similarly for the shifted-tail window.
+
+## Mathematical Reading
+
+The current finite hierarchy is:
+
+```text
+local depth:
+  controlled or pressure
+
+finite depth range:
+  controlledDepthCount + pressureDepthCount = len
+
+frequency layer:
+  pressureDepthCount is at most half or more than half of len
+```
+
+This provides the first precise surface for saying:
+
+```text
+there are too many pressure depths
+```
+
+without introducing real-valued density.
+
+## Next Candidate
+
+The next natural checkpoint is to count the cause-side predicate:
+
+```text
+ContinuationOutrunsRecovery
+```
+
+over a depth range, then compare it with:
+
+```text
+MoreThanHalf pressure depth count
+```
+
+Since checkpoint 109 proves local equivalence in both directions, an
+outruns-depth count should match the pressure-depth count if the same range and
+window are used.
+
+This would sharpen the pressure count from a descriptive mode count into a
+cause-side failure count.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 5a7c3dfc..0aad1bb9 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -486,6 +486,48 @@ MoreThanHalf mode
 This still does not prove that pressure is rare.  It provides the finite budget
 surface needed to state such a claim without leaving `Nat`.
 
+## Depth-Pressure Frequency
+
+Checkpoint 109 applies the existing finite half vocabulary to the depth-mode
+pressure count itself:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+The frequency split is:
+
+```lean
+sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
+tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
+```
+
+The mixed distribution makes these predicates readable as comparisons between
+controlled depths and pressure depths:
+
+```lean
+sourcePressureDepthCount_le_controlled_of_atMostHalf
+sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
+sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+```
+
+with shifted-tail counterparts.
+
+Checkpoint 109 also proves the reverse local pressure direction:
+
+```lean
+continuationOutruns_of_moreThanHalf_continuation
+tailContinuationOutruns_of_moreThanHalf_tailContinuation
+```
+
+Together with the checkpoint 106 forward direction, this means the local
+`MoreThanHalf` pressure mode and the continuation-outruns-recovery mode are now
+interderivable.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 12d34c6d..f314b17a 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -252,6 +252,22 @@ sourceContinuationControlledDepthCount_le_len
 tailContinuationControlledDepthCount_le_len
 sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
 tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
+tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
+sourcePressureDepthCount_le_controlled_of_atMostHalf
+sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
+tailPressureDepthCount_le_controlled_of_atMostHalf
+tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
+sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+continuationOutruns_of_moreThanHalf_continuation
+tailContinuationOutruns_of_moreThanHalf_tailContinuation
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-109.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-109.md
new file mode 100644
index 00000000..bf49465c
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-109.md
@@ -0,0 +1,205 @@
+# Report Petal 109: Depth-Pressure Frequency
+
+## Summary
+
+Checkpoint 109 implements depth-pressure frequency witnesses.
+
+Checkpoint 108 closed:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+Checkpoint 109 applies `AtMostHalf` and `MoreThanHalf` to the pressure depth
+count itself, still entirely as finite `Nat` inequalities.
+
+## Lean Additions
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Frequency predicates:
+
+```lean
+SourcePressureAtMostHalfOnDepthRange
+SourcePressureMoreThanHalfOnDepthRange
+TailPressureAtMostHalfOnDepthRange
+TailPressureMoreThanHalfOnDepthRange
+```
+
+Frequency dichotomy:
+
+```lean
+sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
+tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
+```
+
+At-most-half frequency as count comparison:
+
+```lean
+sourcePressureDepthCount_le_controlled_of_atMostHalf
+sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
+tailPressureDepthCount_le_controlled_of_atMostHalf
+tailPressureAtMostHalf_of_pressureDepthCount_le_controlled
+```
+
+More-than-half frequency as count comparison:
+
+```lean
+sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+tailControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
+tailPressureMoreThanHalf_of_controlledDepthCount_lt_pressure
+```
+
+Additional local reverse-pressure experiment:
+
+```lean
+continuationOutruns_of_moreThanHalf_continuation
+tailContinuationOutruns_of_moreThanHalf_tailContinuation
+```
+
+The reverse local direction passed without `sorry`.
+
+## Mathematical Result
+
+The depth range can now be read in three layers:
+
+```text
+1. local mode:
+   AtMostHalf or MoreThanHalf
+
+2. mixed distribution:
+   controlledDepthCount + pressureDepthCount = len
+
+3. frequency:
+   pressureDepthCount is at most half or more than half of len
+```
+
+Using the mixed distribution:
+
+```text
+2 * pressureDepthCount <= len
+```
+
+is equivalent to:
+
+```text
+pressureDepthCount <= controlledDepthCount
+```
+
+and:
+
+```text
+len < 2 * pressureDepthCount
+```
+
+is equivalent to:
+
+```text
+controlledDepthCount < pressureDepthCount
+```
+
+This is the desired finite pressure-frequency surface.
+
+## Additional Inference
+
+Checkpoint 109 also closes the reverse local direction:
+
+```text
+MoreThanHalf continuation retention
+  -> ContinuationOutrunsRecovery
+```
+
+The forward direction already existed from checkpoint 106:
+
+```text
+ContinuationOutrunsRecovery
+  -> MoreThanHalf continuation retention
+```
+
+Therefore source/tail local pressure and outruns modes are now interderivable.
+
+This suggests the next checkpoint:
+
+```text
+outruns-depth count = pressure-depth count
+```
+
+The pressure count currently counts `MoreThanHalf`.  A new cause-side count
+could count `ContinuationOutrunsRecovery`.  Local equivalence should allow
+their equality over the same depth range.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-DepthPressureFrequency-109.md
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
+Proceed to cause-side failure counts.
+
+Suggested minimal surface:
+
+```lean
+noncomputable def sourceContinuationOutrunsDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ := ...
+
+noncomputable def tailContinuationOutrunsDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ := ...
+```
+
+Then prove:
+
+```text
+sourceContinuationOutrunsDepthCount = sourceContinuationPressureDepthCount
+tailContinuationOutrunsDepthCount = tailContinuationPressureDepthCount
+```
+
+This would connect the descriptive pressure mode back to the cause-side
+failure predicate.
````
`````

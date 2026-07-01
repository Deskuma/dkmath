# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: ea0f6d055dd7f4ccc78e6d6ebe007ba5cf25cdd1

## Report

107 チェックポイント完了です。

`DkMath.Collatz.PetalBridge` に pressure profile 層を追加しました。主な追加は以下です。

```lean
MoreThanHalfOnRange
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
moreThanHalf_of_sourceContinuationPressure
moreThanHalf_of_tailContinuationPressure
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

本筋の `failure range -> pressure range` に加えて、おまけ実験として pressure depth count まで通しました。これで「全 depth が pressure なら pressure count = len」が source/tail 両方で no-sorry です。途中で `decide (MoreThanHalf ...)` の `Decidable` が足りず一度失敗しましたが、`classical` を明示して修正済みです。

文書も同期しました。

- [Collatz-PressureProfile-107.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureProfile-107.md)
- [report-petal-107.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-107.md)
- README / Guide / Status も 107 の theorem 名と解説を反映済み

検証結果:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

既知の上流 `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6` の `sorry` warning は今回範囲外です。

次は自然に `controlled depth count + pressure depth count = len` の mixed depth-mode distribution へ進めます。checkpoint 100 の「window mass distribution」が、ここで「depth-mode distribution」に持ち上がり始めました。

## Review

## 1. 状況分析

うむ。checkpoint `107` は、No.106 で得た **MoreThanHalf pressure** を、単発の depth から **有限 depth range の profile** へ持ち上げた回じゃ。

ここまでの流れは綺麗に続いている。

```text id="q3g91n"
No.104:
  K <= R -> AtMostHalf

No.105:
  RecoveryDominates / ContinuationOutruns を predicate 化

No.106:
  ContinuationOutruns -> MoreThanHalf pressure

No.107:
  failure range -> pressure profile -> pressure depth count
```

今回の主な追加は、

```lean id="fn41wb"
MoreThanHalfOnRange
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

じゃ。レポートでも、`ContinuationOutrunsRecoveryOnRange -> SourceContinuationPressureOnRange -> sourceContinuationPressureDepthCount = len` という形で、長く続く失敗範囲を有限 depth-mode object に変換できた、と整理されている。

これは大きい。
いままでは「window 内の residue mass」を数えていた。
今回からは「depth range 内の pressure mode」を数え始めた。

## 2. 今回の核心

今回の一番大きな概念上の変化は、数える対象が変わったことじゃ。

これまでの count は、

```text id="lf7j8s"
固定 depth における orbit label の residue count
```

だった。

つまり、

$$
C_{d,a}(n,k)=\#{i<k\mid q_i\bmod 2^d=a}
$$

のようなもの。

今回の pressure depth count は違う。

```text id="ovm93v"
有限 depth range の中で、何個の depth が pressure mode か
```

を数える。

つまり、depth \(r,r+1,\ldots,r+len-1\) に対して、

$$
\text{MoreThanHalf at depth }r+j
$$

が成り立つ \(j\) の数を数える。

この違いは大きい。

```text id="84j74p"
window residue distribution:
  ひとつの depth で label mass を数える

depth-mode distribution:
  depth range で mode を数える
```

ここで、DkMath の観測階層が一段上がった。

## 3. レビュー

## 3.1. `MoreThanHalfOnRange` は良い抽象化

今回の generic predicate は良い。

```lean id="zwm9j6"
def MoreThanHalfOnRange
    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))
```

これは Collatz に閉じていない。
単に depth-indexed な count / total があり、各 depth で `MoreThanHalf` が成り立つ、という抽象述語じゃ。

この抽象度はちょうどよい。

source / tail はその特殊化として、

```lean id="vvu70k"
SourceContinuationPressureOnRange
TailContinuationPressureOnRange
```

に落とされている。

## 3.2. failure range から pressure profile への昇格が自然

今回の theorem、

```lean id="ls6pip"
sourceContinuationPressure_of_outRunsOnRange
tailContinuationPressure_of_outRunsOnRange
```

は、No.106 の流れを range に持ち上げたものじゃ。

数学的には、

$$
\forall j<len,\;R_{r+j}<K_{r+j}
$$

なら、

$$
\forall j<len,\;M_{r+j}<2K_{r+j}
$$

ということ。

つまり、

```text id="1f67gb"
continuation が recovery を上回る range
  -> continuation が retention の半分を超える range
```

である。

これは obstruction route の入力としてかなり扱いやすい。

## 3.3. pressure depth count まで通したのが偉い

今回、おまけ実験として count まで通ったのは良い。

```lean id="uppn99"
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
```

そして、

```lean id="v7ds6z"
sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
```

が no-sorry で通っている。

これは小さく見えるが、実は次の `mixed depth-mode distribution` への実証実験になっている。

`decide (MoreThanHalf ...)` に `classical` が必要だった点も、今後の depth-mode count API の注意点として良い記録じゃ。

## 4. 数学的解説

いまの局所分岐はこうだった。

$$
\text{RecoveryDominatesContinuation}\quad\Longrightarrow\quad\text{AtMostHalf}
$$

$$
\text{ContinuationOutrunsRecovery}\quad\Longrightarrow\quad\text{MoreThanHalf}
$$

今回、これを有限 depth range に上げた。

もし、

$$
\forall j<len,\;\text{ContinuationOutrunsRecovery at }r+j
$$

なら、

$$
\forall j<len,\;\text{MoreThanHalf at }r+j
$$

となる。

そして、pressure depth count を

$$
P(n,k,r,len)=\#{j<len\mid \text{MoreThanHalf at }r+j}
$$

と読むと、

$$
P(n,k,r,len)=len
$$

が得られる。

つまり、全 depth が failure branch なら、pressure depth count は全範囲を埋める。

これは、まだ矛盾ではない。
だが、「失敗が長く続いた」という曖昧な状態を、

$$
P=len
$$

という有限 count の命題へ変換した。

これが今回の数学的成果じゃ。

## 5. 今回閉じたもの

今回閉じたのは、

```text id="u0s7za"
failure range
  -> pressure profile
  -> pressure depth count = len
```

というルートじゃ。

これまでの主語は、

```text id="lt3uon"
単発 depth の分岐
```

だった。

今回からは、

```text id="bwwulp"
depth range の profile
```

が主語になる。

これは非常に重要。
Collatz の low-peeling は単発ではなく、深く潜る連続現象だからじゃ。

## 6. まだ閉じていないもの

今回まだ閉じていないのは、controlled depth 側との分割じゃ。

現状あるのは pressure depth count。

```lean id="r8yc20"
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
```

しかし、その相方である controlled depth count がまだない。

各 depth には No.106 の dichotomy がある。

```text id="bsoz7b"
AtMostHalf
or
MoreThanHalf
```

したがって、depth range 全体は、

```text id="rh4g9u"
controlled depths
pressure depths
```

に分かれるはずじゃ。

次はここを閉じるのが自然。

## 7. 次の指示

No.108 は、report にある通り、**mixed depth-mode distribution** を作るのがよい。

つまり、

```text id="ja0s2s"
controlledDepthCount + pressureDepthCount = len
```

を目標にする。

ここで controlled をどう定義するかは二通りある。

## 7.1. AtMostHalf ベースの controlled count

一番自然なのは、pressure count の相方として `AtMostHalf` を数える形じゃ。

```lean id="vbqhat"
noncomputable def sourceContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))
```

tail 版も同様。

この場合、partition theorem は `atMostHalf_or_moreThanHalf` から出す。

$$
\text{controlledCount}+\text{pressureCount}=len
$$

これは美しい。
なぜなら、これは純粋に `AtMostHalf / MoreThanHalf` の二分岐だからじゃ。

## 7.2. Dominance ベースの controlled count

もう一つは、`RecoveryDominatesContinuation` を数える形。

```lean id="8d1c3o"
noncomputable def sourceRecoveryDominanceDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ := ...
```

この場合、相方は `ContinuationOutrunsRecovery` で、partition は

```lean id="78g8ay"
recoveryDominates_or_continuationOutruns
```

から出る。

ただ、今の pressure depth count は `MoreThanHalf` を数えているので、まずは `AtMostHalf` ベースの controlled count を推す。

## 8. 一歩先ゆく推論

mixed depth-mode distribution が入ると、構造は checkpoint 100 と完全に対応する。

checkpoint 100 では、

$$
\sum_{a<2^d}C_{d,a}=k
$$

だった。

これは、

```text id="t6hdsa"
window 内の label mass が residue cell に分配される
```

という保存則。

次に狙う

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=len
$$

は、

```text id="m91g2b"
depth range 内の mode が controlled / pressure に分配される
```

という保存則じゃ。

つまり、DkMath の観測階層はこうなる。

```text id="csdgb2"
label distribution over residue cells
  -> mass flow

depth distribution over modes
  -> pressure profile
```

この二段目が閉じると、次は pressure frequency を `Nat` 不等式で読める。

たとえば、

$$
2\cdot pressureCount\le len
$$

または、

$$
len<2\cdot pressureCount
$$

を言える。

これにより、depth range の中で pressure branch が多すぎるかどうかを扱える。

## 9. さらに次の一手

mixed distribution の次は、**pressure density witness** じゃ。

ただし、これも \(\mathbb{Q}\) や \(\mathbb{R}\) には行かない。

No.101 で作った `AtMostRatioNat` を再利用すればよい。

```lean id="17f2dh"
AtMostHalf sourceContinuationPressureDepthCount len
```

あるいは、

```lean id="f7bws7"
MoreThanHalf sourceContinuationPressureDepthCount len
```

つまり、window mass に対して使っていた half/range ratio を、depth-mode count にも使う。

これで、

```text id="eqr6md"
depth range の半分以上が pressure
```

という命題が Nat で扱える。

その先に、ようやく obstruction が見えてくる。

```text id="piu9yg"
pressure が多すぎる
  -> low-peeling cylinder に残りすぎる
  -> height drift / collision / carrier pressure が必要
```

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source controlled depth count

```lean id="qtzi0d"
noncomputable def sourceContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
              (orbitWindowRetentionMassPow2 n k (r + j))))
```

## 実験 B: tail controlled depth count

```lean id="vphux8"
noncomputable def tailContinuationControlledDepthCount
    (n : OddNat) (k r len : ℕ) : ℕ :=
  by
    classical
    exact
      (List.range len).countP
        (fun j =>
          decide
            (AtMostHalf
              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
              (orbitWindowRetentionMassPow2Tail n k (r + j))))
```

## 実験 C: source mode indicator partition

まずは一点 \(j\) の indicator split を作るとよい。

```lean id="qncwfn"
theorem sourceContinuationModeIndicator_split
    (n : OddNat) (k r j : ℕ) :
    (if AtMostHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j))
      then 1 else 0) +
      (if MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k (r + j))
        (orbitWindowRetentionMassPow2 n k (r + j))
      then 1 else 0) = 1 := by
  classical
  have hsplit :=
    atMostHalf_or_moreThanHalf
      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
      (orbitWindowRetentionMassPow2 n k (r + j))
  unfold AtMostHalf MoreThanHalf at hsplit
  omega
```

ただし `if Prop then` で `Decidable` 周りが面倒なら、`by_cases` で分ける方が安全じゃ。

## 実験 D: source controlled + pressure count equals len

```lean id="o1akjy"
theorem sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationControlledDepthCount n k r len +
      sourceContinuationPressureDepthCount n k r len = len := by
  classical
  induction len with
  | zero =>
      simp [sourceContinuationControlledDepthCount,
        sourceContinuationPressureDepthCount]
  | succ len ih =>
      -- List.range_succ / countP_append / singleton を使う
      -- 最後の index len について atMostHalf_or_moreThanHalf を使う
      sorry
```

ここは最初 `sorry` なしで通すには調整が要る。
先に indicator split を通すのが良い。

## 実験 E: tail mode indicator partition

```lean id="y4hpo8"
theorem tailContinuationModeIndicator_split
    (n : OddNat) (k r j : ℕ) :
    (if AtMostHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
        (orbitWindowRetentionMassPow2Tail n k (r + j))
      then 1 else 0) +
      (if MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
        (orbitWindowRetentionMassPow2Tail n k (r + j))
      then 1 else 0) = 1 := by
  classical
  have hsplit :=
    atMostHalf_or_moreThanHalf
      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
      (orbitWindowRetentionMassPow2Tail n k (r + j))
  unfold AtMostHalf MoreThanHalf at hsplit
  omega
```

## 実験 F: tail controlled + pressure count equals len

```lean id="bqwwiw"
theorem tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationControlledDepthCount n k r len +
      tailContinuationPressureDepthCount n k r len = len := by
  classical
  induction len with
  | zero =>
      simp [tailContinuationControlledDepthCount,
        tailContinuationPressureDepthCount]
  | succ len ih =>
      -- source 版と同様
      sorry
```

## 実験 G: pressure count bound by len

partition が重ければ、まずは簡単な bound でもよい。

```lean id="q6we17"
theorem sourceContinuationPressureDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    sourceContinuationPressureDepthCount n k r len ≤ len := by
  -- countP over List.range len
```

tail 版も。

```lean id="muepgb"
theorem tailContinuationPressureDepthCount_le_len
    (n : OddNat) (k r len : ℕ) :
    tailContinuationPressureDepthCount n k r len ≤ len := by
  -- countP over List.range len
```

これは `List.countP_le_length` 的な補題が使えるなら楽なはずじゃ。

## 11. 次コミットの推奨順

```text id="s6rdot"
1. sourceContinuationControlledDepthCount を追加

2. tailContinuationControlledDepthCount を追加

3. source/tail の pressureDepthCount_le_len を追加

4. source/tail の mode indicator split を試す

5. controlledDepthCount + pressureDepthCount = len を source/tail で証明

6. docs:
   PressureProfile から MixedDepthModeDistribution への接続を追加
```

もし partition theorem が重ければ、まずは `controlled` count の定義と `pressureDepthCount_le_len` だけでも良い。
ただ、今回 pressure count equality が通っているので、次の partition も十分射程内に見える。

## 12. 総括

checkpoint `107` は、failure range を pressure profile へ変え、さらに pressure depth count まで通した良い checkpoint じゃ。

いま到達した構図は、

$$
\text{ContinuationOutrunsRecoveryOnRange}\quad\Longrightarrow\quad\text{PressureDepthCount}=len
$$

じゃ。

次はその相方として、

$$
\text{ControlledDepthCount}+\text{PressureDepthCount}=len
$$

を作る。

これは checkpoint 100 の residue distribution theorem の depth-mode 版になる。

うむ。
いよいよ Collatz.PetalBridge は、`window mass distribution` から `depth-mode distribution` へ進み始めた。これはかなり面白い段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index e80fb837..5fd1d2a0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -2130,6 +2130,180 @@ theorem moreThanHalf_tailContinuation_of_outRunsOnRange
   moreThanHalf_tailContinuation_of_tailContinuationOutruns
     n k (r + j) (tailContinuationOutrunsRecovery_of_onRange n k r len j h hj)
 
+/--
+Generic finite range profile for strict more-than-half pressure.
+
+The functions `count` and `total` are indexed by depth.  The predicate says
+that every depth in the interval `[r, r + len)` carries `MoreThanHalf` pressure.
+-/
+def MoreThanHalfOnRange
+    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
+  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))
+
+/--
+Source continuation pressure profile over a finite depth range.
+
+This packages the statement that source continuation occupies more than half
+of source retention at every depth in `[r, r + len)`.
+-/
+def SourceContinuationPressureOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalfOnRange
+    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
+    (fun d => orbitWindowRetentionMassPow2 n k d)
+    r len
+
+/--
+Tail continuation pressure profile over a finite depth range.
+
+This is the shifted-tail counterpart of
+`SourceContinuationPressureOnRange`.
+-/
+def TailContinuationPressureOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalfOnRange
+    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
+    (fun d => orbitWindowRetentionMassPow2Tail n k d)
+    r len
+
+/-- A source failure range promotes to a source continuation pressure profile. -/
+theorem sourceContinuationPressure_of_outRunsOnRange
+    (n : OddNat) (k r len : ℕ)
+    (h : ContinuationOutrunsRecoveryOnRange n k r len) :
+    SourceContinuationPressureOnRange n k r len := by
+  intro j hj
+  exact moreThanHalf_continuation_of_outRunsOnRange n k r len j h hj
+
+/-- A tail failure range promotes to a tail continuation pressure profile. -/
+theorem tailContinuationPressure_of_outRunsOnRange
+    (n : OddNat) (k r len : ℕ)
+    (h : TailContinuationOutrunsRecoveryOnRange n k r len) :
+    TailContinuationPressureOnRange n k r len := by
+  intro j hj
+  exact moreThanHalf_tailContinuation_of_outRunsOnRange n k r len j h hj
+
+/-- Extract source more-than-half pressure from a source pressure profile. -/
+theorem moreThanHalf_of_sourceContinuationPressure
+    (n : OddNat) (k r len j : ℕ)
+    (h : SourceContinuationPressureOnRange n k r len)
+    (hj : j < len) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+      (orbitWindowRetentionMassPow2 n k (r + j)) :=
+  h j hj
+
+/-- Extract tail more-than-half pressure from a tail pressure profile. -/
+theorem moreThanHalf_of_tailContinuationPressure
+    (n : OddNat) (k r len j : ℕ)
+    (h : TailContinuationPressureOnRange n k r len)
+    (hj : j < len) :
+    MoreThanHalf
+      (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+      (orbitWindowRetentionMassPow2Tail n k (r + j)) :=
+  h j hj
+
+/--
+Number of depths in `[r, r + len)` where source continuation has
+more-than-half pressure.
+
+This is a finite depth-mode count, not a window-mass count.
+-/
+noncomputable def sourceContinuationPressureDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (MoreThanHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+              (orbitWindowRetentionMassPow2 n k (r + j))))
+
+/--
+Number of depths in `[r, r + len)` where tail continuation has
+more-than-half pressure.
+-/
+noncomputable def tailContinuationPressureDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (MoreThanHalf
+              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+              (orbitWindowRetentionMassPow2Tail n k (r + j))))
+
+/--
+If source continuation pressure holds at every depth of the range, then the
+source pressure-depth count fills the whole range.
+-/
+theorem sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
+    (n : OddNat) (k r len : ℕ)
+    (h : SourceContinuationPressureOnRange n k r len) :
+    sourceContinuationPressureDepthCount n k r len = len := by
+  classical
+  unfold sourceContinuationPressureDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_singleton]
+      have ih' :
+          (List.range len).countP
+              (fun j =>
+                decide
+                  (MoreThanHalf
+                    (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+                    (orbitWindowRetentionMassPow2 n k (r + j)))) = len := by
+        apply ih
+        intro j hj
+        exact h j (Nat.lt_trans hj (Nat.lt_succ_self len))
+      have hlast :
+          decide
+              (MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len))) = true := by
+        exact decide_eq_true (h len (Nat.lt_succ_self len))
+      rw [ih', hlast]
+      simp
+
+/--
+If tail continuation pressure holds at every depth of the range, then the tail
+pressure-depth count fills the whole range.
+-/
+theorem tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
+    (n : OddNat) (k r len : ℕ)
+    (h : TailContinuationPressureOnRange n k r len) :
+    tailContinuationPressureDepthCount n k r len = len := by
+  classical
+  unfold tailContinuationPressureDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_singleton]
+      have ih' :
+          (List.range len).countP
+              (fun j =>
+                decide
+                  (MoreThanHalf
+                    (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+                    (orbitWindowRetentionMassPow2Tail n k (r + j)))) = len := by
+        apply ih
+        intro j hj
+        exact h j (Nat.lt_trans hj (Nat.lt_succ_self len))
+      have hlast :
+          decide
+              (MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len))) = true := by
+        exact decide_eq_true (h len (Nat.lt_succ_self len))
+      rw [ih', hlast]
+      simp
+
 /--
 Predicate-facing source half criterion.
 
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 06b26b6c..9903d1eb 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -141,6 +141,7 @@ docs/Collatz-TailDepthRefinement-103.md
 docs/Collatz-FiniteHalfCriterion-104.md
 docs/Collatz-ComparisonPredicates-105.md
 docs/Collatz-MoreThanHalfPressure-106.md
+docs/Collatz-PressureProfile-107.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -326,3 +327,26 @@ The new layer still does not assert that either branch is globally preferred.
 It makes the failure branch measurable: if dominance fails, the obstruction is
 not vague; it is strict more-than-half continuation pressure inside the
 retention cylinder.
+
+Checkpoint 107 packages repeated pressure over a finite depth range:
+
+```lean
+MoreThanHalfOnRange
+SourceContinuationPressureOnRange
+TailContinuationPressureOnRange
+sourceContinuationPressure_of_outRunsOnRange
+tailContinuationPressure_of_outRunsOnRange
+sourceContinuationPressureDepthCount
+tailContinuationPressureDepthCount
+```
+
+The added count theorems show that an all-pressure range fills the whole
+depth-mode count:
+
+```lean
+sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
+tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
+```
+
+This moves the observation from local mass pressure to finite depth-profile
+counting.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index 7b533a6d..fee69a24 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -395,6 +395,53 @@ This gives the obstruction route a concrete finite signature.  If the desired
 dominance condition fails over a range, each failed depth carries strict
 continuation pressure inside the corresponding retention cylinder.
 
+## Pressure Profiles
+
+Checkpoint 107 packages repeated more-than-half pressure over a depth range:
+
+```lean
+MoreThanHalfOnRange
+SourceContinuationPressureOnRange
+TailContinuationPressureOnRange
+```
+
+The range-failure predicates from checkpoint 106 now promote directly to
+pressure profiles:
+
+```lean
+sourceContinuationPressure_of_outRunsOnRange
+tailContinuationPressure_of_outRunsOnRange
+```
+
+Use the extraction theorems when a later proof has a range profile and needs a
+single depth:
+
+```lean
+moreThanHalf_of_sourceContinuationPressure
+moreThanHalf_of_tailContinuationPressure
+```
+
+Checkpoint 107 also starts depth-mode counting:
+
+```lean
+sourceContinuationPressureDepthCount
+tailContinuationPressureDepthCount
+sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
+tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
+```
+
+This is a different finite distribution from the window residue counts.  It
+counts how many depths in `[r, r + len)` are pressure depths.  The first count
+theorems only cover the all-pressure case:
+
+```text
+pressure at every depth
+  -> pressure depth count = len
+```
+
+The next natural layer is a mixed depth-mode distribution: controlled depths
+versus pressure depths.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
@@ -427,22 +474,22 @@ For a new residue channel:
 
 1. Prove the pointwise transition:
 
-```text
-if oddOrbitLabel n i is in source cell A,
-then oddOrbitLabel n (i + 1) is in tail cell B.
-```
+    ```text
+    if oddOrbitLabel n i is in source cell A,
+    then oddOrbitLabel n (i + 1) is in tail cell B.
+    ```
 
 2. Apply:
 
-```lean
-pow2ChannelFlow_of_pointwise
-```
+    ```lean
+    pow2ChannelFlow_of_pointwise
+    ```
 
 3. State a named theorem for the channel:
 
-```text
-sourceChannelCount <= tailChannelCount
-```
+    ```text
+    sourceChannelCount <= tailChannelCount
+    ```
 
 Avoid writing a fresh count induction unless the helper does not fit.
 
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 18446f1e..3e4a335c 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -235,6 +235,17 @@ moreThanHalf_continuation_of_continuationOutruns
 moreThanHalf_tailContinuation_of_tailContinuationOutruns
 moreThanHalf_continuation_of_outRunsOnRange
 moreThanHalf_tailContinuation_of_outRunsOnRange
+MoreThanHalfOnRange
+SourceContinuationPressureOnRange
+TailContinuationPressureOnRange
+sourceContinuationPressure_of_outRunsOnRange
+tailContinuationPressure_of_outRunsOnRange
+moreThanHalf_of_sourceContinuationPressure
+moreThanHalf_of_tailContinuationPressure
+sourceContinuationPressureDepthCount
+tailContinuationPressureDepthCount
+sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
+tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
 atMostHalf_tailContinuation_of_tailRecoveryDominates
 atMostHalf_continuation_of_recoveryCoversHalf
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureProfile-107.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureProfile-107.md
new file mode 100644
index 00000000..283bbe14
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PressureProfile-107.md
@@ -0,0 +1,192 @@
+# Collatz Pressure Profile 107
+
+## Purpose
+
+Checkpoint 106 converted a failed local comparison into a positive observation:
+
+```text
+ContinuationOutrunsRecovery
+  -> MoreThanHalf continuation retention
+```
+
+Checkpoint 107 packages this observation over a finite depth range.
+
+The goal is to move from:
+
+```text
+one depth has pressure
+```
+
+to:
+
+```text
+a finite range has a pressure profile
+```
+
+and then to start counting pressure depths.
+
+## Generic Range Predicate
+
+The generic pressure profile is:
+
+```lean
+def MoreThanHalfOnRange
+    (count total : ℕ → ℕ) (r len : ℕ) : Prop :=
+  ∀ j, j < len → MoreThanHalf (count (r + j)) (total (r + j))
+```
+
+This is deliberately independent of Collatz.  It only says that a pair of
+depth-indexed finite counts satisfies `MoreThanHalf` at every depth in
+`[r, r + len)`.
+
+## Source And Tail Profiles
+
+Source continuation pressure:
+
+```lean
+def SourceContinuationPressureOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalfOnRange
+    (fun d => orbitWindowContinuationSiblingMassPow2 n k d)
+    (fun d => orbitWindowRetentionMassPow2 n k d)
+    r len
+```
+
+Tail continuation pressure:
+
+```lean
+def TailContinuationPressureOnRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalfOnRange
+    (fun d => orbitWindowContinuationSiblingMassPow2Tail n k d)
+    (fun d => orbitWindowRetentionMassPow2Tail n k d)
+    r len
+```
+
+These predicates say that continuation carries strict more-than-half pressure
+against the relevant retention mass at every selected depth.
+
+## From Failure Range To Pressure Range
+
+The failure range predicates now promote directly to pressure profiles:
+
+```lean
+sourceContinuationPressure_of_outRunsOnRange
+tailContinuationPressure_of_outRunsOnRange
+```
+
+The reading is:
+
+```text
+continuation outruns recovery at every depth
+  -> continuation is more than half of retention at every depth
+```
+
+This makes the obstruction range reusable without unfolding the local
+retention split theorem each time.
+
+## Extraction
+
+The profile can be consumed one depth at a time:
+
+```lean
+moreThanHalf_of_sourceContinuationPressure
+moreThanHalf_of_tailContinuationPressure
+```
+
+These are intentionally thin aliases.  Their job is to keep later proofs
+readable when a range hypothesis has already been established.
+
+## Depth-Mode Count
+
+Checkpoint 107 also introduces pressure depth counts:
+
+```lean
+sourceContinuationPressureDepthCount
+tailContinuationPressureDepthCount
+```
+
+These do not count points in the orbit window.  They count depths in a depth
+interval:
+
+```text
+how many j < len are pressure depths?
+```
+
+This is a new finite distribution layer:
+
+```text
+window residue distribution
+  counts labels inside a fixed depth
+
+depth-mode distribution
+  counts pressure/control modes across depths
+```
+
+The first count theorems are the all-pressure cases:
+
+```lean
+sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
+tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
+```
+
+They say:
+
+```text
+pressure at every depth in the range
+  -> pressure depth count = len
+```
+
+## Mathematical Reading
+
+The current finite observation chain is:
+
+```text
+ContinuationOutrunsRecoveryOnRange
+  -> SourceContinuationPressureOnRange
+  -> pressure depth count = len
+```
+
+and similarly for the shifted-tail window.
+
+This still does not prove that long pressure ranges are impossible.  Instead,
+it names the object that a future obstruction theorem should attack:
+
+```text
+a prolonged pressure profile
+```
+
+## Next Candidate
+
+The next natural checkpoint is a mixed depth-mode distribution.
+
+Each depth already has a dichotomy:
+
+```text
+RecoveryDominatesContinuation
+or
+ContinuationOutrunsRecovery
+```
+
+Therefore a range should eventually split into:
+
+```text
+controlled depth count
+pressure depth count
+```
+
+with a theorem of the shape:
+
+```text
+controlledCount + pressureCount = len
+```
+
+This would mirror checkpoint 100, but one level higher:
+
+```text
+checkpoint 100:
+  finite window mass distribution
+
+next route:
+  finite depth-mode distribution
+```
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-107.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-107.md
new file mode 100644
index 00000000..014e0483
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-107.md
@@ -0,0 +1,218 @@
+# Report Petal 107: Pressure Profile
+
+## Summary
+
+Checkpoint 107 implements the pressure-profile layer requested by
+`__next_implementation-107.md`.
+
+Checkpoint 106 proved the local pressure conversion:
+
+```text
+ContinuationOutrunsRecovery
+  -> MoreThanHalf continuation retention
+```
+
+Checkpoint 107 packages that statement across a finite depth range and adds a
+small depth-mode counting experiment.
+
+## Lean Additions
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Generic range predicate:
+
+```lean
+MoreThanHalfOnRange
+```
+
+Source and tail continuation pressure profiles:
+
+```lean
+SourceContinuationPressureOnRange
+TailContinuationPressureOnRange
+```
+
+Failure-range to pressure-profile bridges:
+
+```lean
+sourceContinuationPressure_of_outRunsOnRange
+tailContinuationPressure_of_outRunsOnRange
+```
+
+Profile extraction theorems:
+
+```lean
+moreThanHalf_of_sourceContinuationPressure
+moreThanHalf_of_tailContinuationPressure
+```
+
+Additional experiment: pressure depth counts:
+
+```lean
+sourceContinuationPressureDepthCount
+tailContinuationPressureDepthCount
+sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
+tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
+```
+
+The count experiment passed without `sorry`.
+
+## Mathematical Result
+
+The new route is:
+
+```text
+ContinuationOutrunsRecoveryOnRange
+  -> SourceContinuationPressureOnRange
+  -> sourceContinuationPressureDepthCount = len
+```
+
+and similarly:
+
+```text
+TailContinuationOutrunsRecoveryOnRange
+  -> TailContinuationPressureOnRange
+  -> tailContinuationPressureDepthCount = len
+```
+
+This converts a prolonged failure range into a finite depth-mode object.
+
+The important distinction is:
+
+```text
+window residue counts:
+  count orbit labels inside one residue channel
+
+pressure depth counts:
+  count depths where the local branch is pressure
+```
+
+Thus the implementation has moved from mass distribution inside a fixed depth
+to mode distribution across depths.
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-PressureProfile-107.md
+```
+
+## Additional Inference
+
+Checkpoint 107 suggests that the next useful object is a mixed depth-mode
+distribution.
+
+At each depth, checkpoint 106 gives:
+
+```text
+RecoveryDominatesContinuation
+or
+ContinuationOutrunsRecovery
+```
+
+Therefore a finite range should be decomposable into:
+
+```text
+controlled depths
+pressure depths
+```
+
+The expected next target is:
+
+```lean
+noncomputable def sourceContinuationControlledDepthCount ...
+noncomputable def sourceContinuationPressureDepthCount ...
+```
+
+with a theorem of the shape:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+This is the depth-mode analogue of the checkpoint 100 source distribution
+theorem:
+
+```text
+sum of residue channel counts = window size
+```
+
+The difference is that the new distribution is over modes across depths, not
+over residues across orbit labels.
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
+The first targeted build passed after one repair:
+
+```text
+pressure depth count definitions needed explicit classical decidability
+around decide (MoreThanHalf ...)
+```
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
+Proceed to mixed pressure/control depth counts.
+
+Suggested minimal surface:
+
+```lean
+noncomputable def sourceContinuationControlledDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ := ...
+
+noncomputable def tailContinuationControlledDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ := ...
+```
+
+Then prove a partition theorem:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+The likely proof route is induction on `len`, using the local dichotomy:
+
+```lean
+recoveryDominates_or_continuationOutruns
+tailRecoveryDominates_or_tailContinuationOutruns
+```
+
+This should stay finite and `Nat`-valued.
````
`````

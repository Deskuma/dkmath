# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 789bacac7222f315fca2b824884cc91d5f67059f

## Report

108 チェックポイント完了です。

`DkMath.Collatz.PetalBridge` に mixed depth-mode distribution を追加しました。主な追加は以下です。

```lean
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

これで source/tail ともに、

```text
controlled depth count + pressure depth count = len
```

が no-sorry で閉じました。checkpoint 100 の「window mass distribution」に対して、今回は「depth-mode distribution」が閉じた形です。

文書も同期済みです。

- [Collatz-MixedDepthModeDistribution-108.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-MixedDepthModeDistribution-108.md)
- [report-petal-108.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-108.md)
- README / Guide / Status も 108 の theorem 名と解説を反映済み

検証結果:

```text
lake build DkMath.Collatz.PetalBridge: passed
lake build DkMath.Collatz.Collatz2K26: passed
rg sorry in DkMath/Collatz/PetalBridge.lean: no matches
git diff --check on touched files: passed
```

実装上の注意点として、`if AtMostHalf ... then` や `if decide (AtMostHalf ...) then` を theorem statement に出すと、statement elaboration 時点で `Decidable` が必要になり詰まりました。最終的には indicator split を partition proof 内に閉じ込め、`classical` + `by_cases` で最後の depth だけ処理する形にして通しています。

次は `AtMostHalf (sourceContinuationPressureDepthCount n k r len) len` のような depth-pressure frequency witness へ進めます。まだ有理数・実数に行かず、Nat 不等式のまま「depth range の半分以上が pressure か」を扱える段階です。

## Review

## 1. 状況分析

うむ。checkpoint `108` は、かなり綺麗に閉じた。
No.107 で `pressure depth count` を導入し、今回はその相方として `controlled depth count` を追加して、

```text id="fxur0n"
controlled depth count + pressure depth count = len
```

を source / tail の両方で Lean 定理として閉じた回じゃ。

主な追加は、

```lean id="aotn1q"
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
```

じゃ。レポートでも、checkpoint 100 の「window mass distribution」に対して、今回は「depth-mode distribution」が閉じた形だと整理されている。

これはかなり重要じゃ。
今までの分布は「固定 depth における residue cell への分配」だった。
今回の分布は「有限 depth range における mode への分配」になっている。

## 2. 今回の核心

今回の中心式はこれじゃ。

$$
C(n,k,r,len)+P(n,k,r,len)=len
$$

ここで \(C\) は controlled depth count、\(P\) は pressure depth count。

source 側なら、

$$
C_s+P_s=len
$$

tail 側なら、

$$
C_t+P_t=len
$$

である。

これは、各 depth が必ず次のどちらか一方に分類されることを意味する。

```text id="dhpmvs"
controlled:
  AtMostHalf continuation retention

pressure:
  MoreThanHalf continuation retention
```

つまり、No.106 で得た局所二分岐が、No.108 で有限範囲の保存則になった。

これは checkpoint 100 の構造と対応している。

$$
\sum_{a<2^d}C_{d,a}=k
$$

こちらは orbit window の label が residue cell に分配される保存則だった。

今回の

$$
C+P=len
$$

は、depth range の各 depth が mode に分配される保存則じゃ。

## 3. レビュー

## 3.1. controlled count を足したのが正解

No.107 では pressure count だけがあった。

```lean id="oceox5"
sourceContinuationPressureDepthCount
tailContinuationPressureDepthCount
```

しかし pressure count だけだと、「pressure が何個あるか」は言えても、「残りが何か」が名前を持っていなかった。

今回、

```lean id="d8w338"
sourceContinuationControlledDepthCount
tailContinuationControlledDepthCount
```

が入ったことで、depth range 全体が完全に分解された。

```text id="ozav53"
depth positions
  -> controlled
  -> pressure
```

この二分割は非常に使いやすい。

## 3.2. count bound も良い

今回の bound 群も良い。

```lean id="pwsqzi"
sourceContinuationPressureDepthCount_le_len
tailContinuationPressureDepthCount_le_len
sourceContinuationControlledDepthCount_le_len
tailContinuationControlledDepthCount_le_len
```

これは当然に見えるが、後で `AtMostRatioNat` や `AtMostHalf` に渡すときに便利じゃ。

たとえば、

$$
P\le len
$$

が theorem としてあるので、

```lean id="y4h0ow"
AtMostRatioNat 1 1 P len
```

へ渡せる。

このような小さな橋が、後の API を滑らかにする。

## 3.3. `Decidable` 問題の回避が良い

今回の実装上の注意点も大事じゃ。

`if AtMostHalf ... then` や `if decide (AtMostHalf ...) then` を theorem statement に出すと、statement elaboration 時点で `Decidable` が必要になって詰まった。最終的には indicator split を theorem statement に出さず、partition proof 内で `classical` と `by_cases` を使って最後の depth だけ処理する形で通した、という記録がある。

これは今後の `countP` 系定理でも重要。

```text id="w7hmyr"
Prop-valued indicator は API に露出しすぎない

必要なら proof 内に閉じ込める

classical + by_cases で局所処理する
```

この知見はかなり役立つ。

## 4. 数学的解説

各 depth \(r+j\) では、No.106 により局所的に二分される。

$$
2K_{r+j}\le M_{r+j}
$$

なら controlled。

$$
M_{r+j}<2K_{r+j}
$$

なら pressure。

ここで \(K\) は continuation mass、\(M\) は retention mass。

有限 depth range

$$
r,;r+1,;\ldots,;r+len-1
$$

を考えると、各 depth は controlled か pressure のどちらか一方に入る。

その個数を \(C\)、\(P\) とすれば、

$$
C+P=len
$$

となる。

これは単なる分類ではなく、今後の予算計算の土台じゃ。

なぜなら、今後は

$$
2P\le len
$$

や、

$$
len<2P
$$

のように、depth range における pressure の偏りを Nat 不等式で語れるからじゃ。

## 5. 今回閉じたもの

今回閉じたのは、**depth-mode distribution** じゃ。

```text id="u4votf"
controlled depths
pressure depths
total depth range length
```

の三つが、

$$
\text{controlled}+\text{pressure}=len
$$

で結ばれた。

これにより、DkMath の Collatz.PetalBridge は二つの分布層を持った。

```text id="oifzqy"
1. window mass distribution
   orbit label が residue cell に分配される

2. depth-mode distribution
   depth position が controlled / pressure mode に分配される
```

この二階建て構造は強い。

## 6. まだ閉じていないもの

今回まだ閉じていないのは、pressure frequency の評価じゃ。

つまり、

```lean id="u2ze86"
AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
```

や、

```lean id="wbgqgy"
MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
```

のような depth range 全体の比率判定は、まだ predicate として固定されていない。

また、partition から次のような比較もまだ整理前じゃ。

$$
2P\le len\quad\Longleftrightarrow\quad P\le C
$$

$$
len<2P\quad\Longleftrightarrow\quad C<P
$$

ここを閉じると、pressure frequency が controlled / pressure count の大小比較として読める。

## 7. 次の指示

No.109 は、レポートの提案通り **depth-pressure frequency witness** を作るのがよい。

まずは predicate を置く。

## 7.1. source pressure frequency

```lean id="b4y5q7"
def SourcePressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
```

```lean id="evawto"
def SourcePressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
```

## 7.2. tail pressure frequency

```lean id="ixwatk"
def TailPressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationPressureDepthCount n k r len) len
```

```lean id="ae65nm"
def TailPressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationPressureDepthCount n k r len) len
```

これで、

```text id="xdevy2"
depth range の半分以下が pressure

depth range の半分超えが pressure
```

を \(\mathbb{Q}\) や \(\mathbb{R}\) なしに読める。

## 8. 一歩先ゆく推論

次に欲しいのは、partition との接続じゃ。

いま、

$$
C+P=len
$$

がある。

ここから、

$$
2P\le len
$$

は、

$$
P\le C
$$

と同値になる。

つまり、

```text id="sx4wkh"
pressure が depth range の半分以下
```

とは、

```text id="aayk7n"
pressure depth count <= controlled depth count
```

と同じ意味じゃ。

逆に、

$$
len<2P
$$

は、

$$
C<P
$$

と同値になる。

つまり、

```text id="w6qvq9"
pressure が depth range の半分超え
```

とは、

```text id="jsds6h"
controlled depth count < pressure depth count
```

と同じ意味じゃ。

ここを theorem 化すると、depth-mode distribution がかなり読みやすくなる。

## 9. さらに次の一手

pressure frequency witness の次は、**dominance/pressure の二重分布接続** が見えてくる。

いま pressure count は `MoreThanHalf` mode を数えている。
一方で、No.105/106 には `ContinuationOutrunsRecovery` という原因側 predicate もある。

将来的には、

```text id="rnvyn7"
ContinuationOutrunsRecovery depth count
```

と、

```text id="n8c4b8"
MoreThanHalf pressure depth count
```

の関係を比較したくなる。

`ContinuationOutrunsRecovery` なら `MoreThanHalf` が出るので、

$$
\text{outrunsCount}\le\text{pressureCount}
$$

が期待できる。

逆向きは必ずしも定義上同じではない。
`MoreThanHalf` は \(M<2K\)、`Outruns` は \(R<K\)。split \(M=R+K\) があるので実は同値に近い。
もし source/tail split を使えば、

$$
R<K\quad\Longleftrightarrow\quad M<2K
$$

が出るはずじゃ。

これはかなり面白い。

つまり次々回あたりで、

```text id="fonzd6"
ContinuationOutrunsRecovery <-> MoreThanHalf continuation retention
```

を source / tail で theorem 化できるかもしれない。

片方向はもうある。

```lean id="ecpn9i"
moreThanHalf_continuation_of_continuationOutruns
```

逆向きは新規。

```lean id="jmfe2x"
continuationOutruns_of_moreThanHalf_continuation
```

数学的には、

$$
M=R+K
$$

かつ、

$$
M<2K
$$

なら、

$$
R<K
$$

なので `omega` で通る可能性が高い。

これが通ると、pressure mode と continuation-outruns mode が同値になり、depth count の意味がさらに鋭くなる。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source pressure frequency predicates

```lean id="x3kddy"
def SourcePressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
```

```lean id="h7ddjc"
def SourcePressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
```

## 実験 B: tail pressure frequency predicates

```lean id="p1vwgh"
def TailPressureAtMostHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  AtMostHalf (tailContinuationPressureDepthCount n k r len) len
```

```lean id="43jmal"
def TailPressureMoreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) : Prop :=
  MoreThanHalf (tailContinuationPressureDepthCount n k r len) len
```

## 実験 C: source pressure frequency dichotomy

```lean id="yypdyh"
theorem sourcePressureAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    SourcePressureAtMostHalfOnDepthRange n k r len ∨
      SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange
  unfold SourcePressureMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (sourceContinuationPressureDepthCount n k r len) len
```

## 実験 D: tail pressure frequency dichotomy

```lean id="rogu4d"
theorem tailPressureAtMostHalf_or_moreThanHalfOnDepthRange
    (n : OddNat) (k r len : ℕ) :
    TailPressureAtMostHalfOnDepthRange n k r len ∨
      TailPressureMoreThanHalfOnDepthRange n k r len := by
  unfold TailPressureAtMostHalfOnDepthRange
  unfold TailPressureMoreThanHalfOnDepthRange
  exact atMostHalf_or_moreThanHalf
    (tailContinuationPressureDepthCount n k r len) len
```

## 実験 E: pressure at most half iff pressure <= controlled

まずは片方向だけでもよい。

```lean id="vcey9t"
theorem sourcePressureDepthCount_le_controlled_of_atMostHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourcePressureAtMostHalfOnDepthRange n k r len) :
    sourceContinuationPressureDepthCount n k r len ≤
      sourceContinuationControlledDepthCount n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange at h
  unfold AtMostHalf at h
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega
```

逆方向。

```lean id="z7z2hh"
theorem sourcePressureAtMostHalf_of_pressureDepthCount_le_controlled
    (n : OddNat) (k r len : ℕ)
    (h :
      sourceContinuationPressureDepthCount n k r len ≤
        sourceContinuationControlledDepthCount n k r len) :
    SourcePressureAtMostHalfOnDepthRange n k r len := by
  unfold SourcePressureAtMostHalfOnDepthRange
  unfold AtMostHalf
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega
```

tail 版も同様。

## 実験 F: pressure more than half iff controlled < pressure

source 版。

```lean id="b6mqlw"
theorem sourceControlledDepthCount_lt_pressure_of_pressureMoreThanHalf
    (n : OddNat) (k r len : ℕ)
    (h : SourcePressureMoreThanHalfOnDepthRange n k r len) :
    sourceContinuationControlledDepthCount n k r len <
      sourceContinuationPressureDepthCount n k r len := by
  unfold SourcePressureMoreThanHalfOnDepthRange at h
  unfold MoreThanHalf at h
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega
```

逆方向。

```lean id="wjmlg1"
theorem sourcePressureMoreThanHalf_of_controlledDepthCount_lt_pressure
    (n : OddNat) (k r len : ℕ)
    (h :
      sourceContinuationControlledDepthCount n k r len <
        sourceContinuationPressureDepthCount n k r len) :
    SourcePressureMoreThanHalfOnDepthRange n k r len := by
  unfold SourcePressureMoreThanHalfOnDepthRange
  unfold MoreThanHalf
  have hpart :=
    sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len n k r len
  omega
```

tail 版も同様。

## 実験 G: MoreThanHalf -> ContinuationOutruns source

```lean id="wrfkwb"
theorem continuationOutruns_of_moreThanHalf_continuation
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2 n k r)
        (orbitWindowRetentionMassPow2 n k r)) :
    ContinuationOutrunsRecovery n k r := by
  unfold MoreThanHalf at h
  unfold ContinuationOutrunsRecovery
  rw [orbitWindowRetentionMass_split] at h
  omega
```

## 実験 H: MoreThanHalf -> TailContinuationOutruns

```lean id="mw16yi"
theorem tailContinuationOutruns_of_moreThanHalf_tailContinuation
    (n : OddNat) (k r : ℕ)
    (h :
      MoreThanHalf
        (orbitWindowContinuationSiblingMassPow2Tail n k r)
        (orbitWindowRetentionMassPow2Tail n k r)) :
    TailContinuationOutrunsRecovery n k r := by
  unfold MoreThanHalf at h
  unfold TailContinuationOutrunsRecovery
  rw [orbitWindowRetentionMassPow2Tail_split] at h
  omega
```

## 11. 次コミットの推奨順

```text id="mwq6xg"
1. SourcePressureAtMostHalfOnDepthRange / MoreThanHalf を追加

2. TailPressureAtMostHalfOnDepthRange / MoreThanHalf を追加

3. source/tail pressure frequency dichotomy を追加

4. AtMostHalf pressure count <-> pressure <= controlled を source/tail で追加

5. MoreThanHalf pressure count <-> controlled < pressure を source/tail で追加

6. MoreThanHalf continuation -> ContinuationOutrunsRecovery の逆向きを source/tail で追加

7. docs:
   MixedDepthModeDistribution から DepthPressureFrequency へ接続
```

## 12. 総括

checkpoint `108` は、depth-mode distribution をきっちり閉じた良い回じゃ。

今回の中心は、

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=len
$$

である。

これにより、pressure は単なる局所現象ではなく、depth range 全体で数えられる mode になった。

次は、その pressure count 自体に `AtMostHalf` / `MoreThanHalf` を適用する。

つまり、

```text id="xbb7ne"
pressure depths が depth range の半分以下か

pressure depths が depth range の半分超えか
```

を Nat 不等式で読む。

ここまで行くと、いよいよ「圧力が多すぎる」という obstruction route の入口が見えてくる。

うむ。
Collatz.PetalBridge は、有限観測を一段ずつ積み上げて、かなり良い抽象層に入ってきた。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 5fd1d2a0..b7b6dca5 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -2231,10 +2231,212 @@ noncomputable def tailContinuationPressureDepthCount
     exact
       (List.range len).countP
         (fun j =>
+          decide
+          (MoreThanHalf
+              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+              (orbitWindowRetentionMassPow2Tail n k (r + j))))
+
+/--
+Number of depths in `[r, r + len)` where source continuation is controlled,
+meaning it occupies at most half of source retention.
+-/
+noncomputable def sourceContinuationControlledDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (AtMostHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+              (orbitWindowRetentionMassPow2 n k (r + j))))
+
+/--
+Number of depths in `[r, r + len)` where tail continuation is controlled,
+meaning it occupies at most half of tail retention.
+-/
+noncomputable def tailContinuationControlledDepthCount
+    (n : OddNat) (k r len : ℕ) : ℕ :=
+  by
+    classical
+    exact
+      (List.range len).countP
+        (fun j =>
+          decide
+            (AtMostHalf
+              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+              (orbitWindowRetentionMassPow2Tail n k (r + j))))
+
+/-- Source pressure-depth count is bounded by the depth-range length. -/
+theorem sourceContinuationPressureDepthCount_le_len
+    (n : OddNat) (k r len : ℕ) :
+    sourceContinuationPressureDepthCount n k r len ≤ len := by
+  classical
+  unfold sourceContinuationPressureDepthCount
+  simpa using
+    (List.countP_le_length
+      (p :=
+        fun j =>
+          decide
+            (MoreThanHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+              (orbitWindowRetentionMassPow2 n k (r + j))))
+      (l := List.range len))
+
+/-- Tail pressure-depth count is bounded by the depth-range length. -/
+theorem tailContinuationPressureDepthCount_le_len
+    (n : OddNat) (k r len : ℕ) :
+    tailContinuationPressureDepthCount n k r len ≤ len := by
+  classical
+  unfold tailContinuationPressureDepthCount
+  simpa using
+    (List.countP_le_length
+      (p :=
+        fun j =>
           decide
             (MoreThanHalf
               (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
               (orbitWindowRetentionMassPow2Tail n k (r + j))))
+      (l := List.range len))
+
+/-- Source controlled-depth count is bounded by the depth-range length. -/
+theorem sourceContinuationControlledDepthCount_le_len
+    (n : OddNat) (k r len : ℕ) :
+    sourceContinuationControlledDepthCount n k r len ≤ len := by
+  classical
+  unfold sourceContinuationControlledDepthCount
+  simpa using
+    (List.countP_le_length
+      (p :=
+        fun j =>
+          decide
+            (AtMostHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + j))
+              (orbitWindowRetentionMassPow2 n k (r + j))))
+      (l := List.range len))
+
+/-- Tail controlled-depth count is bounded by the depth-range length. -/
+theorem tailContinuationControlledDepthCount_le_len
+    (n : OddNat) (k r len : ℕ) :
+    tailContinuationControlledDepthCount n k r len ≤ len := by
+  classical
+  unfold tailContinuationControlledDepthCount
+  simpa using
+    (List.countP_le_length
+      (p :=
+        fun j =>
+          decide
+            (AtMostHalf
+              (orbitWindowContinuationSiblingMassPow2Tail n k (r + j))
+              (orbitWindowRetentionMassPow2Tail n k (r + j))))
+      (l := List.range len))
+
+/--
+The source depth range splits into controlled depths and pressure depths.
+-/
+theorem sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+    (n : OddNat) (k r len : ℕ) :
+    sourceContinuationControlledDepthCount n k r len +
+      sourceContinuationPressureDepthCount n k r len = len := by
+  classical
+  unfold sourceContinuationControlledDepthCount
+  unfold sourceContinuationPressureDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_singleton, List.countP_singleton]
+      have hlast :
+          (if decide
+              (AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)))
+            then 1 else 0) +
+            (if decide
+              (MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)))
+            then 1 else 0) = 1 := by
+        by_cases hc :
+            AtMostHalf
+              (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+              (orbitWindowRetentionMassPow2 n k (r + len))
+        · have hnot :
+              ¬ MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)) := by
+            intro hm
+            unfold AtMostHalf at hc
+            unfold MoreThanHalf at hm
+            omega
+          simp [hc, hnot]
+        · have hm :
+              MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                (orbitWindowRetentionMassPow2 n k (r + len)) := by
+            cases
+                atMostHalf_or_moreThanHalf
+                  (orbitWindowContinuationSiblingMassPow2 n k (r + len))
+                  (orbitWindowRetentionMassPow2 n k (r + len)) with
+            | inl hcontrolled => exact False.elim (hc hcontrolled)
+            | inr hpressure => exact hpressure
+          simp [hc, hm]
+      omega
+
+/--
+The tail depth range splits into controlled depths and pressure depths.
+-/
+theorem tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+    (n : OddNat) (k r len : ℕ) :
+    tailContinuationControlledDepthCount n k r len +
+      tailContinuationPressureDepthCount n k r len = len := by
+  classical
+  unfold tailContinuationControlledDepthCount
+  unfold tailContinuationPressureDepthCount
+  induction len with
+  | zero =>
+      simp
+  | succ len ih =>
+      rw [List.range_succ, List.countP_append, List.countP_append,
+        List.countP_singleton, List.countP_singleton]
+      have hlast :
+          (if decide
+              (AtMostHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)))
+            then 1 else 0) +
+            (if decide
+              (MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)))
+            then 1 else 0) = 1 := by
+        by_cases hc :
+            AtMostHalf
+              (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+              (orbitWindowRetentionMassPow2Tail n k (r + len))
+        · have hnot :
+              ¬ MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
+            intro hm
+            unfold AtMostHalf at hc
+            unfold MoreThanHalf at hm
+            omega
+          simp [hc, hnot]
+        · have hm :
+              MoreThanHalf
+                (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                (orbitWindowRetentionMassPow2Tail n k (r + len)) := by
+            cases
+                atMostHalf_or_moreThanHalf
+                  (orbitWindowContinuationSiblingMassPow2Tail n k (r + len))
+                  (orbitWindowRetentionMassPow2Tail n k (r + len)) with
+            | inl hcontrolled => exact False.elim (hc hcontrolled)
+            | inr hpressure => exact hpressure
+          simp [hc, hm]
+      omega
 
 /--
 If source continuation pressure holds at every depth of the range, then the
diff --git a/lean/dk_math/DkMath/Collatz/README.md b/lean/dk_math/DkMath/Collatz/README.md
index 9903d1eb..145980af 100644
--- a/lean/dk_math/DkMath/Collatz/README.md
+++ b/lean/dk_math/DkMath/Collatz/README.md
@@ -142,6 +142,7 @@ docs/Collatz-FiniteHalfCriterion-104.md
 docs/Collatz-ComparisonPredicates-105.md
 docs/Collatz-MoreThanHalfPressure-106.md
 docs/Collatz-PressureProfile-107.md
+docs/Collatz-MixedDepthModeDistribution-108.md
 docs/Collatz-PetalBridge-Guide.md
 docs/Collatz-PetalBridge-Status.md
 ```
@@ -350,3 +351,21 @@ tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 
 This moves the observation from local mass pressure to finite depth-profile
 counting.
+
+Checkpoint 108 closes the mixed depth-mode distribution:
+
+```lean
+sourceContinuationControlledDepthCount
+tailContinuationControlledDepthCount
+sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+```
+
+The reading is:
+
+```text
+controlled depth count + pressure depth count = depth range length
+```
+
+This is the depth-mode analogue of the finite residue distribution from
+checkpoint 100.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-MixedDepthModeDistribution-108.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-MixedDepthModeDistribution-108.md
new file mode 100644
index 00000000..a7ed1d0b
--- /dev/null
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-MixedDepthModeDistribution-108.md
@@ -0,0 +1,140 @@
+# Collatz Mixed Depth-Mode Distribution 108
+
+## Purpose
+
+Checkpoint 107 introduced pressure depth counts:
+
+```lean
+sourceContinuationPressureDepthCount
+tailContinuationPressureDepthCount
+```
+
+Checkpoint 108 adds the complementary controlled counts and proves that every
+depth in a finite range is counted by exactly one of the two modes:
+
+```text
+controlled
+pressure
+```
+
+## Controlled Counts
+
+Source controlled depths:
+
+```lean
+sourceContinuationControlledDepthCount
+```
+
+Tail controlled depths:
+
+```lean
+tailContinuationControlledDepthCount
+```
+
+These count depths where continuation is at most half of the relevant
+retention mass:
+
+```text
+AtMostHalf continuation retention
+```
+
+The pressure counts from checkpoint 107 count the strict complementary mode:
+
+```text
+MoreThanHalf continuation retention
+```
+
+## Basic Bounds
+
+Checkpoint 108 records that all four depth-mode counts are bounded by the
+range length:
+
+```lean
+sourceContinuationPressureDepthCount_le_len
+tailContinuationPressureDepthCount_le_len
+sourceContinuationControlledDepthCount_le_len
+tailContinuationControlledDepthCount_le_len
+```
+
+These are finite `List.countP` bounds over `List.range len`.
+
+## Main Partition
+
+Source depth-mode distribution:
+
+```lean
+sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+```
+
+Tail depth-mode distribution:
+
+```lean
+tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+```
+
+The reading is:
+
+```text
+controlled depth count + pressure depth count = len
+```
+
+This is the depth-mode counterpart of the checkpoint 100 residue distribution.
+
+## Proof Shape
+
+The proof is by induction on `len`.
+
+At the final depth of the successor step, the local dichotomy is:
+
+```lean
+atMostHalf_or_moreThanHalf
+```
+
+The two branches are exclusive because:
+
+```text
+AtMostHalf count total     means 2 * count <= total
+MoreThanHalf count total   means total < 2 * count
+```
+
+The final singleton therefore contributes exactly one count to either the
+controlled side or the pressure side.
+
+## Mathematical Reading
+
+The Collatz/Petal bridge now has two finite distribution layers:
+
+```text
+checkpoint 100:
+  orbit-window labels distribute across residue cells
+
+checkpoint 108:
+  depth positions distribute across controlled/pressure modes
+```
+
+This does not assert that pressure is rare.  It gives a precise finite
+accounting identity that future obstruction arguments can use.
+
+## Next Candidate
+
+The next natural step is to reuse the existing finite-ratio vocabulary on the
+depth-mode counts:
+
+```lean
+AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
+MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
+```
+
+This would allow statements such as:
+
+```text
+at most half of the depth range is pressure
+```
+
+or:
+
+```text
+more than half of the depth range is pressure
+```
+
+still entirely as `Nat` inequalities.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
index fee69a24..5a7c3dfc 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Guide.md
@@ -442,6 +442,50 @@ pressure at every depth
 The next natural layer is a mixed depth-mode distribution: controlled depths
 versus pressure depths.
 
+## Mixed Depth-Mode Distribution
+
+Checkpoint 108 adds the controlled side of the pressure count:
+
+```lean
+sourceContinuationControlledDepthCount
+tailContinuationControlledDepthCount
+```
+
+Both pressure and controlled counts are bounded by the range length:
+
+```lean
+sourceContinuationPressureDepthCount_le_len
+tailContinuationPressureDepthCount_le_len
+sourceContinuationControlledDepthCount_le_len
+tailContinuationControlledDepthCount_le_len
+```
+
+The main partition theorems are:
+
+```lean
+sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+```
+
+They say:
+
+```text
+controlled depth count + pressure depth count = len
+```
+
+This is the depth-mode analogue of the finite channel distribution theorem.
+Checkpoint 100 counted how orbit-window labels distribute across residue
+cells.  Checkpoint 108 counts how depth positions distribute across the two
+local modes:
+
+```text
+AtMostHalf mode
+MoreThanHalf mode
+```
+
+This still does not prove that pressure is rare.  It provides the finite budget
+surface needed to state such a claim without leaving `Nat`.
+
 ## Recursive Petal Residues
 
 The current recursive two-adic Petal channels are:
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 3e4a335c..12d34c6d 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -244,6 +244,14 @@ moreThanHalf_of_sourceContinuationPressure
 moreThanHalf_of_tailContinuationPressure
 sourceContinuationPressureDepthCount
 tailContinuationPressureDepthCount
+sourceContinuationControlledDepthCount
+tailContinuationControlledDepthCount
+sourceContinuationPressureDepthCount_le_len
+tailContinuationPressureDepthCount_le_len
+sourceContinuationControlledDepthCount_le_len
+tailContinuationControlledDepthCount_le_len
+sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
 sourceContinuationPressureDepthCount_eq_len_of_pressureOnRange
 tailContinuationPressureDepthCount_eq_len_of_pressureOnRange
 atMostHalf_continuation_of_recoveryDominates
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-108.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-108.md
new file mode 100644
index 00000000..14ffad0a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-108.md
@@ -0,0 +1,220 @@
+# Report Petal 108: Mixed Depth-Mode Distribution
+
+## Summary
+
+Checkpoint 108 implements the mixed depth-mode distribution requested by
+`__next_implementation-108.md`.
+
+Checkpoint 107 introduced pressure depth counts.  Checkpoint 108 adds the
+controlled side and proves:
+
+```text
+controlled depth count + pressure depth count = len
+```
+
+for both the source and shifted-tail windows.
+
+## Lean Additions
+
+Implemented in:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Controlled depth counts:
+
+```lean
+sourceContinuationControlledDepthCount
+tailContinuationControlledDepthCount
+```
+
+Depth-count bounds:
+
+```lean
+sourceContinuationPressureDepthCount_le_len
+tailContinuationPressureDepthCount_le_len
+sourceContinuationControlledDepthCount_le_len
+tailContinuationControlledDepthCount_le_len
+```
+
+Mixed distribution theorems:
+
+```lean
+sourceContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+tailContinuationControlledDepthCount_add_pressureDepthCount_eq_len
+```
+
+The final partition theorems passed without `sorry`.
+
+## Mathematical Result
+
+At each depth, the local finite split is:
+
+```text
+AtMostHalf continuation retention
+or
+MoreThanHalf continuation retention
+```
+
+Checkpoint 108 counts these modes across a finite depth interval:
+
+```text
+[r, r + len)
+```
+
+The resulting conservation law is:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+This is the depth-mode analogue of checkpoint 100:
+
+```text
+sum of residue channel counts = window size
+```
+
+The new distribution is not over orbit labels.  It is over depth positions.
+
+## Implementation Note
+
+An initial attempt exposed indicator theorems with theorem statements of the
+form:
+
+```lean
+if AtMostHalf ... then 1 else 0
+```
+
+and later:
+
+```lean
+if decide (AtMostHalf ...) then 1 else 0
+```
+
+That failed because the statement itself needed `Decidable` instances before
+the proof body could introduce `classical`.
+
+The working route keeps the final singleton indicator split inside the
+partition proof.  There, `classical` is already available, and `by_cases`
+handles the final depth directly.
+
+This is worth remembering for later `countP`-based mixed profiles:
+
+```text
+avoid exposing Prop-valued if/decide indicators in theorem statements
+unless a decidability surface is deliberately part of the API.
+```
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
+lean/dk_math/DkMath/Collatz/docs/Collatz-MixedDepthModeDistribution-108.md
+```
+
+## Additional Inference
+
+The useful next layer is pressure frequency over depth ranges.
+
+Now that we have:
+
+```text
+controlledDepthCount + pressureDepthCount = len
+```
+
+we can reuse the finite ratio predicates:
+
+```lean
+AtMostHalf
+MoreThanHalf
+AtMostRatioNat
+```
+
+on the depth-mode counts themselves.
+
+Candidate next statements:
+
+```lean
+AtMostHalf
+  (sourceContinuationPressureDepthCount n k r len)
+  len
+```
+
+or:
+
+```lean
+MoreThanHalf
+  (sourceContinuationPressureDepthCount n k r len)
+  len
+```
+
+These would say that pressure occupies at most half, or more than half, of the
+depth range.  This remains finite and `Nat`-valued.
+
+The obstruction route then becomes:
+
+```text
+too many pressure depths
+  -> retention cylinder remains too dominant
+  -> height drift / collision / carrier pressure must compensate
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
+The targeted `DkMath.Collatz.PetalBridge` build passed after repairing the
+indicator theorem approach described above.
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
+Proceed to depth-pressure frequency witnesses.
+
+Minimal API:
+
+```lean
+def SourcePressureAtMostHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  AtMostHalf (sourceContinuationPressureDepthCount n k r len) len
+
+def SourcePressureMoreThanHalfOnDepthRange
+    (n : OddNat) (k r len : ℕ) : Prop :=
+  MoreThanHalf (sourceContinuationPressureDepthCount n k r len) len
+```
+
+Add tail counterparts and thin projection/constructor theorems.  Do not move
+to rational or real frequencies yet.
````
`````

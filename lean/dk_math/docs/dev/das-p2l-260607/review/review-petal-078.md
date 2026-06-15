# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: fefbc51d335661262fc787df2dc0b71180e51eec

## Report

実装しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、Collatz 観測窓の順序付き height profile を追加しました。

```lean
orbitWindowHeightSeq
orbitWindowHeightSeq_length
orbitWindowHeightSeq_sum_eq_sumS
```

核心はこれです。

```lean
(orbitWindowHeightSeq n k).sum = sumS n k
```

これで Petal 側の「有限窓の順序付き高さ列」と、Collatz 側の既存 `sumS` が正式に接続されました。

[Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md) も同期し、`heightSeq -> sumS -> drift input` の読みを追記しています。

検証済み:

```bash
lake build DkMath.Collatz.PetalBridge
lake build DkMath.Collatz.Collatz2K26
git diff --check -- lean/dk_math/DkMath/Collatz/PetalBridge.lean lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
```

いずれも成功です。既存の `ZsigmondyCyclotomicResearch.lean` の `sorry` warning は出ていますが、今回の変更とは無関係です。

## Review

うむ。これは **Collatz Petal 窓に「順序」が入った** という進展じゃ。
前回までの窓は、

```text id="izdz5m"
OrbitWindow n k = Finset.range k
```

として、有限範囲の点集合を見ていた。
今回の `orbitWindowHeightSeq` によって、その窓の中を **時系列として読む** ことができるようになった。

## 1. 今回の核心

追加された主役はこれ。

```lean id="9x00yg"
orbitWindowHeightSeq
orbitWindowHeightSeq_length
orbitWindowHeightSeq_sum_eq_sumS
```

意味は、

```text id="s9d4uv"
orbitWindowHeightSeq n k
  = [height at time 0, height at time 1, ..., height at time k-1]
```

そして核心 theorem が、

```lean id="p5oojb"
(orbitWindowHeightSeq n k).sum = sumS n k
```

これで、Petal 側の「観測窓の高さ列」と、Collatz 側の既存 `sumS` が正式に同一データだと接続された。

## 2. 何が前進したか

前回までは、各時刻ごとに

```lean id="xmleic"
orbitWindowHeight n i = s (iterateT i n)
```

が見えていた。

今回は、それを順序付きリストにまとめた。

```text id="unjyyd"
点ごとの height
  -> 窓全体の height profile
```

さらに、その合計が

```text id="6l3mz9"
sumS n k
```

と一致する。

つまり、Petal の観測語彙で見た height profile が、Collatz の drift / growth 側で使う累積高さと同じものになった。

## 3. なぜ List が重要か

`Finset` は順序を忘れる。

だから、

```text id="sf3da9"
どの height が何回出たか
```

を見るにはよいが、

```text id="gjlm7z"
どの順番で height が出たか
```

は見えにくい。

Collatz では順序が重要じゃ。

```text id="ewg0l5"
低い height が続く
高い height が途中で来る
高低が交互に現れる
collision の直前に height がどう変わる
```

こういう情報は、集合ではなく列でないと見えない。

今回 `List.range k` を使ったことで、Petal 窓は単なる点集合から、

```text id="lzxajr"
時系列観測窓
```

になった。

## 4. Collatz の肥大化・縮小化が読める

加速 Collatz の一歩は粗く読むと、

```text id="b0dviz"
T(n) ≈ 3n / 2^h
```

ここで

```text id="ni21vi"
h = v2(3n + 1)
```

じゃ。

したがって、`orbitWindowHeightSeq n k` は、

```text id="eqdcf0"
各ステップでどれだけ 2 の単位核を剥がしたか
```

の列になる。

そして合計

```text id="pwb0jz"
sumS n k
```

は、k ステップ全体で剥がした 2-adic height の総量。

つまり、k ステップの相対伸縮は、

```text id="f6naoj"
3^k による肥大化
2^(sumS n k) による縮小化
```

の競合として読める。

今回の定理は、その縮小化側のデータを Petal 窓から正式に読めるようにした、ということじゃ。

## 5. Petal 語彙での読み

今回の構造はこう読める。

```text id="v1tqc6"
OrbitWindow:
  観測窓

oddOrbitLabel:
  窓内の点

orbitWindowHeight:
  各点の address-like height

orbitWindowHeightSeq:
  窓内を進む height の履歴

sumS:
  height 履歴の総量
```

つまり、

```text id="k1llpi"
点
  -> 高さ
  -> 高さ列
  -> 累積高さ
  -> drift input
```

という流れができた。

これは、Collatz を Petal 窓で見るためのかなり重要な段階じゃ。

## 6. 今回の Lean 実装の良さ

`orbitWindowHeightSeq_sum_eq_sumS` の証明は、構造的に素直じゃ。

```lean id="1l7jwt"
induction k
```

で、`List.range_succ` と `sumS` の再帰に合わせている。

ここは良い。
なぜなら、今後 prefix / suffix / sliding window の補題を追加するときにも、同じ再帰構造で進められるからじゃ。

## 7. まだ言っていないこと

今回も、これは Collatz 予想の収束証明ではない。

まだ示していないのは、

```text id="shrl8t"
sumS n k が常に十分大きい
drift が必ず負になる
非自明周期が存在しない
```

などじゃ。

今回示したのは、

```text id="m2lhnu"
Petal 観測窓の順序付き height 列の合計が、
Collatz 側の既存累積 height と一致する
```

という橋。

つまり、証明本体ではなく、観測量の同一化じゃ。

だが、これはとても大事。
観測量が一致していないと、Petal 側で見た統計を Collatz の drift へ渡せないからじゃ。

## 8. 次に欲しい theorem

次はかなり明確じゃ。

### 8.1. 平均 height

```lean id="rywp4w"
def orbitWindowHeightAvg ...
```

または自然数のまま、

```text id="7h7eov"
k * threshold <= sumS n k
```

のような形。

特に Collatz drift では、直感的に

```text id="03jihb"
sumS n k が k * log₂ 3 を超えるか
```

が重要になる。

Lean では実数化が必要になるので、まずは整数 threshold で、

```lean id="1o88xd"
theorem orbitWindowHeightSeq_sum_ge_of_forall_ge
```

のような補題が欲しい。

### 8.2. prefix sum

```lean id="p2yjhc"
(orbitWindowHeightSeq n k).take r
```

と `sumS n r` の接続。

これは、窓の先頭部分を観測するために必要。

```lean id="pb5c2q"
theorem orbitWindowHeightSeq_take_sum_eq_sumS
```

### 8.3. nth 取得

```lean id="lw6krn"
(orbitWindowHeightSeq n k).get? i = some (orbitWindowHeight n i)
```

これは、リスト profile と時刻 `i` の観測を往復するために便利。

### 8.4. collision と height profile

collision があると、

```text id="7rgdwk"
iterateT i n = iterateT j n
```

が出る。

すると当然、

```text id="f3kpst"
orbitWindowHeight n i = orbitWindowHeight n j
```

も出るはず。

これはかなり欲しい。

```lean id="3aw577"
theorem orbitWindowHeight_eq_of_collision
```

意味は、

```text id="75qzga"
同じ odd state に戻ったなら、次の height も同じ
```

これで fold/cycle の height pattern が見える。

## 9. 現在の到達点

いまの Collatz.PetalBridge は、次の段階まで来た。

```text id="zlhvhb"
Step 1:
  oddOrbitLabel
  -> Collatz 軌道点を Petal label として読む

Step 2:
  OrbitWindow
  -> 有限窓を明示する

Step 3:
  Separated / Collision
  -> 窓内の基本分岐を固定する

Step 4:
  orbitWindowHeight
  -> 各点に v2 height を貼る

Step 5:
  orbitWindowHeightSeq
  -> height を順序付き profile として読む

Step 6:
  profile sum = sumS
  -> Petal 窓と Collatz drift 入力を接続する
```

これはかなり良い流れじゃ。

## 10. 総括

今回の進展を一言で言えば、

```text id="oyrngq"
Collatz Petal 窓の height 観測が、
順序付き列として定義され、
その合計が既存の sumS と一致することが Lean で固定された。
```

これにより、Petal 側では、

```text id="tj0vs1"
窓内の局所 height profile
```

を見られる。

Collatz 側では、

```text id="azec6g"
sumS による累積 drift 入力
```

として使える。

つまり、

```text id="a4ygrg"
局所観測 profile
  -> 累積 height
  -> drift / growth estimate
```

の橋ができた。

うむ。
これは **Petal 窓が、Collatz の肥大化・縮小化を時系列で測る計器になった** 段階じゃ。次は `sumS` から `driftReal` へ、あるいは prefix / average height へ接続すると、統計確率論の入口がかなり開く。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index c61a4c6c..97258d2c 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -75,6 +75,16 @@ This is the first address-like label attached to the Collatz observation window.
 noncomputable def orbitWindowHeight (n : OddNat) (i : ℕ) : ℕ :=
   rawHeightLabel (oddOrbitLabel n i)
 
+/--
+The ordered height profile observed in the first `k` accelerated Collatz
+states.
+
+This keeps order, unlike a finite support/image view.  It is the window-level
+form of the sequence summed by `sumS`.
+-/
+noncomputable def orbitWindowHeightSeq (n : OddNat) (k : ℕ) : List ℕ :=
+  (List.range k).map (orbitWindowHeight n)
+
 /--
 The first `k` accelerated Collatz odd-state labels are pairwise separated.
 
@@ -119,6 +129,31 @@ corresponding accelerated state.
 theorem orbitWindowHeight_eq_s_iterateT (n : OddNat) (i : ℕ) :
     orbitWindowHeight n i = s (iterateT i n) := rfl
 
+/--
+The ordered height profile has length equal to the window size.
+-/
+theorem orbitWindowHeightSeq_length (n : OddNat) (k : ℕ) :
+    (orbitWindowHeightSeq n k).length = k := by
+  simp [orbitWindowHeightSeq]
+
+/--
+The sum of the ordered height profile is exactly the existing Collatz `sumS`.
+
+This connects the Petal-style finite observation window with the existing
+Collatz drift/statistics API.
+-/
+theorem orbitWindowHeightSeq_sum_eq_sumS (n : OddNat) (k : ℕ) :
+    (orbitWindowHeightSeq n k).sum = sumS n k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowHeightSeq, sumS]
+  | succ k ih =>
+      have ih' :
+          (List.map (orbitWindowHeight n) (List.range k)).sum = sumS n k := by
+        simpa [orbitWindowHeightSeq] using ih
+      simp [orbitWindowHeightSeq, List.range_succ, sumS,
+        orbitWindowHeight_eq_s_iterateT, ih']
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 589bf5c2..6a23086d 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -78,6 +78,7 @@ OrbitWindow
 rawHeightLabel
 oddOrbitLabel
 orbitWindowHeight
+orbitWindowHeightSeq
 OddOrbitLabelsPairwiseSeparated
 OrbitWindowSeparated
 OrbitWindowCollision
@@ -89,6 +90,7 @@ where:
 OrbitWindow n k = Finset.range k
 oddOrbitLabel n i = the natural value of iterateT i n
 orbitWindowHeight n i = v2 (3 * oddOrbitLabel n i + 1)
+orbitWindowHeightSeq n k = the ordered list of the first k height labels
 ```
 
 The first theorem set is deliberately thin:
@@ -97,6 +99,8 @@ The first theorem set is deliberately thin:
 orbitWindow_eq_range
 rawHeightLabel_eq_s
 orbitWindowHeight_eq_s_iterateT
+orbitWindowHeightSeq_length
+orbitWindowHeightSeq_sum_eq_sumS
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -173,6 +177,26 @@ rawHeightLabel n = v2 (3n + 1)
 orbitWindowHeight n i = rawHeightLabel (oddOrbitLabel n i)
 ```
 
+The ordered height profile is now explicitly connected to the existing
+Collatz accumulated-height API:
+
+```text
+(orbitWindowHeightSeq n k).sum = sumS n k
+```
+
+This means the Petal observation window can read the same data in two ways:
+
+```text
+ordered local profile:
+  [height at time 0, height at time 1, ...]
+
+accumulated drift input:
+  sumS n k
+```
+
+The profile form is useful for address/window diagnostics, while `sumS` is the
+existing Collatz side used by drift and growth estimates.
+
 The bridge theorem
 
 ```lean
@@ -191,6 +215,7 @@ orbit labels are usable carrier labels
 orbit labels are mapped to prime labels
 orbit collision implies a specific fold/cycle condition
 2-adic height controls Petal address movement
+ordered height profile controls accumulated Collatz drift
 ```
 
 ## Next Candidate Work
@@ -198,10 +223,11 @@ orbit collision implies a specific fold/cycle condition
 The next safe steps are:
 
 ```text
-1. Connect v2_shift_invariant to a Petal address/residue reading.
+1. Connect the ordered height profile to a Petal address/residue reading.
 2. Add a window occupation/address transition layer.
-3. Test whether an external label transform can turn orbit labels into carrier labels.
-4. Only after that, test whether Collatz labels can feed ABC support/rad.
+3. Use `sumS`/height-profile bounds as the Collatz-side drift input.
+4. Test whether an external label transform can turn orbit labels into carrier labels.
+5. Only after that, test whether Collatz labels can feed ABC support/rad.
 ```
 
 The main caution is that Collatz state labels are not prime labels.  Any bridge
````
`````

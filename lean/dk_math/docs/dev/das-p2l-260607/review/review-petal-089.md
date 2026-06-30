# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: f1d59dc12281b3618b17605acc02325e7a915729

## Report

088 を実装しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に `orbitWindowHeightCountGeTail` を追加し、tail residue count から tail height count へ戻す橋を入れました。さらに `3 mod 8` source count を `sumS n (k + 1)` の drift budget に渡す強い版まで通しています。

主な到達点はこれです。

```lean
theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

つまり、`3 mod 8` は「今は height 1 だが、次時刻の追加剥離を供給する channel」として、一般の `k` 窓で数えられるようになりました。

同期済み:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-088.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-088.md)

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check` pass

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き出ますが、今回の変更で新しい `sorry` は入れていません。

## Review

## 1. 状況分析

これは checkpoint `088` で、かなり重要な段階に入った。
今回の主語は、もはや単なる transition ではなく、**transition が drift budget に戻ってきた** ことじゃ。

前回までの流れはこうだった。

```text id="d8dkvi"
3 mod 8
  -> next 1 mod 4
  -> next height >= 2
```

今回、それが一般の `k` 窓で、

```text id="vi4mjq"
3 mod 8 の出現回数
  -> tail height >= 2 の出現回数
  -> sumS n (k + 1) の下界
```

まで繋がった。

本命はこれ。

```lean id="u1webc"
theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

添付レポートでも、この theorem は `3 mod 8` を「今は height 1 だが、次時刻の追加剥離を供給する channel」として一般の `k` 窓で数えられるようにしたもの、と整理されている。

これは大きい。
`3 mod 8` が、単なる residue cell ではなく **delayed-peeling source** として drift に寄与することが Lean で固定された。

## 2. 今回の核心

今回追加された軸は四つ。

```text id="raf9dz"
1. tail height count

2. tail residue count -> tail height count

3. tail count -> ordinary longer window

4. 3 mod 8 source count -> delayed drift
```

特に重要なのはこの中間橋じゃ。

```lean id="a12awx"
orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
```

意味は、

```text id="jj8vmc"
0..k-1 で 3 mod 8 にいる回数
  <= 1..k で height >= 2 になる回数
```

これにより、residue transition が height count に戻る。

その後、

```lean id="yphcoa"
orbitWindowHeightCountGeTail_le_countGe_succ
```

で、

```text id="mwpdh3"
tail window 1..k
  は ordinary window 0..k に含まれる
```

を使い、既存の drift theorem へ渡している。

この証明構成は非常に良い。
新しい drift theorem を直接 induction で証明せず、既存の `CountGe 2` drift budget を再利用している。

## 3. 数学的な意味

数学的には、いまこういうことが起きている。

```text id="nsa44h"
time i:
  label is 3 mod 8
  height is exactly 1

time i + 1:
  label is 1 mod 4
  height is at least 2
```

つまり、`3 mod 8` はその時点では弱い。

```text id="wsm6cz"
current contribution:
  height = 1
```

しかし一歩後に追加剥離を生む。

```text id="x1ud5z"
next contribution:
  height >= 2
```

だから、`3 mod 8` の個数は、次の tail window における追加剥離の下界になる。

これは、Collatz の軌道を「その場の height」だけで見ると見落とす構造じゃ。
Petal residue address によって初めて、

```text id="pk00hz"
弱い step の中にも、
次に縮小を予約している channel がある
```

と見える。

## 4. レビュー

今回の実装は、とても良い設計じゃ。

### 4.1. `orbitWindowHeightCountGeTail`

```lean id="p4abv0"
noncomputable def orbitWindowHeightCountGeTail
    (n : OddNat) (k threshold : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
```

これは必要な定義だった。

transition では source が `0..k-1`、receiver が `1..k` になる。
その receiver 側を height count として明示したことで、以後の delayed drift が扱える。

### 4.2. successor formula が良い

```lean id="y4cj49"
orbitWindowHeightCountGe_succ
orbitWindowHeightCountGeTail_succ
```

これらは地味だが重要。
今後、tail / prefix / shifted window を扱うときに、逐次分解がしやすくなる。

### 4.3. tail inclusion の設計が良い

```lean id="wt2a9s"
orbitWindowHeightCountGeTail_le_countGe_succ
```

これは今後の shifted-window work の基本パターンになる。

```text id="p0t3xq"
shifted local count
  -> ordinary longer-window count
  -> existing sumS budget
```

この再利用パターンはかなり強い。

### 4.4. localized two-step theorem も良い

```lean id="dzys7d"
sumS_two_steps_ge_three_of_mod_eight_eq_three_at
```

これにより、任意時刻 `i` で軌道を再始動して、二歩 delayed-peeling を読める。

これは今後、局所パターン解析や path fragment 解析に使える。

## 5. 現在の到達点

いまの Collatz.PetalBridge はこう読める。

```text id="vyzyly"
static layer:
  height occupation

residue layer:
  mod 4 / mod 8 address occupation

transition layer:
  3 mod 8 -> next 1 mod 4
  7 mod 8 -> next 3 mod 4

tail layer:
  next 1 mod 4 -> tail height >= 2

drift layer:
  delayed extra peeling -> sumS lower bound
```

つまり、

```text id="e4f2ps"
residue transition
  -> delayed height count
  -> drift budget
```

が閉じた。

これは相当大きい。
Petal residue graph の辺が、単なる構造記述ではなく、`sumS` の下界に寄与する量として読めるようになった。

## 6. 次の指示：`7 mod 8` の滞留 channel を形式化する

次は、対になる obstruction 側を作るのがよい。

`3 mod 8` は delayed peeling channel だった。

```text id="n7kidx"
3 mod 8
  -> next height >= 2
```

一方、`7 mod 8` は retaining channel じゃ。

```text id="rrzjrv"
7 mod 8
  -> next 3 mod 4
  -> next height = 1
```

これを count level で height 側へ戻したい。

まず定義。

```lean id="x1sjxv"
noncomputable def orbitWindowHeightCountEqTail
    (n : OddNat) (k h : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (orbitWindowHeight n (i + 1) = h))
```

bound。

```lean id="qiztpg"
theorem orbitWindowHeightCountEqTail_le_window
    (n : OddNat) (k h : ℕ) :
    orbitWindowHeightCountEqTail n k h ≤ k := by
  unfold orbitWindowHeightCountEqTail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (orbitWindowHeight n (i + 1) = h))
      (l := List.range k))
```

tail exact height 1 と tail mod 4 = 3 の同一視。

```lean id="mwzp8n"
theorem orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEqTail n k 1 =
      orbitWindowResidueCountMod4EqThreeTail n k := by
  unfold orbitWindowHeightCountEqTail orbitWindowResidueCountMod4EqThreeTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_eq_one_iff_mod_four_eq_three n (k + 1)
      by_cases hheight : orbitWindowHeight n (k + 1) = 1
      · have hres : oddOrbitLabel n (k + 1) % 4 = 3 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n (k + 1) % 4 ≠ 3 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]
```

そして本命。

```lean id="c53ia9"
theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤
      orbitWindowHeightCountEqTail n k 1 := by
  rw [orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three]
  exact residueCountMod8EqSeven_le_nextResidueCountMod4EqThree n k
```

意味は、

```text id="dum2n2"
7 mod 8 の出現数
  <= 次時刻 tail で exact height 1 になる数
```

これで `7 mod 8` が **height-one retention source** として形式化される。

## 7. 一歩先ゆく推論：delayed peeling と retention の分解

ここまで来ると、height-one layer は二種類に分解できる。

```text id="qj0p5s"
height = 1 source:
  3 mod 8:
    next height >= 2

  7 mod 8:
    next height = 1
```

つまり、

```text id="qcj6x2"
height-one は全部同じではない
```

ということが Lean で語れる。

これは Collatz 解析において非常に重要じゃ。
なぜなら、悪いのは「height = 1 が多いこと」ではなく、

```text id="pxtmkw"
height-one retention channel が長く続くこと
```

だからじゃ。

`3 mod 8` は一見 height 1 だが、次で追加剥離を供給する。
`7 mod 8` は次も height 1 側に残る。

この差が Petal address の本質じゃ。

## 8. 次の実装：two-step `7 -> 7` retention experiment

次に試すなら、これ。

```lean id="n0yfpj"
theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7)
    (h1 : oddOrbitLabel n 1 % 8 = 7) :
    sumS n 2 = 2
```

意味は、

```text id="htsasq"
step 0:
  7 mod 8 -> height = 1

step 1:
  7 mod 8 -> height = 1

therefore:
  sumS over two steps = 2
```

これは obstruction 側の witness になる。

ただし、`h1` を仮定に入れるので、これは transition theorem ではなく、pattern witness じゃ。

もう少し安全な補題はこれ。

```lean id="njx4x7"
theorem sumS_two_steps_ge_two_of_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7) :
    2 ≤ sumS n 2
```

ただしこれは `height >= 1` だけでも出るので、研究価値は低い。
やはり本命は exact equality 版。

## 9. もう一つの次手：`3 mod 8` の local delayed drift を任意位置で使う

すでに

```lean id="pg1aja"
sumS_two_steps_ge_three_of_mod_eight_eq_three_at
```

が入った。

次は、それを orbit fragment の記法に寄せたい。

例えば、任意の `i` に対して、

```text id="gh6o04"
time i と i+1 の局所合計が 3 以上
```

を表す localized sum API が欲しくなる。

候補定義。

```lean id="cty7z6"
noncomputable def sumSFrom (n : OddNat) (start len : ℕ) : ℕ :=
  (List.range len).map
    (fun j => orbitWindowHeight n (start + j))
  |>.sum
```

そして、

```lean id="c6yzpa"
theorem sumSFrom_two_ge_three_of_mod_eight_eq_three
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    3 ≤ sumSFrom n i 2
```

これは、`sumS (iterateT i n) 2` より軌道窓の中で読みやすい。
ただし導入は少し早いかもしれぬ。今はまだ `sumS (iterateT i n) 2` でも十分。

## 10. 賢狼が試して欲しいおまけ実験補題

### 実験 A: `7 mod 8` retention を tail exact count に戻す

```lean id="d54mvw"
theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤
      orbitWindowHeightCountEqTail n k 1
```

これは最優先のおまけ。
`3 mod 8` の delayed-peeling に対する、`7 mod 8` の retention counterpart じゃ。

### 実験 B: exact height-one tail partition

tail 側でも、

```text id="vfd6o9"
tail height = 1
  <-> tail mod 4 = 3
```

が入るなら、さらに、

```lean id="ne9v6n"
theorem orbitWindowHeightCountGeTail_two_add_eqTail_one_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 +
      orbitWindowHeightCountEqTail n k 1 = k
```

のような partition が見えるかもしれない。

ただし `height >= 2` と `height = 1` が全 tail を分割するには、全ての tail height が `>= 1` であることを使う。
これは `orbitWindowHeight_one_le n (i+1)` でいけるはず。

名前は、もう少し明確にするなら、

```lean id="le8o4p"
theorem orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 +
      orbitWindowHeightCountEqTail n k 1 = k
```

これは tail window の第一 partition じゃ。

### 実験 C: `3` source と `7` source の tail split

`3 mod 8` は tail `height >= 2` に入り、`7 mod 8` は tail `height = 1` に入る。

したがって、

```lean id="ksyd2m"
theorem residueCountMod8EqThree_add_seven_le_tail_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k
```

これは mod 8 partition からも出るが、tail split の観点では、

```text id="aaoh1h"
height-one source channels split the next tail into
extra-peeling receiver and retention receiver
```

として読める。

## 11. さらに先：finite transition graph vocabulary

ここまで来ると、そろそろ用語を少し立てても良い。

例えば、

```lean id="lfv8sh"
def DelayedPeelingSourceMod8 (r : ℕ) : Prop :=
  r = 3

def RetentionSourceMod8 (r : ℕ) : Prop :=
  r = 7
```

まではまだ早いかもしれぬが、ドキュメント上では次の名前が使える。

```text id="z06gzv"
DelayedPeeling channel:
  3 mod 8

Retention channel:
  7 mod 8

Immediate strong channel:
  5 mod 8

Exact-two channel:
  1 mod 8
```

mod 8 Petal cell の意味が揃ってきた。

```text id="wrfrb1"
1 mod 8:
  exact height 2

3 mod 8:
  height 1 now, height >= 2 next

5 mod 8:
  height >= 3 now

7 mod 8:
  height 1 now, height 1 next at mod 4 level
```

## 12. 実装順序まとめ

次コミットの推奨順はこれ。

```text id="kbb3hu"
1. orbitWindowHeightCountEqTail

2. orbitWindowHeightCountEqTail_le_window

3. orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three

4. orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one

5. orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window

6. sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven

7. optional:
   sumSFrom definition

8. optional:
   sumSFrom_two_ge_three_of_mod_eight_eq_three
```

## 13. 総括

今回の checkpoint `088` で、

```text id="vjcm0r"
3 mod 8 source count
```

は、ついに

```text id="amy6ii"
delayed drift contribution
```

として一般 `k` 窓で `sumS` に入った。

これは、Petal residue graph の有向辺が、単なる遷移ではなく、

```text id="edkvbk"
一拍後の縮小力
```

として測定可能になったことを意味する。

うむ。
次は反対側の `7 mod 8`。
`3` が delayed-peeling channel なら、`7` は retention channel。
この二つを対にして閉じると、mod 8 の exact height-one layer は、**次に縮む枝**と**低剥離に留まる枝**へ分解される。
ここまで行けば、Petal はいよいよ「有限遷移グラフによる Collatz 軌道観測器」と呼べる段階になる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 3b51d3a7..83890785 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -463,6 +463,17 @@ window profile.
 noncomputable def orbitWindowHeightCountGe (n : OddNat) (k threshold : ℕ) : ℕ :=
   (orbitWindowHeightSeq n k).countP (fun x => decide (threshold ≤ x))
 
+/--
+Number of shifted-tail entries whose height is at least `threshold`.
+
+This counts the observations at times `1, 2, ..., k`, indexed as `i + 1` for
+`i < k`.  It is the height-side receiver for delayed transition counts.
+-/
+noncomputable def orbitWindowHeightCountGeTail
+    (n : OddNat) (k threshold : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
+
 /--
 Number of in-window odd-state labels in residue class `1 mod 4`.
 
@@ -579,6 +590,46 @@ theorem orbitWindowHeightCountGe_le_window
     (List.countP_le_length
       (p := fun x => decide (threshold ≤ x)) (l := orbitWindowHeightSeq n k))
 
+/--
+The shifted-tail threshold occupation count is bounded by the tail window size.
+-/
+theorem orbitWindowHeightCountGeTail_le_window
+    (n : OddNat) (k threshold : ℕ) :
+    orbitWindowHeightCountGeTail n k threshold ≤ k := by
+  unfold orbitWindowHeightCountGeTail
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
+      (l := List.range k))
+
+/--
+Successor formula for ordinary threshold occupation counts.
+-/
+theorem orbitWindowHeightCountGe_succ
+    (n : OddNat) (k threshold : ℕ) :
+    orbitWindowHeightCountGe n (k + 1) threshold =
+      orbitWindowHeightCountGe n k threshold +
+        if threshold ≤ orbitWindowHeight n k then 1 else 0 := by
+  unfold orbitWindowHeightCountGe orbitWindowHeightSeq
+  rw [List.range_succ]
+  by_cases h : threshold ≤ orbitWindowHeight n k
+  · simp [h]
+  · simp [h]
+
+/--
+Successor formula for shifted-tail threshold occupation counts.
+-/
+theorem orbitWindowHeightCountGeTail_succ
+    (n : OddNat) (k threshold : ℕ) :
+    orbitWindowHeightCountGeTail n (k + 1) threshold =
+      orbitWindowHeightCountGeTail n k threshold +
+        if threshold ≤ orbitWindowHeight n (k + 1) then 1 else 0 := by
+  unfold orbitWindowHeightCountGeTail
+  rw [List.range_succ]
+  by_cases h : threshold ≤ orbitWindowHeight n (k + 1)
+  · simp [h]
+  · simp [h]
+
 /--
 The mod `4` residue count is bounded by the window size.
 -/
@@ -717,6 +768,29 @@ theorem orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
           exact hheight (hiff.mpr h)
         simp [ih, hheight, hres]
 
+/--
+Tail `height >= 2` occupation is the same as shifted-tail residue occupation
+in class `1 mod 4`.
+-/
+theorem orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGeTail n k 2 =
+      orbitWindowResidueCountMod4EqOneTail n k := by
+  unfold orbitWindowHeightCountGeTail orbitWindowResidueCountMod4EqOneTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_two_le_iff_mod_four_eq_one n (k + 1)
+      by_cases hheight : 2 ≤ orbitWindowHeight n (k + 1)
+      · have hres : oddOrbitLabel n (k + 1) % 4 = 1 := hiff.mp hheight
+        simp [ih, hheight, hres]
+      · have hres : oddOrbitLabel n (k + 1) % 4 ≠ 1 := by
+          intro h
+          exact hheight (hiff.mpr h)
+        simp [ih, hheight, hres]
+
 /--
 Counting `height >= 3` entries is the same as counting odd-state labels in
 residue class `5 mod 8`.
@@ -1217,6 +1291,17 @@ theorem orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
             simpa [hsource, htail] using Nat.le_succ_of_le ih
         · simp [hsource, htail, ih]
 
+/--
+Every `3 mod 8` source label contributes a shifted-tail entry with
+height at least `2`.
+-/
+theorem orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k ≤
+      orbitWindowHeightCountGeTail n k 2 := by
+  rw [orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one]
+  exact orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne n k
+
 /--
 Every `7 mod 8` label in a window contributes a `3 mod 4` label in the
 shifted tail window.
@@ -1243,6 +1328,41 @@ theorem residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
             simpa [hsource, htail] using Nat.le_succ_of_le ih
         · simp [hsource, htail, ih]
 
+/--
+The shifted-tail threshold count is contained in the ordinary count over the
+one-step-longer window.
+
+The tail observes times `1..k`; the ordinary `(k + 1)` window observes
+`0..k`, so it contains the same tail entries plus the initial time.
+-/
+theorem orbitWindowHeightCountGeTail_le_countGe_succ
+    (n : OddNat) (k threshold : ℕ) :
+    orbitWindowHeightCountGeTail n k threshold ≤
+      orbitWindowHeightCountGe n (k + 1) threshold := by
+  induction k with
+  | zero =>
+      unfold orbitWindowHeightCountGeTail
+      simp
+  | succ k ih =>
+      rw [orbitWindowHeightCountGeTail_succ]
+      rw [orbitWindowHeightCountGe_succ]
+      exact Nat.add_le_add ih le_rfl
+
+/--
+The zeroth natural orbit label is the initial odd state.
+-/
+theorem oddOrbitLabel_zero_eq
+    (n : OddNat) :
+    oddOrbitLabel n 0 = n.1 := rfl
+
+/--
+Restarting the orbit at `iterateT i n` makes its zeroth label equal to the
+original label at time `i`.
+-/
+theorem oddOrbitLabel_iterateT_zero_eq
+    (n : OddNat) (i : ℕ) :
+    oddOrbitLabel (iterateT i n) 0 = oddOrbitLabel n i := rfl
+
 /--
 Two-step delayed-peeling experiment.
 
@@ -1265,6 +1385,19 @@ theorem sumS_two_steps_ge_three_of_mod_eight_eq_three
     _ = sumS n 2 := by
       simp [sumS, orbitWindowHeight_eq_s_iterateT]
 
+/--
+Localized two-step delayed-peeling experiment.
+
+The pointwise two-step theorem can be restarted at any accelerated state
+`iterateT i n`.
+-/
+theorem sumS_two_steps_ge_three_of_mod_eight_eq_three_at
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 3) :
+    3 ≤ sumS (iterateT i n) 2 := by
+  apply sumS_two_steps_ge_three_of_mod_eight_eq_three
+  simpa [oddOrbitLabel_iterateT_zero_eq] using hmod
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
@@ -1662,6 +1795,71 @@ theorem orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
     (Nat.add_le_add_left hm k)
     (orbitWindowHeightSeq_sum_ge_window_add_countGe_two n k)
 
+/--
+Strong tail-count drift budget.
+
+The `(k + 1)` ordinary window supplies the base peeling layer, and the shifted
+tail `height >= 2` count supplies the delayed extra layer.
+-/
+theorem orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
+    (n : OddNat) (k : ℕ) :
+    (k + 1) + orbitWindowHeightCountGeTail n k 2 ≤ sumS n (k + 1) := by
+  exact orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+    n (k + 1) (orbitWindowHeightCountGeTail n k 2)
+    (orbitWindowHeightCountGeTail_le_countGe_succ n k 2)
+
+/--
+Weak tail-count drift budget.
+
+The shifted-tail `height >= 2` entries contribute extra peeling inside the
+one-step-longer accumulated window.
+-/
+theorem orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+    (n : OddNat) (k : ℕ) :
+    k + orbitWindowHeightCountGeTail n k 2 ≤ sumS n (k + 1) := by
+  exact le_trans
+    (by
+      have h :
+          k + orbitWindowHeightCountGeTail n k 2 ≤
+            (k + 1) + orbitWindowHeightCountGeTail n k 2 := by
+        omega
+      exact h)
+    (orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two n k)
+
+/--
+Delayed-drift theorem from the `3 mod 8` source channel.
+
+Every source occurrence of `3 mod 8` feeds a shifted-tail `height >= 2` entry,
+so it contributes to the accumulated drift over the one-step-longer window.
+-/
+theorem orbitWindowResidueCountMod8EqThree_delayed_drift
+    (n : OddNat) (k : ℕ) :
+    k + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1) := by
+  exact le_trans
+    (Nat.add_le_add_left
+      (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k) k)
+    (orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two n k)
+
+/--
+Strong delayed-drift theorem from the `3 mod 8` source channel.
+
+This is the count-level form of delayed peeling:
+
+```text
+base layer over 0..k
+  +
+source count of 3 mod 8 over 0..k-1
+  <= sumS over 0..k
+```
+-/
+theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
+    (n : OddNat) (k : ℕ) :
+    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1) := by
+  exact le_trans
+    (Nat.add_le_add_left
+      (orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k) (k + 1))
+    (orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two n k)
+
 /--
 Residue-address drift bridge.
 
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 3f0ba9ab..8ff3f266 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -131,6 +131,7 @@ orbitWindowHeight_eq_of_collision
 orbitWindowHeight_eq_of_same_iterateT
 orbitWindowHeightCountEq
 orbitWindowHeightCountGe
+orbitWindowHeightCountGeTail
 orbitWindowResidueCountMod4EqOne
 orbitWindowResidueCountMod4EqThree
 orbitWindowResidueCountMod8EqOne
@@ -142,6 +143,9 @@ orbitWindowResidueCountMod4EqThreeTail
 orbitWindowPrefixResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
+orbitWindowHeightCountGeTail_le_window
+orbitWindowHeightCountGe_succ
+orbitWindowHeightCountGeTail_succ
 orbitWindowResidueCountMod4EqOne_le_window
 orbitWindowResidueCountMod4EqThree_le_window
 orbitWindowResidueCountMod8EqOne_le_window
@@ -153,6 +157,7 @@ orbitWindowResidueCountMod4EqThreeTail_le_window
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
+orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
 orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
 orbitWindowHeightCountEq_eq_window_of_forall_eq
 orbitWindowHeightCountGe_eq_window_of_forall_ge
@@ -178,8 +183,11 @@ oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
 orbitWindowNextHeight_two_le_of_mod_eight_eq_three
 orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
 orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
+orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
+orbitWindowHeightCountGeTail_le_countGe_succ
 sumS_two_steps_ge_three_of_mod_eight_eq_three
+sumS_two_steps_ge_three_of_mod_eight_eq_three_at
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
 orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
@@ -195,6 +203,10 @@ orbitWindowHeightPrefix_sum_ge_sum_countGe_range
 orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
 orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
 orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+orbitWindowResidueCountMod8EqThree_delayed_drift
+orbitWindowResidueCountMod8EqThree_delayed_drift_strong
 orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
 orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
 orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
@@ -359,6 +371,10 @@ orbitWindowHeightCountEq n k h
 orbitWindowHeightCountGe n k threshold
   = number of entries with height at least threshold
 
+orbitWindowHeightCountGeTail n k threshold
+  = number of shifted tail entries, at times i + 1 for i < k,
+    whose height is at least threshold
+
 orbitWindowResidueCountMod4EqOne n k
   = number of odd orbit labels congruent to 1 modulo 4
 
@@ -450,6 +466,12 @@ prefix mod 4 residue occupation lower bound
 mod 8 residue occupation lower bound
   -> m <= residueCountMod8EqFive
   -> k + CountGe 2 + m <= sumS n k
+
+tail `height >= 2` lower bound
+  -> (k + 1) + tail CountGe 2 <= sumS n (k + 1)
+
+delayed `3 mod 8` drift
+  -> (k + 1) + residueCountMod8EqThree n k <= sumS n (k + 1)
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -612,6 +634,26 @@ residueCountMod8EqThree <= tail residueCountMod4EqOne
 residueCountMod8EqSeven <= tail residueCountMod4EqThree
 ```
 
+The `3 mod 8` source channel has also been returned to the height-count side:
+
+```text
+residueCountMod8EqThree
+  <= tail CountGe 2
+```
+
+Since the tail `1..k` sits inside the ordinary `(k + 1)` window `0..k`, this
+feeds the Collatz drift budget:
+
+```text
+(k + 1) + tail CountGe 2 <= sumS n (k + 1)
+
+(k + 1) + residueCountMod8EqThree n k <= sumS n (k + 1)
+```
+
+This is the first general-window delayed-peeling theorem.  A source count in
+the current window now produces a lower bound on accumulated height one step
+later.
+
 The next higher-coordinate experiment also passed:
 
 ```text
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-088.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-088.md
new file mode 100644
index 00000000..c0203006
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-088.md
@@ -0,0 +1,227 @@
+# Report Petal 088: Tail Height Count and Delayed Drift
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-088.md`.
+
+The previous checkpoint proved that the `3 mod 8` source channel maps into
+the shifted tail residue class `1 mod 4`.  This checkpoint converts that tail
+residue information back into a height count and then pushes it into the
+Collatz accumulated-height budget `sumS`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New shifted-tail height count:
+
+```lean
+orbitWindowHeightCountGeTail
+```
+
+New basic count API:
+
+```lean
+orbitWindowHeightCountGeTail_le_window
+orbitWindowHeightCountGe_succ
+orbitWindowHeightCountGeTail_succ
+orbitWindowHeightCountGeTail_le_countGe_succ
+```
+
+The key inclusion is:
+
+```text
+tail CountGe threshold over times 1..k
+  <= ordinary CountGe threshold over times 0..k
+```
+
+New tail height/residue bridge:
+
+```lean
+orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
+```
+
+New delayed-peeling height bridge:
+
+```lean
+orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
+```
+
+New drift budget theorems:
+
+```lean
+orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
+orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
+orbitWindowResidueCountMod8EqThree_delayed_drift
+orbitWindowResidueCountMod8EqThree_delayed_drift_strong
+```
+
+New restart/localization helpers:
+
+```lean
+oddOrbitLabel_zero_eq
+oddOrbitLabel_iterateT_zero_eq
+sumS_two_steps_ge_three_of_mod_eight_eq_three_at
+```
+
+## Main Result
+
+The strong delayed-drift theorem passed:
+
+```lean
+theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
+    (n : OddNat) (k : ℕ) :
+    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
+```
+
+Reading:
+
+```text
+source window:
+  times 0..k-1
+  count labels congruent to 3 mod 8
+
+tail window:
+  times 1..k
+  these source entries force height >= 2
+
+accumulated window:
+  times 0..k
+  base layer contributes k + 1
+  delayed 3 mod 8 events contribute one extra unit each
+```
+
+So `3 mod 8` is now a counted delayed-peeling source, not just a pointwise
+transition edge.
+
+## Proof Shape
+
+The useful intermediate bridge is:
+
+```lean
+orbitWindowHeightCountGeTail_le_countGe_succ
+```
+
+This avoids proving a new drift theorem by induction.  Instead:
+
+```text
+tail CountGe 2 <= ordinary CountGe 2 over k + 1
+ordinary drift theorem:
+  (k + 1) + ordinary CountGe 2 <= sumS n (k + 1)
+```
+
+Then monotonicity of addition gives the tail version.
+
+This is a good pattern for future shifted-window work:
+
+```text
+shifted local count
+  -> included in ordinary longer-window count
+  -> reuse existing sumS budget theorem
+```
+
+## Localized Two-Step Experiment
+
+The two-step theorem was also localized:
+
+```lean
+theorem sumS_two_steps_ge_three_of_mod_eight_eq_three_at
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 3) :
+    3 ≤ sumS (iterateT i n) 2
+```
+
+This uses the restart identity:
+
+```lean
+oddOrbitLabel (iterateT i n) 0 = oddOrbitLabel n i
+```
+
+This is useful because future local graph arguments can restart the accelerated
+system at any observed time.
+
+## Documentation Sync
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status note now records:
+
+```text
+tail height count
+tail height/residue bridge
+tail inclusion into the ordinary longer window
+strong delayed drift from the 3 mod 8 source channel
+localized two-step delayed-peeling theorem
+```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+The targeted build still reports the existing upstream warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
+```
+
+No new `sorry` was introduced in this checkpoint.
+
+## Next Implementation Candidates
+
+Candidate A: tail exact-height-one count for the `7 mod 8` retaining channel.
+
+```lean
+noncomputable def orbitWindowHeightCountEqTail
+    (n : OddNat) (k h : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (orbitWindowHeight n (i + 1) = h))
+```
+
+Then:
+
+```text
+residueCountMod8EqSeven <= tail CountEq 1
+```
+
+This would formalize the obstruction side:
+
+```text
+7 mod 8 -> next exact height one
+```
+
+Candidate B: two-step `7 -> 7` retention experiment.
+
+```lean
+theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
+    (n : OddNat)
+    (h0 : oddOrbitLabel n 0 % 8 = 7)
+    (h1 : oddOrbitLabel n 1 % 8 = 7) :
+    sumS n 2 = 2
+```
+
+This is stronger and more brittle, but it would isolate a true height-one
+retention pattern.
+
+Candidate C: define a small finite transition graph vocabulary.
+
+Current edges:
+
+```text
+3 mod 8 -> next 1 mod 4 -> next height >= 2
+7 mod 8 -> next 3 mod 4 -> next height = 1
+```
+
+The next abstraction could name these as source/receiver channels before
+expanding to mod `16` or longer paths.
````
`````

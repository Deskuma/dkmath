# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 15b31a07d8d5713d0150bc35bb4ead18d37816e3

## Report

087 を実装しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、`iterateT (i + 1) = T (iterateT i)` から始まる next-label transition、tail residue count、count-level transition、二歩遅延縮小補題 `sumS_two_steps_ge_three_of_mod_eight_eq_three` を追加しました。

あわせて [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md) を同期し、新規レポート [report-petal-087.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-087.md) を作成しました。次の候補として、tail height count を定義して `mod8 = 3` から drift budget へ繋ぐ道筋を書いてあります。

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check` pass

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き表示されますが、今回の変更で新しい `sorry` は入れていません。

## Review

## 1. 状況分析

これは checkpoint `087` で、**Petal residue graph が「静的な滞在統計」から「一歩遷移の統計」へ進んだ** 局面じゃ。

前回までの主語は、

```text id="bm7swt"
現在の時刻 i で、どの residue cell にいるか
```

だった。

今回からは、

```text id="zjqu9n"
現在の時刻 i でこの residue cell にいるなら、
次の時刻 i + 1 でどの residue cell に入るか
```

が Lean に入った。

特に重要なのは、

```text id="z8qk7s"
3 mod 8
  -> next 1 mod 4

7 mod 8
  -> next 3 mod 4
```

という **height-one channel の分岐遷移** が、`oddOrbitLabel n (i + 1)` の形まで持ち上がったことじゃ。添付レポートでも、今回の checkpoint は orbit-level transition を実際の label sequence `oddOrbitLabel n (i + 1)` へ持ち上げたものとして整理されている。

これは大きい。
Collatz.PetalBridge は、いよいよ **finite directed graph / symbolic dynamics** の入口に立った。

## 2. 今回の核心

今回の追加 API の柱はこれ。

```lean id="t9jgo0"
iterateT_succ_eq_T_iterateT
oddOrbitLabel_succ_eq_T_iterateT
oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
orbitWindowNextHeight_two_le_of_mod_eight_eq_three
orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
sumS_two_steps_ge_three_of_mod_eight_eq_three
```

特に本命はこの二つじゃ。

```lean id="j1j5ey"
oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
```

これで、

```text id="t7eqgo"
current label % 8 = 3
  -> next label % 4 = 1

current label % 8 = 7
  -> next label % 4 = 3
```

が軌道ラベル列そのものに乗った。

## 3. 数学的な意味

mod 8 の height-one channel は二つあった。

```text id="q19eft"
3 mod 8:
  height = 1

7 mod 8:
  height = 1
```

どちらも現在 step では exact height 1。
つまり、その瞬間だけ見ると弱い剥離に見える。

しかし次 step を見ると違う。

```text id="tjgzyj"
3 mod 8:
  next mod 4 = 1
  -> next height >= 2

7 mod 8:
  next mod 4 = 3
  -> next height = 1
```

つまり、同じ height-one でも、

```text id="llxhvm"
3 mod 8:
  遅延して追加剥離を生む channel

7 mod 8:
  height-one 側に残る channel
```

に分かれる。

これは非常に重要じゃ。
height だけを見ると同じ `1` だが、Petal residue address で見ると、次の縮小力が違う。

## 4. 「遅延縮小」が Lean に入った

今回の象徴はこれ。

```lean id="zj29x3"
sumS_two_steps_ge_three_of_mod_eight_eq_three
```

意味は、

```text id="ixpja0"
start at 3 mod 8

step 0:
  height = 1

step 1:
  height >= 2

therefore:
  sumS over first 2 steps >= 3
```

これは小さい補題に見えるが、意味は大きい。

今までの drift は、

```text id="fs0f4d"
その時刻でどれだけ剥がすか
```

だった。

今回から、

```text id="e9k76x"
その時刻では弱いが、次時刻に強い剥離を予約する
```

という **delayed drift / delayed peeling** が見えた。

これは Collatz の軌道解析でかなり重要な構造じゃ。

## 5. Count-level transition の意味

今回、tail count も入った。

```lean id="mkrmwi"
orbitWindowResidueCountMod4EqOneTail
orbitWindowResidueCountMod4EqThreeTail
```

これは時刻 `1, 2, ..., k` を見る shifted-tail window じゃ。

そして、

```lean id="aa09l4"
orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
```

が入った。

意味は、

```text id="r4s8x1"
0..k-1 にある 3 mod 8 の個数
  <= 1..k にある 1 mod 4 の個数

0..k-1 にある 7 mod 8 の個数
  <= 1..k にある 3 mod 4 の個数
```

これは **有限窓上の directed edge count** じゃ。

Petal residue graph の辺が、点ごとだけではなく、count レベルで見え始めた。

## 6. レビュー

今回の構成は非常に良い。

### 6.1. `iterateT_succ_eq_T_iterateT` が正しい橋になった

これで `T (iterateT i n)` という内部表現から、

```lean id="gqu02j"
oddOrbitLabel n (i + 1)
```

へ移れた。

この橋がないと、transition theorem は使いにくい。
今回ここを固定したことで、以後は軌道ラベル列として transition を書ける。

### 6.2. Tail count の導入が正しい

transition は index が一つずれる。
したがって普通の `0..k-1` window ではなく、受け側には `1..k` の tail window が必要になる。

```text id="jpupw4"
source window:
  time 0..k-1

receiver window:
  time 1..k
```

このずれを定義として切ったのが良い。

### 6.3. 二歩補題が良い実験になっている

`sumS_two_steps_ge_three_of_mod_eight_eq_three` は、delayed-peeling の最小 witness じゃ。

大きな theorem に行く前に、こういう小さな実験補題を通しておくのは正しい。
Lean 的にも、数学的にも、ルートが見える。

## 7. 現在の到達点

いまの流れはこうじゃ。

```text id="hgflod"
mod 8 partition:
  1, 3, 5, 7

height interpretation:
  1 mod 8 -> height = 2
  3 mod 8 -> height = 1
  5 mod 8 -> height >= 3
  7 mod 8 -> height = 1

transition:
  3 mod 8 -> next 1 mod 4
  7 mod 8 -> next 3 mod 4

drift:
  3 mod 8 -> next height >= 2
```

つまり、Petal はもう単なる residue 分類ではなく、

```text id="lmi1an"
residue cell の有向グラフ
```

を持ち始めた。

## 8. 次の指示：tail height count を作る

次の最優先は、レポートにもある通り、**tail height count** を定義して、tail residue count と tail height count をつなぐことじゃ。

まず定義。

```lean id="u2tve7"
noncomputable def orbitWindowHeightCountGeTail
    (n : OddNat) (k threshold : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
```

基本 bound。

```lean id="mh292a"
theorem orbitWindowHeightCountGeTail_le_window
    (n : OddNat) (k threshold : ℕ) :
    orbitWindowHeightCountGeTail n k threshold ≤ k := by
  unfold orbitWindowHeightCountGeTail
  simpa using
    (List.countP_le_length
      (p := fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
      (l := List.range k))
```

次に、tail の `height >= 2` と tail の `mod 4 = 1` を同一視する。

```lean id="k6hci3"
theorem orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 =
      orbitWindowResidueCountMod4EqOneTail n k := by
  unfold orbitWindowHeightCountGeTail orbitWindowResidueCountMod4EqOneTail
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hiff := orbitWindowHeight_two_le_iff_mod_four_eq_one n (k + 1)
      by_cases hheight : 2 ≤ orbitWindowHeight n (k + 1)
      · have hres : oddOrbitLabel n (k + 1) % 4 = 1 := hiff.mp hheight
        simp [ih, hheight, hres]
      · have hres : oddOrbitLabel n (k + 1) % 4 ≠ 1 := by
          intro h
          exact hheight (hiff.mpr h)
        simp [ih, hheight, hres]
```

これで tail residue が tail height に変換できる。

## 9. 次の一手：`3 mod 8` が tail height を供給する

次にこれ。

```lean id="is9e3d"
theorem orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k ≤
      orbitWindowHeightCountGeTail n k 2 := by
  rw [orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one]
  exact orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne n k
```

意味は、

```text id="spb4pz"
3 mod 8 の出現数
  <= 次時刻 tail における height >= 2 の出現数
```

これは delayed-peeling を count level で height 側に戻す橋じゃ。

## 10. drift budget へ渡す

次は tail height count を `sumS n (k + 1)` に渡す。

狙いはまず弱めでよい。

```lean id="z2v5ps"
theorem orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
    (n : OddNat) (k : ℕ) :
    k + orbitWindowHeightCountGeTail n k 2 ≤ sumS n (k + 1)
```

ただし実際には、`sumS n (k + 1)` は時刻 `0..k` を含むので、より強く

```lean id="cqgl7x"
theorem orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowHeightCountGeTail n k 2 ≤ sumS n (k + 1)
```

が狙えるはずじゃ。

理由は、

```text id="nlkcew"
時刻 0..k の k+1 個は全て height >= 1
tail の時刻 1..k で height >= 2 なら追加で 1
```

つまり、

```text id="qbd191"
base peeling:
  k + 1

delayed extra peeling:
  tail CountGe 2
```

ただ、Lean 証明は少し重いかもしれぬ。
まず弱い `k + tail <= sumS` を通し、次に強い `(k+1)+tail <= sumS` を狙うのが安全。

## 11. `3 mod 8` delayed drift theorem

上の橋が通ると、本命はこれ。

```lean id="cnv22j"
theorem orbitWindowResidueCountMod8EqThree_delayed_drift
    (n : OddNat) (k : ℕ) :
    k + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

強い版なら、

```lean id="ycg6hq"
theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

意味は、

```text id="lw4pys"
source window 0..k-1 で 3 mod 8 が m 回あるなら、
次の tail window 1..k に height >= 2 が少なくとも m 回生じる。
したがって sumS n (k+1) は base layer に m を足しただけ大きい。
```

これはかなり強い。
`3 mod 8` は「今は弱いが、次に追加剥離を生む」ことを drift budget に反映できる。

## 12. 一歩先ゆく推論：`7 mod 8` は滞留 channel

`7 mod 8` は次も `3 mod 4`、つまり exact height 1 側に残る。

これは drift としては弱いが、重要な obstruction 情報になる。

```text id="gvtbrn"
7 mod 8
  -> next 3 mod 4
  -> next height = 1
```

つまり、`7 mod 8` が多いと、

```text id="pue0su"
height-one が連続しやすい
```

という滞留 channel になる。

次に試したいのは、`7 mod 8` の二歩先をさらに細分化することじゃ。

次時刻が `3 mod 4` なので、次時刻は mod 8 で `3` か `7` のどちらか。
ここを見れば、

```text id="pwf6g4"
7 -> 3 -> delayed peeling
7 -> 7 -> still height-one
```

という分岐が見える。

つまり、長く height-one に留まる軌道は、`7 mod 8` 系 channel を多く通るはずじゃ。

## 13. 賢狼が試して欲しいおまけ実験補題

### 実験 A: tail height count と delayed drift

```lean id="axrny6"
theorem orbitWindowResidueCountMod8EqThree_delayed_drift_strong
    (n : OddNat) (k : ℕ) :
    (k + 1) + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
```

これは今回の最重要おまけじゃ。
通れば、count-level transition がそのまま drift theorem になる。

### 実験 B: 二歩補題の prefix generalization

いまは `i = 0` の二歩補題。

```lean id="fw5fai"
sumS_two_steps_ge_three_of_mod_eight_eq_three
```

次は任意 `i` の局所二歩にしたい。
そのためには localized sum が必要になるかもしれない。

簡易版としては、`iterateT i n` を新しい初期値にする。

```lean id="jmmo27"
theorem sumS_two_steps_ge_three_of_mod_eight_eq_three_at
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 8 = 3) :
    3 ≤ sumS (iterateT i n) 2 := by
  -- hmod を初期値 iterateT i n の label 0 に読み替える
  -- oddOrbitLabel (iterateT i n) 0 = oddOrbitLabel n i が必要
  sorry
```

これには補助補題が欲しい。

```lean id="bfdva5"
theorem oddOrbitLabel_zero_eq
    (n : OddNat) :
    oddOrbitLabel n 0 = n.1
```

```lean id="jtxpxn"
theorem oddOrbitLabel_iterateT_zero_eq
    (n : OddNat) (i : ℕ) :
    oddOrbitLabel (iterateT i n) 0 = oddOrbitLabel n i
```

### 実験 C: `7 mod 8` の二歩滞留

```lean id="x5248q"
theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7)
    (h1 : oddOrbitLabel n 1 % 8 = 7) :
    sumS n 2 = 2
```

これは少し実験的じゃが、`7` channel が height-one 滞留を表すことを確認できる。

安全に行くなら等号ではなく、

```lean id="l1cyk2"
theorem sumS_two_steps_ge_two_of_mod_eight_eq_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 8 = 7) :
    2 ≤ sumS n 2
```

からでよい。
ただこれは `height >= 1` だけでほぼ自明なので、研究価値は低い。
本命は `7 -> 7` の exact height-one chain じゃ。

## 14. 実装順序まとめ

次コミットのおすすめ順はこれ。

```text id="eizlj7"
1. orbitWindowHeightCountGeTail

2. orbitWindowHeightCountGeTail_le_window

3. orbitWindowHeightCountGeTail_two_eq_tailResidueCount_mod4_eq_one

4. orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two

5. orbitWindowHeightSeq_sum_ge_window_add_tailCountGe_two
   まず弱い版

6. orbitWindowHeightSeq_sum_ge_succ_window_add_tailCountGe_two
   強い版

7. orbitWindowResidueCountMod8EqThree_delayed_drift

8. orbitWindowResidueCountMod8EqThree_delayed_drift_strong

9. oddOrbitLabel_zero_eq

10. oddOrbitLabel_iterateT_zero_eq

11. sumS_two_steps_ge_three_of_mod_eight_eq_three_at
```

## 15. 総括

今回の checkpoint `087` で、

```text id="kv4a3z"
3 mod 8 -> next 1 mod 4
```

が、点ごと・count ごと・二歩 drift ごとに Lean に入った。

これは、Collatz.PetalBridge に初めて

```text id="oyzfng"
遅延して戻ってくる縮小力
```

が現れたということじゃ。

うむ。
次は tail height count を作って、この delayed-peeling を一般の `k` 窓で drift budget に入れる。
そこまで行けば、Petal residue graph は「どこにいるか」だけでなく、**一拍後にどれだけ縮小力を供給するか**を数えられるようになる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 70e1a039..3b51d3a7 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -523,6 +523,30 @@ noncomputable def orbitWindowResidueCountMod8EqSeven
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n i % 8 = 7))
 
+/--
+Number of shifted-tail labels in residue class `1 mod 4`.
+
+This counts the labels at times `1, 2, ..., k`, indexed as `i + 1` for
+`i < k`.  It is the receiving window for the transition
+`current mod 8 = 3 -> next mod 4 = 1`.
+-/
+noncomputable def orbitWindowResidueCountMod4EqOneTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 1))
+
+/--
+Number of shifted-tail labels in residue class `3 mod 4`.
+
+This counts the labels at times `1, 2, ..., k`, indexed as `i + 1` for
+`i < k`.  It is the receiving window for the transition
+`current mod 8 = 7 -> next mod 4 = 3`.
+-/
+noncomputable def orbitWindowResidueCountMod4EqThreeTail
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3))
+
 /--
 Residue count inside a prefix of an ambient observation window.
 
@@ -621,6 +645,28 @@ theorem orbitWindowResidueCountMod8EqSeven_le_window
     (List.countP_le_length
       (p := fun i => decide (oddOrbitLabel n i % 8 = 7)) (l := List.range k))
 
+/--
+The shifted-tail mod `4 = 1` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod4EqOneTail_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod4EqOneTail n k ≤ k := by
+  unfold orbitWindowResidueCountMod4EqOneTail
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n (i + 1) % 4 = 1)) (l := List.range k))
+
+/--
+The shifted-tail mod `4 = 3` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod4EqThreeTail_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod4EqThreeTail n k ≤ k := by
+  unfold orbitWindowResidueCountMod4EqThreeTail
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3)) (l := List.range k))
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
@@ -1062,6 +1108,163 @@ theorem orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
   rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one (iterateT i n) hs]
   exact next_mod_four_of_mod_eight_eq_seven hmod
 
+/--
+One-step recursion for the accelerated Collatz iterator.
+
+This repackages the recursive definition of `iterateT` in the orientation
+needed by orbit-label transition theorems: the next label is obtained by
+applying `T` to the current accelerated state.
+-/
+theorem iterateT_succ_eq_T_iterateT
+    (n : OddNat) (i : ℕ) :
+    iterateT (i + 1) n = T (iterateT i n) := by
+  induction i generalizing n with
+  | zero =>
+      rfl
+  | succ i ih =>
+      change iterateT (i + 1) (T n) = T (iterateT i (T n))
+      exact ih (T n)
+
+/--
+The next natural orbit label is the natural value of `T` applied to the
+current accelerated state.
+-/
+theorem oddOrbitLabel_succ_eq_T_iterateT
+    (n : OddNat) (i : ℕ) :
+    oddOrbitLabel n (i + 1) = (T (iterateT i n)).1 := by
+  unfold oddOrbitLabel
+  rw [iterateT_succ_eq_T_iterateT]
+
+/--
+Label-sequence transition from the `3 mod 8` height-one channel.
+
+If the current label is `3 mod 8`, then the next orbit label lies in
+residue class `1 mod 4`.
+-/
+theorem oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 3) :
+    oddOrbitLabel n (i + 1) % 4 = 1 := by
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  exact orbitNext_mod_four_eq_one_of_mod_eight_eq_three n i hmod
+
+/--
+Label-sequence transition from the `7 mod 8` height-one channel.
+
+If the current label is `7 mod 8`, then the next orbit label lies in
+residue class `3 mod 4`.
+-/
+theorem oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 7) :
+    oddOrbitLabel n (i + 1) % 4 = 3 := by
+  rw [oddOrbitLabel_succ_eq_T_iterateT]
+  exact orbitNext_mod_four_eq_three_of_mod_eight_eq_seven n i hmod
+
+/--
+Delayed peeling from the `3 mod 8` height-one channel.
+
+The current step has exact height `1`, but the next label lands in
+`1 mod 4`, so the next observed height is at least `2`.
+-/
+theorem orbitWindowNextHeight_two_le_of_mod_eight_eq_three
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 3) :
+    2 ≤ orbitWindowHeight n (i + 1) := by
+  apply (orbitWindowHeight_two_le_iff_mod_four_eq_one n (i + 1)).mpr
+  exact oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three n i hmod
+
+/--
+The `7 mod 8` height-one channel remains an exact height-one channel at the
+next label.
+
+This is the complementary transition to the delayed-peeling
+`3 mod 8 -> next height >= 2` edge.
+-/
+theorem orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+    (n : OddNat) (i : ℕ)
+    (hmod : oddOrbitLabel n i % 8 = 7) :
+    orbitWindowHeight n (i + 1) = 1 := by
+  apply (orbitWindowHeight_eq_one_iff_mod_four_eq_three n (i + 1)).mpr
+  exact oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven n i hmod
+
+/--
+Every `3 mod 8` label in a window contributes a `1 mod 4` label in the
+shifted tail window.
+
+This is the first count-level transition statistic: the source channel is
+counted at time `i`, and the receiver channel is counted at time `i + 1`.
+-/
+theorem orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k ≤
+      orbitWindowResidueCountMod4EqOneTail n k := by
+  unfold orbitWindowResidueCountMod8EqThree orbitWindowResidueCountMod4EqOneTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have htransition :
+          oddOrbitLabel n k % 8 = 3 →
+            oddOrbitLabel n (k + 1) % 4 = 1 :=
+        oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three n k
+      by_cases hsource : oddOrbitLabel n k % 8 = 3
+      · have htail : oddOrbitLabel n (k + 1) % 4 = 1 := htransition hsource
+        simp [hsource, htail, ih]
+      · by_cases htail : oddOrbitLabel n (k + 1) % 4 = 1
+        · exact by
+            simpa [hsource, htail] using Nat.le_succ_of_le ih
+        · simp [hsource, htail, ih]
+
+/--
+Every `7 mod 8` label in a window contributes a `3 mod 4` label in the
+shifted tail window.
+-/
+theorem residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k ≤
+      orbitWindowResidueCountMod4EqThreeTail n k := by
+  unfold orbitWindowResidueCountMod8EqSeven orbitWindowResidueCountMod4EqThreeTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have htransition :
+          oddOrbitLabel n k % 8 = 7 →
+            oddOrbitLabel n (k + 1) % 4 = 3 :=
+        oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven n k
+      by_cases hsource : oddOrbitLabel n k % 8 = 7
+      · have htail : oddOrbitLabel n (k + 1) % 4 = 3 := htransition hsource
+        simp [hsource, htail, ih]
+      · by_cases htail : oddOrbitLabel n (k + 1) % 4 = 3
+        · exact by
+            simpa [hsource, htail] using Nat.le_succ_of_le ih
+        · simp [hsource, htail, ih]
+
+/--
+Two-step delayed-peeling experiment.
+
+Starting at `3 mod 8`, the current step contributes height `1`, and the next
+step contributes at least height `2`.  Hence the first two accelerated
+Collatz height observations sum to at least `3`.
+-/
+theorem sumS_two_steps_ge_three_of_mod_eight_eq_three
+    (n : OddNat)
+    (hmod : oddOrbitLabel n 0 % 8 = 3) :
+    3 ≤ sumS n 2 := by
+  have h0 : orbitWindowHeight n 0 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
+      (Or.inl hmod)
+  have h1 : 2 ≤ orbitWindowHeight n 1 :=
+    orbitWindowNextHeight_two_le_of_mod_eight_eq_three n 0 hmod
+  calc
+    3 ≤ orbitWindowHeight n 0 + orbitWindowHeight n 1 := by
+      omega
+    _ = sumS n 2 := by
+      simp [sumS, orbitWindowHeight_eq_s_iterateT]
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 97563db7..3f0ba9ab 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -137,6 +137,8 @@ orbitWindowResidueCountMod8EqOne
 orbitWindowResidueCountMod8EqThree
 orbitWindowResidueCountMod8EqFive
 orbitWindowResidueCountMod8EqSeven
+orbitWindowResidueCountMod4EqOneTail
+orbitWindowResidueCountMod4EqThreeTail
 orbitWindowPrefixResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
@@ -146,6 +148,8 @@ orbitWindowResidueCountMod8EqOne_le_window
 orbitWindowResidueCountMod8EqThree_le_window
 orbitWindowResidueCountMod8EqFive_le_window
 orbitWindowResidueCountMod8EqSeven_le_window
+orbitWindowResidueCountMod4EqOneTail_le_window
+orbitWindowResidueCountMod4EqThreeTail_le_window
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -167,6 +171,15 @@ orbitWindowHeight_eq_one_iff_mod_four_eq_three
 orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
 orbitNext_mod_four_eq_one_of_mod_eight_eq_three
 orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
+iterateT_succ_eq_T_iterateT
+oddOrbitLabel_succ_eq_T_iterateT
+oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
+oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
+orbitWindowNextHeight_two_le_of_mod_eight_eq_three
+orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
+residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
+sumS_two_steps_ge_three_of_mod_eight_eq_three
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
 orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
@@ -364,6 +377,14 @@ orbitWindowResidueCountMod8EqFive n k
 orbitWindowResidueCountMod8EqSeven n k
   = number of odd orbit labels congruent to 7 modulo 8
 
+orbitWindowResidueCountMod4EqOneTail n k
+  = number of shifted tail labels, at times i + 1 for i < k,
+    congruent to 1 modulo 4
+
+orbitWindowResidueCountMod4EqThreeTail n k
+  = number of shifted tail labels, at times i + 1 for i < k,
+    congruent to 3 modulo 4
+
 orbitWindowPrefixResidueCountMod4EqOne n k r
   = number of prefix labels congruent to 1 modulo 4 inside an ambient k-window
 ```
@@ -558,6 +579,39 @@ oddOrbitLabel % 8 = 7
   -> (T current).val % 4 = 3
 ```
 
+This has now been lifted to the actual orbit-label sequence:
+
+```text
+oddOrbitLabel n i % 8 = 3
+  -> oddOrbitLabel n (i + 1) % 4 = 1
+
+oddOrbitLabel n i % 8 = 7
+  -> oddOrbitLabel n (i + 1) % 4 = 3
+```
+
+The `3 mod 8` channel is a delayed-peeling edge:
+
+```text
+current label is 3 mod 8
+  -> current height is exactly 1
+  -> next label is 1 mod 4
+  -> next height is at least 2
+```
+
+Thus the first two-step experiment is fixed:
+
+```text
+oddOrbitLabel n 0 % 8 = 3
+  -> 3 <= sumS n 2
+```
+
+At count level, the two exact height-one channels feed shifted tail counts:
+
+```text
+residueCountMod8EqThree <= tail residueCountMod4EqOne
+residueCountMod8EqSeven <= tail residueCountMod4EqThree
+```
+
 The next higher-coordinate experiment also passed:
 
 ```text
@@ -610,8 +664,8 @@ The immediate residue candidates are:
 ```text
 general 2^r residue coordinate for height >= r
 prefix mod 8 residue occupation
-next-label formulation of the T transition using iterateT (i + 1)
-count-level transition statistics for mod 8 height-one channels
+shifted-tail prefix versions of the transition-count inequalities
+2-step and 3-step delayed-peeling drift estimates
 ```
 
 The main caution is that Collatz state labels are not prime labels.  Any bridge
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-087.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-087.md
new file mode 100644
index 00000000..a98621c5
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-087.md
@@ -0,0 +1,209 @@
+# Report Petal 087: Collatz Tail Transition Window
+
+## Checkpoint
+
+This checkpoint implements the next-label transition layer requested in
+`__next_implementation-087.md`.
+
+The previous checkpoint had already proved the orbit-level transition:
+
+```text
+oddOrbitLabel % 8 = 3 -> (T current).val % 4 = 1
+oddOrbitLabel % 8 = 7 -> (T current).val % 4 = 3
+```
+
+This checkpoint lifts that observation to the actual label sequence
+`oddOrbitLabel n (i + 1)`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New shifted-tail count definitions:
+
+```lean
+orbitWindowResidueCountMod4EqOneTail
+orbitWindowResidueCountMod4EqThreeTail
+```
+
+New basic bounds:
+
+```lean
+orbitWindowResidueCountMod4EqOneTail_le_window
+orbitWindowResidueCountMod4EqThreeTail_le_window
+```
+
+New next-label transition bridge:
+
+```lean
+iterateT_succ_eq_T_iterateT
+oddOrbitLabel_succ_eq_T_iterateT
+oddOrbitLabel_succ_mod_four_eq_one_of_mod_eight_eq_three
+oddOrbitLabel_succ_mod_four_eq_three_of_mod_eight_eq_seven
+```
+
+New next-height consequences:
+
+```lean
+orbitWindowNextHeight_two_le_of_mod_eight_eq_three
+orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
+```
+
+New count-level transition inequalities:
+
+```lean
+orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
+residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
+```
+
+New two-step drift experiment:
+
+```lean
+sumS_two_steps_ge_three_of_mod_eight_eq_three
+```
+
+## Mathematical Reading
+
+The `3 mod 8` height-one channel is not merely weak peeling.  It is a delayed
+peeling edge:
+
+```text
+time i:
+  oddOrbitLabel n i % 8 = 3
+  height = 1
+
+time i + 1:
+  oddOrbitLabel n (i + 1) % 4 = 1
+  height >= 2
+```
+
+Therefore the first two observations already satisfy:
+
+```text
+oddOrbitLabel n 0 % 8 = 3 -> 3 <= sumS n 2
+```
+
+The `7 mod 8` channel has the complementary behavior:
+
+```text
+time i:
+  oddOrbitLabel n i % 8 = 7
+
+time i + 1:
+  oddOrbitLabel n (i + 1) % 4 = 3
+  height = 1
+```
+
+Thus the exact height-one layer splits into two different transition edges:
+
+```text
+3 mod 8 -> next extra peeling
+7 mod 8 -> next exact height-one
+```
+
+## Count-Level Interpretation
+
+The new tail counts make the transition statistical:
+
+```text
+count(current 3 mod 8 in 0..k-1)
+  <= count(next 1 mod 4 in 1..k)
+
+count(current 7 mod 8 in 0..k-1)
+  <= count(next 3 mod 4 in 1..k)
+```
+
+This is the first finite directed-edge observation for the Collatz Petal
+window.  The bridge is no longer only a static occupation table; it now records
+one-step flow between residue channels.
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
+tail residue count definitions
+next-label transition theorems
+next-height delayed-peeling interpretation
+count-level transition inequalities
+two-step drift experiment
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
+The next useful step is to turn this one-step edge into a prefix/tail drift
+budget.
+
+Candidate A:
+
+```lean
+theorem orbitWindowHeightSeq_sum_ge_window_add_tailMod4EqOne
+    (n : OddNat) (k : ℕ) :
+    k + orbitWindowResidueCountMod4EqOneTail n k ≤ sumS n (k + 1)
+```
+
+This should be treated carefully because the tail window is `1..k`, while
+`sumS n (k + 1)` observes `0..k`.  It will likely need a small prefix/tail
+count bridge.
+
+Candidate B:
+
+```lean
+theorem orbitWindowResidueCountMod8EqThree_delayed_drift
+    (n : OddNat) (k : ℕ) :
+    k + orbitWindowResidueCountMod8EqThree n k ≤ sumS n (k + 1)
+```
+
+This would combine:
+
+```text
+3 mod 8 count <= next 1 mod 4 tail count
+next 1 mod 4 tail count -> height >= 2 on the shifted window
+```
+
+Candidate C:
+
+Define shifted-tail height counts:
+
+```lean
+noncomputable def orbitWindowHeightCountGeTail
+    (n : OddNat) (k threshold : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (threshold <= orbitWindowHeight n (i + 1)))
+```
+
+Then prove:
+
+```text
+tail CountGe 2 = tail residue mod 4 = 1
+mod8EqThree <= tail CountGe 2
+```
+
+This is probably the cleanest next bridge before deriving larger drift
+inequalities.
````
`````

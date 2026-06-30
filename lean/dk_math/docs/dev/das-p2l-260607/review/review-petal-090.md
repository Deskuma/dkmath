# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: cb43668a5bd9e51ad79e5a82e00a81a6e6fa9f54

## Report

089 を実装しました。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に `orbitWindowHeightCountEqTail` を追加し、`7 mod 8` source が次時刻 tail の exact height `1` に入ることを count level で固定しました。

主な追加 theorem はこのあたりです。

```lean
orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
```

これで `3 mod 8` は delayed-peeling channel、`7 mod 8` は retention channel として対になりました。tail 側も `height >= 2` と `height = 1` の分割が入ったので、mod 8 の exact height-one 層を「次に縮む枝」と「低剥離に留まる枝」として読めます。

同期済み:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-089.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-089.md)

検証:

- `lake build DkMath.Collatz.PetalBridge` pass
- `lake build DkMath.Collatz.Collatz2K26` pass
- `git diff --check` pass

既存の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean` の `sorry` warning は引き続き出ますが、今回の変更で新しい `sorry` は入れていません。

## Review

## 1. 状況分析

これは checkpoint `089` で、かなり良い。
今回で **mod 8 の exact height-one 層が、二つの遷移 channel に分解された**。

前回までで、

```text
3 mod 8
  -> next tail height >= 2
  -> delayed-peeling channel
```

が閉じていた。

今回さらに、

```text
7 mod 8
  -> next tail height = 1
  -> retention channel
```

が閉じた。

つまり、`height = 1` という一見同じ弱剥離 step が、Petal residue address では二種類に分かれた。

```text
3 mod 8:
  今は height = 1
  次に height >= 2 を生む

7 mod 8:
  今は height = 1
  次も exact height 1 側に残る
```

添付レポートでも、checkpoint `089` は `3 mod 8` の delayed-peeling counterpart として、`7 mod 8` の retention channel を閉じたものと整理されている。

これは「コラッツを閉じに行く」上で、かなり良い足場じゃ。
まだ予想そのものの証明ではないが、**悪い区間が何で構成されるか** が見え始めた。

## 2. 今回の核心

追加された主なものはこれ。

```lean
orbitWindowHeightCountEqTail
orbitWindowHeightCountEqTail_le_window
orbitWindowHeightCountEqTail_succ
orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
```

本命はこの二つ。

```lean
theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k ≤
      orbitWindowHeightCountEqTail n k 1
```

```lean
theorem orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountGeTail n k 2 +
      orbitWindowHeightCountEqTail n k 1 = k
```

これで tail 側が、

```text
extra-peeling side:
  tail height >= 2

retention side:
  tail height = 1
```

に完全分割された。

## 3. 数学的な意味

今回の定理群は、次の事実を形式化している。

```text
source window:
  times 0..k-1

tail window:
  times 1..k
```

ここで、source 側の `3 mod 8` と `7 mod 8` は、tail 側で異なる働きをする。

```text
3 mod 8 source
  -> tail CountGe 2

7 mod 8 source
  -> tail CountEq 1
```

つまり、height-one source layer は同質ではない。

```text
height = 1 source
  = delayed-peeling source
    + retention source
```

この観測はかなり重要じゃ。
なぜなら、Collatz の難所は「height = 1 が多いこと」ではなく、より細かく言えば、

```text
retention channel が長く続くこと
```

だからじゃ。

`3 mod 8` は height 1 でも次に縮む。
`7 mod 8` は height 1 を次にも残す。

ここが、Petal が提供する座標系の価値じゃな。

## 4. レビュー

### 4.1. `orbitWindowHeightCountEqTail` は正しい追加

前回 `tail CountGe` が入ったので、今回 `tail CountEq` を入れたのは自然。

```lean
noncomputable def orbitWindowHeightCountEqTail
    (n : OddNat) (k h : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (orbitWindowHeight n (i + 1) = h))
```

これで tail window の exact-height 側を扱えるようになった。

### 4.2. tail partition が強い

```lean
orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
```

これはよい。
全 tail state で `height >= 1` が成り立つので、tail の各点は必ず、

```text
height = 1
```

または、

```text
height >= 2
```

のどちらかに入る。

この補題は、以後の transition graph の保存則になる。

DkMath 風に言えば、

```text
tail window
  = retention side
    + extra-peeling side
```

じゃ。

### 4.3. `7 mod 8` retention が count level で固定された

```lean
orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
```

これで、`7 mod 8` は単なる residue cell ではなく、

```text
次時刻の exact height 1 を供給する source
```

になった。

前回の

```text
3 mod 8 -> tail height >= 2
```

と対になる。

### 4.4. two-step witness が良い

```lean
sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
```

これは diagnostic として良い。

```text
7 -> 7
```

が続くと、

```text
height 1 + height 1
```

なので、

```text
sumS n 2 = 2
```

になる。

これは「低剥離が本当に連続している状態」を Lean 上で切り出した witness じゃ。

## 5. 現在の構造

いま、mod 8 Petal cell はこう読める。

```text
1 mod 8:
  exact height 2

3 mod 8:
  height 1 now
  next height >= 2
  delayed-peeling channel

5 mod 8:
  height >= 3 now
  immediate strong channel

7 mod 8:
  height 1 now
  next height 1 side
  retention channel
```

ここまで来ると、Collatz の局所構造がかなり整理されてきた。

```text
ImmediateStrong:
  5 mod 8

ExactTwo:
  1 mod 8

DelayedPeeling:
  3 mod 8

Retention:
  7 mod 8
```

この四分類はかなり使える。

## 6. 次の指示：source-channel sum bound を入れる

次は、レポートにも候補として出ているこの補題を入れるのがよい。

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k
```

これは mod 8 partition からすぐ出せる。

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k := by
  have hpart := orbitWindowResidueCountMod8_partition_eq_window n k
  omega
```

ただし、これは単なる数の不等式以上の意味を持つ。

```text
height-one source channels
  = 3 mod 8 + 7 mod 8
```

であり、それらは window size を超えない。
つまり、height-one source layer の総量制限じゃ。

## 7. さらに次：tail split 経由の source-channel bound

上の補題は mod 8 partition から出せるが、Petal transition の意味を強く出すなら、tail split 経由でも欲しい。

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k := by
  have h3 :
      orbitWindowResidueCountMod8EqThree n k ≤
        orbitWindowHeightCountGeTail n k 2 :=
    orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two n k
  have h7 :
      orbitWindowResidueCountMod8EqSeven n k ≤
        orbitWindowHeightCountEqTail n k 1 :=
    orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one n k
  have hsplit := orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window n k
  omega
```

この形は非常に良い。

意味は、

```text
3 source は tail extra-peeling side に入る
7 source は tail retention side に入る
tail は二つに分割される
だから 3 source + 7 source <= tail size
```

これは transition graph の保存則っぽい。

## 8. 一歩先ゆく推論：bad channel は `7 mod 8` に濃縮される

ここから先、コラッツ攻略として重要なのはこれ。

```text
低剥離が続くなら、7 mod 8 retention channel を多く通る。
```

なぜなら、`3 mod 8` は次に `height >= 2` を生むので、悪い低剥離列からは脱落する。

つまり、長い間 `height = 1` が続くには、

```text
7 mod 8 -> next 3 mod 4 -> さらに mod 8 で 3 or 7
```

のうち、さらに `7` 側へ寄る必要がある。

次の本丸は、

```text
7 -> 7 retention path
```

の構造を掘ることじゃ。

この path がどの合同条件を要求するかを見ると、mod 16 / mod 32 の座標へ進む理由が出る。

## 9. 次の実装：`7 -> 7` の条件を mod 16 で読む

いま、

```text
m % 8 = 7
```

なら、

```text
T(m) % 4 = 3
```

までは分かった。

次に、

```text
T(m) % 8 = 7
```

まで要求すると、より細かい mod 16 条件が出るはずじゃ。

計算してみると、\(m = 16a + r\) で奇数かつ \(r \equiv 7 \pmod 8\) なので \(r = 7\) または \(15\)。

```text
r = 7:
  (3r + 1) / 2 = 11
  11 % 8 = 3

r = 15:
  (3r + 1) / 2 = 23
  23 % 8 = 7
```

つまり、

```text
m % 16 = 15
  -> T(m) % 8 = 7
```

が retention continuation。

一方、

```text
m % 16 = 7
  -> T(m) % 8 = 3
```

で、これは次に delayed-peeling 側へ行く可能性がある。

候補 theorem:

```lean
theorem next_mod_eight_of_mod_sixteen_eq_seven
    {m : ℕ} (hm : m % 16 = 7) :
    ((3 * m + 1) / 2) % 8 = 3 := by
  omega
```

```lean
theorem next_mod_eight_of_mod_sixteen_eq_fifteen
    {m : ℕ} (hm : m % 16 = 15) :
    ((3 * m + 1) / 2) % 8 = 7 := by
  omega
```

その orbit 版。

```lean
theorem oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 7) :
    oddOrbitLabel n (i + 1) % 8 = 3
```

```lean
theorem oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen
    (n : OddNat) (i : ℕ)
    (hmod : oddOrbitLabel n i % 16 = 15) :
    oddOrbitLabel n (i + 1) % 8 = 7
```

これで、retention channel がさらに二分される。

```text
7 mod 16:
  retention exits toward 3 mod 8

15 mod 16:
  retention continues as 7 mod 8
```

## 10. ここが「閉じに行く」道

この路線でコラッツを閉じに行くなら、狙いはこうじゃ。

```text
低剥離が長く続くには、
7 mod 8,
15 mod 16,
31 mod 32,
63 mod 64,
...
のような狭い residue channel に入らざるを得ない。
```

つまり、bad path はどんどん細い 2-adic cylinder に押し込まれる。

これは直感的には強い。

```text
height-one retention が長い
  -> residue condition が深くなる
  -> 取り得る点が薄くなる
```

この「薄くなる」を有限観測窓・count・transition で言えれば、かなり攻められる。

## 11. 賢狼が試して欲しいおまけ実験補題

### 実験 A: source-channel sum bound

```lean
theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqThree n k +
      orbitWindowResidueCountMod8EqSeven n k ≤ k
```

これは基本。
mod 8 partition 由来と tail split 由来、どちらでも通るはず。

### 実験 B: retention continuation の mod 16 分岐

```lean
theorem next_mod_eight_of_mod_sixteen_eq_seven
    {m : ℕ} (hm : m % 16 = 7) :
    ((3 * m + 1) / 2) % 8 = 3
```

```lean
theorem next_mod_eight_of_mod_sixteen_eq_fifteen
    {m : ℕ} (hm : m % 16 = 15) :
    ((3 * m + 1) / 2) % 8 = 7
```

これはかなり重要なおまけ。
`7 mod 8` retention channel の内部構造を見る。

### 実験 C: two-step delayed recovery from `7 mod 16`

```lean
theorem sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
    (n : OddNat)
    (hmod : oddOrbitLabel n 0 % 16 = 7) :
    4 ≤ sumS n 3
```

読みはこう。

```text
m % 16 = 7
  -> step 0 height = 1
  -> next label % 8 = 3
  -> step 1 height = 1
  -> next-next height >= 2
```

だから三歩で、

```text
1 + 1 + 2 = 4
```

が期待できる。

これは、`7` retention が永遠に悪いわけではなく、`7 mod 16` なら次に recovery する、という補題じゃ。

### 実験 D: true retention continuation witness

```lean
theorem sumS_three_steps_eq_three_of_mod_sixteen_eq_fifteen_and_next_next_seven
    (n : OddNat)
    (h0 : oddOrbitLabel n 0 % 16 = 15)
    (h1 : oddOrbitLabel n 1 % 8 = 7)
    (h2 : oddOrbitLabel n 2 % 8 = 7) :
    sumS n 3 = 3
```

これは少し重いし仮定も多いが、`15 mod 16` が retention continuation 側であることを確認する witness になる。

## 12. 次の実装順序

おすすめ順はこう。

```text
1. orbitWindowResidueCountMod8EqThree_add_seven_le_window

2. orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition

3. next_mod_eight_of_mod_sixteen_eq_seven

4. next_mod_eight_of_mod_sixteen_eq_fifteen

5. oddOrbitLabel_succ_mod_eight_eq_three_of_mod_sixteen_eq_seven

6. oddOrbitLabel_succ_mod_eight_eq_seven_of_mod_sixteen_eq_fifteen

7. orbitWindowNextHeight_two_le_of_mod_sixteen_eq_seven_after_two
   または小さく分けて作る

8. sumS_three_steps_ge_four_of_mod_sixteen_eq_seven
```

その後で、`15 mod 16` 側の retention continuation を掘る。

## 13. 総括

今回の checkpoint `089` で、mod 8 の height-one 層は完全に二分された。

```text
3 mod 8:
  delayed-peeling channel

7 mod 8:
  retention channel
```

これは、コラッツ攻略において非常に良い。

なぜなら、悪い挙動をただ

```text
height = 1 が多い
```

と曖昧に見るのではなく、

```text
retention channel がどれだけ続くか
```

へ局所化できるからじゃ。

うむ、この調子で行こう。
閉じに行くなら、次は `7 mod 8` の内部を mod 16 で割る。
`7 mod 16` は recovery 側、`15 mod 16` は retention continuation 側。
この分岐を Lean で固定できれば、低剥離 path はどんどん細い 2-adic cylinder に追い込まれていく。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 83890785..7d3a3ec0 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -474,6 +474,17 @@ noncomputable def orbitWindowHeightCountGeTail
   (List.range k).countP
     (fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
 
+/--
+Number of shifted-tail entries whose height is exactly `h`.
+
+This is the exact-height counterpart of `orbitWindowHeightCountGeTail`.  It is
+used to record retention channels such as `7 mod 8 -> next exact height 1`.
+-/
+noncomputable def orbitWindowHeightCountEqTail
+    (n : OddNat) (k h : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (orbitWindowHeight n (i + 1) = h))
+
 /--
 Number of in-window odd-state labels in residue class `1 mod 4`.
 
@@ -602,6 +613,19 @@ theorem orbitWindowHeightCountGeTail_le_window
       (p := fun i => decide (threshold ≤ orbitWindowHeight n (i + 1)))
       (l := List.range k))
 
+/--
+The shifted-tail exact-height occupation count is bounded by the tail window
+size.
+-/
+theorem orbitWindowHeightCountEqTail_le_window
+    (n : OddNat) (k h : ℕ) :
+    orbitWindowHeightCountEqTail n k h ≤ k := by
+  unfold orbitWindowHeightCountEqTail
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (orbitWindowHeight n (i + 1) = h))
+      (l := List.range k))
+
 /--
 Successor formula for ordinary threshold occupation counts.
 -/
@@ -630,6 +654,20 @@ theorem orbitWindowHeightCountGeTail_succ
   · simp [h]
   · simp [h]
 
+/--
+Successor formula for shifted-tail exact-height occupation counts.
+-/
+theorem orbitWindowHeightCountEqTail_succ
+    (n : OddNat) (k h : ℕ) :
+    orbitWindowHeightCountEqTail n (k + 1) h =
+      orbitWindowHeightCountEqTail n k h +
+        if orbitWindowHeight n (k + 1) = h then 1 else 0 := by
+  unfold orbitWindowHeightCountEqTail
+  rw [List.range_succ]
+  by_cases hlast : orbitWindowHeight n (k + 1) = h
+  · simp [hlast]
+  · simp [hlast]
+
 /--
 The mod `4` residue count is bounded by the window size.
 -/
@@ -1111,6 +1149,57 @@ theorem orbitWindowHeight_eq_one_iff_mod_four_eq_three
       omega
     omega
 
+/--
+Tail exact height `1` occupation is the same as shifted-tail residue
+occupation in class `3 mod 4`.
+-/
+theorem orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountEqTail n k 1 =
+      orbitWindowResidueCountMod4EqThreeTail n k := by
+  unfold orbitWindowHeightCountEqTail orbitWindowResidueCountMod4EqThreeTail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_eq_one_iff_mod_four_eq_three n (k + 1)
+      by_cases hheight : orbitWindowHeight n (k + 1) = 1
+      · have hres : oddOrbitLabel n (k + 1) % 4 = 3 := hiff.mp hheight
+        simp [ih, hheight, hres]
+      · have hres : oddOrbitLabel n (k + 1) % 4 ≠ 3 := by
+          intro h
+          exact hheight (hiff.mpr h)
+        simp [ih, hheight, hres]
+
+/--
+The shifted tail splits into exact height `1` and height at least `2`.
+
+Every accelerated Collatz tail state has height at least `1`, so an entry is
+either the retaining exact-height-one layer or the extra-peeling layer.
+-/
+theorem orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGeTail n k 2 +
+      orbitWindowHeightCountEqTail n k 1 = k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowHeightCountGeTail, orbitWindowHeightCountEqTail]
+  | succ k ih =>
+      rw [orbitWindowHeightCountGeTail_succ]
+      rw [orbitWindowHeightCountEqTail_succ]
+      have hone : 1 ≤ orbitWindowHeight n (k + 1) :=
+        orbitWindowHeight_one_le n (k + 1)
+      by_cases htwo : 2 ≤ orbitWindowHeight n (k + 1)
+      · have hnotOne : orbitWindowHeight n (k + 1) ≠ 1 := by
+          omega
+        simp [htwo, hnotOne]
+        omega
+      · have hOne : orbitWindowHeight n (k + 1) = 1 := by
+          omega
+        simp [hOne]
+        omega
+
 /--
 Exact height `1` is the union of the two mod `8` channels `3` and `7`.
 -/
@@ -1328,6 +1417,20 @@ theorem residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
             simpa [hsource, htail] using Nat.le_succ_of_le ih
         · simp [hsource, htail, ih]
 
+/--
+Every `7 mod 8` source label contributes a shifted-tail entry with exact
+height `1`.
+
+This is the retention-channel counterpart of the delayed-peeling theorem for
+the `3 mod 8` source channel.
+-/
+theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k ≤
+      orbitWindowHeightCountEqTail n k 1 := by
+  rw [orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three]
+  exact residueCountMod8EqSeven_le_nextResidueCountMod4EqThree n k
+
 /--
 The shifted-tail threshold count is contained in the ordinary count over the
 one-step-longer window.
@@ -1398,6 +1501,30 @@ theorem sumS_two_steps_ge_three_of_mod_eight_eq_three_at
   apply sumS_two_steps_ge_three_of_mod_eight_eq_three
   simpa [oddOrbitLabel_iterateT_zero_eq] using hmod
 
+/--
+Two-step retention witness for the `7 -> 7` pattern.
+
+If the first two labels both lie in residue class `7 mod 8`, then both
+observed heights are exact height `1`, so the two-step accumulated height is
+exactly `2`.
+-/
+theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
+    (n : OddNat)
+    (h0 : oddOrbitLabel n 0 % 8 = 7)
+    (h1 : oddOrbitLabel n 1 % 8 = 7) :
+    sumS n 2 = 2 := by
+  have hh0 : orbitWindowHeight n 0 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 0).mpr
+      (Or.inr h0)
+  have hh1 : orbitWindowHeight n 1 = 1 :=
+    (orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven n 1).mpr
+      (Or.inr h1)
+  calc
+    sumS n 2 = orbitWindowHeight n 0 + orbitWindowHeight n 1 := by
+      simp [sumS, orbitWindowHeight_eq_s_iterateT]
+    _ = 2 := by
+      omega
+
 /--
 Counting exact height `1` entries is the same as counting odd-state labels in
 residue class `3 mod 4`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 8ff3f266..4fc4df3c 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -132,6 +132,7 @@ orbitWindowHeight_eq_of_same_iterateT
 orbitWindowHeightCountEq
 orbitWindowHeightCountGe
 orbitWindowHeightCountGeTail
+orbitWindowHeightCountEqTail
 orbitWindowResidueCountMod4EqOne
 orbitWindowResidueCountMod4EqThree
 orbitWindowResidueCountMod8EqOne
@@ -144,8 +145,10 @@ orbitWindowPrefixResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
 orbitWindowHeightCountGeTail_le_window
+orbitWindowHeightCountEqTail_le_window
 orbitWindowHeightCountGe_succ
 orbitWindowHeightCountGeTail_succ
+orbitWindowHeightCountEqTail_succ
 orbitWindowResidueCountMod4EqOne_le_window
 orbitWindowResidueCountMod4EqThree_le_window
 orbitWindowResidueCountMod8EqOne_le_window
@@ -173,6 +176,8 @@ orbitWindowHeightCountGe_one_eq_window
 orbitWindowHeightSeq_sum_ge_window_add_countGe_two
 orbitWindowHeight_eq_two_iff_mod_eight_eq_one
 orbitWindowHeight_eq_one_iff_mod_four_eq_three
+orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
+orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
 orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
 orbitNext_mod_four_eq_one_of_mod_eight_eq_three
 orbitNext_mod_four_eq_three_of_mod_eight_eq_seven
@@ -185,9 +190,11 @@ orbitWindowNextHeight_eq_one_of_mod_eight_eq_seven
 orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
 orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
+orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
 orbitWindowHeightCountGeTail_le_countGe_succ
 sumS_two_steps_ge_three_of_mod_eight_eq_three
 sumS_two_steps_ge_three_of_mod_eight_eq_three_at
+sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
 orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
 orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
 orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
@@ -375,6 +382,10 @@ orbitWindowHeightCountGeTail n k threshold
   = number of shifted tail entries, at times i + 1 for i < k,
     whose height is at least threshold
 
+orbitWindowHeightCountEqTail n k h
+  = number of shifted tail entries, at times i + 1 for i < k,
+    whose height is exactly h
+
 orbitWindowResidueCountMod4EqOne n k
   = number of odd orbit labels congruent to 1 modulo 4
 
@@ -472,6 +483,12 @@ tail `height >= 2` lower bound
 
 delayed `3 mod 8` drift
   -> (k + 1) + residueCountMod8EqThree n k <= sumS n (k + 1)
+
+tail first-layer partition
+  -> tail CountGe 2 + tail CountEq 1 = k
+
+retaining `7 mod 8` source
+  -> residueCountMod8EqSeven <= tail CountEq 1
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -654,6 +671,36 @@ This is the first general-window delayed-peeling theorem.  A source count in
 the current window now produces a lower bound on accumulated height one step
 later.
 
+The `7 mod 8` source channel is now the retention counterpart:
+
+```text
+residueCountMod8EqSeven
+  <= tail CountEq 1
+```
+
+The shifted tail itself has the first exact/threshold partition:
+
+```text
+tail CountGe 2 + tail CountEq 1 = k
+```
+
+This records the first mod `8` transition split:
+
+```text
+3 mod 8 source:
+  next tail enters the extra-peeling side
+
+7 mod 8 source:
+  next tail remains exact height one
+```
+
+A concrete two-step witness is also available:
+
+```text
+label 0 = 7 mod 8 and label 1 = 7 mod 8
+  -> sumS n 2 = 2
+```
+
 The next higher-coordinate experiment also passed:
 
 ```text
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-089.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-089.md
new file mode 100644
index 00000000..5dd23c3a
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-089.md
@@ -0,0 +1,228 @@
+# Report Petal 089: Retention Channel for 7 mod 8
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-089.md`.
+
+Checkpoint 088 closed the delayed-peeling side:
+
+```text
+3 mod 8 source
+  -> next tail height >= 2
+  -> delayed drift contribution
+```
+
+Checkpoint 089 closes the retention counterpart:
+
+```text
+7 mod 8 source
+  -> next tail exact height 1
+```
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+New shifted-tail exact-height count:
+
+```lean
+orbitWindowHeightCountEqTail
+```
+
+New basic API:
+
+```lean
+orbitWindowHeightCountEqTail_le_window
+orbitWindowHeightCountEqTail_succ
+```
+
+New tail exact-height/residue bridge:
+
+```lean
+orbitWindowHeightCountEqTail_one_eq_tailResidueCount_mod4_eq_three
+```
+
+New retention-channel theorem:
+
+```lean
+orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
+```
+
+New tail partition:
+
+```lean
+orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
+```
+
+New two-step retention witness:
+
+```lean
+sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
+```
+
+## Main Reading
+
+The exact height-one source layer is no longer homogeneous.
+
+It splits into two transition behaviors:
+
+```text
+3 mod 8:
+  height 1 now
+  next tail height >= 2
+  delayed peeling source
+
+7 mod 8:
+  height 1 now
+  next tail height = 1
+  retention source
+```
+
+The new theorem:
+
+```lean
+theorem orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k ≤
+      orbitWindowHeightCountEqTail n k 1
+```
+
+formalizes the retention side at count level.
+
+## Tail Partition
+
+The shifted tail now has a clean first-layer partition:
+
+```lean
+theorem orbitWindowHeightTail_countGe_two_add_countEq_one_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGeTail n k 2 +
+      orbitWindowHeightCountEqTail n k 1 = k
+```
+
+Meaning:
+
+```text
+every tail entry has height at least 1
+therefore it is either:
+  exact height 1
+or:
+  height >= 2
+```
+
+This gives a useful finite observation split for the next directed graph layer.
+
+## Two-Step Witness
+
+The following exact witness passed:
+
+```lean
+theorem sumS_two_steps_eq_two_of_mod_eight_eq_seven_and_next_mod_eight_eq_seven
+    (n : OddNat)
+    (h0 : oddOrbitLabel n 0 % 8 = 7)
+    (h1 : oddOrbitLabel n 1 % 8 = 7) :
+    sumS n 2 = 2
+```
+
+This is not a transition theorem by itself because it assumes the second
+label is again `7 mod 8`.  Its value is diagnostic: it isolates a genuine
+two-step low-peeling retention pattern.
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
+tail exact-height count
+retention channel for 7 mod 8
+tail CountGe 2 / CountEq 1 partition
+two-step 7 -> 7 exact-height witness
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
+Candidate A: source-channel sum bound.
+
+Since:
+
+```text
+3 source <= tail CountGe 2
+7 source <= tail CountEq 1
+tail CountGe 2 + tail CountEq 1 = k
+```
+
+we should be able to record:
+
+```lean
+theorem orbitWindowResidueCountMod8EqThree_add_seven_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqThree n k +
+      orbitWindowResidueCountMod8EqSeven n k ≤ k
+```
+
+This already follows from the mod `8` partition, but proving it through the
+tail split would document the transition-graph reading.
+
+Candidate B: introduce source/receiver vocabulary in docs or thin defs.
+
+Suggested names:
+
+```text
+DelayedPeeling channel:
+  3 mod 8
+
+Retention channel:
+  7 mod 8
+
+ImmediateStrong channel:
+  5 mod 8
+
+ExactTwo channel:
+  1 mod 8
+```
+
+Candidate C: local `sumSFrom`.
+
+The current local theorem uses restart:
+
+```lean
+sumS (iterateT i n) 2
+```
+
+A window-native local sum would make future graph reasoning more readable:
+
+```lean
+noncomputable def sumSFrom (n : OddNat) (start len : ℕ) : ℕ :=
+  (List.range len).map
+    (fun j => orbitWindowHeight n (start + j))
+  |>.sum
+```
+
+This is worth adding only if the next transition-graph checkpoint needs
+several local two-step or three-step statements.
````
`````

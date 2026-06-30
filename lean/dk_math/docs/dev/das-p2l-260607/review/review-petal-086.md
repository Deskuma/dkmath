# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: b3929c7112d21fa6a83e95ba3be4cd9ebdeab2ef

## Report

checkpoint 085 完了です。

[PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean) に、prefix 版の `mod 4 = 1` residue count と、そのまま `r + m <= sumS n r` へ渡す橋を追加しました。さらに `height >= 3` を `mod 8 = 5` の occupation count へ持ち上げ、三層版の `k + CountGe 2 + m <= sumS n k` も通しています。

おまけとして、第一 mod 4 partition も閉じました。つまり `height = 1 <-> mod 4 = 3`、`CountEq 1 = residue mod 4 = 3`、`residue mod 4 = 1` と `3` の count 合計が window size `k` になるところまで固定済みです。

文書同期:

- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-085.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-085.md)

検証:

- `lake build DkMath.Collatz.PetalBridge`
- `lake build DkMath.Collatz.Collatz2K26`
- `git diff --check -- ...`

すべて通過。既存の無関係な `ZsigmondyCyclotomicResearch.lean:152` の `sorry` warning は引き続き表示されています。

## Review

## 1. 状況分析

これは checkpoint `085` で、局面がさらに一段進んだ。
前回 `height >= 2` を `mod 4 = 1` に翻訳した段階から、今回は **prefix・mod 8・mod 4 partition** まで進んでいる。

今回の到達点を一言で言うなら、

```text id="s6z1nj"
Collatz の height occupation が、
2-adic residue address occupation として本格的に読めるようになった。
```

添付レポートでも、checkpoint `085` は「full window -> prefix window」「height >= 2 -> height >= 3」へ拡張し、さらに第一 mod 4 partition を閉じたものとして整理されている。

つまり Petal はもう、

```text id="mp0ht8"
height を数える窓
```

ではなく、

```text id="s4i30c"
2-adic residue address の滞在統計を測る窓
```

になり始めている。

## 2. 今回の核心

今回追加された柱は三つある。

```text id="ev6a18"
1. prefix mod 4 residue occupation

2. mod 8 residue occupation

3. mod 4 partition
```

それぞれ意味がはっきりしている。

## 3. Prefix residue bridge

まず prefix 版。

```lean id="d0s14l"
orbitWindowPrefixResidueCountMod4EqOne
orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
```

これで、

```text id="ze6si7"
prefix 内で mod 4 = 1 の点が m 個以上ある
  -> r + m <= sumS n r
```

が使える。

これはかなり重要じゃ。
全体窓ではなく、先頭 `r` の局所 drift を residue occupation から評価できる。

つまり今後は、

```text id="jbg89r"
この prefix では 1 mod 4 が少なすぎる
この prefix では 1 mod 4 が十分に出た
```

という局所診断ができる。

## 4. Mod 8 occupation bridge

次に mod 8。

```lean id="gdg9yo"
orbitWindowResidueCountMod8EqFive
orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
```

意味は、

```text id="z5eswp"
height >= 3
  <-> oddOrbitLabel % 8 = 5
```

を count レベルに持ち上げ、

```text id="mgm4go"
m <= residueCountMod8EqFive
  -> k + CountGe 2 + m <= sumS n k
```

へ渡すものじゃ。

これは三層 drift の residue 版。
つまり、

```text id="yo97sb"
base layer:
  k

second layer:
  CountGe 2 = mod 4 = 1 の回数

third layer:
  CountGe 3 = mod 8 = 5 の回数
```

という読みができる。

この時点で、`sumS` はかなり明確に

```text id="x6374q"
2-adic residue address layers の総予算
```

として見えてきた。

## 5. 第一 mod 4 partition が閉じた意味

今回のおまけの本丸はここ。

```lean id="ry60hl"
orbitWindowHeight_eq_one_iff_mod_four_eq_three
orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
```

これで、odd state の mod 4 は完全に二分された。

```text id="on59gi"
mod 4 = 1
  <-> height >= 2

mod 4 = 3
  <-> height = 1
```

count レベルでは、

```text id="bbrjsm"
residueCountMod4EqOne + residueCountMod4EqThree = k
```

つまり、観測窓は mod 4 の二つの Petal cell に完全分割された。

これは単なる便利補題ではない。
**第一 Petal partition が閉じた** という意味じゃ。

## 6. 数学的な解説

現状の数学的構造は、次のようになっている。

```text id="og28hw"
odd orbit label m
  -> residue class modulo 4 / 8
  -> height layer
  -> occupation count
  -> layer-cake
  -> sumS drift lower bound
```

より具体的には、

```text id="o1kfah"
m % 4 = 3
  -> height = 1

m % 4 = 1
  -> height >= 2

m % 8 = 5
  -> height >= 3
```

つまり、height の情報は、2-adic residue の cylinder set として読める。

これは力学系の言葉で言えば、

```text id="a8m0nn"
finite symbolic coding
```

に近い。

Collatz 軌道を値そのものとして追うのではなく、

```text id="yl9m00"
mod 4 cell
mod 8 cell
mod 16 cell
...
```

への訪問列として読む方向に入った。

## 7. レビュー

今回の実装はとても良い。

### 良い点 1: Prefix を先に閉じた

prefix residue bridge が入ったことで、局所診断ができる。
これは後で「ある区間だけ膨張する」「ある prefix で drift が不足する」などを扱うときに効く。

### 良い点 2: mod 8 を count-level まで持ち上げた

点ごとの `height >= 3 <-> mod 8 = 5` で止まらず、occupation count と drift bridge まで接続したのが良い。

### 良い点 3: mod 4 partition を閉じた

`mod 4 = 1` と `mod 4 = 3` の二分が count レベルで閉じたので、第一 residue layer は完全に観測可能になった。

これは今後の transition analysis の入口になる。

## 8. 次の指示：transition map へ進む

次は、いよいよ residue occupation の「静的 count」から、**遷移規則**へ進むのが自然じゃ。

今は、

```text id="a97xfm"
どの residue cell に何回入ったか
```

まで見ている。

次は、

```text id="n6jsah"
その residue cell から次にどこへ行くか
```

を見る。

まず狙うのは height = 1 channel。

奇数 \(m\) で、

```text id="xrel0y"
m % 4 = 3
```

なら、

```text id="czql70"
height = 1
```

なので、

```text id="rfmu96"
T(m) = (3m + 1) / 2
```

になる。

この遷移をさらに mod 4 で見るには、mod 8 まで細分化する必要がある。

計算すると、

```text id="qf8pne"
m % 8 = 3
  -> T(m) % 4 = 1

m % 8 = 7
  -> T(m) % 4 = 3
```

候補 theorem はこれ。

```lean id="dui2xj"
theorem next_mod_four_of_mod_eight_eq_three
    {m : ℕ} (hm : m % 8 = 3) :
    (((3 * m + 1) / 2) % 4 = 1)
```

```lean id="ed4dms"
theorem next_mod_four_of_mod_eight_eq_seven
    {m : ℕ} (hm : m % 8 = 7) :
    (((3 * m + 1) / 2) % 4 = 3)
```

その後に、`iterateT` / `T` へ持ち上げる。

## 9. 一歩先ゆく推論：residue transition graph

ここから見たいのは、Petal address の有向グラフじゃ。

第一層では、

```text id="a20xz9"
mod 4 = 1:
  strong peel cell

mod 4 = 3:
  exact height 1 cell
```

だった。

でも次の状態への遷移を見るには、mod 8 で分ける。

```text id="mnptpo"
3 mod 8
  -> height = 1
  -> next mod 4 = 1

7 mod 8
  -> height = 1
  -> next mod 4 = 3

5 mod 8
  -> height >= 3
  -> strong peel

1 mod 8
  -> height = 2? or at least 2 but not 3
```

実際、奇数 mod 8 の各クラスはこう読める。

```text id="symx8o"
1 mod 8:
  3m+1 ≡ 4 mod 8
  -> height = 2

3 mod 8:
  3m+1 ≡ 2 mod 8
  -> height = 1

5 mod 8:
  3m+1 ≡ 0 mod 8
  -> height >= 3

7 mod 8:
  3m+1 ≡ 6 mod 8
  -> height = 1
```

これを Lean に入れると、mod 8 partition が非常に強くなる。

## 10. 次の一手の実装案

次のコミットでは、まず mod 8 partition を固定するのが良い。

候補 theorem:

```lean id="m5g7ej"
theorem odd_mod_eight_eq_one_or_three_or_five_or_seven
    {m : ℕ} (hmOdd : m % 2 = 1) :
    m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7
```

次に height classification。

```lean id="chqzrt"
theorem orbitWindowHeight_eq_two_iff_mod_eight_eq_one
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 2 ↔ oddOrbitLabel n i % 8 = 1
```

これは `height >= 2` と `not height >= 3` を使う。

```text id="dy51mu"
height = 2
  <-> height >= 2 and not height >= 3
  <-> mod 4 = 1 and not mod 8 = 5
  <-> mod 8 = 1
```

また、

```lean id="lqa0w8"
theorem orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven
    (n : OddNat) (i : ℕ) :
    orbitWindowHeight n i = 1 ↔
      oddOrbitLabel n i % 8 = 3 ∨ oddOrbitLabel n i % 8 = 7
```

これで mod 8 height partition が閉じる。

## 11. 賢狼が試してほしいおまけ実験補題

### 実験 A: exact height 2 の count

```lean id="p87s7p"
noncomputable def orbitWindowResidueCountMod8EqOne
    (n : OddNat) (k : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % 8 = 1))
```

```lean id="xdyph7"
theorem orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one
    (n : OddNat) (k : ℕ) :
    orbitWindowHeightCountEq n k 2 =
      orbitWindowResidueCountMod8EqOne n k
```

これは非常に良い。
`height = 2` が residue count になる。

### 実験 B: mod 8 partition count

```lean id="g71ypu"
theorem orbitWindowResidueCountMod8_partition_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqOne n k
      + orbitWindowResidueCountMod8EqThree n k
      + orbitWindowResidueCountMod8EqFive n k
      + orbitWindowResidueCountMod8EqSeven n k = k
```

これは少し定義が増えるが、mod 8 Petal cell が完全に閉じる。

### 実験 C: mod 16 fixed residue

前回候補にあったこれ。

```lean id="uzvdpt"
theorem orbitWindowHeight_four_le_iff_mod_sixteen_eq_five
    (n : OddNat) (i : ℕ) :
    4 ≤ orbitWindowHeight n i ↔ oddOrbitLabel n i % 16 = 5
```

これはぜひ試す価値がある。

すでに、

```text id="levtrt"
height >= 3 <-> mod 8 = 5
```

が通っているので、次の higher coordinate の確認になる。

## 12. 実装順序まとめ

次のおすすめ順はこれ。

```text id="pn0cvk"
1. odd_mod_eight_eq_one_or_three_or_five_or_seven

2. orbitWindowHeight_eq_two_iff_mod_eight_eq_one

3. orbitWindowHeight_eq_one_iff_mod_eight_eq_three_or_seven

4. orbitWindowResidueCountMod8EqOne

5. orbitWindowHeightCountEq_two_eq_residueCount_mod8_eq_one

6. orbitWindowResidueCountMod8EqThree / EqSeven

7. mod 8 partition count

8. next_mod_four_of_mod_eight_eq_three

9. next_mod_four_of_mod_eight_eq_seven

10. orbit-level transition theorem for height = 1 channel
```

おまけで、

```text id="asly9i"
11. height >= 4 <-> mod 16 = 5
```

を試す。

## 13. 総括

今回の checkpoint `085` で、

```text id="jwxoyr"
first mod 4 partition
```

は閉じた。

さらに、

```text id="tvkbuh"
mod 8 residue occupation
```

も drift bridge まで接続された。

これにより、次の本丸ははっきりした。

```text id="ifav7u"
residue occupation
  -> residue transition
  -> Petal address dynamics
```

うむ。
いま Collatz.PetalBridge は、単なる観測窓から **有限 symbolic dynamics の入口** へ入った。
次は mod 8 partition と transition map。そこが通ると、Petal は「座標系」から「遷移系」へ進化する。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index a2b31452..7ddacac6 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -185,6 +185,14 @@ theorem orbitWindowHeight_two_le_iff_mod_four_eq_one
   rw [orbitWindowHeight_two_le_iff_four_dvd]
   exact odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one (iterateT i n).2
 
+/--
+An odd natural number is in residue class `1` or `3` modulo `4`.
+-/
+theorem odd_mod_four_eq_one_or_three
+    {m : ℕ} (hmOdd : m % 2 = 1) :
+    m % 4 = 1 ∨ m % 4 = 3 := by
+  omega
+
 /--
 The `v2` observation is at least `3` exactly when `8` divides the observed
 nonzero natural.
@@ -382,6 +390,37 @@ noncomputable def orbitWindowResidueCountMod4EqOne
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n i % 4 = 1))
 
+/--
+Number of in-window odd-state labels in residue class `3 mod 4`.
+
+This is the residue-address counterpart of exact height `1`.
+-/
+noncomputable def orbitWindowResidueCountMod4EqThree
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % 4 = 3))
+
+/--
+Number of in-window odd-state labels in residue class `5 mod 8`.
+
+This is the residue-address counterpart of `orbitWindowHeightCountGe n k 3`.
+-/
+noncomputable def orbitWindowResidueCountMod8EqFive
+    (n : OddNat) (k : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % 8 = 5))
+
+/--
+Residue count inside a prefix of an ambient observation window.
+
+The ambient window size `k` is kept in the arguments to match the existing
+prefix height-count API.
+-/
+noncomputable def orbitWindowPrefixResidueCountMod4EqOne
+    (n : OddNat) (k r : ℕ) : ℕ :=
+  ((List.range k).take r).countP
+    (fun i => decide (oddOrbitLabel n i % 4 = 1))
+
 /--
 The exact-height occupation count is bounded by the window size.
 -/
@@ -414,6 +453,52 @@ theorem orbitWindowResidueCountMod4EqOne_le_window
     (List.countP_le_length
       (p := fun i => decide (oddOrbitLabel n i % 4 = 1)) (l := List.range k))
 
+/--
+The mod `4 = 3` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod4EqThree_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod4EqThree n k ≤ k := by
+  unfold orbitWindowResidueCountMod4EqThree
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 4 = 3)) (l := List.range k))
+
+/--
+The mod `8` residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountMod8EqFive_le_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqFive n k ≤ k := by
+  unfold orbitWindowResidueCountMod8EqFive
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 8 = 5)) (l := List.range k))
+
+/--
+The prefix mod `4` residue count is bounded by the prefix length.
+-/
+theorem orbitWindowPrefixResidueCountMod4EqOne_le_prefix
+    (n : OddNat) (k r : ℕ) :
+    orbitWindowPrefixResidueCountMod4EqOne n k r ≤ r := by
+  unfold orbitWindowPrefixResidueCountMod4EqOne
+  exact le_trans
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % 4 = 1))
+      (l := (List.range k).take r))
+    (by simp)
+
+/--
+Prefix mod `4` residue occupation agrees with the standalone count for the
+prefix length, as long as the prefix lies inside the ambient window.
+-/
+theorem orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    orbitWindowPrefixResidueCountMod4EqOne n k r =
+      orbitWindowResidueCountMod4EqOne n r := by
+  unfold orbitWindowPrefixResidueCountMod4EqOne orbitWindowResidueCountMod4EqOne
+  simp [List.take_range, Nat.min_eq_left hr]
+
 /--
 Counting `height >= 2` entries is the same as counting odd-state labels in
 residue class `1 mod 4`.
@@ -440,6 +525,31 @@ theorem orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
           exact hheight (hiff.mpr h)
         simp [ih, hheight, hres]
 
+/--
+Counting `height >= 3` entries is the same as counting odd-state labels in
+residue class `5 mod 8`.
+
+This is the mod `8` analogue of the second-layer residue occupation theorem.
+-/
+theorem orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountGe n k 3 =
+      orbitWindowResidueCountMod8EqFive n k := by
+  unfold orbitWindowHeightCountGe orbitWindowResidueCountMod8EqFive orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_three_le_iff_mod_eight_eq_five n k
+      by_cases hheight : 3 ≤ orbitWindowHeight n k
+      · have hres : oddOrbitLabel n k % 8 = 5 := hiff.mp hheight
+        simp [ih, hheight, hres]
+      · have hres : oddOrbitLabel n k % 8 ≠ 5 := by
+          intro h
+          exact hheight (hiff.mpr h)
+        simp [ih, hheight, hres]
+
 /--
 If every in-window height is exactly `h`, then the exact-height occupation
 count fills the whole window.
@@ -579,6 +689,18 @@ theorem orbitWindowHeightPrefixCountGe_eq_countGe
   unfold orbitWindowHeightPrefixCountGe orbitWindowHeightCountGe
   simp [orbitWindowHeightSeq, ← List.map_take, List.take_range, Nat.min_eq_left hr]
 
+/--
+Prefix `height >= 2` occupation is the same as prefix mod `4` residue
+occupation.
+-/
+theorem orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
+    (n : OddNat) {r k : ℕ} (hr : r ≤ k) :
+    orbitWindowHeightPrefixCountGe n k r 2 =
+      orbitWindowPrefixResidueCountMod4EqOne n k r := by
+  rw [orbitWindowHeightPrefixCountGe_eq_countGe n hr]
+  rw [orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one]
+  rw [← orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount n hr]
+
 /--
 Prefix threshold occupation gives a lower bound for the corresponding partial
 Collatz accumulated height.
@@ -648,6 +770,83 @@ theorem orbitWindowHeight_one_le
   simpa [s, threeNPlusOne] using
     v2_3n_plus_1_ge_1 (iterateT i n).1 (iterateT i n).2
 
+/--
+The first Collatz height layer is exact height `1` precisely on residue class
+`3 mod 4`.
+
+Together with `orbitWindowHeight_two_le_iff_mod_four_eq_one`, this closes the
+first mod `4` residue partition at the pointwise level.
+-/
+theorem orbitWindowHeight_eq_one_iff_mod_four_eq_three
+    (n : OddNat) (i : ℕ) :
+    orbitWindowHeight n i = 1 ↔ oddOrbitLabel n i % 4 = 3 := by
+  constructor
+  · intro hheight
+    have hnotTwo : ¬ 2 ≤ orbitWindowHeight n i := by omega
+    have hnotOne : oddOrbitLabel n i % 4 ≠ 1 := by
+      intro hmod
+      exact hnotTwo ((orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mpr hmod)
+    cases odd_mod_four_eq_one_or_three (iterateT i n).2 with
+    | inl hmod =>
+        change oddOrbitLabel n i % 4 = 1 at hmod
+        exact (hnotOne hmod).elim
+    | inr hmod =>
+        change oddOrbitLabel n i % 4 = 3 at hmod
+        exact hmod
+  · intro hmod
+    have hOne : 1 ≤ orbitWindowHeight n i := orbitWindowHeight_one_le n i
+    have hnotTwo : ¬ 2 ≤ orbitWindowHeight n i := by
+      intro htwo
+      have hmodOne := (orbitWindowHeight_two_le_iff_mod_four_eq_one n i).mp htwo
+      omega
+    omega
+
+/--
+Counting exact height `1` entries is the same as counting odd-state labels in
+residue class `3 mod 4`.
+-/
+theorem orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
+    (n : OddNat) (k : ℕ) :
+    orbitWindowHeightCountEq n k 1 =
+      orbitWindowResidueCountMod4EqThree n k := by
+  unfold orbitWindowHeightCountEq orbitWindowResidueCountMod4EqThree orbitWindowHeightSeq
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hiff := orbitWindowHeight_eq_one_iff_mod_four_eq_three n k
+      by_cases hheight : orbitWindowHeight n k = 1
+      · have hres : oddOrbitLabel n k % 4 = 3 := hiff.mp hheight
+        simp [ih, hheight, hres]
+      · have hres : oddOrbitLabel n k % 4 ≠ 3 := by
+          intro h
+          exact hheight (hiff.mpr h)
+        simp [ih, hheight, hres]
+
+/--
+The two odd residue classes modulo `4` fill the whole observation window.
+-/
+theorem orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod4EqOne n k +
+      orbitWindowResidueCountMod4EqThree n k = k := by
+  unfold orbitWindowResidueCountMod4EqOne orbitWindowResidueCountMod4EqThree
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      cases odd_mod_four_eq_one_or_three (iterateT k n).2 with
+      | inl hOne =>
+          change oddOrbitLabel n k % 4 = 1 at hOne
+          simp [hOne]
+          omega
+      | inr hThree =>
+          change oddOrbitLabel n k % 4 = 3 at hThree
+          simp [hThree]
+          omega
+
 /--
 The `height >= 1` occupation count fills the whole observation window.
 
@@ -952,6 +1151,27 @@ theorem orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
   rw [← orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one n k] at hm
   exact orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge n k m hm
 
+/--
+Three-layer residue-address drift bridge.
+
+If at least `m` labels in the window lie in residue class `5 mod 8`, then the
+third height layer contributes at least `m` additional units on top of the
+base layer and the second layer.
+-/
+theorem orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
+    (n : OddNat) (k m : ℕ)
+    (hm : m ≤ orbitWindowResidueCountMod8EqFive n k) :
+    k + orbitWindowHeightCountGe n k 2 + m ≤ sumS n k := by
+  have htail :
+      k + orbitWindowHeightCountGe n k 2 +
+          orbitWindowHeightCountGe n k 3 ≤ sumS n k := by
+    simpa [orbitWindowHeightCountGe_one_eq_window n k, Nat.add_assoc] using
+      orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three n k
+  rw [← orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five n k] at hm
+  exact le_trans
+    (Nat.add_le_add_left hm (k + orbitWindowHeightCountGe n k 2))
+    htail
+
 /--
 Prefix version: a lower bound on the prefix `height >= 2` occupation gives a
 local drift lower bound.
@@ -964,6 +1184,19 @@ theorem orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
     (Nat.add_le_add_left hm r)
     (orbitWindowHeightPrefix_sum_ge_window_add_countGe_two n hr)
 
+/--
+Prefix residue-address drift bridge.
+
+If at least `m` labels in the prefix lie in residue class `1 mod 4`, then the
+prefix accumulated height is at least `r + m`.
+-/
+theorem orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
+    (n : OddNat) {r k m : ℕ} (hr : r ≤ k)
+    (hm : m ≤ orbitWindowPrefixResidueCountMod4EqOne n k r) :
+    r + m ≤ sumS n r := by
+  rw [← orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one n hr] at hm
+  exact orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge n hr hm
+
 /--
 Block shifts preserve the raw height when the observed height is below the
 block exponent.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 29970703..60d5252f 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -105,6 +105,7 @@ rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne
 orbitWindowHeight_two_le_iff_four_dvd
 odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one
 orbitWindowHeight_two_le_iff_mod_four_eq_one
+odd_mod_four_eq_one_or_three
 three_le_v2_iff_eight_dvd
 rawHeightLabel_three_le_iff_eight_dvd_threeNPlusOne
 odd_eight_dvd_three_mul_add_one_iff_mod_eight_eq_five
@@ -123,10 +124,18 @@ orbitWindowHeight_eq_of_same_iterateT
 orbitWindowHeightCountEq
 orbitWindowHeightCountGe
 orbitWindowResidueCountMod4EqOne
+orbitWindowResidueCountMod4EqThree
+orbitWindowResidueCountMod8EqFive
+orbitWindowPrefixResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
 orbitWindowResidueCountMod4EqOne_le_window
+orbitWindowResidueCountMod4EqThree_le_window
+orbitWindowResidueCountMod8EqFive_le_window
+orbitWindowPrefixResidueCountMod4EqOne_le_prefix
+orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
+orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
 orbitWindowHeightCountEq_eq_window_of_forall_eq
 orbitWindowHeightCountGe_eq_window_of_forall_ge
 orbitWindowHeightSeq_sum_ge_countGe_mul_threshold
@@ -139,7 +148,11 @@ orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two
 orbitWindowHeight_one_le
 orbitWindowHeightCountGe_one_eq_window
 orbitWindowHeightSeq_sum_ge_window_add_countGe_two
+orbitWindowHeight_eq_one_iff_mod_four_eq_three
+orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
+orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
 orbitWindowHeightPrefixCountGe_one_eq
+orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
 orbitWindowHeightPrefix_sum_ge_window_add_countGe_two
 orbitWindowHeightCountGe_antitone
 orbitWindowHeightSeq_sum_ge_countGe_one_add_countGe_two_add_countGe_three
@@ -150,7 +163,9 @@ orbitWindowHeightSeq_sum_ge_window_add_sum_countGe_tail
 orbitWindowHeightPrefix_sum_ge_window_add_sum_countGe_tail
 orbitWindowHeightSeq_sum_ge_window_add_of_countGe_two_ge
 orbitWindowHeightSeq_sum_ge_window_add_of_residue_mod4_count_ge
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
 orbitWindowHeightPrefix_sum_ge_window_add_of_countGe_two_ge
+orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
 rawHeightLabel_shift_eq
 oddOrbitLabel_injOn_of_pairwiseSeparated
 iterateT_eq_of_oddOrbitLabel_eq
@@ -313,6 +328,15 @@ orbitWindowHeightCountGe n k threshold
 
 orbitWindowResidueCountMod4EqOne n k
   = number of odd orbit labels congruent to 1 modulo 4
+
+orbitWindowResidueCountMod4EqThree n k
+  = number of odd orbit labels congruent to 3 modulo 4
+
+orbitWindowResidueCountMod8EqFive n k
+  = number of odd orbit labels congruent to 5 modulo 8
+
+orbitWindowPrefixResidueCountMod4EqOne n k r
+  = number of prefix labels congruent to 1 modulo 4 inside an ambient k-window
 ```
 
 The current count API is intentionally minimal:
@@ -369,6 +393,13 @@ external CountGe 2 lower bound
 
 mod 4 residue occupation lower bound
   -> m <= residueCountMod4EqOne -> k + m <= sumS n k
+
+prefix mod 4 residue occupation lower bound
+  -> m <= prefixResidueCountMod4EqOne -> r + m <= sumS n r
+
+mod 8 residue occupation lower bound
+  -> m <= residueCountMod8EqFive
+  -> k + CountGe 2 + m <= sumS n k
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -454,6 +485,30 @@ m <= orbitWindowResidueCountMod4EqOne n k
 This changes the practical target from a valuation-count statement into a
 finite residue-class occupation statement.
 
+The same reading is now available locally in prefixes:
+
+```text
+m <= orbitWindowPrefixResidueCountMod4EqOne n k r
+  -> r + m <= sumS n r
+```
+
+The first mod `4` partition is also closed at pointwise and count level:
+
+```text
+height = 1 <-> oddOrbitLabel % 4 = 3
+CountGe 2 = residue mod 4 = 1
+CountEq 1 = residue mod 4 = 3
+residueCountMod4EqOne + residueCountMod4EqThree = k
+```
+
+The mod `8` layer now has a count-level handoff:
+
+```text
+CountGe 3 = residue mod 8 = 5
+m <= residueCountMod8EqFive
+  -> k + CountGe 2 + m <= sumS n k
+```
+
 This is the intended bridge from a future residue/address occupation theorem
 to a Collatz drift lower bound.
 
@@ -498,10 +553,10 @@ The next safe steps are:
 The immediate residue candidates are:
 
 ```text
-prefix version of residueCountMod4EqOne
-height >= 3 count as a mod 8 residue occupation
 transition map between residue classes under the accelerated map T
 general 2^r residue coordinate for height >= r
+prefix mod 8 residue occupation
+fixed experiment for height >= 4 as a mod 16 residue occupation
 ```
 
 The main caution is that Collatz state labels are not prime labels.  Any bridge
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-085.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-085.md
new file mode 100644
index 00000000..ae7f111b
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-085.md
@@ -0,0 +1,187 @@
+# Report Petal 085: Prefix Residue Counts and First Mod 4 Partition
+
+## Scope
+
+Checkpoint `085` extends the Collatz residue occupation bridge in two
+directions:
+
+```text
+full window  -> prefix window
+height >= 2  -> height >= 3
+```
+
+It also closes the first mod `4` partition:
+
+```text
+odd label mod 4 = 1  <-> height >= 2
+odd label mod 4 = 3  <-> height = 1
+```
+
+## Implemented Lean Surface
+
+File:
+
+```text
+DkMath.Collatz.PetalBridge
+```
+
+Prefix residue count:
+
+```lean
+orbitWindowPrefixResidueCountMod4EqOne
+orbitWindowPrefixResidueCountMod4EqOne_le_prefix
+orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
+orbitWindowHeightPrefixCountGe_two_eq_prefixResidueCount_mod4_eq_one
+orbitWindowHeightPrefix_sum_ge_window_add_of_residue_mod4_count_ge
+```
+
+This gives the prefix handoff:
+
+```lean
+m <= orbitWindowPrefixResidueCountMod4EqOne n k r
+  -> r + m <= sumS n r
+```
+
+Mod `8` occupation count:
+
+```lean
+orbitWindowResidueCountMod8EqFive
+orbitWindowResidueCountMod8EqFive_le_window
+orbitWindowHeightCountGe_three_eq_residueCount_mod8_eq_five
+orbitWindowHeightSeq_sum_ge_window_add_countGe_two_add_of_residue_mod8_count_ge
+```
+
+This gives the three-layer handoff:
+
+```lean
+m <= orbitWindowResidueCountMod8EqFive n k
+  -> k + orbitWindowHeightCountGe n k 2 + m <= sumS n k
+```
+
+## Extra Result
+
+The first mod `4` partition was also closed.
+
+Pointwise:
+
+```lean
+odd_mod_four_eq_one_or_three
+orbitWindowHeight_eq_one_iff_mod_four_eq_three
+```
+
+Count-level:
+
+```lean
+orbitWindowResidueCountMod4EqThree
+orbitWindowResidueCountMod4EqThree_le_window
+orbitWindowHeightCountEq_one_eq_residueCount_mod4_eq_three
+orbitWindowResidueCountMod4EqOne_add_eqThree_eq_window
+```
+
+This gives:
+
+```text
+CountGe 2 = labels with residue 1 mod 4
+CountEq 1 = labels with residue 3 mod 4
+residueCountMod4EqOne + residueCountMod4EqThree = k
+```
+
+The result is useful because the first Collatz peeling layer is no longer just
+a valuation statement.  It is a finite two-channel residue partition.
+
+## Documentation Sync
+
+Updated:
+
+```text
+DkMath.Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status note now records:
+
+```text
+prefix residue occupation -> prefix sumS lower bound
+mod 8 occupation -> three-layer sumS lower bound
+mod 4 partition -> residue counts fill the window
+```
+
+## Inference
+
+The practical observation target is now:
+
+```text
+Find occupation lower bounds for residue classes.
+```
+
+Instead of directly proving average height claims, downstream work can prove
+that enough orbit labels fall into a residue channel:
+
+```text
+mod 4 = 1  -> second layer
+mod 8 = 5  -> third layer
+```
+
+The mod `4` partition also clarifies the obstruction shape.  A prefix with too
+few `1 mod 4` labels has many `3 mod 4` labels, which means many exact
+height-one steps.  This is a concrete place to study transition behavior under
+the accelerated map `T`.
+
+## Next Implementation Candidates
+
+1. Residue transition map under one accelerated step:
+
+    ```lean
+    orbitWindowHeight_eq_one_of_mod_four_eq_three
+    T_residue_mod_four_of_height_one
+    ```
+
+    The intended reading is:
+
+    ```text
+    m % 4 = 3
+      -> height = 1
+      -> T(m) = (3m + 1) / 2
+      -> next residue can be inspected explicitly
+    ```
+
+2. Prefix mod `8` occupation:
+
+    ```lean
+    orbitWindowPrefixResidueCountMod8EqFive
+    orbitWindowHeightPrefixCountGe_three_eq_prefixResidueCount_mod8_eq_five
+    ```
+
+3. Fixed mod `16` experiment:
+
+    ```text
+    height >= 4
+      <-> odd label % 16 = 5
+    ```
+
+    This would confirm the next residue coordinate before attempting a general
+    `2^r` formulation.
+
+4. General residue coordinate remains a later target:
+
+    ```text
+    height >= r
+      <-> 2^r | (3m + 1)
+      <-> m is the odd solution of 3m + 1 = 0 mod 2^r
+    ```
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+lake build DkMath.Collatz.Collatz2K26
+git diff --check -- changed Collatz Petal files
+```
+
+Known unrelated warning observed during the build:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
````
`````

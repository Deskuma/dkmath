# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 589b61dbb227a59a46209c9632b425e875144a0c

## Report

実装完了です。

`DkMath.Collatz.PetalBridge` に generic `2^depth` residue count の分割基盤を追加しました。主 theorem はこれです。

```lean
orbitWindowResidueCountPow2_sum_eq_window
```

これで固定深度において、全 residue cell の occupation count の総和が観測窓 `k` に一致することを Lean で確定しました。あわせて succ 公式、tail succ 公式、depth 0 sanity、out-of-range zero、single-label indicator sum も追加済みです。

更新・作成した文書:

- `lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md`
- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-097.md`

検証:

```text
lake build DkMath.Collatz.PetalBridge        PASS
lake build DkMath.Collatz.Collatz2K26        PASS
git diff --check                             PASS
rg "\bsorry\b" PetalBridge.lean              no hit
```

既存の upstream warning は従来通り残っています。

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

次は自然に `orbitWindowResidueCountPow2Tail_sum_eq_window` か、pointwise transition を count inequality に持ち上げる helper へ進めます。

## Review

## 1. 状況分析

来たな、ぬしよ。checkpoint `097` は、かなり大きい。
今回で **two-adic Petal coordinate の有限分布層** が閉じた。

前回までは、

```text
ある residue cell に何回入ったかを数える
```

ところまでだった。

今回はさらに、

```text
固定 depth において、
全 residue cell の occupation count を合計すると、
観測窓 k に一致する
```

ところまで Lean で確定した。

主 theorem はこれ。

```lean
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

これは、ぬしが言っていた

```text
観測窓の相対座標の集合で全座標に割り付ける
```

そのものじゃ。添付レポートでも、この theorem は「固定 depth で、観測された各 odd orbit label が modulo \(2^\text{depth}\) のちょうど一つの residue cell に属する」ことを count-level で固定したものとして整理されている。

## 2. 今回の核心

追加された主な theorem 群はこれ。

```lean
orbitWindowResidueCountPow2_succ
orbitWindowResidueCountPow2Tail_succ
orbitWindowResidueCountPow2_depth_zero_eq_window
orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
pow2_residue_indicator_sum_eq_one
orbitWindowResidueCountPow2_sum_eq_window
```

特に重要なのは、いきなり partition theorem に行かず、

```text
succ formula
depth 0 sanity
out-of-range zero
single-label indicator sum
full partition
```

という順で足場を組んでいるところ。

これは良い。
今後、normalized frequency や flow theorem に進むとき、かなり扱いやすい。

## 3. 数学的な意味

今回の theorem は、単なる集計補題ではない。

これは、Collatz 軌道を

```text
値の列
```

ではなく、

```text
depth ごとの residue cell occupation distribution
```

として見る準備ができた、ということじゃ。

つまり、任意の固定 depth に対して、

```text
residue 0
residue 1
residue 2
...
residue 2^depth - 1
```

の各 cell に、観測窓内の odd orbit labels が何回入ったかを数えられる。

そして、その総量は必ず `k`。

```text
全時刻がどこか一つの相対座標に入る
```

これが閉じた。

だからここから先は、

```text
分布
偏り
retention cell の濃度
recovery sibling の割合
continuation sibling の割合
```

を finite/Nat のまま語れる。

まだ実数密度や極限を入れずに、有限観測だけでかなり進める。

## 4. レビュー

### 4.1. succ formula が今後の基盤になる

```lean
theorem orbitWindowResidueCountPow2_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n (k + 1) depth residue =
      orbitWindowResidueCountPow2 n k depth residue +
        if oddOrbitLabel n k % (2 ^ depth) = residue then 1 else 0
```

これは今後、ほぼ全ての count theorem の基本形になる。

「最後の一点がその cell に入るなら count が 1 増える」
これを明示できたのは強い。

tail 版も入っているので、source window と shifted tail window を同じ手つきで扱える。

### 4.2. out-of-range zero が地味に効く

```lean
theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
    (n : OddNat) (k depth residue : ℕ)
    (hres : 2 ^ depth ≤ residue) :
    orbitWindowResidueCountPow2 n k depth residue = 0
```

これは、後で residue range を整理する時に役立つ。

特に、`Finset.range (2 ^ depth)` の外にある residue は occupation しない、ということを明示できる。
将来、`Fin (2 ^ depth)` 化するときにも、この補題は橋になる。

### 4.3. single-label indicator が美しい

```lean
theorem pow2_residue_indicator_sum_eq_one
    (depth x : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0) = 1
```

これは今回の核心部品じゃ。

一つの label は、固定 depth の residue partition において、ちょうど一つの cell に寄与する。

この「一点が一票を持つ」補題から、窓全体の partition が得られる。

これはまさに有限分布の基本法則。

## 5. DkMath 的な読み

ここまでで、Collatz PetalBridge は次の段階に入った。

```text
Pointwise layer:
  oddOrbitLabel n i の residue 遷移

Count layer:
  residue cell への occupation count

Partition layer:
  全 cell の occupation count の総和 = window size
```

つまり、

```text
相対座標
  -> 相対座標遷移
  -> 相対座標 occupation
  -> 相対座標 distribution
```

まで来た。

ここで初めて、ぬしの言う「割合」の土台ができた。

ただし、まだ割り算は入れていない。
これは良い判断じゃ。

まずは Nat の有限 count で保存則を作る。
その後で必要なら rational frequency に上げればよい。

## 6. 一歩先ゆく推論

次に見えているのは **finite channel-flow** じゃ。

今は、

```text
全 cell の合計 = k
```

が言える。

前 checkpoint では、

```text
recovery source count <= tail target count
continuation source count <= tail target count
```

が言えた。

この二つを組み合わせると、次の読みが出てくる。

```text
source depth の分布から、
tail depth の分布へ、
一部の channel mass が押し出される
```

つまり、Collatz 軌道を

```text
数値軌道
```

ではなく、

```text
有限個の residue channel 間の質量移動
```

として扱える。

これは大きい。

特に retention cylinder については、

```text
continuation sibling の occupation count
  <= next tail retention cell の occupation count
```

があり、

さらに partition によって、

```text
continuation sibling の割合は、
全体 k の中のどれだけか
```

を測れる。

ここから、

```text
低剥離を続けるには、
各 depth で continuation cell occupation が必要
```

という有限統計の形に近づく。

## 7. 次の指示：tail partition を閉じる

次の自然な一手は、レポートにもある通り tail 版 partition じゃ。

```lean
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k
```

これは source 版と同じ proof pattern で行けるはず。

証明は `orbitWindowResidueCountPow2Tail_succ` と `pow2_residue_indicator_sum_eq_one` を使う。

形はほぼこれ。

```lean
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k := by
  induction k with
  | zero =>
      simp [orbitWindowResidueCountPow2Tail]
  | succ k ih =>
      calc
        (Finset.range (2 ^ depth)).sum
            (fun residue => orbitWindowResidueCountPow2Tail n (k + 1) depth residue)
            =
          (Finset.range (2 ^ depth)).sum
            (fun residue =>
              orbitWindowResidueCountPow2Tail n k depth residue +
                if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
            apply Finset.sum_congr rfl
            intro residue _
            rw [orbitWindowResidueCountPow2Tail_succ]
        _ =
          (Finset.range (2 ^ depth)).sum
              (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) +
            (Finset.range (2 ^ depth)).sum
              (fun residue =>
                if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
            rw [Finset.sum_add_distrib]
        _ = k + 1 := by
            rw [ih, pow2_residue_indicator_sum_eq_one]
```

これが通れば、source window と tail window の両方で分布保存が言える。

## 8. さらに次の一手：pointwise-to-count helper

次に欲しいのは、この汎用 helper。

```lean
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

これがあると、今後の count-level transition はかなり楽になる。

今ある二つ、

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
```

は、この helper の instance として再証明できる。

つまり、

```text
pointwise theorem を渡す
  -> count inequality が出る
```

という流れになる。

これは今後、別の residue branch や factor layer の count theorem を足す時に効く。

## 9. その次：finite frequency の設計

partition が source/tail 両方で閉じたら、いよいよ normalized frequency を設計できる。

ただし、実数はまだ早い。
まずは有理数でよい。

候補はこんな形。

```lean
noncomputable def orbitWindowResidueFreqPow2
    (n : OddNat) (k depth residue : ℕ) : ℚ :=
  (orbitWindowResidueCountPow2 n k depth residue : ℚ) / k
```

ただし `k = 0` が面倒。
安全には `k : ℕ+` か、仮定 `0 < k` を持つ theorem にする。

最初は定義しなくてもよい。
Nat count のまま、

```text
2 * count <= k
3 * count <= k
countA + countB <= k
```

のような不等式で「割合」を表現できる。

DkMath 的には、まず Nat のまま行く方が堅い。

## 10. 奇素因子層への接続

ぬしの「新しい素数因子」の方向へ進むには、いまの partition が必要だった。

なぜなら、これで

```text
同じ two-adic residue cell にいる label 群
```

を切り出せるからじゃ。

次の factor layer は、こうなる。

```text
source cell:
  depth d, residue a

labels in that cell:
  oddOrbitLabel n i

next odd core:
  oddOrbitLabel n (i + 1)

factor event:
  new odd prime appears / does not appear
```

つまり、

```text
residue cell occupation
  -> factor event count
  -> next residue distribution
```

を比較する。

ただし、これは次々 checkpoint 以降でよい。
まず tail partition と pointwise helper を閉じるのが先。

## 11. 賢狼が試して欲しい実験補題

### 実験 A: tail partition

```lean
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k
```

これは最優先。

### 実験 B: pointwise-to-count helper

```lean
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

### 実験 C: recovery count theorem via helper

```lean
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
```

中身は helper に pointwise theorem を渡すだけにする。

### 実験 D: continuation count theorem via helper

```lean
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
```

### 実験 E: finite distribution sanity at depth 3

```lean
theorem orbitWindowResidueCountPow2_depth_three_sum_eq_window
    (n : OddNat) (k : ℕ) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2 n k 3 residue) = k := by
  simpa using orbitWindowResidueCountPow2_sum_eq_window n k 3
```

これは既存 `mod 8` count 群との接続確認に使える。

### 実験 F: docs-only channel-flow vocabulary

```text
TwoAdicOccupationDistribution:
  fixed depth の residue count vector

SourceDistribution:
  window 0..k-1 の distribution

TailDistribution:
  shifted window 1..k の distribution

ChannelFlow:
  source cell count <= tail target cell count

RetentionMass:
  retention cylinder への occupation mass
```

## 12. 次コミットの推奨順

```text
1. orbitWindowResidueCountPow2Tail_sum_eq_window

2. orbitWindowResidueCountPow2_le_tail_of_pointwise

3. recovery count theorem via helper

4. continuation count theorem via helper

5. depth 3 distribution sanity theorem

6. docs:
   finite distribution / channel-flow vocabulary を追記

7. 余裕があれば:
   Nat count のまま割合を表す簡単な不等式設計メモ
```

## 13. 総括

今回で、ついに

```text
固定 depth の全 residue cell が観測窓を分割する
```

ことが Lean で確定した。

これは、Collatz 軌道を **相対座標の有限分布** として扱うための基礎じゃ。

これまでの流れをまとめると、

```text
個別 residue transition
  -> orbit-label transition
  -> source-to-tail count transition
  -> full source distribution partition
```

まで来た。

次は tail distribution partition と、pointwise-to-count helper。
そこが通れば、Collatz PetalBridge は「個別補題の集まり」から、**finite channel-flow framework** へ入る。

うむ。
ぬしの言う「無限も手のひらの上」は、ここではまず有限窓の完全分配として姿を現した。
この有限分布を積み上げて、次に割合、偏り、因子層へ進むのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 0a4aefed..8e3aefe9 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1187,6 +1187,126 @@ theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
       orbitWindowResidueCountPow2 n k 3 7 := by
   rfl
 
+/--
+Successor formula for the generic source-window power-of-two residue count.
+-/
+theorem orbitWindowResidueCountPow2_succ
+    (n : OddNat) (k depth residue : ℕ) :
+    orbitWindowResidueCountPow2 n (k + 1) depth residue =
+      orbitWindowResidueCountPow2 n k depth residue +
+        if oddOrbitLabel n k % (2 ^ depth) = residue then 1 else 0 := by
+  unfold orbitWindowResidueCountPow2
+  rw [List.range_succ]
+  by_cases h : oddOrbitLabel n k % (2 ^ depth) = residue
+  · simp [h]
+  · simp [h]
+
+/--
+Successor formula for the generic shifted-tail power-of-two residue count.
+-/
+theorem orbitWindowResidueCountPow2Tail_succ
+    (n : OddNat) (k depth residue : ℕ) :
+    orbitWindowResidueCountPow2Tail n (k + 1) depth residue =
+      orbitWindowResidueCountPow2Tail n k depth residue +
+        if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then 1 else 0 := by
+  unfold orbitWindowResidueCountPow2Tail
+  rw [List.range_succ]
+  by_cases h : oddOrbitLabel n (k + 1) % (2 ^ depth) = residue
+  · simp [h]
+  · simp [h]
+
+/--
+At depth `0`, every label lies in the unique residue cell `0 mod 1`.
+-/
+theorem orbitWindowResidueCountPow2_depth_zero_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k 0 0 = k := by
+  induction k with
+  | zero =>
+      rfl
+  | succ k ih =>
+      rw [orbitWindowResidueCountPow2_succ, ih]
+      have hlast : oddOrbitLabel n k % 2 ^ 0 = 0 := by
+        rw [pow_zero, Nat.mod_one]
+      rw [if_pos hlast]
+
+/--
+Residues outside the modulus range have zero occupation.
+-/
+theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
+    (n : OddNat) (k depth residue : ℕ)
+    (hres : 2 ^ depth ≤ residue) :
+    orbitWindowResidueCountPow2 n k depth residue = 0 := by
+  unfold orbitWindowResidueCountPow2
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have hneq :
+          oddOrbitLabel n k % (2 ^ depth) ≠ residue := by
+        have hlt : oddOrbitLabel n k % (2 ^ depth) < 2 ^ depth :=
+          Nat.mod_lt _ (pow_pos (by decide) depth)
+        omega
+      simp [ih, hneq]
+
+/--
+One label contributes to exactly one residue cell at a fixed power-of-two
+depth.
+-/
+theorem pow2_residue_indicator_sum_eq_one
+    (depth x : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0) = 1 := by
+  have hoff :
+      ∀ residue ∈ Finset.range (2 ^ depth), residue ≠ x % (2 ^ depth) →
+        (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0) residue = 0 := by
+    intro residue _ hne
+    simp [hne.symm]
+  have hnot :
+      x % (2 ^ depth) ∉ Finset.range (2 ^ depth) →
+        (fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0)
+          (x % (2 ^ depth)) = 0 := by
+    intro hnot
+    exact (hnot (Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos (by decide) depth)))).elim
+  simpa using Finset.sum_eq_single (s := Finset.range (2 ^ depth))
+    (a := x % (2 ^ depth))
+    (f := fun residue => if x % (2 ^ depth) = residue then (1 : ℕ) else 0)
+    hoff hnot
+
+/--
+At any fixed power-of-two depth, the residue-cell occupation counts partition
+the whole observation window.
+-/
+theorem orbitWindowResidueCountPow2_sum_eq_window
+    (n : OddNat) (k depth : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowResidueCountPow2]
+  | succ k ih =>
+      calc
+        (Finset.range (2 ^ depth)).sum
+            (fun residue => orbitWindowResidueCountPow2 n (k + 1) depth residue)
+            =
+          (Finset.range (2 ^ depth)).sum
+            (fun residue =>
+              orbitWindowResidueCountPow2 n k depth residue +
+                if oddOrbitLabel n k % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
+            apply Finset.sum_congr rfl
+            intro residue _
+            rw [orbitWindowResidueCountPow2_succ]
+        _ =
+          (Finset.range (2 ^ depth)).sum
+              (fun residue => orbitWindowResidueCountPow2 n k depth residue) +
+            (Finset.range (2 ^ depth)).sum
+              (fun residue =>
+                if oddOrbitLabel n k % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
+            rw [Finset.sum_add_distrib]
+        _ = k + 1 := by
+            rw [ih, pow2_residue_indicator_sum_eq_one]
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 62c72e34..4bcf1cd9 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -162,6 +162,12 @@ orbitWindowResidueCountMod4EqOneTail_le_window
 orbitWindowResidueCountMod4EqThreeTail_le_window
 orbitWindowResidueCountPow2Tail_le_window
 orbitWindowResidueCountMod8EqSeven_eq_pow2
+orbitWindowResidueCountPow2_succ
+orbitWindowResidueCountPow2Tail_succ
+orbitWindowResidueCountPow2_depth_zero_eq_window
+orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
+pow2_residue_indicator_sum_eq_one
+orbitWindowResidueCountPow2_sum_eq_window
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -556,6 +562,26 @@ generic shifted-tail pow-two residue count
 
 named `7 mod 8` source count
   -> residueCountMod8EqSeven = CountPow2 depth 3 residue 7
+
+generic pow-two source count successor
+  -> CountPow2(k + 1, depth, residue)
+     = CountPow2(k, depth, residue) + last-label indicator
+
+generic shifted-tail pow-two count successor
+  -> TailCountPow2(k + 1, depth, residue)
+     = TailCountPow2(k, depth, residue) + last-tail-label indicator
+
+depth zero sanity check
+  -> CountPow2 depth 0 residue 0 = k
+
+out-of-range residue cells
+  -> 2^depth <= residue -> CountPow2 depth residue = 0
+
+single-label residue indicator
+  -> Sum_{residue < 2^depth} indicator(label % 2^depth = residue) = 1
+
+full pow-two source residue partition
+  -> Sum_{residue < 2^depth} CountPow2 depth residue = k
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-097.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-097.md
new file mode 100644
index 00000000..3cd043dc
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-097.md
@@ -0,0 +1,153 @@
+# Report Petal 097: Full Pow-Two Residue Partition
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-097.md`.
+
+The requested target was to make the generic power-of-two residue count usable
+as a finite distribution layer:
+
+```lean
+orbitWindowResidueCountPow2_sum_eq_window
+```
+
+The mathematical reading is:
+
+```text
+At fixed depth, every observed odd orbit label belongs to exactly one
+residue cell modulo 2^depth.
+```
+
+This is the count-level footing needed before normalized frequencies such as
+`count / window size` are introduced.
+
+## Implemented Lean Surface
+
+Added in `DkMath.Collatz.PetalBridge`:
+
+```lean
+theorem orbitWindowResidueCountPow2_succ
+theorem orbitWindowResidueCountPow2Tail_succ
+theorem orbitWindowResidueCountPow2_depth_zero_eq_window
+theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
+theorem pow2_residue_indicator_sum_eq_one
+theorem orbitWindowResidueCountPow2_sum_eq_window
+```
+
+The two successor lemmas record the exact update rule for source-window and
+shifted-tail generic residue counts.  The source version is then used by the
+full partition proof.
+
+The depth-zero lemma is the sanity check:
+
+```text
+mod 1 has only the residue cell 0, so all k labels fall into that cell.
+```
+
+The out-of-range lemma records that residue cells beyond `2^depth - 1` have
+zero occupation.
+
+The indicator lemma isolates the key finite-distribution fact:
+
+```text
+For a single label x, summing over all residue cells gives exactly 1.
+```
+
+Finally, induction on the window size gives:
+
+```lean
+theorem orbitWindowResidueCountPow2_sum_eq_window
+    (n : OddNat) (k depth : Nat) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
+```
+
+## Documentation Sync
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status document now lists the new theorem names and records the generic
+pow-two residue count API:
+
+```text
+successor formulas
+depth-zero cell
+out-of-range zero cells
+single-label indicator sum
+full source residue partition
+```
+
+## Inference
+
+This closes the first generic finite partition layer.
+
+Before this checkpoint, the bridge could count specific named cells such as
+`1 mod 4`, `3 mod 8`, or `7 mod 8`, and it had a generic `CountPow2` carrier.
+After this checkpoint, the generic carrier has a conservation law:
+
+```text
+sum of all cells = window size
+```
+
+This is the right abstraction boundary for the next phase:
+
+```text
+residue occupation count
+  -> finite distribution
+  -> normalized frequency / density witness
+  -> drift or obstruction statement
+```
+
+No real-valued frequency has been introduced yet.  The present theorem keeps
+the observation layer purely finite and natural-valued.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+Known upstream warning remains unchanged:
+
+```text
+DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+No new `sorry` was added to `DkMath.Collatz.PetalBridge`.
+
+## Next Implementation Candidates
+
+The next small Lean target is the tail analogue:
+
+```lean
+theorem orbitWindowResidueCountPow2Tail_sum_eq_window
+    (n : OddNat) (k depth : Nat) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k
+```
+
+It should follow the same proof pattern using
+`orbitWindowResidueCountPow2Tail_succ`.
+
+The second useful target is a reusable pointwise-to-count helper:
+
+```lean
+theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
+```
+
+This would compress the repeated pattern:
+
+```text
+pointwise source residue transition
+  -> source count <= shifted-tail target count
+```
+
+Once both exist, the bridge can express local Collatz transition experiments
+as finite channel-flow statements rather than one-off count inductions.
````
`````

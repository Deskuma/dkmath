# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 54470384ea6bdc9d714ff5decbfc84c789b48282

## Report

096 checkpoint 完了です。

`DkMath.Collatz.PetalBridge` に generic pow-two residue count API を追加し、pointwise な recursive two-adic Petal transition を count-level の source-to-tail 不等式まで上げました。これで「ある residue cell に何回入ったか」を、任意 depth の `2^depth` 座標で扱える入口ができています。

追加・同期:

- [PetalBridge.lean](/lean/dk_math/DkMath/Collatz/PetalBridge.lean)
  - `orbitWindowResidueCountPow2`
  - `orbitWindowResidueCountPow2Tail`
  - `orbitWindowResidueCountPow2_le_window`
  - `orbitWindowResidueCountPow2Tail_le_window`
  - `orbitWindowResidueCountMod8EqSeven_eq_pow2`
  - `orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount`
  - `orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount`
- [Collatz-PetalBridge-Status.md](/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md)
- [report-petal-096.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-096.md)

検証:

- `lake build DkMath.Collatz.PetalBridge` passed
- `lake build DkMath.Collatz.Collatz2K26` passed
- `git diff --check` passed
- `PetalBridge.lean` 内の `sorry` なし

既存 upstream warning の `DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6 declaration uses sorry` は継続です。今回の追加では新規 `sorry` は入れていません。

## Review

## 1. 状況分析

うむ。checkpoint `096` は、**Petal 座標の分布論への入口**じゃ。

前回までで、

```text id="i1wklu"
点 i が recovery sibling にいる
  -> 点 i+1 が outward retention residue に入る

点 i が continuation sibling にいる
  -> 点 i+1 が next retention cell に入る
```

という **pointwise transition** ができていた。

今回、それが count-level へ上がった。

```text id="l0lsz6"
source window でその cell に何回入ったか
  -> shifted tail window で対応 cell に何回入ったか
```

を言えるようになった。

添付レポートでも、今回の主成果は generic pow-two residue count API を追加し、pointwise な recursive two-adic Petal transition を count-level の source-to-tail 不等式まで上げたことだと整理されている。

これは、ぬしの言っていた

```text id="pk26x7"
観測窓の相対座標の集合で全座標に割り付ける
```

方向へ、かなりはっきり進んでいる。

## 2. 今回の核心

新しい定義はこれ。

```lean id="tg80v5"
noncomputable def orbitWindowResidueCountPow2
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
```

これは、窓 `0, ..., k-1` の中で、各 orbit label が `mod 2^depth` のどの residue cell に入るかを数える。

tail 版も入った。

```lean id="sav68c"
noncomputable def orbitWindowResidueCountPow2Tail
    (n : OddNat) (k depth residue : ℕ) : ℕ :=
  (List.range k).countP
    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
```

これで、

```text id="jmif7w"
source-window occupation
shifted-tail occupation
```

を同じ generic API で扱えるようになった。

## 3. レビュー

## 3.1. generic count API は正しい方向

これまで `mod 4`, `mod 8` の個別 count が増えていた。

```text id="kagzty"
orbitWindowResidueCountMod4EqOne
orbitWindowResidueCountMod8EqThree
orbitWindowResidueCountMod8EqSeven
...
```

今回の `orbitWindowResidueCountPow2` は、それらを統一する入口じゃ。

これはかなり良い。
なぜなら、今後 `mod 16`, `mod 32`, `mod 64`, 一般 `mod 2^r` を扱うたびに個別 count を増やす必要がなくなる。

```text id="z525nl"
depth:
  観測解像度

residue:
  相対座標

count:
  その座標への occupation
```

という形に整理された。

## 3.2. named count bridge が良い

```lean id="veuv0x"
theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountMod8EqSeven n k =
      orbitWindowResidueCountPow2 n k 3 7 := by
  rfl
```

これは小さいが重要。

既存の concrete API と新 generic API が接続された。
つまり、過去の `mod 8` 議論を捨てずに、一般 API へ移行できる。

## 3.3. count-level Petal transition が本命

今回の本命はこの二つ。

```lean id="gcp8i2"
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
```

```lean id="w929zq"
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
```

読みはこう。

```text id="o3pzcc"
recovery sibling にいた回数
  <= 次窓で outward retention residue にいた回数

continuation sibling にいた回数
  <= 次窓で next retention cell にいた回数
```

これは、個別の枝が count の不等式になったということ。

つまり、

```text id="nzfuec"
点の力学
  -> 窓の統計
```

へ移った。

## 4. 数学的な意味

ここまで来ると、Collatz PetalBridge はこう読める。

```text id="huew28"
相対座標 cell を定義する

軌道がその cell に何回入ったかを数える

cell の遷移法則により、
source count が tail count に押し出される
```

これは、ぬしの言う「軌道の割合が分岐とどう関わるか」にかなり近い。

まだ「割合」そのものではなく count だが、割合は count を `k` で割ったものとして後から読める。

```text id="c85ifp"
count / window size
```

という観測量へ進める。

## 5. 一歩先ゆく推論

次に必要なのは、全 residue cell への割り付け。

いまは、特定の residue cell について

```text id="lxzkna"
この cell には何回入った
```

を数えられる。

しかし、割合を扱うには、

```text id="mg2x5v"
全時刻が、ちょうど一つの residue cell に入る
```

を Lean で固定したい。

つまり次の本丸はこれ。

```lean id="ju8x0k"
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

これが通ると、

```text id="isy4hk"
depth ごとの全 residue 分布
```

が得られる。

これこそ、ぬしの言う

```text id="yu1hrd"
観測窓の相対座標の集合で全座標に割り付ける
```

の形式化じゃ。

## 6. 次の指示：まず partition の足場

いきなり full partition に行く前に、次の順番が安全。

## 6.1. depth zero sanity check

```lean id="y4342o"
theorem orbitWindowResidueCountPow2_depth_zero_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k 0 0 = k
```

これは `mod 1` では全て `0` なので、全 label が residue `0` に入るという確認。

証明はおそらくこれで行ける。

```lean id="je7vss"
by
  unfold orbitWindowResidueCountPow2
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      simp [ih]
```

## 6.2. out-of-range residue はゼロ

```lean id="ec9f55"
theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
    (n : OddNat) (k depth residue : ℕ)
    (hres : 2 ^ depth ≤ residue) :
    orbitWindowResidueCountPow2 n k depth residue = 0
```

これは、`a % M < M` なので、`residue >= M` なら絶対に一致しない。

証明方針は `List.countP_eq_zero` 系があればそれを使う。なければ induction。

```lean id="w45oet"
by
  unfold orbitWindowResidueCountPow2
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [List.range_succ]
      have hneq :
          oddOrbitLabel n k % (2 ^ depth) ≠ residue := by
        have hlt : oddOrbitLabel n k % (2 ^ depth) < 2 ^ depth :=
          Nat.mod_lt _ (pow_pos (by decide) depth)
        omega
      simp [ih, hneq]
```

## 6.3. full residue partition

その後で本命。

```lean id="nxbz5t"
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

証明は `k` induction が良さそう。

`k+1` の最後の label の residue を

```lean id="ns7a1k"
oddOrbitLabel n k % (2 ^ depth)
```

として、その residue だけ count が 1 増える、という構図。

このため、先に succ lemma を作ると良い。

## 7. 追加で入れると強い succ lemma

source count の succ formula。

```lean id="ivvv2x"
theorem orbitWindowResidueCountPow2_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n (k + 1) depth residue =
      orbitWindowResidueCountPow2 n k depth residue +
        if oddOrbitLabel n k % (2 ^ depth) = residue then 1 else 0
```

tail 版。

```lean id="fip9g2"
theorem orbitWindowResidueCountPow2Tail_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2Tail n (k + 1) depth residue =
      orbitWindowResidueCountPow2Tail n k depth residue +
        if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then 1 else 0
```

これがあると、partition theorem も source-to-tail theorem も後で楽になる。

## 8. さらに次の一手：pointwise-to-count helper

今回、recovery と continuation の count theorem は同じ induction を二回書いている。

今後、類似 theorem が増えるなら、この一般 helper が欲しい。

```lean id="symyo1"
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

これが通ると、今後の count theorem は

```text id="wb53cz"
pointwise transition を渡すだけ
```

で済む。

ただし、今すぐ最優先ではない。
まず partition の足場を固めた方がよい。

## 9. 奇素因子層への一歩先ゆく推論

ここまでで two-adic 座標分布が見え始めた。

次に odd factor carrier を重ねるなら、こういう流れになる。

```text id="mwzb1s"
同じ residue cell にいる複数の label を集める

それらの次 odd core を見る

次 odd core に新しい奇素因子が現れるかを見る

その有無で、次の residue occupation が偏るかを見る
```

つまり、

```text id="uzm4s3"
TwoAdicPetalCoordinate
  -> branch skeleton

OddFactorCarrier
  -> branch weight / drift perturbation
```

という二層構造。

しかし、Lean に入れるのはまだ早い。
まず `orbitWindowResidueCountPow2_sum_eq_window` で coordinate distribution を閉じるのが先じゃ。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source count succ

```lean id="g4y6rr"
theorem orbitWindowResidueCountPow2_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2 n (k + 1) depth residue =
      orbitWindowResidueCountPow2 n k depth residue +
        if oddOrbitLabel n k % (2 ^ depth) = residue then 1 else 0
```

## 実験 B: tail count succ

```lean id="eytnzj"
theorem orbitWindowResidueCountPow2Tail_succ
    (n : OddNat) (k depth residue : ℕ) :
    orbitWindowResidueCountPow2Tail n (k + 1) depth residue =
      orbitWindowResidueCountPow2Tail n k depth residue +
        if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then 1 else 0
```

## 実験 C: depth zero

```lean id="q8v4py"
theorem orbitWindowResidueCountPow2_depth_zero_eq_window
    (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k 0 0 = k
```

## 実験 D: out-of-range zero

```lean id="o9puuv"
theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
    (n : OddNat) (k depth residue : ℕ)
    (hres : 2 ^ depth ≤ residue) :
    orbitWindowResidueCountPow2 n k depth residue = 0
```

## 実験 E: full partition

```lean id="jf3fv7"
theorem orbitWindowResidueCountPow2_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
```

## 実験 F: reusable pointwise-to-count helper

```lean id="ug9rrg"
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

## 11. 次コミットの推奨順

```text id="thtdmj"
1. orbitWindowResidueCountPow2_succ

2. orbitWindowResidueCountPow2Tail_succ

3. orbitWindowResidueCountPow2_depth_zero_eq_window

4. orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue

5. orbitWindowResidueCountPow2_sum_eq_window

6. 余裕があれば:
   orbitWindowResidueCountPow2_le_tail_of_pointwise

7. docs:
   coordinate distribution / full residue partition の説明を追加
```

`pointwise-to-count helper` は便利だが、本丸は partition。
まず「全座標への割り付け」を閉じるのが良い。

## 12. 総括

今回で、

```text id="cjxr7r"
相対座標 cell の点遷移
```

から、

```text id="c33fur"
相対座標 cell の occupation 遷移
```

へ進んだ。

これは大きい。

次は、

```text id="m1n6by"
全ての時刻が、depth ごとのどこか一つの residue cell に入る
```

を Lean で固定する。

これができれば、two-adic Petal coordinate の分布が手に入る。
その次に、分布の偏り、retention 濃度、recovery sibling の割合、そして odd factor carrier との相互作用へ進める。

道は見えている。
いまは Collatz 軌道を「値の列」ではなく、**相対座標 occupation の流れ**として掴み始めている段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 8eb448e7..0a4aefed 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -918,6 +918,18 @@ noncomputable def orbitWindowResidueCountMod8EqSeven
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n i % 8 = 7))
 
+/--
+Generic residue-cell occupation count for a power-of-two modulus.
+
+This is the coordinate-count version of the concrete `mod 4` and `mod 8`
+counts above.  It counts how many labels in the window lie in a chosen residue
+class modulo `2^depth`.
+-/
+noncomputable def orbitWindowResidueCountPow2
+    (n : OddNat) (k depth residue : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
+
 /--
 Number of shifted-tail labels in residue class `1 mod 4`.
 
@@ -942,6 +954,17 @@ noncomputable def orbitWindowResidueCountMod4EqThreeTail
   (List.range k).countP
     (fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3))
 
+/--
+Generic shifted-tail residue-cell occupation count for a power-of-two modulus.
+
+This counts labels at times `1, 2, ..., k`, indexed as `i + 1`, in a chosen
+residue class modulo `2^depth`.
+-/
+noncomputable def orbitWindowResidueCountPow2Tail
+    (n : OddNat) (k depth residue : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
+
 /--
 Residue count inside a prefix of an ambient observation window.
 
@@ -1107,6 +1130,18 @@ theorem orbitWindowResidueCountMod8EqSeven_le_window
     (List.countP_le_length
       (p := fun i => decide (oddOrbitLabel n i % 8 = 7)) (l := List.range k))
 
+/--
+The generic power-of-two residue count is bounded by the window size.
+-/
+theorem orbitWindowResidueCountPow2_le_window
+    (n : OddNat) (k depth residue : ℕ) :
+    orbitWindowResidueCountPow2 n k depth residue ≤ k := by
+  unfold orbitWindowResidueCountPow2
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
+      (l := List.range k))
+
 /--
 The shifted-tail mod `4 = 1` residue count is bounded by the window size.
 -/
@@ -1129,6 +1164,29 @@ theorem orbitWindowResidueCountMod4EqThreeTail_le_window
     (List.countP_le_length
       (p := fun i => decide (oddOrbitLabel n (i + 1) % 4 = 3)) (l := List.range k))
 
+/--
+The generic shifted-tail power-of-two residue count is bounded by the window
+size.
+-/
+theorem orbitWindowResidueCountPow2Tail_le_window
+    (n : OddNat) (k depth residue : ℕ) :
+    orbitWindowResidueCountPow2Tail n k depth residue ≤ k := by
+  unfold orbitWindowResidueCountPow2Tail
+  simpa using
+    (List.countP_le_length
+      (p := fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
+      (l := List.range k))
+
+/--
+The named `7 mod 8` source count is the depth-`3` instance of the generic
+power-of-two residue count.
+-/
+theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k =
+      orbitWindowResidueCountPow2 n k 3 7 := by
+  rfl
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
@@ -2012,6 +2070,72 @@ theorem residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
             simpa [hsource, htail] using Nat.le_succ_of_le ih
         · simp [hsource, htail, ih]
 
+/--
+Count-level recursive Petal transition for the recovery sibling.
+
+Every source-window label in the recovery sibling modulo `2^(r + 2)`
+contributes a shifted-tail label in the outward retention residue modulo
+`2^(r + 1)`.
+-/
+theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1) := by
+  unfold orbitWindowResidueCountPow2 orbitWindowResidueCountPow2Tail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have htransition :
+          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1 →
+            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 :=
+        oddOrbitLabel_succ_recovery_residue_of_mod r hr n k
+      by_cases hsource :
+          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 1) - 1
+      · have htail :
+            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1 :=
+          htransition hsource
+        simp [hsource, htail, ih]
+      · by_cases htail :
+            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ r - 1
+        · exact by
+            simpa [hsource, htail] using Nat.le_succ_of_le ih
+        · simp [hsource, htail, ih]
+
+/--
+Count-level recursive Petal transition for the continuation sibling.
+
+Every source-window label in the continuation sibling modulo `2^(r + 2)`
+contributes a shifted-tail label in the next retention cell modulo
+`2^(r + 1)`.
+-/
+theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1) := by
+  unfold orbitWindowResidueCountPow2 orbitWindowResidueCountPow2Tail
+  induction k with
+  | zero =>
+      simp
+  | succ k ih =>
+      rw [List.range_succ]
+      have htransition :
+          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1 →
+            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 :=
+        oddOrbitLabel_succ_continuation_residue_of_mod r hr n k
+      by_cases hsource :
+          oddOrbitLabel n k % (2 ^ (r + 2)) = 2 ^ (r + 2) - 1
+      · have htail :
+            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1 :=
+          htransition hsource
+        simp [hsource, htail, ih]
+      · by_cases htail :
+            oddOrbitLabel n (k + 1) % (2 ^ (r + 1)) = 2 ^ (r + 1) - 1
+        · exact by
+            simpa [hsource, htail] using Nat.le_succ_of_le ih
+        · simp [hsource, htail, ih]
+
 /--
 Every `7 mod 8` source label contributes a shifted-tail entry with exact
 height `1`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index bbbd2937..62c72e34 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -139,8 +139,10 @@ orbitWindowResidueCountMod8EqOne
 orbitWindowResidueCountMod8EqThree
 orbitWindowResidueCountMod8EqFive
 orbitWindowResidueCountMod8EqSeven
+orbitWindowResidueCountPow2
 orbitWindowResidueCountMod4EqOneTail
 orbitWindowResidueCountMod4EqThreeTail
+orbitWindowResidueCountPow2Tail
 orbitWindowPrefixResidueCountMod4EqOne
 orbitWindowHeightCountEq_le_window
 orbitWindowHeightCountGe_le_window
@@ -155,8 +157,11 @@ orbitWindowResidueCountMod8EqOne_le_window
 orbitWindowResidueCountMod8EqThree_le_window
 orbitWindowResidueCountMod8EqFive_le_window
 orbitWindowResidueCountMod8EqSeven_le_window
+orbitWindowResidueCountPow2_le_window
 orbitWindowResidueCountMod4EqOneTail_le_window
 orbitWindowResidueCountMod4EqThreeTail_le_window
+orbitWindowResidueCountPow2Tail_le_window
+orbitWindowResidueCountMod8EqSeven_eq_pow2
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -229,6 +234,8 @@ orbitWindowNextNextNextNextHeight_two_le_of_mod_sixtyfour_eq_thirtyone
 orbitWindowResidueCountMod8EqThree_le_tailMod4EqOne
 orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
+orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
+orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
 orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
 orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
 orbitWindowHeightCountGeTail_le_countGe_succ
@@ -448,6 +455,9 @@ orbitWindowResidueCountMod8EqFive n k
 orbitWindowResidueCountMod8EqSeven n k
   = number of odd orbit labels congruent to 7 modulo 8
 
+orbitWindowResidueCountPow2 n k depth residue
+  = number of odd orbit labels congruent to residue modulo 2^depth
+
 orbitWindowResidueCountMod4EqOneTail n k
   = number of shifted tail labels, at times i + 1 for i < k,
     congruent to 1 modulo 4
@@ -456,6 +466,10 @@ orbitWindowResidueCountMod4EqThreeTail n k
   = number of shifted tail labels, at times i + 1 for i < k,
     congruent to 3 modulo 4
 
+orbitWindowResidueCountPow2Tail n k depth residue
+  = number of shifted tail labels, at times i + 1 for i < k,
+    congruent to residue modulo 2^depth
+
 orbitWindowPrefixResidueCountMod4EqOne n k r
   = number of prefix labels congruent to 1 modulo 4 inside an ambient k-window
 ```
@@ -533,6 +547,15 @@ tail first-layer partition
 
 retaining `7 mod 8` source
   -> residueCountMod8EqSeven <= tail CountEq 1
+
+generic pow-two residue count
+  -> CountPow2 depth residue <= k
+
+generic shifted-tail pow-two residue count
+  -> TailCountPow2 depth residue <= k
+
+named `7 mod 8` source count
+  -> residueCountMod8EqSeven = CountPow2 depth 3 residue 7
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -979,6 +1002,20 @@ This is the first general orbit-level statement of the narrowing retention
 cylinder: recovery exits one level outward, while continuation becomes the next
 retention cell.
 
+The same recursive rule is now lifted to occupation counts.  Source cells in
+the current window inject into target cells in the shifted tail window:
+
+```text
+CountPow2 depth (r+2) residue (2^(r+1)-1), 2 <= r
+  <= TailCountPow2 depth (r+1) residue (2^r - 1)
+
+CountPow2 depth (r+2) residue (2^(r+2)-1), 1 <= r
+  <= TailCountPow2 depth (r+1) residue (2^(r+1)-1)
+```
+
+This is the first count-level recursive Petal statistic: individual address
+transitions now become source-to-tail occupation inequalities.
+
 At count level, the two exact-height-one source channels also have a source
 mass bound:
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-096.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-096.md
new file mode 100644
index 00000000..88c46478
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-096.md
@@ -0,0 +1,261 @@
+# Report Petal 096: Generic Pow-Two Residue Counts
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-096.md`.
+
+Checkpoint 095 lifted the recursive two-adic Petal transition to actual
+orbit-label theorems.  The next task was to count how often a window visits a
+given two-adic residue cell, then lift pointwise transitions to count-level
+source-to-tail inequalities.
+
+The checkpoint closed with no new Lean `sorry`.
+
+## Implemented Lean Surface
+
+File:
+
+```text
+lean/dk_math/DkMath/Collatz/PetalBridge.lean
+```
+
+Generic source-window residue count:
+
+```lean
+orbitWindowResidueCountPow2
+orbitWindowResidueCountPow2_le_window
+```
+
+Generic shifted-tail residue count:
+
+```lean
+orbitWindowResidueCountPow2Tail
+orbitWindowResidueCountPow2Tail_le_window
+```
+
+Bridge from a named concrete count:
+
+```lean
+orbitWindowResidueCountMod8EqSeven_eq_pow2
+```
+
+Count-level recursive Petal transitions:
+
+```lean
+orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
+orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
+```
+
+## Generic Count API
+
+Source-window count:
+
+```lean
+noncomputable def orbitWindowResidueCountPow2
+    (n : OddNat) (k depth residue : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n i % (2 ^ depth) = residue))
+```
+
+Shifted-tail count:
+
+```lean
+noncomputable def orbitWindowResidueCountPow2Tail
+    (n : OddNat) (k depth residue : ℕ) : ℕ :=
+  (List.range k).countP
+    (fun i => decide (oddOrbitLabel n (i + 1) % (2 ^ depth) = residue))
+```
+
+Both counts have the expected window-size bound:
+
+```text
+source count <= k
+tail count <= k
+```
+
+The named `7 mod 8` source count is now fixed as a concrete instance:
+
+```lean
+theorem orbitWindowResidueCountMod8EqSeven_eq_pow2
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountMod8EqSeven n k =
+      orbitWindowResidueCountPow2 n k 3 7
+```
+
+## Count-Level Recursive Petal Transition
+
+Recovery sibling:
+
+```lean
+theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
+```
+
+Continuation sibling:
+
+```lean
+theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
+```
+
+Reading:
+
+```text
+source-window recovery occupation
+  <= shifted-tail outward-retention occupation
+
+source-window continuation occupation
+  <= shifted-tail next-retention occupation
+```
+
+This is the first count-level version of the recursive two-adic Petal.  The
+previous theorem said that a single source address determines a next address.
+The new theorem says that the number of visits to a source address is bounded
+by the number of visits to the corresponding shifted target address.
+
+## Proof Shape
+
+The proofs use the same induction pattern as the earlier concrete count
+bridges:
+
+```text
+induct on k
+split on whether index k is in the source cell
+if yes, pointwise orbit-label theorem gives the tail target cell
+if no, the target may or may not occur, but the inequality follows by monotonicity
+```
+
+The pointwise input is exactly checkpoint 095:
+
+```lean
+oddOrbitLabel_succ_recovery_residue_of_mod
+oddOrbitLabel_succ_continuation_residue_of_mod
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
+The status note now records:
+
+```text
+generic pow-two residue counts
+generic shifted-tail pow-two residue counts
+named 7 mod 8 count as depth-3 instance
+count-level recovery transition
+count-level continuation transition
+```
+
+## Factor-Layer Note
+
+The odd factor layer remains design-level only in this checkpoint.
+
+The current formal layer is:
+
+```text
+TwoAdicPetalCoordinate:
+  residue address modulo 2^depth
+
+TwoAdicOccupation:
+  how often an orbit window visits a residue address
+```
+
+The future layer remains:
+
+```text
+OddFactorCarrier:
+  odd-prime factor structure of the current or next odd core
+
+NewOddPrimeFactor:
+  an odd prime appearing in the next odd core but not in the current label
+
+CoordinateFactorInteraction:
+  how two-adic branch occupation interacts with odd-prime carrier changes
+```
+
+The reason to wait is now clearer: before studying factor interaction, we need
+the coordinate distribution itself.  This checkpoint provides the occupation
+API for that distribution.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge
+```
+
+The build still reports the existing upstream warning:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean: declaration uses `sorry`
+```
+
+No new `sorry` was introduced in `DkMath.Collatz.PetalBridge`.
+
+## What Was Not Done Yet
+
+The full residue partition theorem was not attempted in this checkpoint:
+
+```lean
+theorem orbitWindowResidueCountPow2_sum_eq_window
+    (n : OddNat) (k depth : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
+```
+
+This is the next natural theorem.  It says every orbit-label index in the
+window is assigned to exactly one residue cell at the chosen depth.
+
+## Next Implementation Candidates
+
+Candidate A: zero-depth sanity check.
+
+```lean
+theorem orbitWindowResidueCountPow2_depth_zero_eq_window
+    (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k 0 0 = k
+```
+
+Candidate B: out-of-range residue count is zero.
+
+```lean
+theorem orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
+    (n : OddNat) (k depth residue : ℕ)
+    (hres : 2 ^ depth ≤ residue) :
+    orbitWindowResidueCountPow2 n k depth residue = 0
+```
+
+Candidate C: full residue partition.
+
+```lean
+theorem orbitWindowResidueCountPow2_sum_eq_window
+    (n : OddNat) (k depth : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k
+```
+
+Candidate D: source-to-tail count theorem as a reusable implication helper.
+
+```lean
+theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
+    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
+    (h :
+      ∀ i, i < k →
+        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
+          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
+    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
+      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
+```
+
+Candidate D would remove duplicated induction from future count transitions.
+It is not necessary yet, but if the next checkpoint adds more source-to-tail
+rules, it should be considered.
````
`````

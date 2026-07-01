# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 33f5aea3ce7cd1e9fe694a4a0081208b12120a8e

## Report

098 完了です。

`DkMath.Collatz.PetalBridge` に tail 側の分布保存を追加しました。

```lean
orbitWindowResidueCountPow2Tail_sum_eq_window
```

さらにおまけとして、pointwise residue transition を count inequality に持ち上げる汎用 helper も実装しました。

```lean
orbitWindowResidueCountPow2_le_tail_of_pointwise
```

これで構図はかなり明確です。

```text
source residue partition
tail residue partition
pointwise transition
  -> count-level channel flow
```

更新・作成:

- `lean/dk_math/DkMath/Collatz/PetalBridge.lean`
- `lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md`
- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-098.md`

検証:

```text
lake build DkMath.Collatz.PetalBridge   PASS
lake build DkMath.Collatz.Collatz2K26   PASS
git diff --check                        PASS
rg "\bsorry\b" PetalBridge.lean         no hit
```

既存 upstream warning は従来通りです。

```text
DkMath.NumberTheory.ZsigmondyCyclotomicResearch.lean:152:6:
declaration uses `sorry`
```

次は既存の recovery / continuation count theorem を、この helper の corollary として薄く再接続するのが自然です。

## Review

## 1. 状況分析

うむ。これは **checkpoint No.100 に向けての区切り** と見てよい。

今回の checkpoint `098` で、Collatz.PetalBridge はかなり明確に次の形へ入った。

```text id="zhwd79"
source residue partition

tail residue partition

pointwise transition
  -> count-level channel flow
```

つまり、前回までで source 側の有限分布が閉じ、今回で tail 側の有限分布も閉じた。さらに `orbitWindowResidueCountPow2_le_tail_of_pointwise` が入り、点ごとの residue 遷移を count inequality へ持ち上げる汎用 helper まで入った。レポートでも、この構図が「finite channel-flow system」として整理されている。

これはかなり綺麗な区切りじゃ。
No.100 は「checkpoint 100: finite channel-flow layer stabilized」として締められる位置に来ている。

## 2. 今回の核心

追加された主 theorem は二つ。

```lean id="u4ydgt"
theorem orbitWindowResidueCountPow2Tail_sum_eq_window
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k
```

```lean id="px9vm3"
theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
```

前者で tail 側の全 residue cell が窓 `k` を分割する。
後者で、pointwise transition が count-level channel-flow に変換できる。

つまり、これまで個別に証明していた

```text id="uwhw6p"
この source cell にいたら、
次の tail cell に行く
```

という命題を、

```text id="x58ajn"
この source cell にいた回数は、
対応する tail cell に入った回数以下
```

へ機械的に上げられる。

これは API としてかなり強い。

## 3. レビュー

## 3.1. tail partition は必須だった

source partition だけでは、まだ片翼だった。

```text id="x4c5mg"
source window:
  labels 0..k-1

tail window:
  labels 1..k
```

Collatz の一歩遷移は `i -> i+1` なので、tail 側にも同じ分布保存がないと、channel-flow を有限分布として読めない。

今回、

```text id="a4odta"
source distribution total = k
tail distribution total = k
```

が両方そろった。

これで、source 側の質量と tail 側の質量を同じ土俵で比較できる。

## 3.2. pointwise-to-count helper が大きい

この補題は、今後かなり効く。

```text id="r2v2ac"
pointwise theorem を作る
  -> helper に渡す
  -> count inequality が出る
```

という流れになるからじゃ。

今までは、recovery / continuation それぞれで count induction を書く必要があった。
今後は、pointwise theorem さえあれば、count theorem は薄い corollary にできる。

これは checkpoint No.100 に向けて、かなり良い整理ポイント。

## 3.3. 証明の抽象境界が見えた

いまの層はこう分かれている。

```text id="pbf3l0"
Residue arithmetic:
  raw residue step

Orbit-label transition:
  actual oddOrbitLabel n i -> oddOrbitLabel n (i+1)

Count distribution:
  source/tail residue occupation

Channel-flow:
  pointwise transition -> count inequality
```

この分離はとてもよい。
数学的にも実装的にも、今後の拡張がしやすい。

## 4. 数学的な意味

ここで初めて、Collatz の `mod 2^depth` 観測は **有限流量系** として読める。

```text id="ifri9l"
source residue distribution
  -> Collatz transition
  -> tail residue distribution
```

各 residue cell は「座標」。
occupation count は「その座標に滞在した質量」。
pointwise theorem は「その座標からどこへ流れるか」。
helper は「点の流れを質量の流れに持ち上げる装置」。

つまり、Collatz 軌道は、

```text id="hokmad"
値の列
```

から、

```text id="keecg6"
finite residue-channel flow
```

へ翻訳され始めた。

これはかなり大きい。

## 5. No.100 に向けた位置づけ

checkpoint No.100 に向けて、次は「締め」に相応しい作業がよい。

いま候補は二つある。

```text id="mhnsx8"
A. 既存 recovery / continuation count theorem を helper 由来の thin corollary として再接続する

B. finite channel-flow vocabulary と docs を整備する
```

賢狼としては、No.99 で A、No.100 で B が綺麗だと思う。

つまり、

```text id="a739el"
No.99:
  helper を使って既存 count theorem を再接続

No.100:
  finite channel-flow layer の総括 docs
  ここまでの theorem chain を整理
```

これが一番「キリ番」らしい。

新しい重い概念、たとえば odd factor layer には、No.100 の後で入る方がよい。
No.100 は、今の two-adic coordinate layer を締める checkpoint にするのが美しい。

## 6. 次の指示：既存 count theorem を helper で再接続

次は、既存の二つを helper から再証明する薄い corollary を置く。

### recovery 側

```lean id="lm728m"
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1) := by
  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
  intro i hi hsource
  exact oddOrbitLabel_succ_recovery_residue_of_mod r hr n i hsource
```

### continuation 側

```lean id="pmm64h"
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1) := by
  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
  intro i hi hsource
  exact oddOrbitLabel_succ_continuation_residue_of_mod r hr n i hsource
```

`hi` は使わないので、Lean が warning を出すなら `_hi` にする。

この二つは、既存 theorem と同値の薄い wrapper じゃ。
しかし意味は大きい。
「今後はこの route で行ける」と固定できる。

## 7. さらに一歩先：source/tail distribution pair

次に、source と tail の分布をまとめて扱う名前が欲しい。

まだ structure までは不要だが、docs には置ける。

```text id="xlub7i"
SourceDistribution(depth):
  orbitWindowResidueCountPow2 n k depth residue

TailDistribution(depth):
  orbitWindowResidueCountPow2Tail n k depth residue

DistributionConservation:
  sum source = k
  sum tail = k

ChannelFlow:
  source cell occupation <= tail target cell occupation
```

Lean に入れるなら、軽い abbreviation だけでもよい。

```lean id="y9nn0h"
abbrev SourcePow2Distribution :=
  orbitWindowResidueCountPow2

abbrev TailPow2Distribution :=
  orbitWindowResidueCountPow2Tail
```

ただし、今は theorem 名がすでに明確なので、必須ではない。

## 8. No.100 でやると美しい総括 theorem

No.100 の締めに、次のような「パッケージ theorem」を docs に置くと良い。

Lean theorem として無理に一つにまとめる必要はない。
docs で theorem chain を整理するのが良い。

```text id="ssfzih"
Finite channel-flow layer:

1. Source partition:
   sum source cells = k

2. Tail partition:
   sum tail cells = k

3. Pointwise-to-count helper:
   pointwise cell transition
     -> source count <= tail target count

4. Recursive two-adic Petal instances:
   recovery source <= outward tail
   continuation source <= next-retention tail
```

この四つが揃ったら、checkpoint 100 としてかなり締まる。

## 9. その後に進むべき方向

No.100 の後は、二つの道がある。

```text id="vme72z"
A. finite frequency / ratio layer

B. odd factor carrier layer
```

賢狼としては、まず A を薄く入れるのがよい。

実数ではなく、Nat inequality で割合を表す。

たとえば、

```text id="trpmlt"
2 * retentionCount <= k
3 * recoveryCount <= 2 * k
```

のような形。

いきなり \(\mathbb{Q}\) や \(\mathbb{R}\) の frequency を入れると、ゼロ除算や coercion が増える。
DkMath らしく、まず finite Nat ratio で攻めるのが堅い。

その後で odd factor carrier。

```text id="xk91g2"
TwoAdicPetalCoordinate:
  分岐骨格

OddFactorCarrier:
  奇素因子構造

CoordinateFactorInteraction:
  座標分布と因子変化の相関
```

## 10. 賢狼が試して欲しい実験補題

## 実験 A: recovery via helper

```lean id="l7g73w"
theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1) := by
  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
  intro i _hi hsource
  exact oddOrbitLabel_succ_recovery_residue_of_mod r hr n i hsource
```

## 実験 B: continuation via helper

```lean id="kxosys"
theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1) := by
  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
  intro i _hi hsource
  exact oddOrbitLabel_succ_continuation_residue_of_mod r hr n i hsource
```

## 実験 C: depth 3 source/tail finite distribution sanity

```lean id="kecg7e"
theorem orbitWindowResidueCountPow2_depth_three_sum_eq_window
    (n : OddNat) (k : ℕ) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2 n k 3 residue) = k := by
  simpa using orbitWindowResidueCountPow2_sum_eq_window n k 3
```

```lean id="h916iu"
theorem orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
    (n : OddNat) (k : ℕ) :
    (Finset.range 8).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k 3 residue) = k := by
  simpa using orbitWindowResidueCountPow2Tail_sum_eq_window n k 3
```

## 実験 D: named finite channel-flow docs

docs に以下を追加。

```text id="fz77op"
Finite channel-flow layer:

SourceDistribution:
  CountPow2 over labels 0..k-1

TailDistribution:
  TailCountPow2 over labels 1..k

Conservation:
  total source mass = k
  total tail mass = k

ChannelFlow:
  pointwise source-to-tail transition
    -> source occupation <= tail occupation
```

## 実験 E: future ratio layer design note

docs-only でよい。

```text id="m39jyl"
FiniteRatioWitness:
  use Nat inequalities instead of ℚ/ℝ frequency first

Example:
  a cell occupies at most half the window
    as 2 * count <= k

Reason:
  avoids division by zero and coercion overhead
```

## 11. 次コミットの推奨順

```text id="mm2f6n"
1. recovery count theorem via helper

2. continuation count theorem via helper

3. depth 3 source distribution sanity

4. depth 3 tail distribution sanity

5. docs:
   finite channel-flow layer の総括

6. docs:
   checkpoint 100 に向けた theorem chain summary

7. 余裕があれば:
   finite ratio layer の設計メモ
```

これで No.99 は「helper 接続」。
No.100 は「finite channel-flow layer 総括」で締められる。

## 12. 総括

これは区切りじゃ。
かなり良い区切り。

今の状態は、

```text id="iejefe"
source distribution が保存される

tail distribution も保存される

pointwise transition が count-flow へ持ち上がる
```

ところまで来た。

つまり、Collatz の two-adic PetalBridge は、

```text id="rxzc89"
個別軌道の観察
```

から、

```text id="fgprrx"
有限 channel-flow framework
```

へ入った。

checkpoint No.100 では、新しい重い概念を足すより、この有限 channel-flow framework を締めるのが美しい。
そこまで閉じれば、次の章として「finite ratio layer」や「odd factor carrier layer」へ進める。

うむ。
No.100 は記念 checkpoint にふさわしいところまで来ておる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 8e3aefe9..51100469 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1307,6 +1307,79 @@ theorem orbitWindowResidueCountPow2_sum_eq_window
         _ = k + 1 := by
             rw [ih, pow2_residue_indicator_sum_eq_one]
 
+/--
+At any fixed power-of-two depth, the shifted-tail residue-cell occupation
+counts partition the whole shifted observation window.
+-/
+theorem orbitWindowResidueCountPow2Tail_sum_eq_window
+    (n : OddNat) (k depth : ℕ) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k := by
+  induction k with
+  | zero =>
+      simp [orbitWindowResidueCountPow2Tail]
+  | succ k ih =>
+      calc
+        (Finset.range (2 ^ depth)).sum
+            (fun residue => orbitWindowResidueCountPow2Tail n (k + 1) depth residue)
+            =
+          (Finset.range (2 ^ depth)).sum
+            (fun residue =>
+              orbitWindowResidueCountPow2Tail n k depth residue +
+                if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
+            apply Finset.sum_congr rfl
+            intro residue _
+            rw [orbitWindowResidueCountPow2Tail_succ]
+        _ =
+          (Finset.range (2 ^ depth)).sum
+              (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) +
+            (Finset.range (2 ^ depth)).sum
+              (fun residue =>
+                if oddOrbitLabel n (k + 1) % (2 ^ depth) = residue then (1 : ℕ) else 0) := by
+            rw [Finset.sum_add_distrib]
+        _ = k + 1 := by
+            rw [ih, pow2_residue_indicator_sum_eq_one]
+
+/--
+Lift a pointwise source-to-tail residue transition to an occupation-count
+inequality.
+
+This is the generic finite channel-flow helper: once each source residue hit
+inside the first `k` labels is known to land in a chosen shifted-tail residue
+cell, the source occupation count is bounded by the target tail occupation
+count.
+-/
+theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
+    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
+    (h :
+      ∀ i, i < k →
+        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
+          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
+    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
+      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue := by
+  induction k with
+  | zero =>
+      simp [orbitWindowResidueCountPow2, orbitWindowResidueCountPow2Tail]
+  | succ k ih =>
+      rw [orbitWindowResidueCountPow2_succ]
+      rw [orbitWindowResidueCountPow2Tail_succ]
+      have hprev :
+          ∀ i, i < k →
+            oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
+              oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue := by
+        intro i hi
+        exact h i (Nat.lt_trans hi (Nat.lt_succ_self k))
+      have ih' := ih hprev
+      by_cases hsource : oddOrbitLabel n k % (2 ^ sourceDepth) = sourceResidue
+      · have htail :
+            oddOrbitLabel n (k + 1) % (2 ^ targetDepth) = targetResidue :=
+          h k (Nat.lt_succ_self k) hsource
+        simp [hsource, htail, ih']
+      · by_cases htail : oddOrbitLabel n (k + 1) % (2 ^ targetDepth) = targetResidue
+        · exact by
+            simpa [hsource, htail] using Nat.le_succ_of_le ih'
+        · simpa [hsource, htail] using ih'
+
 /--
 The prefix mod `4` residue count is bounded by the prefix length.
 -/
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 4bcf1cd9..364ae48d 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -168,6 +168,8 @@ orbitWindowResidueCountPow2_depth_zero_eq_window
 orbitWindowResidueCountPow2_eq_zero_of_modulus_le_residue
 pow2_residue_indicator_sum_eq_one
 orbitWindowResidueCountPow2_sum_eq_window
+orbitWindowResidueCountPow2Tail_sum_eq_window
+orbitWindowResidueCountPow2_le_tail_of_pointwise
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -582,6 +584,13 @@ single-label residue indicator
 
 full pow-two source residue partition
   -> Sum_{residue < 2^depth} CountPow2 depth residue = k
+
+full pow-two shifted-tail residue partition
+  -> Sum_{residue < 2^depth} TailCountPow2 depth residue = k
+
+generic pointwise-to-count channel flow
+  -> if every source cell hit lands in a target tail cell,
+     then source CountPow2 <= target TailCountPow2
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-098.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-098.md
new file mode 100644
index 00000000..2ee1ba01
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-098.md
@@ -0,0 +1,158 @@
+# Report Petal 098: Tail Partition and Channel-Flow Helper
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-098.md`.
+
+The main target was the shifted-tail analogue of the generic power-of-two
+residue partition:
+
+```lean
+theorem orbitWindowResidueCountPow2Tail_sum_eq_window
+```
+
+The requested extra direction was the reusable pointwise-to-count bridge:
+
+```lean
+theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
+```
+
+Both targets are now implemented without adding `sorry`.
+
+## Implemented Lean Surface
+
+Added in `DkMath.Collatz.PetalBridge`:
+
+```lean
+theorem orbitWindowResidueCountPow2Tail_sum_eq_window
+    (n : OddNat) (k depth : Nat) :
+    (Finset.range (2 ^ depth)).sum
+      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k
+
+theorem orbitWindowResidueCountPow2_le_tail_of_pointwise
+    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : Nat)
+    (h :
+      ∀ i, i < k →
+        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
+          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
+    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
+      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue
+```
+
+The tail partition uses the same proof pattern as the source partition:
+
+```text
+tail successor formula
+single-label residue indicator sum
+induction on k
+```
+
+The generic helper abstracts the repeated proof shape:
+
+```text
+pointwise residue transition
+  -> count-level source <= shifted-tail target
+```
+
+## Mathematical Reading
+
+The bridge now has both finite distribution laws:
+
+```text
+source window:
+  Sum_{residue < 2^depth} CountPow2(depth, residue) = k
+
+shifted tail window:
+  Sum_{residue < 2^depth} TailCountPow2(depth, residue) = k
+```
+
+So the observation can be read as a finite channel-flow system:
+
+```text
+source residue distribution
+  -> pointwise transition law
+  -> tail residue distribution
+```
+
+This is still purely natural-valued.  No rational or real frequency layer is
+introduced yet.
+
+## Documentation Sync
+
+Updated:
+
+```text
+lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+```
+
+The status document now records:
+
+```text
+full pow-two shifted-tail residue partition
+generic pointwise-to-count channel flow
+```
+
+## Inference
+
+The helper is the important new reusable API.
+
+Previously, each count-level transition had to be proved by its own induction.
+Now the intended route is:
+
+```text
+prove a pointwise theorem:
+  if label i is in source cell A,
+  then label i+1 is in tail cell B
+
+apply:
+  orbitWindowResidueCountPow2_le_tail_of_pointwise
+
+obtain:
+  Count(source A) <= TailCount(target B)
+```
+
+This should allow future recovery / continuation / retention channel theorems
+to be stated as thin corollaries of pointwise residue lemmas.
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
+The next practical step is to re-express existing count transition theorems via
+the generic helper:
+
+```lean
+orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
+orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
+```
+
+These can become short applications of:
+
+```lean
+orbitWindowResidueCountPow2_le_tail_of_pointwise
+```
+
+with pointwise inputs:
+
+```lean
+oddOrbitLabel_succ_recovery_residue_of_mod
+oddOrbitLabel_succ_continuation_residue_of_mod
+```
+
+After that refactor, similar future channel-flow lemmas should only need a
+pointwise transition theorem plus one helper application.
````
`````

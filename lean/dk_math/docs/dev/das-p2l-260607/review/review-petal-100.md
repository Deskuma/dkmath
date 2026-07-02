# Git diff / Report / Review

## Upd: Collatz.PetalBridge

gch: 0c1fa26d87f11449bd1b4a27b9f70b9ba8cd0d49

## Report

099 完了です。

`DkMath.Collatz.PetalBridge` に、helper route を明示する薄い corollary を追加しました。

```lean
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
```

あわせて `mod 8` 層の sanity theorem も追加しています。

```lean
orbitWindowResidueCountPow2_depth_three_sum_eq_window
orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
```

これで既存の recursive two-adic Petal count theorem が、

```text
pointwise transition
  -> orbitWindowResidueCountPow2_le_tail_of_pointwise
  -> count-level channel flow
```

という経路で再接続されました。

更新・作成:

- `lean/dk_math/DkMath/Collatz/PetalBridge.lean`
- `lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md`
- `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-099.md`

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

No.100 は、新規拡張よりも finite channel-flow layer の総括 checkpoint にするのがよさそうです。そこから Nat inequality ベースの ratio layer へ進めます。

## Review

## 1. 状況分析

うむ。これは **checkpoint 100 直前の締め作業として、かなり理想的** じゃ。

今回の checkpoint `099` では、新しい大きな方向へ飛ばずに、前回できた `pointwise-to-count helper` を正式な推奨経路として再接続した。

つまり、これまで直接 induction で証明していた recursive two-adic Petal の count theorem を、

```text id="wzp09x"
pointwise transition
  -> orbitWindowResidueCountPow2_le_tail_of_pointwise
  -> count-level channel flow
```

という経路で薄い corollary にした。レポートでも、今回の目的は既存の recursive two-adic Petal count theorem を generic helper に接続し、finite channel-flow の theorem chain を文書化することだと整理されている。

これは、新規拡張というより、**体系化** じゃ。
No.100 の前にやるべき整理として、とてもよい。

## 2. 今回の核心

追加された Lean theorem はこの四つ。

```lean id="t3ii4a"
orbitWindowResidueCountPow2_depth_three_sum_eq_window
orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
```

前半二つは `mod 8` 層の sanity check。

```text id="nbua1p"
source depth 3:
  Sum_{residue < 8} CountPow2 residue = k

tail depth 3:
  Sum_{residue < 8} TailCountPow2 residue = k
```

後半二つは、helper route の固定。

```text id="hi2q1c"
recovery source
  -> outward-retention tail

continuation source
  -> next-retention tail
```

しかも、どちらも `orbitWindowResidueCountPow2_le_tail_of_pointwise` に pointwise theorem を渡すだけの形になった。

これは、今後の拡張方針を決定づける補題じゃ。

## 3. レビュー

## 3.1. `via_helper` は冗長ではなく、設計宣言

既存 theorem と同じ statement を持つ `via_helper` theorem を置くのは、一見すると重複に見える。

しかし、これは良い重複じゃ。

理由は、今後の推奨 proof route を Lean 上に記録しているから。

```text id="e8so1a"
古い route:
  count theorem ごとに induction

新しい route:
  pointwise theorem
    -> generic helper
    -> count theorem
```

この「新しい route」を定理として明示したのが今回の価値。

No.100 以降で新しい channel-flow lemma を追加するとき、もう count induction を増やさなくてよい。

## 3.2. depth 3 sanity は読みやすい橋

generic theorem は強いが、読者にとっては少し抽象的。

そこで、

```lean id="j8mdx8"
orbitWindowResidueCountPow2_depth_three_sum_eq_window
orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
```

を置いたのは良い。

`depth = 3` は `mod 8`。
Collatz の exact height-one channel `7 mod 8` と直結する。

つまり、既存の concrete `mod 8` 実験と、generic `2^depth` distribution API の橋になっている。

## 3.3. docs の finite channel-flow chain が重要

今回 docs に入った chain は、ほぼ No.100 の骨子そのもの。

```text id="hp3044"
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

Recursive two-adic Petal instances:
  recovery source <= outward-retention tail
  continuation source <= next-retention tail
```

これは非常に良い。
ここまで来ると、Collatz.PetalBridge は「補題が増えた」ではなく、**有限流量系の API ができた** と言える。

## 4. 数学的な意味

今回の checkpoint で、Collatz の two-adic Petal は次の段階へ入った。

```text id="va1we9"
座標 cell を定義する

各 cell への occupation を数える

source / tail の総量保存を証明する

pointwise transition を channel-flow に持ち上げる
```

これは、有限窓の中では完全な分布論じゃ。

まだ極限も確率も使っていない。
にもかかわらず、

```text id="rn7ph3"
どの residue channel にどれだけ質量があるか

その質量が次窓のどこへ押し出されるか
```

を Nat の不等式だけで扱える。

DkMath 的には、これはかなり堅い。

## 5. checkpoint No.100 の位置づけ

No.100 は、無理に新しい重い theorem を入れるより、**finite channel-flow layer の総括 checkpoint** にするのがよい。

理由は三つ。

```text id="fdhbr8"
1. source/tail partition が揃った

2. pointwise-to-count helper が揃った

3. recursive two-adic Petal channel が helper route に再接続された
```

つまり、一区切りとして十分。

No.100 で新しい因子層や ratio 層へ一気に進むと、締めというより新章開始になってしまう。
キリ番としては、ここまでの整理・命名・文書化・薄い theorem alias が美しい。

## 6. 次の指示：No.100 は総括 checkpoint にする

次は、新しい重い数学を足すより、**finite channel-flow layer の theorem chain を明文化する** のが良い。

Lean 側で追加するなら、薄い theorem / alias を少しだけ。

## 6.1. source conservation alias

```lean id="kvw4ll"
theorem sourcePow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k :=
  orbitWindowResidueCountPow2_sum_eq_window n k depth
```

## 6.2. tail conservation alias

```lean id="mv29pn"
theorem tailPow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k :=
  orbitWindowResidueCountPow2Tail_sum_eq_window n k depth
```

## 6.3. channel-flow alias

```lean id="bvom4f"
theorem pow2ChannelFlow_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue :=
  orbitWindowResidueCountPow2_le_tail_of_pointwise
    n k sourceDepth sourceResidue targetDepth targetResidue h
```

これは theorem 名を抽象概念に寄せるための alias。
内部実装は既存補題に任せるだけでよい。

## 7. 一歩先ゆく推論

No.100 の後に進むべき方向は、やはり **finite ratio layer** じゃ。

ただし、まだ \(\mathbb{Q}\) や \(\mathbb{R}\) は入れないほうがよい。

理由は、`k = 0` の扱いや coercion が増え、現在の軽い Nat 層が重くなるから。

まずは Nat inequality で「割合」を表す。

たとえば、

```text id="lgx1vs"
cell A が半分以下:
  2 * countA <= k

cell A と cell B が全体以下:
  countA + countB <= k

cell A が少なくとも m 回:
  m <= countA
```

この形なら、finite count / partition / channel-flow と相性が良い。

つまり、No.101 以降は、

```text id="gunya8"
FiniteRatioWitness
```

という Nat 不等式層に入るのが自然。

## 8. 次のさらに一手：retention mass の定義

No.100 後の最初の実験としては、`RetentionMass` を置くと良い。

```lean id="c9scn5"
noncomputable def orbitWindowRetentionMassPow2
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2 n k r (2 ^ r - 1)
```

これは、

```text id="ditx9q"
depth r の retention cell への occupation count
```

を表す。

tail 版も。

```lean id="p6kgsv"
noncomputable def orbitWindowRetentionMassPow2Tail
    (n : OddNat) (k r : ℕ) : ℕ :=
  orbitWindowResidueCountPow2Tail n k r (2 ^ r - 1)
```

これがあると、narrowing cylinder の量を名前付きで追える。

ただし、これは No.100 の後でよい。
No.100 は総括、No.101 以降で ratio / retention mass。

## 9. 奇素因子層はまだ次章

ぬしの言う「新しい素数因子」の話は、かなり面白い。
だが、今はまだ two-adic channel-flow を締めるべきところじゃ。

順序としては、

```text id="yc60qp"
1. finite channel-flow layer を総括

2. Nat inequality ratio layer

3. retention mass / recovery mass の比較

4. odd factor carrier layer
```

が自然。

奇素因子層に入るなら、その時は

```text id="vlojyc"
same two-adic cell にいる label 群の中で、
nextOdd に新しい奇素因子が出るか
```

を見る。
これは次章の主題にできる。

## 10. 賢狼が試して欲しい実験補題

## 実験 A: source distribution alias

```lean id="o7l00u"
theorem sourcePow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2 n k depth residue) = k :=
  orbitWindowResidueCountPow2_sum_eq_window n k depth
```

## 実験 B: tail distribution alias

```lean id="es7rw3"
theorem tailPow2Distribution_total
    (n : OddNat) (k depth : ℕ) :
    (Finset.range (2 ^ depth)).sum
      (fun residue => orbitWindowResidueCountPow2Tail n k depth residue) = k :=
  orbitWindowResidueCountPow2Tail_sum_eq_window n k depth
```

## 実験 C: channel-flow alias

```lean id="otiu24"
theorem pow2ChannelFlow_of_pointwise
    (n : OddNat) (k sourceDepth sourceResidue targetDepth targetResidue : ℕ)
    (h :
      ∀ i, i < k →
        oddOrbitLabel n i % (2 ^ sourceDepth) = sourceResidue →
          oddOrbitLabel n (i + 1) % (2 ^ targetDepth) = targetResidue) :
    orbitWindowResidueCountPow2 n k sourceDepth sourceResidue ≤
      orbitWindowResidueCountPow2Tail n k targetDepth targetResidue :=
  orbitWindowResidueCountPow2_le_tail_of_pointwise
    n k sourceDepth sourceResidue targetDepth targetResidue h
```

## 実験 D: finite ratio witness docs

docs-only でよい。

```text id="wuppgi"
FiniteRatioWitness:
  Nat inequality form of finite frequency.

Examples:
  2 * count <= k
  countA + countB <= k
  m <= count

Reason:
  avoids division by zero and coercion overhead.
```

## 実験 E: retention mass docs or light def

docs-only なら、

```text id="zhsjbr"
RetentionMass(depth r):
  CountPow2 r (2^r - 1)

RecoverySiblingMass(depth r):
  CountPow2 (r+1) (2^r - 1)

ContinuationSiblingMass(depth r):
  CountPow2 (r+1) (2^(r+1) - 1)
```

Lean に入れるなら後回しでもよい。

## 11. checkpoint No.100 の推奨内容

```text id="sv7fz4"
1. sourcePow2Distribution_total

2. tailPow2Distribution_total

3. pow2ChannelFlow_of_pointwise

4. docs:
   Finite Channel-Flow Layer summary

5. docs:
   theorem chain:
     residue arithmetic
     orbit-label transition
     source/tail distribution
     channel-flow helper
     recursive Petal instances

6. docs:
   next phase:
     Nat inequality finite ratio layer
     later odd factor carrier layer
```

これで No.100 はかなり美しく締まる。

## 12. 総括

今回の checkpoint `099` は、No.100 に向けて非常に良い「整流」じゃ。

いま Collatz.PetalBridge は、

```text id="gm7f5f"
source distribution
tail distribution
channel-flow helper
recursive two-adic Petal channel
```

までそろった。

つまり、有限窓の中で、

```text id="nm45xf"
どの座標に何回いたか
それが次の窓でどこへ流れたか
```

を扱える。

これは区切りとして非常に強い。

No.100 は新章突入ではなく、ここまでの finite channel-flow framework を総括する checkpoint にするのがよい。
その次に、Nat inequality ratio layer、retention mass、そして odd factor carrier へ進む。

うむ。
これはキリ番にふさわしい流れじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge.lean b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
index 51100469..3422dabf 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge.lean
@@ -1340,6 +1340,29 @@ theorem orbitWindowResidueCountPow2Tail_sum_eq_window
         _ = k + 1 := by
             rw [ih, pow2_residue_indicator_sum_eq_one]
 
+/--
+Depth-`3` source distribution sanity check.
+
+This is the `mod 8` instance of the generic power-of-two source partition.
+-/
+theorem orbitWindowResidueCountPow2_depth_three_sum_eq_window
+    (n : OddNat) (k : ℕ) :
+    (Finset.range 8).sum
+      (fun residue => orbitWindowResidueCountPow2 n k 3 residue) = k := by
+  simpa using orbitWindowResidueCountPow2_sum_eq_window n k 3
+
+/--
+Depth-`3` shifted-tail distribution sanity check.
+
+This is the `mod 8` instance of the generic power-of-two shifted-tail
+partition.
+-/
+theorem orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
+    (n : OddNat) (k : ℕ) :
+    (Finset.range 8).sum
+      (fun residue => orbitWindowResidueCountPow2Tail n k 3 residue) = k := by
+  simpa using orbitWindowResidueCountPow2Tail_sum_eq_window n k 3
+
 /--
 Lift a pointwise source-to-tail residue transition to an occupation-count
 inequality.
@@ -2296,6 +2319,23 @@ theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
             simpa [hsource, htail] using Nat.le_succ_of_le ih
         · simp [hsource, htail, ih]
 
+/--
+Helper-routed version of the recovery sibling count transition.
+
+This theorem has the same statement as
+`orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount`, but it records
+the preferred finite channel-flow route:
+
+`pointwise residue transition -> count-level source <= shifted-tail target`.
+-/
+theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
+    (r : ℕ) (hr : 2 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1) := by
+  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
+  intro i _hi hsource
+  exact oddOrbitLabel_succ_recovery_residue_of_mod r hr n i hsource
+
 /--
 Count-level recursive Petal transition for the continuation sibling.
 
@@ -2329,6 +2369,23 @@ theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
             simpa [hsource, htail] using Nat.le_succ_of_le ih
         · simp [hsource, htail, ih]
 
+/--
+Helper-routed version of the continuation sibling count transition.
+
+This theorem has the same statement as
+`orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount`, but it
+records the preferred finite channel-flow route:
+
+`pointwise residue transition -> count-level source <= shifted-tail target`.
+-/
+theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
+    (r : ℕ) (hr : 1 ≤ r) (n : OddNat) (k : ℕ) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1) := by
+  apply orbitWindowResidueCountPow2_le_tail_of_pointwise
+  intro i _hi hsource
+  exact oddOrbitLabel_succ_continuation_residue_of_mod r hr n i hsource
+
 /--
 Every `7 mod 8` source label contributes a shifted-tail entry with exact
 height `1`.
diff --git a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
index 364ae48d..4ed08523 100644
--- a/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
+++ b/lean/dk_math/DkMath/Collatz/docs/Collatz-PetalBridge-Status.md
@@ -170,6 +170,8 @@ pow2_residue_indicator_sum_eq_one
 orbitWindowResidueCountPow2_sum_eq_window
 orbitWindowResidueCountPow2Tail_sum_eq_window
 orbitWindowResidueCountPow2_le_tail_of_pointwise
+orbitWindowResidueCountPow2_depth_three_sum_eq_window
+orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
 orbitWindowPrefixResidueCountMod4EqOne_le_prefix
 orbitWindowPrefixResidueCountMod4EqOne_eq_residueCount
 orbitWindowHeightCountGe_two_eq_residueCount_mod4_eq_one
@@ -244,6 +246,8 @@ orbitWindowResidueCountMod8EqThree_le_tailHeightCountGe_two
 residueCountMod8EqSeven_le_nextResidueCountMod4EqThree
 orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount
 orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount
+orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
+orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
 orbitWindowResidueCountMod8EqSeven_le_tailHeightCountEq_one
 orbitWindowResidueCountMod8EqThree_add_seven_le_tail_partition
 orbitWindowHeightCountGeTail_le_countGe_succ
@@ -591,6 +595,16 @@ full pow-two shifted-tail residue partition
 generic pointwise-to-count channel flow
   -> if every source cell hit lands in a target tail cell,
      then source CountPow2 <= target TailCountPow2
+
+depth `3` source distribution sanity
+  -> Sum_{residue < 8} CountPow2 depth 3 residue = k
+
+depth `3` shifted-tail distribution sanity
+  -> Sum_{residue < 8} TailCountPow2 depth 3 residue = k
+
+helper-routed recursive two-adic Petal channels
+  -> recovery source <= outward-retention tail
+  -> continuation source <= next-retention tail
 ```
 
 This is the first distribution layer.  It still avoids importing the heavier
@@ -610,6 +624,40 @@ current API local and elementary because the data here is just a finite ordered
 list of natural 2-adic heights.  This avoids pulling the ABC analytic stack into
 the observation-window layer before a real carrier/radical bridge exists.
 
+The finite channel-flow layer is now visible as a theorem chain:
+
+```text
+SourceDistribution:
+  CountPow2 over labels 0..k-1
+
+TailDistribution:
+  TailCountPow2 over labels 1..k
+
+Conservation:
+  total source mass = k
+  total tail mass = k
+
+ChannelFlow:
+  pointwise source-to-tail transition
+    -> source occupation <= tail occupation
+
+Recursive two-adic Petal instances:
+  recovery source <= outward-retention tail
+  continuation source <= next-retention tail
+```
+
+The next ratio layer should initially stay in `Nat` inequalities rather than
+introducing `ℚ` or `ℝ` frequencies:
+
+```text
+FiniteRatioWitness:
+  use inequalities such as 2 * count <= k
+  instead of count / k at first
+
+Reason:
+  avoids zero-window division and coercion overhead
+```
+
 The Collatz-specific floor is now also fixed:
 
 ```text
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-099.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-099.md
new file mode 100644
index 00000000..6479868f
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-099.md
@@ -0,0 +1,181 @@
+# Report Petal 099: Helper-Routed Recursive Channel Flow
+
+## Checkpoint
+
+This checkpoint follows `__next_implementation-099.md`.
+
+The main goal was to connect the existing recursive two-adic Petal count
+theorems to the generic pointwise-to-count helper introduced in checkpoint 098.
+
+The checkpoint also requested depth-`3` source/tail distribution sanity
+theorems and documentation for the finite channel-flow layer.
+
+## Implemented Lean Surface
+
+Added in `DkMath.Collatz.PetalBridge`:
+
+```lean
+theorem orbitWindowResidueCountPow2_depth_three_sum_eq_window
+    (n : OddNat) (k : Nat) :
+    (Finset.range 8).sum
+      (fun residue => orbitWindowResidueCountPow2 n k 3 residue) = k
+
+theorem orbitWindowResidueCountPow2Tail_depth_three_sum_eq_window
+    (n : OddNat) (k : Nat) :
+    (Finset.range 8).sum
+      (fun residue => orbitWindowResidueCountPow2Tail n k 3 residue) = k
+
+theorem orbitWindowRecoverySiblingCount_le_tailRetentionResidueCount_via_helper
+    (r : Nat) (hr : 2 ≤ r) (n : OddNat) (k : Nat) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 1) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ r - 1)
+
+theorem orbitWindowContinuationSiblingCount_le_tailRetentionResidueCount_via_helper
+    (r : Nat) (hr : 1 ≤ r) (n : OddNat) (k : Nat) :
+    orbitWindowResidueCountPow2 n k (r + 2) (2 ^ (r + 2) - 1) ≤
+      orbitWindowResidueCountPow2Tail n k (r + 1) (2 ^ (r + 1) - 1)
+```
+
+The two `via_helper` theorems have the same statements as the existing
+recursive count transitions, but their proofs now pass through:
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
+## Mathematical Reading
+
+The helper route fixes the intended finite channel-flow pattern:
+
+```text
+pointwise source residue transition
+  -> source occupation count <= shifted-tail target occupation count
+```
+
+The recursive two-adic Petal channels are now instances of this generic route:
+
+```text
+recovery source
+  -> outward-retention tail
+
+continuation source
+  -> next-retention tail
+```
+
+This matters because future residue-channel theorems no longer need custom
+count inductions.  They only need a pointwise transition theorem.
+
+## Depth-3 Sanity
+
+The depth-`3` theorems pin down the generic distribution theorem at the familiar
+`mod 8` layer:
+
+```text
+Sum_{residue < 8} sourceCount(residue) = k
+Sum_{residue < 8} tailCount(residue) = k
+```
+
+This gives a readable bridge from named `mod 8` experiments back to the generic
+`2^depth` distribution API.
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
+depth 3 source/tail distribution sanity
+helper-routed recovery and continuation channels
+finite channel-flow theorem chain
+future Nat-inequality ratio layer note
+```
+
+## Inference
+
+Checkpoint 099 turns the helper from an isolated theorem into the preferred
+proof route.
+
+The current layer can be summarized as:
+
+```text
+SourceDistribution:
+  CountPow2 over labels 0..k-1
+
+TailDistribution:
+  TailCountPow2 over labels 1..k
+
+Conservation:
+  total source mass = k
+  total tail mass = k
+
+ChannelFlow:
+  pointwise source-to-tail transition
+    -> source occupation <= tail occupation
+
+Recursive instances:
+  recovery source <= outward-retention tail
+  continuation source <= next-retention tail
+```
+
+This is a clean checkpoint before No.100.
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
+Checkpoint 100 should probably be a consolidation checkpoint rather than a wide
+new theorem expansion.
+
+Recommended next work:
+
+```text
+1. Add a short docs/report summary for the finite channel-flow layer.
+
+2. Optionally add very thin theorem aliases for the four-part chain:
+   source partition
+   tail partition
+   pointwise-to-count helper
+   recovery/continuation via-helper instances
+
+3. Start the finite ratio layer only with Nat inequalities.
+```
+
+The first ratio experiments should avoid `ℚ` and `ℝ`:
+
+```text
+cell occupies at most half the window
+  as 2 * count <= k
+
+two channels occupy at most the window
+  as countA + countB <= k
+```
+
+This keeps the next layer compatible with zero-window edge cases and avoids
+coercion overhead.
````
`````

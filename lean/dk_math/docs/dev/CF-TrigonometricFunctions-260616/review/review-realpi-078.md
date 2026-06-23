# Git diff / Report / Review

## Add: Analysis.DkReal.SemanticCF2DDyadic

gch: 5fd06ddd6df2918d82dd5f2b2acccd1eabebd28d

## Report

finite dyadic refinement 層を実装しました。

- `SemanticCF2DDyadic.lean` を新設
- dyadic 節点の端点・範囲・反射則
- even child の親節点一致
- odd child の中点則
- reflected node の `phaseDepth` 一致
- 公開入口・TODO・研究資料・履歴を同期

`lake build DkMath.Analysis` 成功（8290 jobs）、`git diff --check` も成功です。

## Review

うむ。これは良い。
今回の checkpoint は、**内在的 \(\pi\) ルートへ入る前の、有限 refinement の地面作り**としてかなり正しい。

これで、外部 Euclidean 解釈ルートはすでに

```text id="skacwh"
semantic action
  -> rotation (Real.pi / 2)
```

まで握手済み。

そして今回から、内側へ戻って、

```text id="uc7u05"
phaseDepth
dyadic nodes
reflection
subdivision
finite refinement
```

を積み始めた、という段階じゃ。

## 状況解説

今回新設されたのは、

```lean id="is6fya"
DkMath.Analysis.DkReal.SemanticCF2DDyadic
```

じゃな。

ここでは、一区間の phase parameter \(t\) を dyadic 節点で刻む。

$$
t_{n,k}=\frac{k}{2^n}
$$

Lean 側では、

```lean id="wbwjyt"
def dyadicPhaseDenom (n : ℕ) : ℕ :=
  2 ^ n

def dyadicPhaseNode (n k : ℕ) : ℝ :=
  (k : ℝ) / (dyadicPhaseDenom n : ℝ)
```

としている。

これはとても自然。
まだ補正積も、log 和も、Gaussian も出していない。
まず有限節点の combinatorics だけを閉じている。

この順序が良い。

## 今回閉じた定理群

実装された定理は、refinement の基礎として必要なものがきれいに揃っている。

```lean id="h1ewl6"
dyadicPhaseDenom_pos
dyadicPhaseNode_zero
dyadicPhaseNode_last
dyadicPhaseNode_mem_unitInterval
dyadicPhaseNode_reflect
dyadicPhaseNode_child_even
dyadicPhaseNode_child_odd_mid
phaseDepth_dyadic_reflect
```

意味としてはこうじゃ。

```text id="b9xxks"
端点:
  k = 0 なら t = 0
  k = 2^n なら t = 1

範囲:
  0 ≤ k ≤ 2^n なら t ∈ [0,1]

反射:
  2^n - k は 1 - t に対応する

親子:
  level n+1 の even child は level n の親と一致する
  level n+1 の odd child は隣接親節点の中点になる

観測量:
  reflected node では phaseDepth が一致する
```

これはまさに、有限 dyadic refinement の骨格じゃ。

## 一番良い点

一番良いのは、

```text id="xf4n68"
Gaussian をまだ言わない
```

ことじゃ。

この段階で、

```text id="wgsdp5"
無限積になるはず
log 和になるはず
Gaussian になるはず
```

と決め打ちすると危ない。

いま証明したのは有限節点の構造だけ。
この構造から、どの局所補正量が自然に合成されるのかを次に見る。

つまり、今回の層は、

```text id="ck2aq3"
refinement law の前段
```

じゃ。

これは正しい分割。

## phaseDepth との接続

今回の

```lean id="5au7m4"
phaseDepth_dyadic_reflect
```

は小さく見えて重要じゃ。

もともと

$$
\operatorname{phaseDepth}(1-t)=\operatorname{phaseDepth}(t)
$$

があった。
これを dyadic node 上に落とすと、

$$
\operatorname{phaseDepth}(t_{n,2^n-k}) = \operatorname{phaseDepth}(t_{n,k})
$$

になる。

これは、有限節点上で左右対称性が保存されることを意味する。

DkMath 的には、

```text id="h9b6fd"
くぼみの左右対称性が、有限 refinement mesh 上でも壊れない
```

ということじゃ。

この定理は後で、総補正量を半分だけ見ればよい、あるいは中心からの距離だけで整理できる、という方向に効くはず。

## even child / odd child の価値

この二つもかなり大事。

```lean id="kqrvbi"
dyadicPhaseNode_child_even
```

は、

$$
t_{n+1,2k}=t_{n,k}
$$

を言っている。

これは、細分化しても既存節点が残る、ということ。

```lean id="6g3ss2"
dyadicPhaseNode_child_odd_mid
```

は、

$$
t_{n+1,2k+1} = \frac{t_{n,k}+t_{n,k+1}}{2}
$$

を言っている。

これは、新しく追加される節点が、親区間の中点であること。

つまり refinement の一段階は、

```text id="zvofy0"
既存節点を保つ
隣接節点の中点を追加する
```

として形式化された。

これで、次に local correction を定義するとき、

```text id="bpml1b"
親区間の correction
子2区間の correction
```

を比較できる。

## 次の本丸：composition law

次は、資料にもある通り、

```text id="zr8w0g"
local boundary correction の合成則
```

じゃ。

候補となる量はいくつかある。

まず、

$$
\operatorname{phaseDepth}(t)
$$

これは境界からの沈み込み率。

次に、

$$
\operatorname{phaseNormalization}(t) = \frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}
$$

これは境界へ戻す補正率。

さらに、log を取れば、

$$
\log(\operatorname{phaseNormalization}(t))
$$

あるいは、

$$
-\frac12\log(\operatorname{phaseDepth}(t))
$$

が加法的に扱える可能性がある。

ただし、ここはまだ決めないのが正しい。
まず有限親子関係で、どの量が自然に合成されるかを theorem として見るべきじゃ。

## 次の実装候補

次のファイルは同じ `SemanticCF2DDyadic.lean` に足してもよいし、膨らむなら別ファイルにしてもよい。

候補名は、

```text id="lmqqye"
SemanticCF2DRefinement
```

最初に定義するなら、こういうものが自然じゃ。

```lean id="6hy3mk"
def dyadicPhaseDepth (n k : ℕ) : ℝ :=
  phaseDepth (dyadicPhaseNode n k)

def dyadicPhaseNormalization (n k : ℕ) : ℝ :=
  phaseNormalization (dyadicPhaseNode n k)
```

最初の定理候補は、

```lean id="njit7d"
dyadicPhaseDepth_reflect
dyadicPhaseDepth_child_even
dyadicPhaseNormalization_reflect
dyadicPhaseNormalization_child_even
```

あたり。

`child_odd_mid` については、`phaseDepth` が二次式なので、親子 midpoint でかなり具体的な式が出せる可能性がある。

## 重要な注意点

`dyadicPhaseNode_child_odd_mid` は全ての `k` に対して成り立つ形になっている。
式としては正しいが、節点として意味を持つ範囲は通常

```text id="9uyvmb"
k < 2^n
```

じゃ。

今後、隣接 parent pair として扱うなら、`k + 1 ≤ dyadicPhaseDenom n` が必要になる。

つまり次の段階では、範囲付き theorem も欲しくなる。

```lean id="19718b"
dyadicPhaseNode_child_odd_mid_of_lt
```

というより、既存 theorem はそのままでよいが、使う側で

```lean id="qv7vbw"
hk : k < dyadicPhaseDenom n
```

を持つ設計にするのがよい。

特に `Fin (dyadicPhaseDenom n + 1)` で node index を持つか、`Nat` と bound proof を持つかは、次の設計ポイントじゃ。

## Fin 化するか Nat のまま行くか

現段階では `Nat` で良い。
定理が軽い。

ただし、総積や総和を定義するなら、いずれ `Finset.range` を使う。

たとえば節点は、

```lean id="6igya5"
Finset.range (dyadicPhaseDenom n + 1)
```

区間 cell は、

```lean id="r1xmnq"
Finset.range (dyadicPhaseDenom n)
```

で扱うのが自然。

節点と cell を分けるのが大事じゃ。

```text id="md2vj7"
nodes:
  k = 0 ... 2^n

cells:
  k = 0 ... 2^n - 1
  interval [t_{n,k}, t_{n,k+1}]
```

ここを混ぜると、端点処理で苦労する。

## 次の成功条件

次 checkpoint は、こう切るのが良い。

```text id="8b47se"
finite dyadic cells
```

節点だけでなく、隣接区間を定義する。

```lean id="x5kqxs"
def dyadicPhaseCellLeft (n k : ℕ) : ℝ :=
  dyadicPhaseNode n k

def dyadicPhaseCellRight (n k : ℕ) : ℝ :=
  dyadicPhaseNode n (k + 1)
```

範囲条件は、

```lean id="9vg8sy"
hk : k < dyadicPhaseDenom n
```

そして、

```text id="a1h10w"
left ∈ [0,1]
right ∈ [0,1]
left ≤ right
midpoint = odd child
left = even child
right = next even child
```

を閉じる。

これで「親 cell が二つの child cell に分かれる」が言える。

## 総評

今回の更新はとても堅い。

一言で言えば、

```text id="vzgcu1"
内在的 π への道を、有限 dyadic refinement の節点構造から開始した。
```

そして、

```text id="hdfffx"
無限積
logarithmic sum
Gaussian limit
```

をまだ導入していないのが良い。

いま証明されたのは、有限の端点、反射、親子分割、phaseDepth 対称性。
これは次の refinement law のための、必要最小限で正しい地面じゃ。

## 最終評価

ここまでの流れは非常に美しい。

```text id="s3kewn"
外部解釈ルート:
  DkMath semantic action = rotation (Real.pi / 2)

内在導出ルート:
  dyadic nodes から有限 refinement を開始
```

外では \(\pi/2\) と握手した。
内ではまだ \(\pi\) を仮定せず、くぼみの有限分割から掘り始める。

この二重構造が強い。

次は節点から cell へ。
その次に cell correction へ。
そして初めて finite composition law じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis.lean b/lean/dk_math/DkMath/Analysis.lean
index 0bd34133..7b1fa6d2 100644
--- a/lean/dk_math/DkMath/Analysis.lean
+++ b/lean/dk_math/DkMath/Analysis.lean
@@ -14,6 +14,7 @@ import DkMath.Analysis.TaylorBridge
 import DkMath.Analysis.DkReal
 import DkMath.Analysis.DkReal.SemanticCF2D
 import DkMath.Analysis.DkReal.SemanticCF2DPhase
+import DkMath.Analysis.DkReal.SemanticCF2DDyadic
 import DkMath.Analysis.DkReal.SemanticCF2DPath
 import DkMath.Analysis.DkReal.SemanticCF2DNormalize
 import DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 4a7e9d6c..aa8167f7 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -99,6 +99,11 @@ fixed `q2` boundary by the exact factor
 of one half, and reflection about the midpoint proves the first continuous
 half-fold symmetry without introducing circles or angles.
 
+[IMPLEMENTED: semantic-cf2d-dyadic] `DkReal.SemanticCF2DDyadic` samples one
+phase at the finite nodes `k / 2^n`. Endpoint, unit-interval, reflection,
+even-child, odd-child midpoint, and reflected phase-depth laws are proved
+without selecting a correction product or taking a limit.
+
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
 affine edge as a Mathlib `Path`. Four seam-compatible edges concatenate to a
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
new file mode 100644
index 00000000..30ca097b
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DDyadic.lean
@@ -0,0 +1,101 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+import DkMath.Analysis.DkReal.SemanticCF2DPhase
+
+#print "file: DkMath.Analysis.DkReal.SemanticCF2DDyadic"
+
+/-!
+# Finite dyadic refinement of one semantic phase
+
+This module introduces only the finite combinatorics required before any
+refinement limit is considered. At level `n`, the phase interval is sampled
+at
+
+`dyadicPhaseNode n k = k / 2^n`.
+
+The endpoint, reflection, and parent-child laws are exact algebraic
+identities. No infinite product, logarithmic correction, Gaussian weight, or
+identification with `pi` is assumed here.
+-/
+
+namespace DkMath.Analysis.DkNNRealQ
+
+noncomputable section
+
+/-- The number of equal subintervals in the `n`th dyadic phase partition. -/
+def dyadicPhaseDenom (n : ℕ) : ℕ :=
+  2 ^ n
+
+/-- The `k`th real node of the `n`th dyadic phase partition. -/
+def dyadicPhaseNode (n k : ℕ) : ℝ :=
+  (k : ℝ) / (dyadicPhaseDenom n : ℝ)
+
+/-- Every dyadic phase denominator is strictly positive. -/
+theorem dyadicPhaseDenom_pos (n : ℕ) :
+    0 < dyadicPhaseDenom n := by
+  simp [dyadicPhaseDenom]
+
+/-- The first node of every dyadic partition is the phase origin. -/
+@[simp]
+theorem dyadicPhaseNode_zero (n : ℕ) :
+    dyadicPhaseNode n 0 = 0 := by
+  simp [dyadicPhaseNode]
+
+/-- The last node of every dyadic partition is the phase endpoint. -/
+@[simp]
+theorem dyadicPhaseNode_last (n : ℕ) :
+    dyadicPhaseNode n (dyadicPhaseDenom n) = 1 := by
+  simp [dyadicPhaseNode, dyadicPhaseDenom]
+
+/-- Every indexed partition node lies in the closed phase interval. -/
+theorem dyadicPhaseNode_mem_unitInterval
+    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
+    dyadicPhaseNode n k ∈ Set.Icc (0 : ℝ) 1 := by
+  constructor
+  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
+  · apply (div_le_one (by exact_mod_cast dyadicPhaseDenom_pos n)).2
+    exact_mod_cast hk
+
+/--
+Complementary node indices are reflected about the phase midpoint.
+
+The bound ensures that natural subtraction represents the intended
+complement rather than truncated subtraction.
+-/
+theorem dyadicPhaseNode_reflect
+    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
+    dyadicPhaseNode n (dyadicPhaseDenom n - k) =
+      1 - dyadicPhaseNode n k := by
+  rw [dyadicPhaseNode, dyadicPhaseNode, Nat.cast_sub hk]
+  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
+    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
+  field_simp
+
+/-- Every even child node is exactly its parent node. -/
+@[simp]
+theorem dyadicPhaseNode_child_even (n k : ℕ) :
+    dyadicPhaseNode (n + 1) (2 * k) = dyadicPhaseNode n k := by
+  simp [dyadicPhaseNode, dyadicPhaseDenom, pow_succ]
+  ring
+
+/-- Every odd child node is the midpoint of two adjacent parent nodes. -/
+theorem dyadicPhaseNode_child_odd_mid (n k : ℕ) :
+    dyadicPhaseNode (n + 1) (2 * k + 1) =
+      (dyadicPhaseNode n k + dyadicPhaseNode n (k + 1)) / 2 := by
+  simp [dyadicPhaseNode, dyadicPhaseDenom, pow_succ]
+  ring
+
+/-- The exact phase-depth observation agrees at complementary dyadic nodes. -/
+theorem phaseDepth_dyadic_reflect
+    {n k : ℕ} (hk : k ≤ dyadicPhaseDenom n) :
+    phaseDepth (dyadicPhaseNode n (dyadicPhaseDenom n - k)) =
+      phaseDepth (dyadicPhaseNode n k) := by
+  rw [dyadicPhaseNode_reflect hk, phaseDepth_one_sub]
+
+end
+
+end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 204a8b0c..90557e2f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -135,6 +135,13 @@ their reflection symmetry, and a theorem stating how one subdivision level
 refines the preceding level. No infinite product or Gaussian claim belongs
 in that checkpoint.
 
+This finite checkpoint is now implemented in `SemanticCF2DDyadic.lean`.
+Even child indices recover their parent nodes exactly, while odd child
+indices are the midpoints of adjacent parents. Complementary indices produce
+the reflected parameter `1 - t`, and therefore have equal `phaseDepth`.
+The remaining refinement-law task is to identify a mathematically justified
+composition law for local corrections.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 6f8e4895..89f61ed7 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -361,9 +361,10 @@ explicit.
 [IMPLEMENTED: semantic-cf2d-phase/standard-euclidean-space]
 [IMPLEMENTED: semantic-cf2d-phase/quarter-turn-isometry]
 [IMPLEMENTED: semantic-cf2d-phase/oriented-pi-over-two]
-[TODO: semantic-cf2d-phase/dyadic-refinement] Define finite dyadic phase
-nodes, prove their endpoint and reflection laws, and state the finite
-one-step subdivision relation before introducing any limit.
+[IMPLEMENTED: semantic-cf2d-phase/dyadic-refinement]
+`SemanticCF2DDyadic` defines the finite nodes `k / 2^n`, proves their endpoint,
+unit-interval, reflection, even-child, odd-child midpoint, and reflected
+phase-depth laws.
 [TODO: semantic-cf2d-phase/refinement-law] Select and prove the composition
 law for local boundary corrections. Do not assume that it is an infinite
 product or a logarithmic sum before this finite law is established.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 5f2f41c0..230ca15c 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -770,3 +770,23 @@ Archive
      に分解した。
    - infinite product、logarithmic sum、Gaussian limit は、有限合成則が
      証明されるまで仮定しない方針を明記した。
+
+### 2026/06/23 17:59 JST (Finite dyadic phase refinement)
+
+1. module:
+   - `DkMath.Analysis.DkReal.SemanticCF2DDyadic` を新設し、公開 Analysis
+     entry point へ追加した。
+2. finite nodes:
+   - `dyadicPhaseDenom n = 2^n` と
+     `dyadicPhaseNode n k = k / 2^n` を定義した。
+   - denominator positivity、両端点、unit interval membership を証明した。
+3. refinement:
+   - complementary index の reflection law を証明した。
+   - even child が parent と一致し、odd child が隣接 parent の midpoint
+     となることを証明した。
+   - reflected dyadic nodes で `phaseDepth` が一致することを証明した。
+4. boundary:
+   - correction product、logarithmic sum、Gaussian limit は導入していない。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DDyadic` 成功
+     (8275 jobs)。
````
`````

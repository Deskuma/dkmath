# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2DLogComposition

gch: 3b021e232393fcc2ec4e7d27567545a6e0fd5393

## Report

次の checkpoint まで進めました。

`SemanticCF2DLogComposition.lean` に以下を追加しました。

- `dyadicPhaseWeightedLogCancellation`: 任意重み付き log cancellation の短名 alias
- `sum_dyadicPhaseAverageWeight_eq_one`: average weight の総量 `1`
- `sum_dyadicPhaseMeshWeight_eq_one_add`: plain complete mesh-width weight の総量 `1 + h_n`
- `dyadicPhaseEndpointFilter_eq`: complete mesh の端点集合 `{0, 2^n}`
- `sum_dyadicPhaseTrapezoidWeight_eq_one`: trapezoid weight の総量 `1`

これで、average は sample mean candidate、trapezoid は closed-interval candidate、plain mesh-width complete sum は endpoint overcount を持つ候補、という区別が Lean 上で見えるようになりました。まだ canonical limit / Gaussian / `pi` は主張していません。

文書と History も同期済みです。

検証済み:

- `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition`
- `lake build DkMath.Analysis`
- `git diff --check`

## Review

うむ、これはかなり良い checkpoint じゃ。
今回の差分で、`SemanticCF2DLogComposition` は **有限重み付き log observable の分類台** として、だいぶ形が整った。

今回追加されたのは、短名 alias、average / mesh-width / trapezoid weight の総量定理、complete mesh の端点集合定理、そして trapezoid weight の総量 \(1\) の証明じゃな。報告でも、average は sample mean candidate、trapezoid は closed-interval candidate、plain mesh-width complete sum は endpoint overcount を持つ候補として区別できるようになった、と整理されている。

## 1. 総評

採用でよい。

今回の進捗は、単なる補助定理の追加ではない。
これは **candidate observable の性格分類** を Lean 上に持ち込んだ差分じゃ。

前回までで、任意重み付き cancellation は得られていた。

$$
\sum_k w_k\left(2\log(\mathrm{normalization}*{n,k})+\log(\mathrm{depth}*{n,k})\right)=0
$$

今回、その重み \(w_k\) たちの総量を証明したことで、候補の違いがはっきりした。

```text id="bqrcue"
average weight:
  total mass = 1

trapezoid weight:
  total mass = 1

plain complete mesh-width weight:
  total mass = 1 + h_n
```

つまり、同じ cancellation law を満たしていても、観測量としての意味は違う。
ここが Lean 上で見えるようになったのが大きい。

## 2. 数学的な意味

まず average weight は sample mean candidate じゃ。

$$
\sum_k \frac{1}{#\mathrm{mesh}}\ =1
$$

これは「全 node の平均」を見る量で、積分というより標本平均に近い。

次に trapezoid weight は closed interval integration candidate じゃ。

$$
\sum_{k=0}^{2^n} w_{n,k}=1
$$

端点を半分にすることで、閉区間 \([0,1]\) の長さ \(1\) に合う。

一方、plain mesh-width complete weight は全 node に同じ \(h_n=1/2^n\) を掛けるので、

$$
\sum_{k=0}^{2^n}h_n=1+h_n
$$

となる。
これは complete node mesh で端点分が過剰に数えられていることを示す。

この区別は、Gaussian bridge に行く前にかなり重要じゃ。
なぜなら、極限候補を選ぶ時に「同じ finite cancellation を満たす」だけでは足りないからじゃ。
その weight が何を測っているかを見なければならぬ。

## 3. 実装レビュー

短名 alias は良い。

```lean id="movd6l"
theorem dyadicPhaseWeightedLogCancellation
    (n : ℕ) (w : ℕ → ℝ) :
    2 * (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseNormalization n k)) +
        (∑ k ∈ dyadicPhaseNodeIndices n,
          w k * Real.log (dyadicPhaseDepth n k)) = 0 :=
  two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum n w
```

長い定理名は説明的で良いが、後続で頻繁に使うには重い。
`dyadicPhaseWeightedLogCancellation` は、研究文脈でも実装文脈でも使いやすい名前じゃ。

average weight の総量定理も良い。

```lean id="izyylh"
theorem sum_dyadicPhaseAverageWeight_eq_one (n : ℕ) :
    ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseAverageWeight n = 1
```

cardinality が正であることを示してから `field_simp` で閉じる。素直じゃ。

mesh-width weight の総量定理も良い。

```lean id="epk2rm"
theorem sum_dyadicPhaseMeshWeight_eq_one_add (n : ℕ) :
    ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n =
      1 + dyadicPhaseMeshWeight n
```

これが今回の目玉の一つじゃな。
complete mesh の点数が \(2^n+1\) で、mesh width が \(1/2^n\) なので、総量が \(1+1/2^n\) になる。
この endpoint overcount が明示されたのは非常によい。

## 4. endpoint filter の定理

`dyadicPhaseEndpointFilter_eq` は、trapezoid weight の総量証明のための良い補助定理じゃ。

```lean id="y2u63d"
theorem dyadicPhaseEndpointFilter_eq (n : ℕ) :
    (dyadicPhaseNodeIndices n).filter
        (fun k => k = 0 ∨ k = dyadicPhaseDenom n) =
      {0, dyadicPhaseDenom n}
```

これにより、complete mesh の端点集合が正確に `{0, 2^n}` であることが使える。

注意点として、`n` が任意でも `dyadicPhaseDenom n` は正なので、`0` と `dyadicPhaseDenom n` は異なる。ここも `hdistinct` で処理しており、良い。

## 5. trapezoid weight の総量

今回のもう一つの核はこれじゃ。

```lean id="c3nmlb"
theorem sum_dyadicPhaseTrapezoidWeight_eq_one (n : ℕ) :
    ∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseTrapezoidWeight n k = 1
```

証明の構造も良い。

```text id="x9sbjz"
plain complete mesh-width total:
  1 + h_n

endpoint half correction:
  h_n

therefore trapezoid total:
  1
```

つまり、全点に \(h_n\) を掛けたものから、端点二つの余分な半分ずつを引いている。

$$
(1+h_n)-h_n=1
$$

これは finite closed-interval bookkeeping として非常に綺麗じゃ。

## 6. 研究テーマとの関係

今回の差分は、\(\sqrt{\pi}\) へ直接進んだわけではない。
しかし、かなり重要な準備じゃ。

最終目標は、CF2D 内部から normalization constant を作り、後で `Real.pi` と比較すること。
そのためには、どの finite observable が極限で意味を持つかを選ばなければならない。

今回の分類で、少なくとも次がはっきりした。

```text id="sgifnp"
average:
  標本平均候補。総量 1。

trapezoid:
  閉区間積分候補。総量 1。

plain mesh-width:
  endpoint overcount あり。総量 1 + h_n。
```

これは、canonical observable selection のための大事な比較材料じゃ。

## 7. 注意点

大きな問題はない。
ただし、次の一点は意識したい。

`plain mesh-width` の総量は \(1+h_n\) で、極限では \(1\) に近づく。
したがって、極限だけを見ると trapezoid と同じに見える可能性がある。

しかし、有限段階では違う。
DkMath の現在の方針は「有限 law を先に見る」なので、この違いを証明しておいたのは正しい。

特に、Gaussian bridge では小さい差が正規化定数に効く可能性がある。
だから「極限で同じそうだから同一視する」のではなく、有限段階の違いを持ったまま比較するのがよい。

## 8. 次に足すと強い theorem

次は、weight の分類をさらに使いやすくするとよい。

### 8.1. plain mesh-width と trapezoid の差

以下の差分があると、endpoint correction の意味がさらに明確になる。

$$
\sum_k h_n f(k)-\sum_k w^{trap}_{n,k}f(k)=\frac{h_n}{2}\left(f(0)+f(2^n)\right)
$$

log depth 版なら、

$$
\mathrm{MeshWeightedLogDepth}*n-\mathrm{TrapezoidLogDepth}*n
=\frac{h_n}{2}\left(\log D*{n,0}+\log D*{n,2^n}\right)
$$

ただし端点の depth がどうなるかを使えば、さらに簡約できるはずじゃ。

端点では `phaseDepth 0 = 1` と `phaseDepth 1 = 1` なので、

$$
\log D_{n,0}=\log 1=0
$$

$$
\log D_{n,2^n}=\log 1=0
$$

したがって depth については、plain mesh-width と trapezoid の差は消える可能性がある。

一方、normalization も端点で \(1\) のはずなので、こちらも log は \(0\)。
もしそうなら、log observable に関しては plain mesh-width と trapezoid が有限段階でも一致するかもしれぬ。

これは面白い。
総 weight は違うが、endpoint log 値が \(0\) なら log sum では差が出ない。

次に狙う価値がある。

```lean id="okwk2c"
theorem dyadicPhaseWeightedLogDepthSum_eq_trapezoidLogDepthSum ...
```

あるいは、まず端点 log を証明する。

```lean id="yfu88u"
theorem Real.log_dyadicPhaseDepth_left_endpoint ...
theorem Real.log_dyadicPhaseDepth_right_endpoint ...
theorem Real.log_dyadicPhaseNormalization_left_endpoint ...
theorem Real.log_dyadicPhaseNormalization_right_endpoint ...
```

### 8.2. trapezoid cancellation は既にあるので、次は equality comparison

すでに cancellation は任意重みで出る。
次は候補同士の比較じゃ。

```text id="zn9e51"
average vs trapezoid
mesh-width vs trapezoid
complete node vs midpoint
raw vs centered
```

この比較が、canonical selection の本体になる。

## 9. Gaussian bridge への次の入口

今回で weight mass が整ったので、次は centered observable に入るのが自然じゃ。

`phaseDepth` の中心値は、

$$
\mathrm{phaseDepth}\left(\frac{1}{2}\right)=\frac{1}{2}
$$

中心基準を引く。

$$
\Delta\log D(t)=\log(\mathrm{phaseDepth}(t))-\log\left(\frac{1}{2}\right)
$$

すると、

$$
\Delta\log D(t)=\log\left(1+4\left(t-\frac{1}{2}\right)^2\right)
$$

ここから二次型の有限比較が始められる。

例えば、次のような不等式が候補になる。

$$
0\le \log(1+4s^2)\le 4s^2
$$

ただし上界は \(s\) の範囲に依存せず一般に `log(1+x) ≤ x` で出せる。

これは Gaussian へ行く前の重要な橋じゃ。

```text id="uc0bkm"
centered log increment
  ↓
quadratic upper bound
  ↓
finite weighted quadratic sums
  ↓
Gaussian candidate
```

## 10. 結論

今回の差分は採用でよい。

```text id="a2kdd4"
実装:
  良い。重み付き log observable の分類に必要な API が増えた。

数学:
  良い。average、plain mesh-width、trapezoid の総量差が Lean 上で明確になった。

研究位置:
  良い。canonical observable selection の前段として重要。

安全性:
  良い。Gaussian、π、canonical limit は未主張。

次:
  endpoint log 値、
  mesh-width と trapezoid の log observable 比較、
  centered log increment、
  quadratic bound。
```

ぬしよ、これはとてもよい。
「どの重みなら何を測っているのか」が、ようやく Lean の定理として見えてきた。

\(\sqrt{\pi}\) へ向かうには、ただ式を積むだけでは足りぬ。
どの観測が面積になり、どの観測が平均になり、どの観測が端点を過剰に拾うのかを見分けねばならぬ。
今回、その目利きのための秤ができたと言えるぞい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 10f11512..ae434eb9 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -141,7 +141,9 @@ weighted variants are exposed as finite candidate observables, and the same
 cancellation law is proved for them. A pointwise weighted cancellation lemma
 then supplies the standard trapezoidal endpoint half-weight candidate. No
 logarithmic quantity is yet selected as the canonical refinement-limit
-observable.
+observable. The total masses of the average, plain mesh-width, and
+trapezoidal weights are also exposed to distinguish sample-mean,
+endpoint-overcounted complete-mesh, and closed-interval candidates.
 
 [IMPLEMENTED: semantic-cf2d-path] `DkReal.SemanticCF2DPath` uses the
 coordinate-product topology from `CF2D.Topology` to package every translated
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
index 80e0b866..1eb03f0b 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2DLogComposition.lean
@@ -118,6 +118,20 @@ theorem two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum
         rw [two_mul_log_dyadicPhaseNormalization_add_log_depth n k]
         simp
 
+/--
+Short API name for pointwise weighted logarithmic boundary cancellation.
+
+This alias is intended for downstream candidate observables where the weight
+choice is the main object of study.
+-/
+theorem dyadicPhaseWeightedLogCancellation
+    (n : ℕ) (w : ℕ → ℝ) :
+    2 * (∑ k ∈ dyadicPhaseNodeIndices n,
+          w k * Real.log (dyadicPhaseNormalization n k)) +
+        (∑ k ∈ dyadicPhaseNodeIndices n,
+          w k * Real.log (dyadicPhaseDepth n k)) = 0 :=
+  two_mul_weightedLogNormalizationSum_add_weightedLogDepthSum n w
+
 /--
 The complete dyadic mesh has one more node than its dyadic denominator.
 
@@ -145,6 +159,17 @@ theorem dyadicPhaseAverageWeight_pos (n : ℕ) :
     exact Nat.succ_pos _
   exact one_div_pos.2 (by exact_mod_cast hcard)
 
+/-- The uniform average weights on the complete dyadic mesh have total mass one. -/
+theorem sum_dyadicPhaseAverageWeight_eq_one (n : ℕ) :
+    ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseAverageWeight n = 1 := by
+  have hcard_nat : 0 < (dyadicPhaseNodeIndices n).card := by
+    rw [dyadicPhaseNodeIndices_card]
+    exact Nat.succ_pos _
+  have hcard_pos : (0 : ℝ) < (dyadicPhaseNodeIndices n).card := by
+    exact_mod_cast hcard_nat
+  simp [dyadicPhaseAverageWeight]
+  field_simp [(ne_of_gt hcard_pos)]
+
 /-- Uniform average of logarithmic depth observations on the complete mesh. -/
 def dyadicPhaseAverageLogDepth (n : ℕ) : ℝ :=
   dyadicPhaseAverageWeight n * dyadicPhaseLogDepthSum n
@@ -188,6 +213,20 @@ theorem dyadicPhaseMeshWeight_pos (n : ℕ) :
     0 < dyadicPhaseMeshWeight n := by
   exact one_div_pos.2 (by exact_mod_cast dyadicPhaseDenom_pos n)
 
+/--
+The complete-node mesh-width weights have total mass `1 + h_n`.
+
+This records the endpoint overcount of the plain complete-node mesh-width
+candidate relative to a closed-interval integration rule.
+-/
+theorem sum_dyadicPhaseMeshWeight_eq_one_add (n : ℕ) :
+    ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n =
+      1 + dyadicPhaseMeshWeight n := by
+  have hdenom : (dyadicPhaseDenom n : ℝ) ≠ 0 := by
+    exact_mod_cast (dyadicPhaseDenom_pos n).ne'
+  simp [dyadicPhaseNodeIndices, dyadicPhaseMeshWeight]
+  field_simp [hdenom]
+
 /-- Mesh-weighted finite log-depth sum. -/
 def dyadicPhaseWeightedLogDepthSum (n : ℕ) : ℝ :=
   dyadicPhaseMeshWeight n * dyadicPhaseLogDepthSum n
@@ -240,6 +279,80 @@ theorem dyadicPhaseTrapezoidWeight_pos (n k : ℕ) :
   · exact div_pos (dyadicPhaseMeshWeight_pos n) (by norm_num)
   · exact dyadicPhaseMeshWeight_pos n
 
+/--
+The endpoint set of the complete dyadic mesh consists of the two boundary
+indices `0` and `2^n`.
+-/
+theorem dyadicPhaseEndpointFilter_eq (n : ℕ) :
+    (dyadicPhaseNodeIndices n).filter
+        (fun k => k = 0 ∨ k = dyadicPhaseDenom n) =
+      {0, dyadicPhaseDenom n} := by
+  ext k
+  constructor
+  · intro hk
+    exact by
+      simp only [Finset.mem_filter] at hk
+      simpa using hk.2
+  · intro hk
+    have hdenom_pos := dyadicPhaseDenom_pos n
+    have hk' : k = 0 ∨ k = dyadicPhaseDenom n := by
+      simpa using hk
+    simp only [Finset.mem_filter]
+    constructor
+    · simp only [dyadicPhaseNodeIndices, Finset.mem_range,
+        Nat.lt_succ_iff]
+      rcases hk' with rfl | rfl
+      · exact Nat.zero_le _
+      · exact le_rfl
+    · exact hk'
+
+/--
+The trapezoidal weights on the complete dyadic node mesh have total mass one.
+
+This is the finite closed-interval bookkeeping property: two endpoints have
+half mesh width and all interior nodes have full mesh width.
+-/
+theorem sum_dyadicPhaseTrapezoidWeight_eq_one (n : ℕ) :
+    ∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseTrapezoidWeight n k = 1 := by
+  have hmesh :
+      ∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n =
+        1 + dyadicPhaseMeshWeight n :=
+    sum_dyadicPhaseMeshWeight_eq_one_add n
+  have hend :
+      ∑ k ∈ dyadicPhaseNodeIndices n,
+          (if k = 0 ∨ k = dyadicPhaseDenom n then
+            dyadicPhaseMeshWeight n / 2
+          else
+            0) =
+        dyadicPhaseMeshWeight n := by
+    rw [← Finset.sum_filter]
+    rw [dyadicPhaseEndpointFilter_eq]
+    have hdistinct : (0 : ℕ) ≠ dyadicPhaseDenom n :=
+      (dyadicPhaseDenom_pos n).ne
+    simp [hdistinct]
+    ring
+  calc
+    ∑ k ∈ dyadicPhaseNodeIndices n, dyadicPhaseTrapezoidWeight n k
+        = (∑ _k ∈ dyadicPhaseNodeIndices n, dyadicPhaseMeshWeight n) -
+            ∑ k ∈ dyadicPhaseNodeIndices n,
+              (if k = 0 ∨ k = dyadicPhaseDenom n then
+                dyadicPhaseMeshWeight n / 2
+              else
+                0) := by
+          rw [← Finset.sum_sub_distrib]
+          apply Finset.sum_congr rfl
+          intro k hk
+          unfold dyadicPhaseTrapezoidWeight
+          by_cases hendpoint : k = 0 ∨ k = dyadicPhaseDenom n
+          · rw [if_pos hendpoint]
+            simp [hendpoint]
+            ring_nf
+          · rw [if_neg hendpoint]
+            simp [hendpoint]
+    _ = 1 := by
+      rw [hmesh, hend]
+      ring
+
 /-- Trapezoidal finite log-depth sum on the complete dyadic node mesh. -/
 def dyadicPhaseTrapezoidLogDepthSum (n : ℕ) : ℝ :=
   ∑ k ∈ dyadicPhaseNodeIndices n,
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 9ec437cb..51d6fadd 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -229,6 +229,12 @@ two endpoints half a mesh width and every interior node one mesh width. This
 is still a finite observable; it does not by itself prove convergence or
 select the Gaussian-relevant normalization.
 
+The weight totals are now part of the formal comparison. Uniform average and
+trapezoidal weights both have total mass `1`. In contrast, the plain
+mesh-width complete-node weights have total mass `1 + h_n`, exposing the
+endpoint overcount that must be considered before treating that observable as
+a closed-interval integration candidate.
+
 ### Milestone D: limit and Gaussian bridge
 
 1. Prove convergence of the refinement correction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
index 25654644..031a5906 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -390,7 +390,9 @@ mesh-width weighted log sums are now recorded as finite candidate observables,
 with the same cancellation law transported by scalar multiplication. A
 pointwise weighted cancellation lemma now covers arbitrary finite weights on
 the complete mesh, and the trapezoidal endpoint half-weight candidate is
-implemented from it.
+implemented from it. The weight masses are formalized: average and trapezoid
+weights have total mass `1`, while the plain complete mesh-width weights have
+total mass `1 + h_n`.
 [TODO: semantic-cf2d-phase/correction-limit-selection] Determine whether any
 finite product, raw logarithmic sum, average, mesh-weighted sum, trapezoidal
 sum, midpoint sum, or another quantity has a canonical refinement limit. The
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 91221301..ee3615e6 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -961,3 +961,25 @@ Archive
 5. verification:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
      (8281 jobs)。
+
+### 2026/06/27 06:23 JST (Finite weight mass comparison)
+
+1. API:
+   - pointwise weighted cancellation の短名 alias
+     `dyadicPhaseWeightedLogCancellation` を追加した。
+   - average weight、plain complete mesh-width weight、trapezoid weight の
+     total mass theorem を追加した。
+2. finite laws:
+   - average と trapezoid は total mass `1` として証明した。
+   - plain complete mesh-width は total mass `1 + h_n` として証明し、
+     endpoint overcount を Lean 上で可視化した。
+3. boundary:
+   - weight mass の比較は observable selection のための有限分類であり、
+     canonical refinement limit、Gaussian weight、`pi` identification は
+     まだ選択していない。
+4. documentation:
+   - public `DkReal.lean` comment、continuous phase task、pre-geometric
+     pi research note を同期した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2DLogComposition` 成功
+     (8281 jobs)。
````
`````

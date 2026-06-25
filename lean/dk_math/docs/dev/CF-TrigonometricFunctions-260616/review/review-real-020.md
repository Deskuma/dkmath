# Git diff / Report / Review

## Add: DkReal Nonnegative Natural-Power Milestone

gch: 791a44e6623acabeeb6b9cece9efc2a946f49634

## Report

節目の記録とコード整理を完了しました。

- 数学原理の見出しコメントを [PowBound.lean](/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean:23) に追加
- `powNonneg` の有理数・0乗・1乗の簡約定理を追加
- `GapInterval.ext` を基本 API として追加
- 研究向け観測レポートを新規作成: [DkReal-Nonnegative-Power-Milestone.md](/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md:1)

重要点は、実数値そのものを選択せず、有理区間列と収束証明を操作するため、DkReal 層では `noncomputable` が不要ということです。検索でも同層に `noncomputable` が存在しないことを確認しました。

`lake build DkMath.Analysis DkMath` と `git diff --check` は成功しています。次候補は非負 DkReal の加法・乗法です。

## Review

(no review, Continue working.)

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
index a59ea6d5..307fe995 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Interval.lean
@@ -29,6 +29,13 @@ deriving Repr
 
 namespace GapInterval
 
+/-- Two rational gap intervals are equal when both endpoints are equal. -/
+@[ext]
+theorem ext {I J : GapInterval} (hlo : I.lo = J.lo) (hhi : I.hi = J.hi) : I = J := by
+  cases I
+  cases J
+  simp_all
+
 /-- The degenerate rational interval containing only `q`. -/
 def singleton (q : ℚ) : GapInterval :=
   ⟨q, q, le_rfl⟩
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean b/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
index d4862516..f0cdcc96 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/PowBound.lean
@@ -20,6 +20,14 @@ analysis or a mean-value theorem.
 
 namespace DkMath.Analysis.DkReal
 
+/-!
+## I. Positivity and isotonicity of the exact correction kernel
+
+For nonnegative variables, every term in the finite binomial expansion of
+`gapGN` is nonnegative. Coordinatewise order of the base and increment is
+therefore transported through the kernel.
+-/
+
 /-- `gapGN` is nonnegative when both its base and increment are nonnegative. -/
 theorem gapGN_nonneg_of_nonneg
     (d : ℕ) {base delta : ℚ} (hbase : 0 ≤ base) (hdelta : 0 ≤ delta) :
@@ -45,6 +53,14 @@ theorem gapGN_le_of_nonneg_of_le
   intro k hk
   gcongr
 
+/-!
+## II. Order bounds supplied by nested rational intervals
+
+If `Iₙ = [aₙ,bₙ]` is nested, then `aₙ ≤ bₙ ≤ b₀`. Under nonnegativity,
+the width `wₙ = bₙ - aₙ` also satisfies `0 ≤ wₙ ≤ b₀`. These inequalities
+place both arguments of `gapGN d aₙ wₙ` in a fixed nonnegative box.
+-/
+
 /-- Every lower endpoint is bounded above by the initial upper endpoint. -/
 theorem lo_le_initial_hi
     (x : DkMath.Analysis.DkReal) (n : ℕ) :
@@ -69,12 +85,22 @@ theorem gapGN_le_initial_hi
     (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
     gapGN d (x.interval n).lo (x.interval n).width
       ≤ gapGN d (x.interval 0).hi (x.interval 0).hi := by
-  have hhi0 : 0 ≤ (x.interval 0).hi :=
-    (hx 0).trans (x.interval 0).le_lo_hi
   exact gapGN_le_of_nonneg_of_le d
     (hx n) (lo_le_initial_hi x n)
     (x.interval n).width_nonneg (width_le_initial_hi x hx n)
 
+/-!
+## III. Uniform boundedness and propagation of vanishing width
+
+The powered width factors exactly as
+
+`wₙ * gapGN d aₙ wₙ`.
+
+The first factor tends to zero by the definition of `DkReal`; the second is
+uniformly bounded by its value at `(b₀,b₀)`. Hence powered widths also tend to
+zero. This is the closure mechanism for natural powers.
+-/
+
 /-- The `gapGN` sequence along a nested nonnegative approximation is uniformly bounded. -/
 theorem gapGN_bounded_on_nonnegative_nested
     (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) :
@@ -99,10 +125,40 @@ def powNonneg
   powNonnegOfGapGNBounded d x hx
     (gapGN_bounded_on_nonnegative_nested d x hx)
 
+/-!
+## IV. Computable natural-power closure
+
+`powNonneg` transforms rational endpoints stage by stage and packages the
+nestedness and vanishing-width proofs. No evaluation into Mathlib's `ℝ` is
+used, so this construction remains computable.
+-/
+
 /-- The intervals of `powNonneg` are the pointwise powered intervals. -/
 @[simp]
 theorem powNonneg_interval
     (d : ℕ) (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
     (powNonneg d x hx).interval n = powNonnegApprox d x hx n := rfl
 
+/-- Natural power of an embedded nonnegative rational is its powered singleton interval. -/
+@[simp]
+theorem powNonneg_ofRat_interval
+    (d : ℕ) {q : ℚ} (hq : 0 ≤ q) (n : ℕ) :
+    (powNonneg d (DkMath.Analysis.DkReal.ofRat q) (nonnegative_ofRat hq)).interval n
+      = GapInterval.singleton (q ^ d) := by
+  apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]
+
+/-- Zeroth power produces the singleton interval at `1` at every stage. -/
+@[simp]
+theorem powNonneg_zero_interval
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonneg 0 x hx).interval n = GapInterval.singleton 1 := by
+  apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]
+
+/-- First power leaves every approximation interval unchanged. -/
+@[simp]
+theorem powNonneg_one_interval
+    (x : DkMath.Analysis.DkReal) (hx : Nonnegative x) (n : ℕ) :
+    (powNonneg 1 x hx).interval n = x.interval n := by
+  apply GapInterval.ext <;> simp [powNonneg, powNonnegApprox]
+
 end DkMath.Analysis.DkReal
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 0f1f2949..b75109f2 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -57,6 +57,10 @@ DkMath.Analysis.DkReal
   public entry point for the computable approximation layer
 ```
 
+The closure of nonnegative `DkReal` values under natural powers and its
+computability significance are recorded in
+[`DkReal-Nonnegative-Power-Milestone.md`](DkReal-Nonnegative-Power-Milestone.md).
+
 `RealBridge` remains the home of continuity and interval mapping. The separate
 `TaylorBridge` now connects `gapGN` to difference quotients and `HasDerivAt`
 without mixing those concerns into the basic real bridge.
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
new file mode 100644
index 00000000..82a0e33b
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/docs/DkReal-Nonnegative-Power-Milestone.md
@@ -0,0 +1,139 @@
+# DkReal Nonnegative Natural-Power Milestone
+
+## Observation
+
+The first substantial operation on `DkReal` is now complete: every
+nonnegative `DkReal` approximation is closed under natural powers.
+
+This checkpoint is notable because the construction concerns real-number
+approximations but the operation itself does not require `noncomputable`.
+It acts only on exact rational endpoints and carries proofs that the resulting
+interval sequence remains nested and has width tending to zero.
+
+This is not yet a claim that the full real field has been reconstructed.
+It is a precise closure result for the representation currently implemented.
+
+## Representation
+
+A `DkReal` is represented by nested closed rational intervals
+
+```text
+I_n = [a_n, b_n]
+```
+
+whose widths
+
+```text
+w_n = b_n - a_n
+```
+
+tend to zero. A nonnegative `DkReal` additionally satisfies `0 <= a_n` at
+every stage.
+
+For a natural exponent `d`, the stagewise power operation is
+
+```text
+[a_n, b_n] |-> [a_n^d, b_n^d].
+```
+
+Because the power map is monotone on the nonnegative rationals, nestedness is
+preserved by exact order reasoning.
+
+## Width Principle
+
+The decisive identity is the finite algebraic factorization
+
+```text
+b_n^d - a_n^d
+  = w_n * gapGN d a_n w_n,
+```
+
+where `b_n = a_n + w_n`. The kernel `gapGN` is a finite binomial sum, not a
+derivative or an infinite expansion.
+
+Nestedness and nonnegativity give the fixed bounds
+
+```text
+0 <= a_n <= b_0,
+0 <= w_n <= b_0.
+```
+
+Every term of `gapGN` is nonnegative and coordinatewise monotone on this
+quadrant. Therefore
+
+```text
+0 <= gapGN d a_n w_n <= gapGN d b_0 b_0.
+```
+
+Thus the powered width is a sequence tending to zero multiplied by a uniformly
+bounded sequence. It also tends to zero. This proves that the powered interval
+sequence is again a `DkReal`.
+
+## Why `noncomputable` Is Unnecessary Here
+
+The construction never selects a real number from the nested intervals. It
+does not:
+
+- invoke completeness of `Real`;
+- choose a limit point;
+- quotient Cauchy data;
+- evaluate a `DkReal` as a Mathlib `Real`;
+- use a derivative or mean-value theorem to estimate the power map.
+
+Instead, each output interval is computed from rational input endpoints by a
+finite natural power. The proof fields certify the global convergence
+invariant, but they do not change the executable endpoint data.
+
+The distinction is architectural:
+
+```text
+computable representation layer:
+  rational intervals + finite algebra + convergence certificates
+
+semantic bridge layer:
+  interpretation in Mathlib Real + continuity + derivatives
+```
+
+The semantic bridge may legitimately use `noncomputable`, because extracting
+or identifying an abstract real value can require classical completion
+machinery. The present `DkReal` power operation does not cross that boundary.
+
+## Lean Realization
+
+The implementation is divided into four mathematical steps:
+
+1. `gapGN_nonneg_of_nonneg` proves positivity of the exact correction kernel.
+2. `gapGN_le_of_nonneg_of_le` proves coordinatewise monotonicity.
+3. `gapGN_bounded_on_nonnegative_nested` obtains a uniform bound from the
+   initial interval.
+4. `powNonneg` packages the powered intervals as a new `DkReal`.
+
+The public simplification rules record the expected exact cases:
+
+```lean
+powNonneg_ofRat_interval
+powNonneg_zero_interval
+powNonneg_one_interval
+```
+
+No approximation error is hidden in these statements. Embedded rationals
+remain singleton intervals, the zeroth power is the singleton at one, and the
+first power returns the original interval at every stage.
+
+## Research Significance
+
+This checkpoint isolates a useful formalization principle:
+
+> An operation on real-like objects can remain computable when it is defined
+> on finite observations and its analytic obligation is carried separately as
+> a proof of preservation of the representation invariant.
+
+For natural powers on the nonnegative domain, the exact cosmic-formula kernel
+provides precisely the finite correction factor needed to transport vanishing
+width. Real analysis appears later as an interpretation of this construction,
+not as a prerequisite for defining it.
+
+The next natural tests of the same principle are nonnegative addition and
+multiplication. They will determine how much of an ordered semiring structure
+can be built entirely inside the rational-interval layer before introducing a
+semantic map to Mathlib's `Real`.
````
`````

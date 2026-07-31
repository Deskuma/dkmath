# DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNDescentB

## Migration

v4.29.0 to v4.32.2

## review

うむ、これは **Lean 4.32.2 migration の代表事例**として記録価値が高い。修正内容も筋がよい。

今回の本質は、

> 以前は `simpa` が深い再梱包経路まで展開し、同じ座標値だと認識していたが、Lean 4.32.2 では structure projection 間の定義的同一性が表面化しなくなった。

というものじゃ。

## 修正パターン

### 1. Prop を返す `def` を `theorem` へ変更

```lean
def TriominoWieferichShrinkWitnessB.toEq
```

から、

```lean
theorem TriominoWieferichShrinkWitnessB.toEq
```

への変更。

これは新しい `defProp` linter への正規対応じゃ。内容・proof term は変えず、宣言種別だけを正した。

### 2. 二重に包まれた `gap` を明示展開

```lean
simpa [PrimeGe5CounterexamplePack.gap]
```

では足りず、

```lean
simpa [
  PrimeGe5CounterexamplePack.gap,
  PrimeCounterexamplePack.gap
]
```

とした。

これは、

```text
PrimeGe5CounterexamplePack.gap
  → PrimeCounterexamplePack.gap
  → z - y
```

という二段階の definition unfolding を明示した事例。

### 3. 再梱包構造体の projection bridge を追加

特に良いのは、この3本じゃ。

```lean
@[simp] theorem ...ofCandidateSpec_x'
@[simp] theorem ...ofCandidateSpec_y'
@[simp] theorem ...ofCandidateSpec_z'
```

そして、

```lean
@[simp] theorem ...Candidate_of_pack_clean_x'
@[simp] theorem ...Candidate_of_pack_clean_y'
@[simp] theorem ...Candidate_of_pack_clean_z'
```

これにより、

```text
KernelNums.x'
Candidate.x'
Recipe.ofCandidateSpec.x'
```

という異なる衣装の座標値を、`simp` が正式に接続できるようになった。

巨大な定義本体を毎回展開するのではなく、**projection の一致を公開 API として固定した**のが重要じゃ。

### 4. `simpa` 依存を `rw` + `exact` へ変更

例えば、

```lean
simpa [hz] using hzlt_pack
```

を、

```lean
rw [← hz]
exact hzlt_pack
```

へ変更した。

`hpB'` も同じく、

```lean
rw [← hz, ← hy]
exact hpB'_pack
```

としている。

これは migration で非常に有効な修正じゃ。

```text
旧:
  simp が等式の向き・展開順・projection を全部判断

新:
  rw で目的の型を正確に合わせる
  exact で証明項を渡す
```

となり、Lean の simplifier 変更に強くなった。

### 5. 深い wrapper chain を明示展開

```lean
KernelCore
→ Recipe
→ NumsInvCore
→ KernelNumsCore
→ Seed
→ EqSeed
→ Trace
→ TraceCore
```

という経路を `simpa [...]` に列挙している。

これは美しい最終設計とは言い難いが、**migration 修正としては妥当**じゃ。数学構造を変えず、従来の定義経路を明示するだけに留めている。

---

## Report 案

```md
## Report

Lean v4.32.2 への更新により、深く再梱包された shrink candidate / recipe /
kernel structure 間の projection が、従来の `simpa` だけでは同一視されなくなった。

主な failure は、数学的には同一である `x'`, `y'`, `z'` が、次の異なる
structure から射影されているために生じた。

- `TriominoWieferichShrinkKernelNumsB`
- `TriominoWieferichShrinkNumsInvCandidateB`
- `TriominoWieferichShrinkNumsInvRecipeB`
- `TriominoWieferichShrinkKernelCoreB`
- `TriominoWieferichShrinkKernelEqSeedTraceCoreB`

修正として、projection の一致を表す `[simp]` theorem を追加し、必要な箇所では
wrapper definition を明示的に展開した。

また、`simpa` に依存していた順序・非可除性の transport を `rw` と `exact` に
置き換え、定義展開順に依存しない証明へ変更した。

加えて、Prop を返していた一部の `def` を `theorem` へ変更し、
Lean v4.32.2 の `defProp` linter に対応した。

数学的 statement および shrink construction の意味は変更していない。
```

## Review 案

```md
## Review

修正は Lean v4.32.2 migration として妥当。

今回の failure は数学的な破綻ではなく、同じ shrink 座標を複数の wrapper structure
から射影していることに起因する definitional equality / simplifier の差である。

特に次の修正は、単なる局所的な `simpa` 拡張より安定している。

- `ofCandidateSpec` の `x'`, `y'`, `z'` projection lemma の追加
- clean candidate と kernel nums 間の projection bridge の追加
- `simpa` から `rw` + `exact` への変更
- nested `gap` definition の明示展開

一方、kernel / recipe / seed / trace の多数の wrapper を列挙する長い
`simpa [...]` は、将来のリファクタ対象を可視化している。

Migration 中はこの明示展開で正しい。将来的には canonical shrink state を一つ定め、
各 wrapper をその projection または legacy adapter へ縮約するのが望ましい。

現時点では数学的内容を変更せず build compatibility を回復しており、承認できる。
```

これは README では、

```text
Migration Case:
Deep structure repackaging and projection normalization
```

として残せる案件じゃな。

昔の賢狼が積み上げた巨大包装塔を、今の賢狼が `[simp]` 橋で補強したわけじゃ。建て直しではなく耐震工事である🤣

## Git diff / Report / Review

## fix: error: simpa

gch: fbda6ea7c3935d7d45dc2ef0eeb858176026cee8

## Report

_

## Review

_

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean
index d4e27f86..d15d415b 100644
--- a/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean
+++ b/lean/dk_math/DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean
@@ -134,7 +134,7 @@ structure TriominoWieferichShrinkWitnessB
   hz0' : z' ≠ 0
 
 /-- 完全 witness から「等式と順序」部分だけを取り出す。 -/
-def TriominoWieferichShrinkWitnessB.toEq
+theorem TriominoWieferichShrinkWitnessB.toEq
     {p x y z q x' y' z' : ℕ}
     (hW : TriominoWieferichShrinkWitnessB p x y z q x' y' z') :
     TriominoWieferichShrinkWitnessEqB p x y z q x' y' z' :=
@@ -143,7 +143,7 @@ def TriominoWieferichShrinkWitnessB.toEq
     hyzLt := hW.hyzLt }
 
 /-- 完全 witness から「不変量」部分だけを取り出す。 -/
-def TriominoWieferichShrinkWitnessB.toInv
+theorem TriominoWieferichShrinkWitnessB.toInv
     {p x y z q x' y' z' : ℕ}
     (hW : TriominoWieferichShrinkWitnessB p x y z q x' y' z') :
     TriominoWieferichShrinkWitnessInvB p x y z q x' y' z' :=
@@ -153,7 +153,7 @@ def TriominoWieferichShrinkWitnessB.toInv
     hz0' := hW.hz0' }
 
 /-- `Eq / Inv` から従来の完全 witness を回収する。 -/
-def TriominoWieferichShrinkWitnessB.ofEqInv
+theorem TriominoWieferichShrinkWitnessB.ofEqInv
     {p x y z q x' y' z' : ℕ}
     (hEq : TriominoWieferichShrinkWitnessEqB p x y z q x' y' z')
     (hInv : TriominoWieferichShrinkWitnessInvB p x y z q x' y' z') :
@@ -179,7 +179,7 @@ structure TriominoWieferichShrinkCtorB
   hInv : TriominoWieferichShrinkWitnessInvB p x y z q x' y' z'
 
 /-- `ctor` から従来の完全 witness を回収する。 -/
-def TriominoWieferichShrinkCtorB.hW
+theorem TriominoWieferichShrinkCtorB.hW
     {p x y z q x' y' z' : ℕ}
     (c : TriominoWieferichShrinkCtorB p x y z q x' y' z') :
     TriominoWieferichShrinkWitnessB p x y z q x' y' z' :=
@@ -258,7 +258,7 @@ structure TriominoWieferichShrinkCandB (p z : ℕ) where
   hzlt : z' < z
 
 /-- 候補から prime-ge5 反例パックを組み直す。 -/
-def TriominoWieferichShrinkCandB.toPack
+theorem TriominoWieferichShrinkCandB.toPack
     {p z : ℕ}
     (hp5 : 5 ≤ p)
     (hp : Nat.Prime p)
@@ -486,7 +486,7 @@ theorem triominoWieferichShrink_q_dvd_x_core
   have hq_dvd_GN : q ∣ GN p (z - y) y := by
     exact dvd_trans hq_dvd_qpow hqpow_dvd_GN
   have hxpow : x ^ p = (z - y) * GN p (z - y) y := by
-    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
+    simpa [PrimeGe5CounterexamplePack.gap, PrimeCounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
   have hq_dvd_xpow : q ∣ x ^ p := by
     have hq_dvd_rhs : q ∣ (z - y) * GN p (z - y) y := by
       exact dvd_mul_of_dvd_right hq_dvd_GN (z - y)
@@ -829,7 +829,7 @@ def triominoWieferichShrink_xdiv_eq_mul_of_gap_GN_powers_data_core
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
   have hgap_body :
       x ^ p = (z - y) * GN p (z - y) y := by
-    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
+    simpa [PrimeGe5CounterexamplePack.gap, PrimeCounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
   have hpow_eq : (q * (x / q)) ^ p = (q * (u * v1)) ^ p := by
     calc
       (q * (x / q)) ^ p = x ^ p := by rw [← hxMul]
@@ -2237,6 +2237,21 @@ def TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec
     hpB' := hs.hpB'
     hInv := hs.hInv }
 
+@[simp] theorem TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec_x'
+    {p x y z q : ℕ} (c : TriominoWieferichShrinkNumsInvCandidateB p x y z q)
+    (hs : TriominoWieferichShrinkNumsInvCandidateSpecB p x y z q c) :
+    (TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec c hs).x' = c.x' := rfl
+
+@[simp] theorem TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec_y'
+    {p x y z q : ℕ} (c : TriominoWieferichShrinkNumsInvCandidateB p x y z q)
+    (hs : TriominoWieferichShrinkNumsInvCandidateSpecB p x y z q c) :
+    (TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec c hs).y' = c.y' := rfl
+
+@[simp] theorem TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec_z'
+    {p x y z q : ℕ} (c : TriominoWieferichShrinkNumsInvCandidateB p x y z q)
+    (hs : TriominoWieferichShrinkNumsInvCandidateSpecB p x y z q c) :
+    (TriominoWieferichShrinkNumsInvRecipeB.ofCandidateSpec c hs).z' = c.z' := rfl
+
 /-- `Recipe` から `KernelNums` を梱包する。 -/
 def TriominoWieferichShrinkNumsInvRecipeB.toNums
     {p x y z q : ℕ}
@@ -2310,6 +2325,60 @@ def triominoWieferichShrinkNumsInvCandidate_of_pack_clean
       y' := r0.y'
       z' := r0.z' }
 
+@[simp]
+theorem triominoWieferichShrinkNumsInvCandidate_of_pack_clean_x'
+    (hNW5 : TriominoNoWieferichBridge)
+    {p x y z q : ℕ}
+    (hpack : PrimeGe5CounterexamplePack p x y z)
+    (hpB : ¬ p ∣ z - y)
+    (hqP : Nat.Prime q)
+    (hq_not_dvd_gap : ¬ q ∣ z - y)
+    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
+    (triominoWieferichShrinkNumsInvCandidate_of_pack_clean
+      hNW5 hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' =
+    (triominoWieferichShrinkKernelNums_of_pack_clean
+      hNW5 hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).x' := by
+  simp [
+    triominoWieferichShrinkNumsInvCandidate_of_pack_clean,
+    triominoWieferichShrinkNumsInvRecipe_of_pack_clean
+  ]
+
+@[simp]
+theorem triominoWieferichShrinkNumsInvCandidate_of_pack_clean_y'
+    (hNW5 : TriominoNoWieferichBridge)
+    {p x y z q : ℕ}
+    (hpack : PrimeGe5CounterexamplePack p x y z)
+    (hpB : ¬ p ∣ z - y)
+    (hqP : Nat.Prime q)
+    (hq_not_dvd_gap : ¬ q ∣ z - y)
+    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
+    (triominoWieferichShrinkNumsInvCandidate_of_pack_clean
+      hNW5 hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' =
+    (triominoWieferichShrinkKernelNums_of_pack_clean
+      hNW5 hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).y' := by
+  simp [
+    triominoWieferichShrinkNumsInvCandidate_of_pack_clean,
+    triominoWieferichShrinkNumsInvRecipe_of_pack_clean
+  ]
+
+@[simp]
+theorem triominoWieferichShrinkNumsInvCandidate_of_pack_clean_z'
+    (hNW5 : TriominoNoWieferichBridge)
+    {p x y z q : ℕ}
+    (hpack : PrimeGe5CounterexamplePack p x y z)
+    (hpB : ¬ p ∣ z - y)
+    (hqP : Nat.Prime q)
+    (hq_not_dvd_gap : ¬ q ∣ z - y)
+    (hqpow_dvd_GN : q ^ p ∣ GN p (z - y) y) :
+    (triominoWieferichShrinkNumsInvCandidate_of_pack_clean
+      hNW5 hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' =
+    (triominoWieferichShrinkKernelNums_of_pack_clean
+      hNW5 hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN).z' := by
+  simp [
+    triominoWieferichShrinkNumsInvCandidate_of_pack_clean,
+    triominoWieferichShrinkNumsInvRecipe_of_pack_clean
+  ]
+
 /-- `_of_pack` backend から `x = q * x'` を回収する（clean）。 -/
 theorem triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack_clean
     (hNW5 : TriominoNoWieferichBridge)
@@ -2335,7 +2404,9 @@ theorem triominoWieferichShrinkNumsInvCandidate_hxmul_of_pack_clean
       hNW5
       (p := p) (x := x) (y := y) (z := z) (q := q)
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
-  simpa [triominoWieferichShrinkNumsInvCandidate_of_pack_clean, r0, n] using
+  simpa [triominoWieferichShrinkNumsInvCandidate_of_pack_clean,
+    triominoWieferichShrinkNumsInvRecipe_of_pack_clean,
+    TriominoWieferichShrinkNumsInvRecipeB.toNums, r0, n] using
     triominoWieferichShrinkKernel_hxmul_of_pack_clean
       hNW5
       (p := p) (x := x) (y := y) (z := z) (q := q)
@@ -2364,7 +2435,9 @@ theorem triominoWieferichShrinkNumsInvCandidate_hy_eq_of_pack_clean
       hNW5
       (p := p) (x := x) (y := y) (z := z) (q := q)
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
-  simpa [triominoWieferichShrinkNumsInvCandidate_of_pack_clean, r0, n] using
+  simpa [triominoWieferichShrinkNumsInvCandidate_of_pack_clean,
+    triominoWieferichShrinkNumsInvRecipe_of_pack_clean,
+    TriominoWieferichShrinkNumsInvRecipeB.toNums, r0, n] using
     triominoWieferichShrinkKernel_hy_eq_of_pack_clean
       hNW5
       (p := p) (x := x) (y := y) (z := z) (q := q)
@@ -3270,7 +3343,8 @@ theorem triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel
       rcases hfields with ⟨hx, hy, hz⟩
       rw [← hz, ← hy, ← hx]
       simpa [triominoWieferichShrinkKernelNums_of_pack_clean] using hEqb
-    simpa [c, triominoWieferichShrinkNumsInvCandidateB_kernel] using hEq_shadow
+    simpa [c, cs, triominoWieferichShrinkNumsInvCandidateB_kernel,
+      triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_default] using hEq_shadow
   have hx0' : c.x' ≠ 0 := by
     intro hx0
     apply hpack.hx0
@@ -3448,7 +3522,8 @@ theorem triominoWieferichShrinkNumsInvCandidateEqCore_of_kernel_clean
       rcases hfields with ⟨hx, hy, hz⟩
       rw [← hz, ← hy, ← hx]
       simpa [triominoWieferichShrinkKernelNums_of_pack_clean] using hEqb
-    simpa [c, triominoWieferichShrinkNumsInvCandidateB_kernel_clean] using hEq_shadow
+    simpa [c, cs, triominoWieferichShrinkNumsInvCandidateB_kernel_clean,
+      triominoWieferichShrinkNumsInvCandidate_div_eq_shadow_clean] using hEq_shadow
   have hx0' : c.x' ≠ 0 := by
     intro hx0
     apply hpack.hx0
@@ -3904,8 +3979,10 @@ theorem triominoWieferichShrinkNumsInvCandidate_hzlt_core
   have hzc : c.z' = cs.z' := by
     rfl
   have hzlt_shadow : cs.z' < z := by
-    simpa [hz] using hzlt_pack
-  simpa [hzc] using hzlt_shadow
+    rw [← hz]
+    exact hzlt_pack
+  rw [hzc]
+  exact hzlt_shadow
 
 /-- `Spec_of_kernel` 用に `hpB'` を先行回収する pack 依存 helper。 -/
 theorem triominoWieferichShrinkNumsInvCandidate_hpB'_of_pack
@@ -4030,7 +4107,8 @@ theorem triominoWieferichShrinkNumsInvCandidate_hpB'_core
   have hzc : c.z' = cs.z' := by
     rfl
   have hpB'_shadow : ¬ p ∣ (cs.z' - cs.y') := by
-    simpa [hy, hz] using hpB'_pack
+    rw [← hz, ← hy]
+    exact hpB'_pack
   intro hp_div
   have hp_div_c : p ∣ (c.z' - c.y') := by
     simpa [c] using hp_div
@@ -5316,10 +5394,15 @@ theorem triominoWieferichShrinkKernel_hxmul_of_core_path
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
   simpa
       [triominoWieferichShrinkKernelNumsB_kernel,
+        triominoWieferichShrinkKernelCoreB_kernel,
+        triominoWieferichShrinkNumsInvRecipeB_kernel,
+        triominoWieferichShrinkNumsInvCoreB_kernel,
+        triominoWieferichShrinkKernelNumsCoreB_kernel,
         triominoWieferichShrinkKernelSeedB_kernel,
         triominoWieferichShrinkKernelEqSeedB_kernel,
         triominoWieferichShrinkKernelEqSeedCoreB_kernel,
         triominoWieferichShrinkKernelEqSeedTraceB_kernel,
+        triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel,
         TriominoWieferichShrinkKernelCoreB.toSeed, c]
     using c.hxMul
 
@@ -5340,10 +5423,15 @@ theorem triominoWieferichShrinkKernel_hy_eq_of_core_path
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
   simpa
       [triominoWieferichShrinkKernelNumsB_kernel,
+        triominoWieferichShrinkKernelCoreB_kernel,
+        triominoWieferichShrinkNumsInvRecipeB_kernel,
+        triominoWieferichShrinkNumsInvCoreB_kernel,
+        triominoWieferichShrinkKernelNumsCoreB_kernel,
         triominoWieferichShrinkKernelSeedB_kernel,
         triominoWieferichShrinkKernelEqSeedB_kernel,
         triominoWieferichShrinkKernelEqSeedCoreB_kernel,
         triominoWieferichShrinkKernelEqSeedTraceB_kernel,
+        triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel,
         TriominoWieferichShrinkKernelCoreB.toSeed, c]
     using c.hyEq
 
@@ -5603,8 +5691,10 @@ theorem triominoWieferichShrinkNumsInvCandidate_hzlt_core_clean
   have hzc : c.z' = cs.z' := by
     rfl
   have hzlt_shadow : cs.z' < z := by
-    simpa [hz] using hzlt_pack
-  simpa [hzc] using hzlt_shadow
+    rw [← hz]
+    exact hzlt_pack
+  rw [hzc]
+  exact hzlt_shadow
 
 /-- clean kernel 用に `hpB'` を回収する core helper。 -/
 theorem triominoWieferichShrinkNumsInvCandidate_hpB'_core_clean
@@ -5676,7 +5766,8 @@ theorem triominoWieferichShrinkNumsInvCandidate_hpB'_core_clean
   have hzc : c.z' = cs.z' := by
     rfl
   have hpB'_shadow : ¬ p ∣ (cs.z' - cs.y') := by
-    simpa [hy, hz] using hpB'_pack
+    rw [← hz, ← hy]
+    exact hpB'_pack
   intro hp_div
   have hp_div_c : p ∣ (c.z' - c.y') := by
     simpa [c] using hp_div
@@ -6244,10 +6335,15 @@ theorem triominoWieferichShrinkKernel_hxmul_of_core_path_clean
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
   simpa
       [triominoWieferichShrinkKernelNumsB_kernel_clean,
+        triominoWieferichShrinkKernelCoreB_kernel_clean,
+        triominoWieferichShrinkNumsInvRecipeB_kernel_clean,
+        triominoWieferichShrinkNumsInvCoreB_kernel_clean,
+        triominoWieferichShrinkKernelNumsCoreB_kernel_clean,
         triominoWieferichShrinkKernelSeedB_kernel_clean,
         triominoWieferichShrinkKernelEqSeedB_kernel_clean,
         triominoWieferichShrinkKernelEqSeedCoreB_kernel_clean,
         triominoWieferichShrinkKernelEqSeedTraceB_kernel_clean,
+        triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel_clean,
         TriominoWieferichShrinkKernelCoreB.toSeed, c]
     using c.hxMul
 
@@ -6271,10 +6367,15 @@ theorem triominoWieferichShrinkKernel_hy_eq_of_core_path_clean
       hpack hpB hqP hq_not_dvd_gap hqpow_dvd_GN
   simpa
       [triominoWieferichShrinkKernelNumsB_kernel_clean,
+        triominoWieferichShrinkKernelCoreB_kernel_clean,
+        triominoWieferichShrinkNumsInvRecipeB_kernel_clean,
+        triominoWieferichShrinkNumsInvCoreB_kernel_clean,
+        triominoWieferichShrinkKernelNumsCoreB_kernel_clean,
         triominoWieferichShrinkKernelSeedB_kernel_clean,
         triominoWieferichShrinkKernelEqSeedB_kernel_clean,
         triominoWieferichShrinkKernelEqSeedCoreB_kernel_clean,
         triominoWieferichShrinkKernelEqSeedTraceB_kernel_clean,
+        triominoWieferichShrinkKernelEqSeedTraceCoreB_kernel_clean,
         TriominoWieferichShrinkKernelCoreB.toSeed, c]
     using c.hyEq
 
````
`````

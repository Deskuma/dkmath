# 残る２つの Error 対策

**Proved**

## 現在の残敵

```text
DkMath.RH.EulerZetaLemmas
DkMath.CosmicFormula.CosmicFormulaDim
```

`SevenRamifiedFusionCyclotomicSevenPID` を含む、数論・FLT・KUS・valuation 系の障害はすべて解消済み。残った二つは、どちらも **解析系の elaboration / instance 正規化問題**へ集中している。

## 二つは同じ種類の敵

ログに共通して現れているのは、数学的内容の失敗ではなく、同値な表現を Lean がそのまま同一視しなくなった問題じゃ。

### 関数表現

```lean
ofReal ∘ Prod.fst * Prod.snd
```

と、

```lean
fun p ↦ (p.1 : ℂ) * p.2
```

あるいは、

```lean
cexp ∘ fun u ↦ vertical σ u * Real.log p
```

と、

```lean
fun u ↦ cexp (vertical σ u * Real.log p)
```

の差。

### typeclass instance

```text
addCommGroup
instNormedAddCommGroup.toAddCommGroup
Real.instAddCommGroup
Real.normedAddCommGroup.toAddCommGroup
```

および、

```text
Semiring.toModule
RCLike.toInnerProductSpaceReal.toModule
instInnerProductSpaceRealComplex.toModule
NormedAlgebra.toNormedSpace ℂ
```

のように、数学的には同じ構造へ到達しているが、選択された instance の経路が異なる。

`EulerZetaLemmas` では特に、

```text
instContinuousSMulRealComplex_dkMath
```

という DkMath 独自 instance も goal に現れている。

これはかなり重要な信号じゃ。

## 本命原因

わっちの見立てでは、残り二つは別々に大量修正するより先に、

> **DkMath 側で定義している複素数上の scalar multiplication / normed-space instance が、新 mathlib の標準 instance と diamond を形成していないか**

を監査すべきじゃ。

特に `EulerZetaLemmas` のエラーには明示的に、

```text
instContinuousSMulRealComplex_dkMath
```

が入っている一方、実際に得られた証明項は mathlib 標準の、

```text
NormedAlgebra.toNormedSpace ℂ
```

や、

```text
RCLike.toInnerProductSpaceReal
```

を使っている。

つまり、

```text
DkMath 独自 instance
       ↘
        HasDerivAt / DifferentiableAt
       ↗
mathlib 標準 instance
```

という **解析 instance の二重経路**が発生している可能性が高い。

もし独自 instance が現在の mathlib では不要になっているなら、それを削除・局所化するだけで、両 target の多数のエラーが一斉に消える可能性がある。

## 攻略順序

### 1. 独自 instance の出所を確認

```bash
rg "instContinuousSMulRealComplex_dkMath" lean/dk_math
```

その定義が、

```lean
instance ...
```

として global 登録されているなら、まず現在の mathlib 標準 instance だけで成立するかを試す。

候補は、

```lean
local instance
```

への縮小、priority 調整、あるいは完全削除じゃ。

### 2. `EulerZetaLemmas` の最初のエラーを閉じる

最初の line 27 は比較的単純。

```lean
Continuous.mul
  (continuous_ofReal.comp continuous_fst)
  continuous_snd
```

から得た関数を、lambda 表現へ合わせればよい。

典型的には、

```lean
simpa only [Function.comp_apply, Pi.mul_apply]
```

または、

```lean
convert
  (continuous_ofReal.comp continuous_fst).mul continuous_snd using 1
```

じゃ。

ただし instance diamond が残ったままだと、後続の微分証明で再発する。

### 3. `EulerZetaLemmas` の derivative chain

残りはほぼ、

```lean
change ...
convert ... using 1
ext u
rfl
```

で composition と lambda を合わせる問題じゃ。

例えば、

```lean
have h :=
  (Complex.hasDerivAt_exp _).comp t hinner
change HasDerivAt
  (fun u ↦ Complex.exp (vertical σ u * lp))
  _ t
simpa only [Function.comp_apply] using h
```

という方向。

### 4. `CosmicFormulaDim`

こちらも同様に、`volConstC` の定義展開と pointwise 演算を明示する。

```lean
change DifferentiableAt
  (fun s ↦ Complex.exp (Complex.log π * (s / 2)) /
    Complex.Gamma (s / 2 + 1)) s
```

のように goal を証明項の表現へ合わせるか、逆に証明項側を `simpa only [volConstC, Function.comp_apply, Pi.mul_apply, Pi.div_apply]` で戻す。

`ring` の二箇所は、ログの提案どおり `ring_nf` でよい可能性が高い。

## 現在地の評価

```text
初回:
  12 failed targets

現在:
  2 failed targets

解消:
  10 targets
```

しかも残りは、

```text
RH の Euler 積解析
複素 Gamma / 次元宇宙式解析
```

という、同じ解析 instance 世界に固まった。

したがって今回の Lean 4.32.2 移行は、すでに **局所最終戦**へ入ったと見てよい。

README の現在地も、

```text
Initial failures: 12
Resolved: 10
Remaining: 2
```

へ更新できる段階じゃな。詳細報告が届いたら、`SevenRamifiedFusionCyclotomicSevenPID` の修正内容も migration pattern として正式に記録しよう。

# Git diff / Report / Review

## fix(upgrade): migrate cosmic dimension differentiation

gch: e6861c54941c8a749b4489badd2b7715301ad6e5

## Report

_

## Review

_

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean b/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean
index e24ae7ea..e5971244 100644
--- a/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/CosmicFormulaDim.lean
@@ -89,7 +89,7 @@ theorem cosmic_id (d : ℕ) (x u : ℝ) :
   -- 補題1と補題2より、二つの和が相殺されて u^d のみが残る
   rw [h1, h2]
   simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
-  ring
+  ring_nf
 
 
 /-! ### C: 解析接続の橋脚（体積定数） -/
@@ -522,7 +522,7 @@ lemma powPi_eq (s : ℂ) : powPi s = (π : ℂ)^(s/2) := by
   -- 版によっては `Complex.cpow_def` の名前が違うので調整
   simp [powPi, Complex.cpow_def]
   -- π は正の実数なので log π = log |π| + 0*I が成り立つ
-  ring
+  ring_nf
 
 /-- 「Gamma 側がちゃんとしている」ことを仮定する安全な局所条件 -/
 def VolGood (s : ℂ) : Prop :=
@@ -556,7 +556,8 @@ theorem differentiableAt_volConstC_of_good {s : ℂ} (hs : VolGood s) :
   have hden0 : (fun s => Complex.Gamma (s/2 + 1)) s ≠ 0 := hΓ0
   -- いよいよ本体
   -- `volConstC` の定義に合わせて `simp [volConstC]` を使う
-  simpa [volConstC] using hnum.div hden hden0
+  unfold volConstC
+  exact hnum.div hden hden0
 
 /-!
 次の一手：
@@ -584,7 +585,9 @@ lemma differentiableAt_one_div_Gamma_affine (s : ℂ) :
   -- 合成
   have h := h_outer.comp s h_inner
   -- 1/z = z⁻¹ を使って型を合わせる
-  simpa [div_eq_inv_mul, one_mul] using h
+  convert h using 1 <;> try rfl
+  funext z
+  simp only [Function.comp_apply, one_div]
 
 
 /-- `volConstC` は全域で正則（= entire）。 -/
@@ -604,7 +607,10 @@ theorem differentiableAt_volConstC (s : ℂ) :
     differentiableAt_one_div_Gamma_affine s
   -- 仕上げ：積の正則性
   -- `volConstC` の定義が `/` なら `div_eq_mul_inv` と `one_div` で合わせる
-  simpa [volConstC, div_eq_mul_inv, one_div] using hnum.mul hrec
+  unfold volConstC
+  convert hnum.mul hrec using 1 <;> try rfl
+  funext z
+  simp only [div_eq_mul_inv, one_div, mul_one, one_mul, Pi.mul_apply]
 
 
 /-- したがって `volConstC` は関数として全域で微分可能。 -/
@@ -712,7 +718,8 @@ theorem differentiableAt_ballVolC (r : ℝ) (s : ℂ) :
   -- volConstC は entire（既に証明済み）
   have h1 : DifferentiableAt ℂ volConstC s := differentiableAt_volConstC s
   have h2 : DifferentiableAt ℂ (fun s => rpowPos r s) s := differentiableAt_rpowPos r s
-  simpa using h1.mul h2
+  change DifferentiableAt ℂ (fun s : ℂ => volConstC s * rpowPos r s) s
+  exact h1.mul h2
 
 
 /-- r>0 かつ n : ℕ に対し、rpowPos r n = r^n （複素数冪乗） -/
@@ -1097,7 +1104,7 @@ theorem volConstR_odd_eval_prod (m : ℕ) :
       -- まとめ
       calc
         volConstR (2*(m+1) + 1)
-            = volConstR (2*m + 3) := by ring
+            = volConstR (2*m + 3) := by ring_nf
         _ = ((2 * Real.pi) * volConstR (2*m + 1)) / (2*m + 3 : ℝ) := by
               simpa using hsolve
         _ = ((2 * Real.pi) * ((2 : ℝ) * (2 * Real.pi)^m / oddDenomR m)) / (2*m + 3 : ℝ) := by
diff --git a/lean/dk_math/DkMath/RH/EulerZetaLemmas.lean b/lean/dk_math/DkMath/RH/EulerZetaLemmas.lean
index 68276404..c8b2c6d8 100644
--- a/lean/dk_math/DkMath/RH/EulerZetaLemmas.lean
+++ b/lean/dk_math/DkMath/RH/EulerZetaLemmas.lean
@@ -22,11 +22,6 @@ open DkMath.Basic
 open scoped Real
 open Complex
 
-instance : ContinuousSMul ℝ ℂ where
-  continuous_smul := by
-    simpa [Algebra.smul_def] using
-      (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
-
 /-
 補題のモジュール：Euler-zeta の等価性と基本変形
 
@@ -352,7 +347,7 @@ lemma hasDerivAt_vertical_mul_log_p
   have hmul : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I t := by
     simpa [one_mul] using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I
   have hvertical : HasDerivAt (fun u : ℝ => vertical σ u) Complex.I t := by
-    convert hmul.const_add (σ : ℂ) using 1
+    simpa [vertical] using hmul.const_add (σ : ℂ)
   simpa [mul_assoc] using hvertical.mul_const (Real.log (p : ℝ) : ℂ)
 
 /--
@@ -370,10 +365,12 @@ lemma hasDerivAt_eulerZeta_exp_s_log_p_sub_one
   unfold eulerZeta_exp_s_log_p_sub_one
   have hinner :=
     hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
-  convert
-      (((Complex.hasDerivAt_exp
-        (vertical σ t * (Real.log (p : ℝ) : ℂ))).comp t hinner).sub_const (1 : ℂ))
-      using 1
+  have h :=
+    (((Complex.hasDerivAt_exp
+      (vertical σ t * (Real.log (p : ℝ) : ℂ))).comp t hinner).sub_const (1 : ℂ))
+  change HasDerivAt
+    (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ)) - 1) _ t
+  simpa only [Function.comp_apply] using h
 
 /--
 `w_p` の導関数の `deriv` 版。
@@ -450,8 +447,9 @@ lemma hasDerivAt_deriv_eulerZeta_exp_s_log_p_sub_one
       HasDerivAt
         (fun u : ℝ => Complex.exp (vertical σ u * lp))
         (Complex.exp (vertical σ t * lp) * (Complex.I * lp)) t := by
-    simpa [lp] using
-      (Complex.hasDerivAt_exp (vertical σ t * lp)).comp t hinner
+    have h := (Complex.hasDerivAt_exp (vertical σ t * lp)).comp t hinner
+    change HasDerivAt (fun u : ℝ => Complex.exp (vertical σ u * lp)) _ t
+    simpa [lp, Function.comp_def] using h
   have hmul := hexp.mul_const (Complex.I * lp)
   simpa [lp, mul_assoc] using hmul
 
@@ -579,7 +577,9 @@ lemma differentiableAt_eulerZetaExpSubOneFinite
       have hd_p :
           DifferentiableAt ℝ (fun u : ℝ => eulerZeta_exp_s_log_p_sub_one p.1 σ u) t :=
         (hasDerivAt_eulerZeta_exp_s_log_p_sub_one (p := p.1) (σ := σ) (t := t)).differentiableAt
-      simpa [eulerZetaExpSubOneFinite, hp] using hd_p.mul ih
+      unfold eulerZetaExpSubOneFinite
+      convert hd_p.mul ih using 1 <;>
+        first | rfl | (funext u; simp [eulerZetaExpSubOneFinite, hp])
 
 /--
 `insert` 1ステップ版の積→和補題。
@@ -716,7 +716,9 @@ lemma phaseVel_exp_vertical_mul_log_p_eq_log
     have hinner :
         HasDerivAt (fun u : ℝ => vertical σ u * lp) (Complex.I * lp) t := by
       simpa [lp] using hasDerivAt_vertical_mul_log_p (p := p) (σ := σ) (t := t)
-    simpa [lp] using ((Complex.hasDerivAt_exp (vertical σ t * lp)).comp t hinner).deriv
+    have h := ((Complex.hasDerivAt_exp (vertical σ t * lp)).comp t hinner).deriv
+    change deriv (fun u : ℝ => Complex.exp (vertical σ u * lp)) t = _
+    simpa [lp, Function.comp_def] using h
   unfold DkMath.RH.phaseVel
   change
     (((deriv (fun u : ℝ => Complex.exp (vertical σ u * (Real.log (p : ℝ) : ℂ))) t) /
@@ -807,7 +809,9 @@ lemma differentiableAt_eulerZetaFactorVerticalExpFinite_of_ne
       have hd_S :
           DifferentiableAt ℝ (fun u : ℝ => eulerZetaFactorVerticalExpFinite (S := S) σ u) t :=
         ih hS_ne'
-      simpa [eulerZetaFactorVerticalExpFinite, hp] using hd_p.mul hd_S
+      unfold eulerZetaFactorVerticalExpFinite
+      convert hd_p.mul hd_S using 1 <;>
+        first | rfl | (funext u; simp [eulerZetaFactorVerticalExpFinite, hp])
 
 /--
 exp 形 Euler 因子有限積の位相速度は、局所位相速度寄与の有限和に一致する。
````
`````

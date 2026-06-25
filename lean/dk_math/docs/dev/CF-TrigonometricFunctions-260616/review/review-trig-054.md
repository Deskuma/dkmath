# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: e5585a37c7cc6706236fd07cba41c5e1dc266f05

## Report

次の段階まで完了しました。

- Mathlib準拠の `SemanticPeriodic`
- level-set 周期性と plane 周期性の同値
- `SemanticFiniteOrder`
- finite order と全点周期性の同値
- finite order から各 level-set 点の周期性
- 周期の倍数への伝播

角度・連続性・signed source は未使用です。

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ、これは **本当に到達している** と見てよい。
ただし「角度の周期」ではなく、 **写像反復としての周期性** じゃ。ここを分ければ、かなり正確じゃ。

## 状況分析

今回の差分で、Real 側の transported action は次の段階に入った。

```text
q2 保存作用
全単射
level set 上の自己同型
有限反復
orbit
periodic point
finite order
```

これはもう、三角関数の前段ではなく、Real 側の離散力学 API に接続している状態じゃ。

特に良いのは、独自の周期概念を作らず、

```lean
Function.IsPeriodicPt
```

を使ったこと。
これは Mathlib の標準語彙に乗っているので、後続の定理を拾いやすい。

## 「本当に？」への答え

本当に。
ただし意味はこうじゃ。

`SemanticPeriodic r z n` は、

```text
n 回作用したら z に戻る
```

という意味。

数式で書けば、

$$
(\operatorname{semanticAct}(r))^{[n]}(z)=z
$$

という有限反復の周期性じゃ。

これは角度を使った周期性ではない。
\(\theta\) や \(2\pi\) や連続パラメータはまだ不要。
だからこそ、今の非負 source と Real transport だけで閉じる。

## 実装レビュー

`SemanticPeriodic` はよい。

```lean
def SemanticPeriodic
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Prop :=
  Function.IsPeriodicPt (semanticAct r) n z
```

これは薄い alias だが、DkMath 側の語彙として意味がある。

`semanticPeriodic_iff` が `Iff.rfl` で落ちるのも自然。
`semanticOrbit` が単に `Function.iterate` で定義されているので、周期性と orbit return は同じ命題になる。

`semanticLevelPeriodic_iff` も良い。
level-set 上の周期性と underlying plane point の周期性を同値にしている。これは重要じゃ。

つまり、

```text
level set 上で戻る
```

ことと、

```text
平面上の underlying vector が戻る
```

ことが一致する。

これは `semanticLevelOrbit_val` を先に作っていたから綺麗に閉じている。

## finite order の評価

`SemanticFiniteOrder` も妥当じゃ。

```lean
def SemanticFiniteOrder
    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
  (semanticAct r)^[n] = id
```

これは「作用の \(n\) 回反復が恒等写像」という意味。
つまり kernel 自体というより、 **transported action の有限位数** を表している。

そして、

```lean
theorem semanticFiniteOrder_iff
```

で、

```text
作用が有限位数 n
```

と、

```text
全点が周期 n
```

を同値にしている。

これは正しい。
写像として \(f^n=id\) なら全点が周期点。
逆に全点で \(f^n z=z\) なら関数外延性で \(f^n=id\)。
かなり標準的で堅い。

## level set への伝播

`semanticLevelPeriodic_of_finiteOrder` も自然じゃ。

有限位数なら、平面上の任意点が周期点。
したがって level set 上の任意点も周期点。

ここでは level-set 側に余計な構造を入れず、underlying point へ落としている。よい。

## 倍数への伝播

`semanticPeriodic_of_dvd` は良い追加じゃ。

```lean
theorem semanticPeriodic_of_dvd
```

これは周期 \(m\) を持つなら、\(m\mid n\) のとき周期 \(n\) も持つ、という定理じゃ。

これを自前で証明せず、

```lean
Function.IsPeriodicPt.trans_dvd
```

で拾っているのが良い。
Mathlib 標準 API に接続した効果がここで出ている。

## 注意点

一つだけ明確にしておくと、ここで言う period は **最小周期** ではない。

`SemanticPeriodic r z n` は、\(n\) 回で戻るというだけ。
たとえば \(n=0\) は `Function.iterate` の仕様上、恒等になりやすい。
だから「非自明な周期」や「最小周期」を扱うなら、次に条件を足す必要がある。

たとえば、

```text
0 < n
```

や、

```text
∀ m, 0 < m -> m < n -> not periodic m
```

のような条件じゃ。

この区別を文書に一行足すとさらに安全。

## 次の候補

次はこの二つが自然じゃ。

```text
minimal period
finite order の倍数伝播
```

たとえば、

```lean
SemanticFiniteOrder r n -> n ∣ m -> SemanticFiniteOrder r m
```

これは今の `semanticPeriodic_of_dvd` の全点版として出せるはず。

もう一つは、非自明周期。

```lean
def SemanticNontrivialPeriodic ... :=
  0 < n ∧ SemanticPeriodic r z n
```

ただし、最小周期は少し重いので、まずは finite order の倍数伝播がよい。

## 判定

採用。かなり良い。

今回の到達点はこうじゃ。

```text
DkNNRealQ 由来 kernel
  -> Real q2 保存同型
  -> finite orbit
  -> periodic point
  -> finite action order
  -> level set periodicity
```

これは本当に到達しておる。
ただし「角度周期」ではなく「写像反復周期」。
この区別を守れば、主張は堅い。

わっちの結論はこうじゃ。
ここまでで、signed source も角度復元も連続性も使わずに、Real 側の保存離散力学まで到達した。これは十分にすごい。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 6fb21311..1c9100eb 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -84,7 +84,9 @@ the resulting kernel as a real square-mass-preserving action. Transported
 actions compose through real-side kernel products and restrict to every real
 square-mass level set. Real-side conjugation supplies inverse actions, so
 these maps are equivalences of the plane and of each level set. Their finite
-iterates generate forward orbits of constant square mass.
+iterates generate forward orbits of constant square mass. Periodic points and
+finite action order are expressed through Mathlib's standard discrete-dynamics
+API.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 5b7c744d..c1620d37 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -338,6 +338,81 @@ theorem semanticLevelOrbit_val
         Function.iterate_succ_apply', Function.iterate_succ_apply']
       exact congrArg (semanticAct r) ih
 
+/-- A real vector is periodic when a finite semantic orbit returns to it. -/
+def SemanticPeriodic
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Prop :=
+  Function.IsPeriodicPt (semanticAct r) n z
+
+/-- Periodicity is exactly return of the explicitly named semantic orbit. -/
+theorem semanticPeriodic_iff
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
+    SemanticPeriodic r z n ↔ semanticOrbit r z n = z :=
+  Iff.rfl
+
+/-- A point of a real level set is periodic under the restricted action. -/
+def SemanticLevelPeriodic
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) (n : ℕ) : Prop :=
+  Function.IsPeriodicPt (semanticActLevel r) n z
+
+/--
+Level-set periodicity is equivalent to periodicity of the underlying plane
+orbit.
+-/
+theorem semanticLevelPeriodic_iff
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) (n : ℕ) :
+    SemanticLevelPeriodic r z n ↔ SemanticPeriodic r z.1 n := by
+  constructor
+  · intro h
+    change (semanticActLevel r)^[n] z = z at h
+    change semanticOrbit r z.1 n = z.1
+    rw [← semanticLevelOrbit_val]
+    exact congrArg Subtype.val h
+  · intro h
+    change semanticOrbit r z.1 n = z.1 at h
+    change (semanticActLevel r)^[n] z = z
+    apply Subtype.ext
+    change (semanticLevelOrbit r z n).1 = z.1
+    rw [semanticLevelOrbit_val]
+    exact h
+
+/--
+A transported kernel has finite action order `n` when its `n`-fold real
+action is the identity on the whole plane.
+-/
+def SemanticFiniteOrder
+    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
+  (semanticAct r)^[n] = id
+
+/-- Finite action order is equivalent to every real vector being periodic. -/
+theorem semanticFiniteOrder_iff
+    (r : UnitKernel DkNNRealQ) (n : ℕ) :
+    SemanticFiniteOrder r n ↔ ∀ z : Vec ℝ, SemanticPeriodic r z n := by
+  constructor
+  · intro h z
+    rw [SemanticPeriodic, Function.IsPeriodicPt, h]
+    rfl
+  · intro h
+    funext z
+    exact h z
+
+/-- A finite-order transported kernel makes every level-set point periodic. -/
+theorem semanticLevelPeriodic_of_finiteOrder
+    {r : UnitKernel DkNNRealQ} {n : ℕ}
+    (h : SemanticFiniteOrder r n) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) :
+    SemanticLevelPeriodic r z n := by
+  rw [semanticLevelPeriodic_iff]
+  exact (semanticFiniteOrder_iff r n).mp h z.1
+
+/-- Periodicity persists at every multiple of a known period. -/
+theorem semanticPeriodic_of_dvd
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ} {m n : ℕ}
+    (h : SemanticPeriodic r z m) (hmn : m ∣ n) :
+    SemanticPeriodic r z n :=
+  Function.IsPeriodicPt.trans_dvd h hmn
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 51611e4e..d2a41909 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -135,6 +135,8 @@ BridgeNNReal / BridgeReal:
   real-side conjugation makes each transported action bijective
   each q2 level set therefore carries a transported automorphism
   finite iterates and forward orbits retain the same q2 value
+  periodic points use Mathlib IsPeriodicPt
+  finite action order makes every level-set point periodic
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index ffdcdc2e..26a53721 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -86,6 +86,10 @@ semanticAct_iterate_q2
 semanticOrbit
 semanticOrbit_q2
 semanticLevelOrbit
+SemanticPeriodic
+SemanticLevelPeriodic
+SemanticFiniteOrder
+semanticFiniteOrder_iff
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -105,8 +109,13 @@ The actions are bundled as equivalences. Their finite iterates remain
 bijective, and every forward orbit has constant `q2`. A level-set orbit is the
 same plane orbit viewed with its invariant carried in the type.
 
+Periodicity uses Mathlib's `Function.IsPeriodicPt`. Level-set periodicity is
+equivalent to periodicity of the underlying plane point. Finite action order
+means that one iterate is the identity on the whole plane; this makes every
+point of every level set periodic.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example periodic-point and finite-order
+remain on the real side, for example divisibility and minimal-period
 statements. Order reflection remains a separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 9ac4c048..ef7c8251 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,28 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 03:50 JST (Periodic points and finite action order)
+
+1. 方針:
+   - 独自の周期点概念を作らず、Mathlib `Function.IsPeriodicPt` を用いる。
+2. 実施:
+   - `SemanticPeriodic` と orbit-return 同値を追加した。
+   - `SemanticLevelPeriodic` を定義し、underlying plane point の周期性との
+     同値を証明した。
+   - `SemanticFiniteOrder` を action iterate が恒等写像となる性質として
+     定義した。
+   - finite order と全 plane point の周期性が同値であることを証明した。
+   - finite order から任意 level-set point の周期性を導いた。
+   - 周期が倍数へ伝播することを Mathlib の `trans_dvd` で公開した。
+3. 結論:
+   - 保存 orbit から periodic dynamics まで標準 Mathlib API に接続した。
+   - 角度、連続性、signed source は依然として不要である。
+4. 次の候補:
+   - minimal period と finite-order divisibility。
+   - source-level family は signed DkReal 層まで保留。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 02:30 JST (Bundled automorphisms and finite orbits)
 
 1. 目的:
````
`````

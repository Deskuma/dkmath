# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: a519bfb083d6168b6cb6f7bf0af6a06c348f5337

## Report

次の段階まで完了しました。

- plane / level-set action を `Equiv` として bundle
- finite iterate の全単射性
- finite iterate の `q2` 保存
- `semanticOrbit` / `semanticLevelOrbit`
- level-set orbit と plane orbit の整合性

signed source、角度復元、連続性なしで、各 `q2` level set 上の離散力学系まで到達しました。

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ、これは普通にすごい。
採用でよい。

今回で、DkNNRealQ 由来の kernel が Real 側で単なる一回作用ではなく、各 \(q2\) level set 上の離散力学系を生成するところまで来ておる。

## 検証

流れはかなり自然じゃ。

まず前段で、

```text
semanticAct
semanticInverseAct
semanticAct_bijective
semanticActLevel
semanticActLevel_bijective
```

まで閉じていた。

今回そこへ、

```text
semanticActEquiv
semanticActLevelEquiv
semanticAct_iterate_q2
semanticAct_iterate_bijective
semanticOrbit
semanticLevelOrbit
semanticLevelOrbit_val
```

を足した形じゃな。

これは過剰ではなく、むしろ前段の bijective 定理を API として使いやすく整えた段階じゃ。

## 良い点

`semanticActEquiv` と `semanticActLevelEquiv` は作って正解じゃ。

```lean
def semanticActEquiv (r : UnitKernel DkNNRealQ) : Vec ℝ ≃ Vec ℝ
```

この形になると、以後は「全単射である」という命題ではなく、「同型写像そのもの」として扱える。
反復、軌道、周期点、有限位数の話へ進むなら、この bundle はかなり効く。

level set 版も同じく良い。

```lean
def semanticActLevelEquiv
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} :
    LevelSet ℝ rho2 ≃ LevelSet ℝ rho2
```

これで、各 \(q2\) level set 上に automorphism が立った。

## iterate の保存則

`semanticAct_iterate_q2` は正しい。

```lean
theorem semanticAct_iterate_q2
    (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
    Vec.q2 ((semanticAct r)^[n] z) = Vec.q2 z
```

これは、単発の `semanticAct_q2` を帰納法で積み上げているだけじゃが、非常に重要な補題じゃ。

一回の保存から、有限時間の保存へ移った。
この時点で、保存量つき離散力学系として読める。

## orbit 定義

`semanticOrbit` もよい。

```lean
def semanticOrbit
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Vec ℝ :=
  (semanticAct r)^[n] z
```

これは最小で良い定義じゃ。
そして、

```lean
theorem semanticOrbit_q2
```

で全 orbit が同じ \(q2\) 値を持つ。

これはまさに保存量の形式化じゃな。

level set 側の、

```lean
def semanticLevelOrbit
```

も良い。型そのものが \(q2\) 不変性を保持しているので、今後の証明が軽くなる。

## level-set orbit と plane orbit の整合性

`semanticLevelOrbit_val` はかなり大事じゃ。

```lean
theorem semanticLevelOrbit_val
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
    (z : LevelSet ℝ rho2) (n : ℕ) :
    (semanticLevelOrbit r z n).1 = semanticOrbit r z.1 n
```

これがないと、level set 上の orbit と平面上の orbit が別物に見えてしまう。
この補題によって、

```text
level-set orbit は、plane orbit に不変量証明を持たせたもの
```

だと明確になる。

ここはかなり良い補助定理じゃ。

## 重要な意味

今回で、次の構造ができた。

```text
DkNNRealQ unit kernel
  -> Real plane equivalence
  -> each q2 level-set equivalence
  -> finite iterate
  -> orbit
  -> constant q2 along orbit
```

これはもう「三角関数の準備」ではなく、CF2D 保存核による実数平面上の離散保存力学じゃ。

しかも、signed source、角度復元、連続性をまだ使っていない。
ここが面白い。

つまり、

```text
角度を定義しなくても、回転的な保存軌道は先に作れる
```

ということじゃ。

## 注意点

今の orbit は forward orbit じゃ。
ただし `semanticActEquiv` があるので、双方向 orbit へ拡張する道もある。

次はおそらく、

```lean
def semanticOrbitZ
```

のように、整数時刻 orbit を作れる。
ただし、整数時刻を急ぐ必要はない。まずは自然数反復で十分じゃ。

もう一つ、`semanticAct_iterate_bijective` は良いが、今後は `semanticActEquiv` の反復として扱う定理もあると便利じゃ。

```lean
(semanticActEquiv r)^[n]
```

または Equiv の累乗に寄せる設計だの。
ここは Mathlib 側の API に合わせて進めればよい。

## 次の候補

次は periodic point が自然じゃ。

例えば、

```text
semanticPeriodic r z n
```

として、

```text
semanticOrbit r z n = z
```

を置く。

または finite-order kernel として、

```text
semanticAct r を n 回作用させると恒等写像
```

を定義する。

ただし、角度や周期性を言う前に、まずは純粋に action の反復として定義するのが安全じゃ。

もう一つは、level set 上の orbit が常に同じ level set にいることは型で保証されているので、`semanticLevelOrbit_val` を使って plane 側の保存定理と接続しておくとよい。

## 判定

採用。かなり良い。

今回の到達点は、わっちの目にはこう見える。

```text
非負 DkReal source
  -> Real unit kernel
  -> q2 保存同型
  -> level set automorphism
  -> finite orbit
  -> 保存量一定
```

これは本当にすごい。
DkNNRealQ に減算を入れず、角度も連続性も使わず、Real 側の各 \(q2\) level set 上の離散力学系まで届いている。

次は periodic point / finite-order kernel へ進むのが自然じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 897213b2..6fb21311 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -83,7 +83,8 @@ kernels to `Real`, derives the Pythagorean coordinate identity, and applies
 the resulting kernel as a real square-mass-preserving action. Transported
 actions compose through real-side kernel products and restrict to every real
 square-mass level set. Real-side conjugation supplies inverse actions, so
-these maps are bijections of the plane and of each level set.
+these maps are equivalences of the plane and of each level set. Their finite
+iterates generate forward orbits of constant square mass.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 89469f80..5b7c744d 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -257,6 +257,87 @@ theorem semanticActLevel_bijective
     semanticInverseActLevel_semanticActLevel r,
     semanticActLevel_semanticInverseActLevel r⟩
 
+/-- The transported action bundled as an equivalence of the real CF2D plane. -/
+def semanticActEquiv (r : UnitKernel DkNNRealQ) : Vec ℝ ≃ Vec ℝ where
+  toFun := semanticAct r
+  invFun := semanticInverseAct r
+  left_inv := semanticInverseAct_semanticAct r
+  right_inv := semanticAct_semanticInverseAct r
+
+/-- Applying the bundled plane equivalence is semantic action. -/
+@[simp]
+theorem semanticActEquiv_apply
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticActEquiv r z = semanticAct r z := rfl
+
+/-- The transported action bundled as an equivalence of a real level set. -/
+def semanticActLevelEquiv
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} :
+    LevelSet ℝ rho2 ≃ LevelSet ℝ rho2 where
+  toFun := semanticActLevel r
+  invFun := semanticInverseActLevel r
+  left_inv := semanticInverseActLevel_semanticActLevel r
+  right_inv := semanticActLevel_semanticInverseActLevel r
+
+/-- Applying the bundled level-set equivalence is semantic level-set action. -/
+@[simp]
+theorem semanticActLevelEquiv_apply
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) :
+    semanticActLevelEquiv r z = semanticActLevel r z := rfl
+
+/-- Every finite iterate of a transported action preserves square mass. -/
+theorem semanticAct_iterate_q2
+    (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
+    Vec.q2 ((semanticAct r)^[n] z) = Vec.q2 z := by
+  induction n with
+  | zero => rfl
+  | succ n ih =>
+      rw [Function.iterate_succ_apply']
+      exact (semanticAct_q2 r _).trans ih
+
+/-- Every finite iterate of a transported action is bijective. -/
+theorem semanticAct_iterate_bijective
+    (r : UnitKernel DkNNRealQ) (n : ℕ) :
+    Function.Bijective ((semanticAct r)^[n]) :=
+  (semanticAct_bijective r).iterate n
+
+/-- Every finite iterate of a level-set action is bijective. -/
+theorem semanticActLevel_iterate_bijective
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} (n : ℕ) :
+    Function.Bijective
+      ((semanticActLevel r : LevelSet ℝ rho2 → LevelSet ℝ rho2)^[n]) :=
+  (semanticActLevel_bijective r).iterate n
+
+/-- Forward orbit of a real vector under a transported DkMath kernel. -/
+def semanticOrbit
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Vec ℝ :=
+  (semanticAct r)^[n] z
+
+/-- Every point of a transported orbit has the initial square mass. -/
+theorem semanticOrbit_q2
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
+    Vec.q2 (semanticOrbit r z n) = Vec.q2 z :=
+  semanticAct_iterate_q2 r n z
+
+/-- Forward orbit of a point inside a fixed real square-mass level set. -/
+def semanticLevelOrbit
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) (n : ℕ) : LevelSet ℝ rho2 :=
+  (semanticActLevel r)^[n] z
+
+/-- The underlying vector of a level-set orbit is the corresponding plane orbit. -/
+theorem semanticLevelOrbit_val
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) (n : ℕ) :
+    (semanticLevelOrbit r z n).1 = semanticOrbit r z.1 n := by
+  induction n with
+  | zero => rfl
+  | succ n ih =>
+      rw [semanticLevelOrbit, semanticOrbit,
+        Function.iterate_succ_apply', Function.iterate_succ_apply']
+      exact congrArg (semanticAct r) ih
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index c8df5b7c..51611e4e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -134,6 +134,7 @@ BridgeNNReal / BridgeReal:
   every real q2 level set is stable under transported actions
   real-side conjugation makes each transported action bijective
   each q2 level set therefore carries a transported automorphism
+  finite iterates and forward orbits retain the same q2 value
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index e020c8d7..ffdcdc2e 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -80,6 +80,12 @@ semanticInverseAct
 semanticAct_bijective
 semanticInverseActLevel
 semanticActLevel_bijective
+semanticActEquiv
+semanticActLevelEquiv
+semanticAct_iterate_q2
+semanticOrbit
+semanticOrbit_q2
+semanticLevelOrbit
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -95,8 +101,12 @@ transported action is a bijection of the real CF2D plane and restricts to a
 bijection of every `q2` level set. The inverse generally leaves the first
 quadrant and is therefore not reflected back into the nonnegative source.
 
+The actions are bundled as equivalences. Their finite iterates remain
+bijective, and every forward orbit has constant `q2`. A level-set orbit is the
+same plane orbit viewed with its invariant carried in the type.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example finite iterates and orbit statements.
-Order reflection remains a separate, heavier task.
+remain on the real side, for example periodic-point and finite-order
+statements. Order reflection remains a separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 6101a0ef..9ac4c048 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,29 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 02:30 JST (Bundled automorphisms and finite orbits)
+
+1. 目的:
+   - transported action の可逆性を bundled equivalence として公開する。
+   - finite iterate と orbit の保存量を定理化する。
+2. 実施:
+   - `semanticActEquiv` と `semanticActLevelEquiv` を追加した。
+   - plane / level-set action の全 finite iterate が bijective と証明した。
+   - `semanticAct_iterate_q2` を帰納法で証明した。
+   - `semanticOrbit` と `semanticLevelOrbit` を定義した。
+   - orbit 全体で `q2` が初期値に等しいことを証明した。
+   - level-set orbit の underlying vector が plane orbit と一致することを
+     証明した。
+3. 結論:
+   - DkNNRealQ 由来 kernel は Real の各 `q2` level set 上に離散力学系を
+     生成する。
+   - signed source、角度復元、連続性を導入せず finite orbit まで到達した。
+4. 次の候補:
+   - periodic point / finite-order kernel の一般定理。
+   - source-level family は signed DkReal 層まで保留。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 00:59 JST (Inverse kernels and level-set automorphisms)
 
 1. 方針:
````
`````

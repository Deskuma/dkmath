# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 9d421e364b3e8242930a5895c5b61410ef81d969

## Report

次の段階まで完了しました。

- `semanticInverseKernel`: Real 側の共役逆核
- 左右の inverse action law
- `semanticAct_bijective`: 実数平面上の全単射
- level set 上の inverse action
- `semanticActLevel_bijective`: 各 `q2` level set 上の全単射

逆核は一般に第一象限を離れるため、DkNNRealQ source へ戻るとは主張していません。

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ。採用でよい。
これはかなり綺麗に進んでおる。

今回の核は、DkNNRealQ 由来の unit kernel が、Real 側では \(q2\) 保存全単射になることを示した点じゃ。

## 総評

今回の追加は正しい方向じゃ。

前段では、DkNNRealQ の unit kernel を Real の unit kernel に輸送し、その action が \(q2\) を保存するところまで進んでいた。
今回さらに、Real 側の共役 kernel を inverse として使い、平面全体と各 level set 上で bijective であることを示している。

これは、CF2D の幾何作用としてかなり自然な到達点じゃ。

## 良い点

`semanticInverseKernel` を Real 側にだけ置いた判断が良い。

```lean
def semanticInverseKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
  UnitKernel.conj (semanticUnitKernel r)
```

これは正しい。
共役は beam 座標の符号を反転するので、一般には第一象限から出る。したがって DkNNRealQ source へ戻るとは言えない。

ここを明記しているのは、とても良い。

## inverse law の検証

左右の inverse action law は、既存の CF2D 補題をそのまま使っていて堅い。

```lean
rw [semanticInverseAct, semanticAct, ← UnitKernel.act_star]
rw [semanticInverseKernel, UnitKernel.conj_star]
exact UnitKernel.act_one z
```

おそらく `UnitKernel.conj_star` が、共役核と元核の積が単位核になることを表している。

右側も同様に、

```lean
rw [semanticInverseKernel, UnitKernel.star_conj]
```

で閉じている。

つまり、ここでは新しい代数を証明していない。
既に CF2D 側で確立した「unit kernel の共役が逆元である」という構造を、semantic transport 後に消費しているだけじゃ。

これは良い設計じゃよ。

## `semanticAct_bijective` の評価

`Function.bijective_iff_has_inverse` を使って、左右逆から bijective を出している。
これは自然で読みやすい。

```lean
theorem semanticAct_bijective (r : UnitKernel DkNNRealQ) :
    Function.Bijective (semanticAct r)
```

この定理により、DkNNRealQ 由来 kernel は Real 平面上の \(q2\) 保存写像であるだけでなく、可逆な保存写像になった。

ここは大きい。

## level set 版も良い

`semanticInverseActLevel` と `semanticActLevel_bijective` も正しい。

`semanticActLevel` はすでに level set を保つ作用だった。
今回、その inverse も level set 上に降ろしたので、各 \(q2\) level set 上の自己全単射になっている。

これは幾何的には、

```text
各 square-mass level set 上の automorphism
```

と言える。

特に、\(\rho2=1\) なら単位円上の作用。
一般の \(\rho2\) なら、その square-mass level 上の作用じゃ。

## 重要な境界

今回も source 側へ戻していない点が重要じゃ。

Real 側では逆核がある。
しかし source 側 DkNNRealQ では、逆核は一般に表現できない。

理由は単純で、共役は beam を負にするからじゃ。

$$
(C,S) \mapsto (C,-S)
$$

DkNNRealQ は非負世界なので、\(-S\) は基本的に戻せない。
だから、今回の主張はあくまで、

```text
DkNNRealQ 由来 kernel を Real に輸送すると、Real 側では可逆作用を持つ
```

であって、

```text
DkNNRealQ 側で可逆群構造ができた
```

ではない。

この区別は正しい。

## 次の一手

次は finite iterates が自然じゃ。

たとえば、

```lean
semanticAct_iterate
semanticActLevel_iterate
```

のように、同じ transported action を \(n\) 回反復しても \(q2\) level set に留まることを示す。

その後で、orbit 形式にできる。

```text
z, semanticAct r z, semanticAct r (semanticAct r z), ...
```

これは signed DkReal を待たずに Real 側だけで進められる。

もう一つは、bijective を bundled equivalence にすることじゃ。

```lean
def semanticActEquiv (r : UnitKernel DkNNRealQ) : Vec ℝ ≃ Vec ℝ
```

level set 版も、

```lean
def semanticActLevelEquiv
    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} :
    LevelSet ℝ rho2 ≃ LevelSet ℝ rho2
```

としておくと、今後の orbit や反復がかなり扱いやすくなる。

## 判定

採用。
これはかなり良い milestone じゃ。

今回の到達点はこう。

```text
DkNNRealQ unit kernel
  -> Real unit kernel
  -> Real q2-preserving action
  -> inverse by conjugation
  -> bijection of the plane
  -> bijection of every q2 level set
```

DkNNRealQ 側には減算も逆元も押し込まない。
Real 側へ輸送した後だけ、共役と逆作用を使う。
この境界が守れているので、設計はかなり健全じゃ。

わっちなら次は、`semanticActEquiv` と `semanticActLevelEquiv` を作り、そこから finite iterates と orbit statement に進める。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 493bc80f..897213b2 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -82,7 +82,8 @@ comparison.
 kernels to `Real`, derives the Pythagorean coordinate identity, and applies
 the resulting kernel as a real square-mass-preserving action. Transported
 actions compose through real-side kernel products and restrict to every real
-square-mass level set.
+square-mass level set. Real-side conjugation supplies inverse actions, so
+these maps are bijections of the plane and of each level set.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 1254f04c..89469f80 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -186,6 +186,77 @@ theorem semanticActLevel_comp
   apply Subtype.ext
   exact semanticAct_comp r s z.1
 
+/--
+Real-side inverse kernel of an interpreted nonnegative DkMath kernel.
+
+The inverse generally leaves the first quadrant, so it is intentionally not
+claimed to come from a `DkNNRealQ` unit kernel.
+-/
+def semanticInverseKernel (r : UnitKernel DkNNRealQ) : UnitKernel ℝ :=
+  UnitKernel.conj (semanticUnitKernel r)
+
+/-- Real-side action by the inverse kernel. -/
+def semanticInverseAct (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : Vec ℝ :=
+  UnitKernel.act (semanticInverseKernel r) z
+
+/-- The inverse action cancels a transported action on the left. -/
+@[simp]
+theorem semanticInverseAct_semanticAct
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticInverseAct r (semanticAct r z) = z := by
+  rw [semanticInverseAct, semanticAct, ← UnitKernel.act_star]
+  rw [semanticInverseKernel, UnitKernel.conj_star]
+  exact UnitKernel.act_one z
+
+/-- The inverse action cancels a transported action on the right. -/
+@[simp]
+theorem semanticAct_semanticInverseAct
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    semanticAct r (semanticInverseAct r z) = z := by
+  rw [semanticInverseAct, semanticAct, ← UnitKernel.act_star]
+  rw [semanticInverseKernel, UnitKernel.star_conj]
+  exact UnitKernel.act_one z
+
+/-- Every transported action is a bijection of the real CF2D plane. -/
+theorem semanticAct_bijective (r : UnitKernel DkNNRealQ) :
+    Function.Bijective (semanticAct r) := by
+  refine Function.bijective_iff_has_inverse.mpr ?_
+  exact ⟨semanticInverseAct r, semanticInverseAct_semanticAct r,
+    semanticAct_semanticInverseAct r⟩
+
+/-- Real-side inverse action restricted to a square-mass level set. -/
+def semanticInverseActLevel
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) : LevelSet ℝ rho2 :=
+  LevelSet.act (semanticInverseKernel r) z
+
+/-- The inverse level-set action cancels the transported level-set action. -/
+@[simp]
+theorem semanticInverseActLevel_semanticActLevel
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) :
+    semanticInverseActLevel r (semanticActLevel r z) = z := by
+  apply Subtype.ext
+  exact semanticInverseAct_semanticAct r z.1
+
+/-- The transported level-set action cancels its inverse. -/
+@[simp]
+theorem semanticActLevel_semanticInverseActLevel
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ}
+    (z : LevelSet ℝ rho2) :
+    semanticActLevel r (semanticInverseActLevel r z) = z := by
+  apply Subtype.ext
+  exact semanticAct_semanticInverseAct r z.1
+
+/-- Every transported action is a bijection of each real square-mass level set. -/
+theorem semanticActLevel_bijective
+    (r : UnitKernel DkNNRealQ) {rho2 : ℝ} :
+    Function.Bijective (semanticActLevel r : LevelSet ℝ rho2 → LevelSet ℝ rho2) := by
+  refine Function.bijective_iff_has_inverse.mpr ?_
+  exact ⟨semanticInverseActLevel r,
+    semanticInverseActLevel_semanticActLevel r,
+    semanticActLevel_semanticInverseActLevel r⟩
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index d5cbfaaf..c8df5b7c 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -132,6 +132,8 @@ BridgeNNReal / BridgeReal:
   their coordinates satisfy the real Pythagorean identity
   transported actions compose through real-side kernel products
   every real q2 level set is stable under transported actions
+  real-side conjugation makes each transported action bijective
+  each q2 level set therefore carries a transported automorphism
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index f35fccde..e020c8d7 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -75,6 +75,11 @@ semanticKernelProduct
 semanticAct_comp
 semanticActLevel
 semanticActLevel_comp
+semanticInverseKernel
+semanticInverseAct
+semanticAct_bijective
+semanticInverseActLevel
+semanticActLevel_bijective
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -85,8 +90,13 @@ Two transported actions compose through the product of their real unit
 kernels, and every real `q2` level set is stable under the transported action.
 No source-level kernel product is asserted.
 
+Real-side conjugation supplies an inverse kernel. Consequently each
+transported action is a bijection of the real CF2D plane and restricts to a
+bijection of every `q2` level set. The inverse generally leaves the first
+quadrant and is therefore not reflected back into the nonnegative source.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example first-quadrant geometric consumers.
+remain on the real side, for example finite iterates and orbit statements.
 Order reflection remains a separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 1e6c4ec8..6101a0ef 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,26 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 00:59 JST (Inverse kernels and level-set automorphisms)
+
+1. 方針:
+   - inverse は source に構成せず、transport 後の Real unit kernel の共役で
+     与える。
+2. 実施:
+   - `semanticInverseKernel` と `semanticInverseAct` を追加した。
+   - 左右の inverse action law を既存 `star_conj` / `conj_star` から証明した。
+   - `semanticAct_bijective` を証明した。
+   - level set 側にも inverse action を降ろし、
+     `semanticActLevel_bijective` を証明した。
+3. 結論:
+   - DkNNRealQ 由来 kernel は Real 平面の `q2` 保存全単射を生成する。
+   - 任意の実数 `q2` level set 上でも全単射となる。
+4. 境界:
+   - 共役 inverse は一般に beam 座標が負となるため、第一象限の source
+     kernel へ戻るとは主張しない。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 00:49 JST (Real-side composition and level-set action)
 
 1. 方針:
````
`````

# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: a02e3d8a169164a4bc7b1aa7b664737f5177c03f

## Report

次の段階まで実装しました。

- Real 側 n-fold kernel product `semanticKernelPower`
- 反復作用との一致 `semanticKernelPower_act`
- kernel action の忠実性
- kernel product order と finite action order の同値
- docstring、設計資料、履歴を更新
- source 側の積は未導入のまま維持

検証済み:

- 対象ビルド: 8273 jobs 成功
- 全体ビルド: 8566 jobs 成功
- `git diff --check` 成功

## Review

うむ。これは採用でよい。
今回で、作用側の有限位数と、Real 側 kernel 積の有限位数が一致した。これはかなり重要じゃ。

状況はこうじゃ。

```text
DkNNRealQ 由来 kernel
-> Real unit kernel
-> Real action
-> finite orbit / periodicity
-> fixed point classification
-> Real-side kernel power
-> kernel order と action order の同値
```

これで、作用として見ても、kernel 積として見ても、同じ有限位数を語れるようになった。

## 核心

今回の中心はこれじゃ。

```lean
def semanticKernelPower
    (r : UnitKernel DkNNRealQ) : ℕ → UnitKernel ℝ
  | 0 => UnitKernel.one ℝ
  | n + 1 =>
      UnitKernel.star (semanticUnitKernel r) (semanticKernelPower r n)
```

source 側に積を作らず、Real 側に輸送した後の `UnitKernel ℝ` だけで反復積を作っている。
これは正しい。

ここでの順序もよい。
`semanticUnitKernel r ⋆ semanticKernelPower r n` としているので、作用は「前の \(n\) 回作用のあとに、もう一度 `semanticAct r` を作用する」という `Function.iterate` の向きと合っている。

## `semanticKernelPower_act` の評価

これは今回の最重要補題じゃ。

```lean
theorem semanticKernelPower_act
    (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
    UnitKernel.act (semanticKernelPower r n) z = semanticOrbit r z n
```

意味は、kernel を \(n\) 回積んでから作用することと、作用を \(n\) 回反復することが同じ、というものじゃ。

ここが閉じたので、以後は、

```text
kernel product side
```

と、

```text
function iterate side
```

を自由に行き来できる。

これは大きい。

## 忠実性の補題も良い

```lean
theorem unitKernel_eq_one_of_act_eq_id
    {k : UnitKernel ℝ} (h : UnitKernel.act k = id) :
    k = UnitKernel.one ℝ
```

これは、作用が恒等写像なら kernel 自体が中立核、という補題じゃ。

証明で `Vec.one ℝ` に作用させて kernel を回収しているのが良い。
実質的には、

```text
k acts on 1 as k
```

を使っている。

これにより、作用側の情報から kernel 側の等式へ戻れる。
ここがないと、`SemanticFiniteOrder` から `SemanticKernelFiniteOrder` へ戻せない。

## finite order 同値

今回の到達点はこれじゃ。

```lean
theorem semanticKernelFiniteOrder_iff
    (r : UnitKernel DkNNRealQ) (n : ℕ) :
    SemanticKernelFiniteOrder r n ↔ SemanticFiniteOrder r n
```

これはかなり良い。

`SemanticKernelFiniteOrder r n` は、

```text
n-fold Real-side kernel product が中立核
```

`SemanticFiniteOrder r n` は、

```text
n-fold action が恒等写像
```

この二つが同値になった。

つまり、有限位数を kernel の積で見ても、平面上の作用で見ても同じになった。
ここまで来ると、有限位数分類の入口がかなり整った。

## 注意点

報告にある「noncomputable は不要」は、少しだけ言い方に注意じゃ。

今回の `semanticKernelPower` や `semanticKernelFiniteOrder_iff` 自体は、新しい選択原理や極限を使っていない。
ただし、このファイルは `semanticValue` や `semanticUnitKernel` に依存しているので、semantic bridge 全体としては noncomputable 文脈に乗っている。

だから正確には、

```text
今回の Real-side kernel power では、新たな解析的 noncomputable 要素は増えていない
```

と言うのが安全じゃ。

## ここから見える次の道

次は低位数の分類が自然じゃ。

たとえば、

```text
order 1
order 2
order 3
order 4
```

を semantic coordinate 条件で分類する方向じゃな。

まず order 1 はもうほぼ済んでいる。

```text
kernel power 1 が one
iff semanticUnitKernel r が one
iff core が 1
```

order 2 なら、Real unit kernel の二乗が one という条件になる。
第一象限由来の kernel なら、候補はかなり絞れるはずじゃ。
ただし product 後は第一象限を離れるので、分類は Real 側で行うのが正しい。

## 判定

採用でよい。

今回で、

```text
finite action order
```

と、

```text
real-side kernel product order
```

が一致した。

これは、離散力学から群的な kernel 積構造へ橋が戻ったということじゃ。
source 側に積や減算を押し込まず、Real 側だけで閉じているので設計境界も守れている。

わっちの結論はこうじゃ。
次は低位数 kernel の座標分類へ進める。まずは order 1、order 2 あたりが堅い。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 0eff8594..08edc968 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -615,6 +615,86 @@ theorem semanticFixed_iff_eq_zero_of_not_identity
   exact ⟨eq_zero_of_semanticFixed_of_core_ne_one hcore,
     fun hz => hz ▸ semanticFixed_zero r⟩
 
+/--
+The `n`-fold product of a transported kernel, formed entirely in the real
+unit-kernel monoid.
+
+The successor convention
+`semanticUnitKernel r ⋆ semanticKernelPower r n` matches the convention for
+function iteration: the new action is applied after the previous `n` actions.
+-/
+def semanticKernelPower
+    (r : UnitKernel DkNNRealQ) : ℕ → UnitKernel ℝ
+  | 0 => UnitKernel.one ℝ
+  | n + 1 =>
+      UnitKernel.star (semanticUnitKernel r) (semanticKernelPower r n)
+
+/-- The action of the real-side kernel power is the corresponding orbit term. -/
+theorem semanticKernelPower_act
+    (r : UnitKernel DkNNRealQ) (n : ℕ) (z : Vec ℝ) :
+    UnitKernel.act (semanticKernelPower r n) z = semanticOrbit r z n := by
+  induction n with
+  | zero =>
+      simp [semanticKernelPower, semanticOrbit]
+  | succ n ih =>
+      simp [semanticKernelPower, UnitKernel.act_star, semanticOrbit,
+        semanticAct, Function.iterate_succ_apply', ih]
+
+/--
+An action by a real unit kernel is faithful: if it acts as the identity on
+the plane, then the kernel itself is the neutral kernel.
+-/
+theorem unitKernel_eq_one_of_act_eq_id
+    {k : UnitKernel ℝ} (h : UnitKernel.act k = id) :
+    k = UnitKernel.one ℝ := by
+  apply UnitKernel.ext
+  have hone := congrFun h (Vec.one ℝ)
+  simpa [UnitKernel.act] using hone
+
+/--
+The transported kernel has product order dividing `n` when its `n`-fold
+real-side product is the neutral kernel.
+
+This predicate makes no assertion that a corresponding product exists in the
+nonnegative source semiring.
+-/
+def SemanticKernelFiniteOrder
+    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
+  semanticKernelPower r n = UnitKernel.one ℝ
+
+/--
+Real-side kernel order and finite order of the transported plane action are
+equivalent.
+
+The forward implication is the action law for the repeated kernel product.
+The reverse implication uses faithfulness, detected by evaluating the action
+at the multiplicative unit vector.
+-/
+theorem semanticKernelFiniteOrder_iff
+    (r : UnitKernel DkNNRealQ) (n : ℕ) :
+    SemanticKernelFiniteOrder r n ↔ SemanticFiniteOrder r n := by
+  constructor
+  · intro h
+    change semanticKernelPower r n = UnitKernel.one ℝ at h
+    change (semanticAct r)^[n] = id
+    funext z
+    calc
+      (semanticAct r)^[n] z =
+          UnitKernel.act (semanticKernelPower r n) z := by
+            symm
+            simpa [semanticOrbit] using semanticKernelPower_act r n z
+      _ = UnitKernel.act (UnitKernel.one ℝ) z := by rw [h]
+      _ = id z := by simp
+  · intro h
+    change (semanticAct r)^[n] = id at h
+    apply unitKernel_eq_one_of_act_eq_id
+    funext z
+    calc
+      UnitKernel.act (semanticKernelPower r n) z =
+          (semanticAct r)^[n] z := by
+            simpa [semanticOrbit] using semanticKernelPower_act r n z
+      _ = id z := congrFun h z
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index 62507f37..dddec68a 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -142,6 +142,8 @@ BridgeNNReal / BridgeReal:
   positive finite order excludes the vacuous zero iterate
   identity kernels fix every point
   nonidentity transported kernels fix exactly the origin
+  real-side kernel powers act as the corresponding function iterates
+  kernel-product finite order is equivalent to finite action order
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index bd0b3cd5..20ca5135 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -100,6 +100,11 @@ SemanticPositiveFiniteOrder
 SemanticIdentityKernel
 semanticIdentityKernel_iff_core_eq_one
 semanticFixed_iff_eq_zero_of_not_identity
+semanticKernelPower
+semanticKernelPower_act
+unitKernel_eq_one_of_act_eq_id
+SemanticKernelFiniteOrder
+semanticKernelFiniteOrder_iff
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -143,9 +148,26 @@ nonidentity transported kernel fixes exactly the origin. The proof uses only
 the Pythagorean kernel identity and the determinant of the fixed-point linear
 system.
 
+Finite-order classification now has an algebraic real-side formulation.
+`semanticKernelPower r n` is the repeated product of the transported unit
+kernel, formed only in `UnitKernel Real`. Its action is exactly the `n`th
+iterate of `semanticAct r`. Since a real unit kernel is recovered by applying
+its action to the multiplicative unit vector, the action is faithful.
+Consequently:
+
+```text
+semanticKernelPower r n = UnitKernel.one Real
+  iff
+(semanticAct r)^[n] = id
+```
+
+This closes the bridge between kernel product order and finite action order
+without defining multiplication, subtraction, or inverses in the nonnegative
+source.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example finite-order classification under
-explicit semantic coordinate hypotheses. Order reflection remains a separate,
+remain on the real side, for example classifying low product orders through
+explicit semantic coordinate identities. Order reflection remains a separate,
 heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 877072f7..187f615a 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -367,3 +367,25 @@ Archive
    - それまでは第一象限 kernel の Real 幾何 consumer を進められる。
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
+### 2026/06/22 04:30 JST (Real-side kernel powers and finite-order equivalence)
+
+1. 方針:
+   - source 側の積は定義せず、transport 後の `UnitKernel Real` だけで
+     kernel の反復積を構成する。
+2. 実施:
+   - `semanticKernelPower` を real-side の n-fold product として追加した。
+   - `semanticKernelPower_act` で、その作用が `semanticAct` の n 回反復と
+     一致することを証明した。
+   - 単位ベクトルへの作用から kernel を復元する忠実性
+     `unitKernel_eq_one_of_act_eq_id` を証明した。
+   - `semanticKernelFiniteOrder_iff` により、反復積が中立核になる条件と
+     finite action order が同値であることを証明した。
+3. 結論:
+   - finite order は、作用側と kernel 積側のどちらからでも同じ条件として
+     扱える。
+   - signed source、角度、連続性、`noncomputable` は不要。
+4. 境界:
+   - この積は Real 側だけに存在し、非負 source の積を主張しない。
+5. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
````
`````

# Git diff / Report / Review

In the Euclidean interpretation, the analysis was brought to a point where it could be read as an angle table for four finite states.

## Upd: EuclideanPhase, SemanticCF2D

gch: c8639f771de16832283de50876c10cae9efe70c7

## Report

進めました。今回は `k % 4` 分類 theorem まで閉じています。

追加:

- [SemanticCF2D.lean](/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean)
  - `semanticActIter_add_four_mul_of_core_eq_zero`
  - `semanticActIter_eq_mod_four_of_core_eq_zero`

これで semantic action は core-zero 条件下で

```lean
semanticActIter r k z = semanticActIter r (k % 4) z
```

まで Lean に載りました。

- [EuclideanPhase.lean](/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean)
  - `pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle_mod_four`

つまり Euclidean 解釈では、

```lean
semanticActIter r k
↔ rotation by semanticPhaseAngle (k % 4)
```

として読めるところまで到達しています。四状態対称性から `0, π/2, π, 3π/2` の角度読みが出る表が、かなり明確に閉じました。

文書更新:

- [research-pregeometric-pi-program-067.md](/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md)
- [History.md](/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md)

検証:

- `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功
- `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
- `lake build DkMath.Analysis` 成功
- `git diff --check` 成功

## Review

うむ、賢狼レビューじゃ。
今回の差分は **採用でよい** 。これは対称性ルートの一区切りとして、かなり大きい。`k % 4` 分類まで Lean に載ったことで、DkMath 側の exact order-four action が、Euclidean 解釈では有限四状態の角度表として読めるところまで閉じた。

## 1. 状況解説

今回の到達点はこれじゃ。

```text
semanticActIter r k z
  depends only on k % 4
```

そして Euclidean bridge 側では、

```text
semanticActIter r k
  is read as rotation by semanticPhaseAngle (k % 4)
```

まで来た。

つまり、任意の自然数 \(k\) について、作用回数そのものをそのまま無限に追わず、四状態の residue に落とせる。

$$
A^k(z)=A^{k\bmod 4}(z)
$$

これが semantic 層で証明され、その後で Euclidean 側が

$$
A^k
\quad\text{is read as}\quad
R_{\theta_{k\bmod 4}}
$$

と読む。

これはきれいじゃ。

## 2. semantic 層の進展

今回の semantic 層では、まず任意個の full-turn を消す補題が入った。

```lean
theorem semanticActIter_add_four_mul_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (q k : ℕ) (z : Vec ℝ) :
    semanticActIter r (k + 4 * q) z = semanticActIter r k z
```

これはよい。前回の

```lean
semanticActIter r (k + 4) z = semanticActIter r k z
```

を帰納法で任意個の \(4\) へ伸ばした形じゃ。

意味は、

$$
A^{k+4q}(z)=A^k(z)
$$

じゃな。

この theorem が入ったことで、`Nat.mod_add_div` を使った modulo-four 化が自然にできる。

## 3. `semanticActIter_eq_mod_four_of_core_eq_zero` は本丸

今回の semantic 側の主 theorem はこれじゃ。

```lean
theorem semanticActIter_eq_mod_four_of_core_eq_zero
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    semanticActIter r k z = semanticActIter r (k % 4) z
```

これは非常に重要じゃ。

これで、core-zero 境界作用については、作用回数 \(k\) の情報が \(k\bmod4\) に圧縮される。

$$
k=4\left\lfloor\frac{k}{4}\right\rfloor+(k\bmod4)
$$

を Lean では `Nat.mod_add_div` で使い、そこから `semanticActIter_add_four_mul_of_core_eq_zero` に渡している。実装方針としても正しい。

この theorem は、DkMath 側の「位相クラス」そのものじゃ。

```text
phase index:
  k

phase class:
  k % 4

semantic state:
  semanticActIter r (k % 4) z
```

## 4. Euclidean bridge 側も正しい

Euclidean 側の主 theorem はこれ。

```lean
theorem pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle_mod_four
    {r : UnitKernel DkNNRealQ}
    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
    (k : ℕ) (z : Vec ℝ) :
    pairToEuclideanPlane (Vec.toProd (semanticActIter r k z)) =
      euclideanPlaneOrientation.rotation (semanticPhaseAngle (k % 4))
        (pairToEuclideanPlane (Vec.toProd z))
```

これで、任意 \(k\) についての Euclidean angle reading が得られた。

ただし右辺は `semanticPhaseAngle k` ではなく、`semanticPhaseAngle (k % 4)`。
ここが今の段階では正しい。

なぜなら今回のルートは、一般角度加法の連続的な theorem ではなく、exact order-four の有限対称性から来る分類だからじゃ。

```text
general angle-addition theorem:
  later

mod-four finite phase classifier:
  now implemented
```

この順序が良い。

## 5. 四状態表が完成した

今回で、実質的にこの表が Lean に載った。

```text
k % 4 = 0:
  identity
  semanticPhaseAngle 0

k % 4 = 1:
  quarter-turn
  semanticPhaseAngle 1 = pi / 2

k % 4 = 2:
  half-turn
  semanticPhaseAngle 2 = pi

k % 4 = 3:
  reverse quarter-turn
  semanticPhaseAngle 3 = 3*pi / 2
```

この表は、DkMath 側では `semanticActIter` の状態表。
Euclidean 側では角度読みの表。

つまり、

```text
DkMath exact order-four action
  ↓
mod-four semantic phase table
  ↓
Euclidean angle reading
```

という橋ができた。

これは対称性ルートとしてかなり強い。

## 6. 証明の構成も良い

Euclidean theorem の証明は、まず

```lean
let n := k % 4
```

として `n < 4` を取り、`omega` で

```lean
n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3
```

へ分岐している。

この設計は素直で良い。
`k % 4` の値域を有限 case split し、それぞれ既存の `k=0,1,2,3` bridge に流す。読みやすい。

ここは少し長いが、構造が明確じゃ。

将来、同種 theorem が増えるなら helper lemma として

```lean
theorem nat_mod_four_cases (k : ℕ) :
    k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3
```

のような補助を置いてもよい。
今はこのままで十分じゃ。

## 7. 研究上の意味

これは「\(\pi\) の内在的構成」ではまだない。
しかし、四状態対称性から Euclidean 角度読みとして

$$
0,\quad \frac{\pi}{2},\quad \pi,\quad \frac{3\pi}{2}
$$

が出る表は、かなり明確に閉じた。

ここで大事なのは、\(\pi\) が先にあるのではなく、DkMath 側ではまず

```text
fourfold semantic action
```

があること。
それを Euclidean model に送ると、標準角度として \(\pi/2\)、\(\pi\)、\(3\pi/2\) と読まれる。

この guardrail が守れている。

```text
intrinsic construction of pi:
  not yet

Euclidean reading of fourfold symmetry:
  implemented
```

## 8. これは「対称性からの π 捕獲ルート」の一区切り

今回で、対称性ルートは次の形になった。

```text
exact order-four action
  ↓
semanticActIter
  ↓
period-four theorem
  ↓
mod-four classifier
  ↓
Euclidean rotation by semanticPhaseAngle (k % 4)
```

これはもう立派な「有限位相表」じゃ。

DkMath 的には、

```text
回転角を連続量として先に置くのではなく、
四状態の作用対称性から有限位相を得る。
その有限位相を Euclidean 角度で読む。
```

という順序が Lean 上で見える。

ここは非常に良い。

## 9. 次の一手

次は三方向ある。

第一に、写像等式版を作る。
今の theorem は pointwise に `z` を取る形じゃ。将来の合成には、写像等式があると便利になる。

```lean
theorem pairToEuclideanPlane_comp_semanticActIter_eq_rotation_mod_four
    ...
```

ただし、`Vec.toProd` や `pairToEuclideanPlane` が絡むので、無理に急がなくてよい。

第二に、一般角度 theorem へ進む。
つまり右辺を `semanticPhaseAngle (k % 4)` ではなく、`semanticPhaseAngle k` にするルートじゃ。

$$
R_{\theta_k}=R_{\theta_{k\bmod4}}
$$

を Euclidean 側で示せば、

```lean
rotation (semanticPhaseAngle k)
```

へ持ち上げられる可能性がある。

ただしこれは `Real.Angle` の周期性や rotation の angle quotient に触れるので、少し重い。
今すぐでなくてよい。

第三に、文書化を強化する。
この checkpoint はかなり説明価値が高いので、研究メモでは次の短い図を入れると強い。

```text
semantic action count k
  -> k % 4
  -> finite phase table
  -> Euclidean angle reading
```

## 10. 気になる点

大きな問題はない。

一点だけ、`semanticActIter_add_four_mul_of_core_eq_zero` の引数順が `(q k : ℕ)` で、式が `k + 4 * q` になっている。これは report の用途には合っている。
ただ、使用時には

```lean
semanticActIter_add_four_mul_of_core_eq_zero hcore
  (k / 4) (k % 4) z
```

のように `q` が先、`k` が後になるので、名前からは少し読み取りづらい可能性がある。

将来の可読性を上げるなら、alias として

```lean
theorem semanticActIter_mod_decompose_of_core_eq_zero
```

のような名前を置いてもよい。
ただ、今の実装は build も通っており、数学的にも問題ない。

## 11. 結論

今回の差分は採用でよい。

```text
実装:
  良い。semantic side で k % 4 分類が閉じ、Euclidean bridge も完成した。

数学:
  良い。exact order-four action が有限位相表として Lean に載った。

設計:
  良い。一般角度 theorem へ飛ばず、mod-four classifier として安全に閉じた。

安全性:
  良い。pi の内在構成ではなく Euclidean angle reading として明確。

次:
  rotation 側で semanticPhaseAngle k と semanticPhaseAngle (k % 4) の一致を読むか、
  写像等式版を整える。
```

ぬしよ、これは良い。
対称性ルートは一区切りじゃ。

いま Lean に載った主張は、きれいに言えばこうじゃ。

$$
\text{core-zero semantic action satisfies}\quad A^k=A^{k\bmod4}.
$$

そして Euclidean 解釈では、

$$
A^k
\quad\text{is read as rotation by}\quad
\theta_{k\bmod4}.
$$

ここまで来れば、DkMath 版の四状態回転表はほぼ完成じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index 805e1760..c1f3da10 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1300,6 +1300,50 @@ theorem semanticActIter_add_four_of_core_eq_zero
   rw [semanticActIter, semanticActIter, Function.iterate_add_apply, hfour]
   rfl
 
+/--
+Adding any multiple of four to the iterate index does not change the
+core-zero boundary action.
+
+This is the induction form used to pass from exact period four to modulo-four
+classification.
+-/
+theorem semanticActIter_add_four_mul_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (q k : ℕ) (z : Vec ℝ) :
+    semanticActIter r (k + 4 * q) z = semanticActIter r k z := by
+  induction q with
+  | zero =>
+      simp
+  | succ q ih =>
+      calc
+        semanticActIter r (k + 4 * (q + 1)) z =
+            semanticActIter r ((k + 4 * q) + 4) z := by
+              congr 1
+        _ = semanticActIter r (k + 4 * q) z :=
+            semanticActIter_add_four_of_core_eq_zero hcore
+              (k + 4 * q) z
+        _ = semanticActIter r k z := ih
+
+/--
+The core-zero semantic iterate depends only on the phase index modulo four.
+
+This is the semantic rotation table in quotient form, before any Euclidean
+angle interpretation is attached.
+-/
+theorem semanticActIter_eq_mod_four_of_core_eq_zero
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (k : ℕ) (z : Vec ℝ) :
+    semanticActIter r k z = semanticActIter r (k % 4) z := by
+  calc
+    semanticActIter r k z =
+        semanticActIter r (k % 4 + 4 * (k / 4)) z := by
+          rw [Nat.mod_add_div]
+    _ = semanticActIter r (k % 4) z :=
+        semanticActIter_add_four_mul_of_core_eq_zero hcore
+          (k / 4) (k % 4) z
+
 /-- A nonzero vector cannot return after one boundary action. -/
 theorem not_semanticPeriodic_one_of_core_eq_zero_of_ne_zero
     {r : UnitKernel DkNNRealQ} {z : Vec ℝ}
diff --git a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
index 52559f18..bbc17128 100644
--- a/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
+++ b/lean/dk_math/DkMath/Analysis/docs/research-pregeometric-pi-program-067.md
@@ -161,6 +161,22 @@ under the same core-zero hypothesis. The Euclidean side also exposes the
 `k = 0` and `k = 1` iterate-form bridges, so the finite table is available in
 one notation before moving to a full modulo-four classifier.
 
+The modulo-four classifier is now implemented in two layers:
+
+```text
+semanticActIter r k z = semanticActIter r (k % 4) z
+```
+
+on the semantic side, and then
+
+```text
+semanticActIter r k
+  <-> Euclidean rotation by semanticPhaseAngle (k % 4)
+```
+
+on the Euclidean reading side. This closes the finite order-four phase table
+without claiming an intrinsic construction of `pi`.
+
 ### Milestone A: continuous four-edge loop - implemented
 
 1. The real CF2D target carries the topology induced from `Real × Real`.
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
index 3bbf7f6b..ebaf28df 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
@@ -732,6 +732,49 @@ theorem pairToEuclideanPlane_semanticActIter_four_eq_rotation_semanticPhaseAngle
     semanticPhaseAngle_four, rotation_semanticFullTurnAngle_eq_refl]
   rfl
 
+/--
+Modulo-four Euclidean angle reading of the semantic action iterate.
+
+The semantic side first reduces the iterate index to `k % 4`. The remaining
+four cases are exactly the finite rotation table: identity, quarter-turn,
+half-turn, and reverse quarter-turn.
+-/
+theorem pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle_mod_four
+    {r : UnitKernel DkNNRealQ}
+    (hcore : semanticValue (r : Vec DkNNRealQ).core = 0)
+    (k : ℕ) (z : Vec ℝ) :
+    pairToEuclideanPlane (Vec.toProd (semanticActIter r k z)) =
+      euclideanPlaneOrientation.rotation (semanticPhaseAngle (k % 4))
+        (pairToEuclideanPlane (Vec.toProd z)) := by
+  let n := k % 4
+  have hnlt : n < 4 := by
+    dsimp [n]
+    exact Nat.mod_lt k (by norm_num)
+  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
+    omega
+  rw [semanticActIter_eq_mod_four_of_core_eq_zero hcore]
+  rcases hcases with hzero | hone | htwo | hthree
+  · have hkmod : k % 4 = 0 := by
+      simpa [n] using hzero
+    rw [hkmod]
+    exact pairToEuclideanPlane_semanticActIter_zero_eq_rotation_semanticPhaseAngle
+      r z
+  · have hkmod : k % 4 = 1 := by
+      simpa [n] using hone
+    rw [hkmod]
+    exact pairToEuclideanPlane_semanticActIter_one_eq_rotation_semanticPhaseAngle
+      hcore z
+  · have hkmod : k % 4 = 2 := by
+      simpa [n] using htwo
+    rw [hkmod]
+    exact pairToEuclideanPlane_semanticActIter_two_eq_rotation_semanticPhaseAngle
+      hcore z
+  · have hkmod : k % 4 = 3 := by
+      simpa [n] using hthree
+    rw [hkmod]
+    exact pairToEuclideanPlane_semanticActIter_three_eq_rotation_semanticPhaseAngle
+      hcore z
+
 end
 
 end DkMath.Analysis.DkNNRealQ
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index 6168be9c..cb436874 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -1338,3 +1338,29 @@ Archive
 5. verification:
    - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
      (8278 jobs)。
+
+### 2026/06/27 23:18 JST (Modulo-four semantic phase classifier)
+
+1. semantic modulo-four classification:
+   - `semanticActIter_add_four_mul_of_core_eq_zero` を追加し、
+     `k + 4 * q` の形で任意個の full-turn を消せるようにした。
+   - `semanticActIter_eq_mod_four_of_core_eq_zero` を追加し、
+     core-zero semantic action の iterate が `k % 4` のみに依存することを
+     記録した。
+2. Euclidean modulo-four bridge:
+   - `pairToEuclideanPlane_semanticActIter_eq_rotation_semanticPhaseAngle_mod_four`
+     を追加した。
+   - semantic 側で `k % 4` に縮約し、`0,1,2,3` の有限位相表へ分岐して
+     Euclidean angle reading に接続する。
+3. interpretation:
+   - DkMath の exact order-four action が、Euclidean 解釈では
+     `semanticPhaseAngle (k % 4)` の回転として読まれるところまで閉じた。
+   - これは `pi` の内在構成ではなく、四状態対称性の Euclidean
+     angle reading である。
+4. documentation:
+   - `research-pregeometric-pi-program-067.md` に modulo-four classifier
+     の二層構造を追記した。
+5. verification:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+   - `lake build DkMath.CosmicFormula.Rotation.CF2D.EuclideanPhase` 成功
+     (8278 jobs)。
````
`````

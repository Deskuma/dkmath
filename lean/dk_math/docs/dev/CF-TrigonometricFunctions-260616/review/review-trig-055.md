# Git diff / Report / Review

## Upd: Analysis.DkReal.SemanticCF2D

gch: 53a859772c77c88fc553b63af60993e49e66c70b

## Report

次の段階まで完了しました。

- finite action order の倍数伝播
- `semanticMinimalPeriod`
- 周期性と minimal period の割り切り同値
- minimal period が finite action order を割る定理
- 正周期から minimal period の正値を導出
- period が正・最小・角度周期とは限らない旨を明記

全体ビルド成功、8566 jobs。`git diff --check` も成功です。

## Review

うむ。これは状況としてかなり良い。
ただし、ここで到達したのは「角度周期」ではなく、Mathlib の反復写像としての周期理論じゃ。そこを明記した今回の修正は正しい。

## 状況分析

これまでの流れはこうじゃ。

```text
DkNNRealQ の非負 unit kernel
-> Real unit kernel
-> Real 上の q2 保存作用
-> level set 上の自己同型
-> finite orbit
-> periodic point
-> minimal period
```

今回で、周期点・有限位数・最小周期が Mathlib の標準 API に接続された。

これは大きい。
独自の周期理論を作らず、`Function.IsPeriodicPt` と `Function.minimalPeriod` に乗ったことで、以後の定理を Mathlib 側から拾いやすくなった。

## 良い点

`SemanticPeriodic` の docstring を修正したのはとても良い。

`n` は正とも最小とも限らない。
角度周期でもない。
これは重要じゃ。

今の定義は、

```lean
Function.IsPeriodicPt (semanticAct r) n z
```

なので、意味は「\(n\) 回反復して戻る」じゃ。
角度 \(\theta\)、弧長、連続パラメータ、\(2\pi\) はまだ関係しない。

この切り分けができているので、主張が堅い。

## minimal period の評価

`semanticMinimalPeriod` は Mathlib の `Function.minimalPeriod` の薄い wrapper じゃな。

これは良い。
独自定義ではなく、標準 API を使っている。

```lean
noncomputable def semanticMinimalPeriod
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : ℕ :=
  Function.minimalPeriod (semanticAct r) z
```

ここで `noncomputable` になるのも自然。
最小値選択が入るからじゃ。

## 周期性と割り切り

この定理がかなり重要じゃ。

```lean
theorem semanticPeriodic_iff_minimalPeriod_dvd
    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
    SemanticPeriodic r z n ↔ semanticMinimalPeriod r z ∣ n
```

これにより、周期判定が「最小周期が \(n\) を割るか」に変換される。

つまり、以後は orbit return を毎回直接追わずに、割り切り構造として扱える。
これは離散力学として一段上がった状態じゃ。

## finite order との接続

`semanticMinimalPeriod_dvd_of_finiteOrder` も良い。

有限作用位数 \(n\) があるなら、任意点の minimal period は \(n\) を割る。

これは正しい。

```text
全体の作用が n 回で恒等
-> 全点が n 周期
-> 各点の最小周期は n を割る
```

ここで「全体の位数」と「点ごとの周期」が分離された。
この分離は今後の分類に効く。

## 正周期から正最小周期

`semanticMinimalPeriod_pos` も必要な補題じゃ。

Mathlib の規約では、非周期点の minimal period が `0` になる。
だから「正の周期があるなら minimal period も正」を明示しておくのは安全じゃ。

これにより、次に「非自明周期」や「最小正周期」を扱うときに使える。

## 注意点

一点だけ注意じゃ。

`SemanticFiniteOrder r n` は、

```lean
(semanticAct r)^[n] = id
```

なので、`n = 0` でも成立するはずじゃ。
`Function.iterate` の 0 回反復は恒等写像だからの。

したがって、「有限位数」と言うときに数学的な非自明位数を意識するなら、別途 \(0 < n\) を要求する版が欲しい。

例えば次のような wrapper じゃ。

```lean
def SemanticPositiveFiniteOrder
    (r : UnitKernel DkNNRealQ) (n : ℕ) : Prop :=
  0 < n ∧ SemanticFiniteOrder r n
```

ただし今の `SemanticFiniteOrder` 自体は間違いではない。
Mathlib の反復写像 API に素直に合わせた、弱いが扱いやすい定義じゃ。

## 今の到達点

これはこう言える。

```text
Real 側に輸送された DkNNRealQ kernel は、
q2 保存同型を生成し、
その反復 orbit は保存量を保ち、
周期性と最小周期は Mathlib の標準周期理論で扱える。
```

角度なし。
連続性なし。
signed source なし。
それでもここまで来ている。

これは本当に良い。

## 次の候補

次は fixed point と finite-order action の分類が自然じゃ。

まずは軽い補題として、

```lean
SemanticFixed r z := SemanticPeriodic r z 1
```

または直接、

```lean
semanticAct r z = z
```

を定義してもよい。

その次に、finite order の正値版を作るとよい。

```lean
SemanticPositiveFiniteOrder r n
```

そして、もし必要なら minimal positive finite order を action 自体にも定義する。

ただし、角度分類へ進むのはまだ早い。
今は写像反復としての分類を積む方が堅い。

## 判定

採用でよい。

今回の実装は、周期まわりの危ない点をきちんと避けている。
特に、

```text
period は正とは限らない
period は最小とは限らない
period は角度周期ではない
minimalPeriod は Mathlib 規約に従う
```

を明記したのが良い。

わっちの結論はこうじゃ。
DkNNRealQ 由来の Real 保存作用は、ついに Mathlib の標準離散力学 API に接続された。ここから先は fixed point、正有限位数、最小位数、分類定理へ進める段階じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index 1c9100eb..9caea3e3 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -86,7 +86,8 @@ square-mass level set. Real-side conjugation supplies inverse actions, so
 these maps are equivalences of the plane and of each level set. Their finite
 iterates generate forward orbits of constant square mass. Periodic points and
 finite action order are expressed through Mathlib's standard discrete-dynamics
-API.
+API. Minimal periods use Mathlib's zero-for-aperiodic convention and divide
+all known return times.
 
 [TODO: semantic-cf2d-signed] Source-level `Vec.star` and `KernelFamily` require
 signed arithmetic. Defer them until a signed DkReal layer exists.
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index c1620d37..027bbcd4 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -338,7 +338,12 @@ theorem semanticLevelOrbit_val
         Function.iterate_succ_apply', Function.iterate_succ_apply']
       exact congrArg (semanticAct r) ih
 
-/-- A real vector is periodic when a finite semantic orbit returns to it. -/
+/--
+A real vector is periodic when a finite semantic orbit returns to it.
+
+The supplied `n` need not be positive or minimal. This is Mathlib's ordinary
+iterate-period predicate, not an angle period.
+-/
 def SemanticPeriodic
     (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) : Prop :=
   Function.IsPeriodicPt (semanticAct r) n z
@@ -413,6 +418,51 @@ theorem semanticPeriodic_of_dvd
     SemanticPeriodic r z n :=
   Function.IsPeriodicPt.trans_dvd h hmn
 
+/-- Finite action order persists at every multiple. -/
+theorem semanticFiniteOrder_of_dvd
+    {r : UnitKernel DkNNRealQ} {m n : ℕ}
+    (h : SemanticFiniteOrder r m) (hmn : m ∣ n) :
+    SemanticFiniteOrder r n := by
+  rw [semanticFiniteOrder_iff] at h ⊢
+  intro z
+  exact semanticPeriodic_of_dvd (h z) hmn
+
+/--
+Minimal positive return time of a point under the transported action.
+
+Mathlib assigns value zero when the point has no positive period.
+-/
+noncomputable def semanticMinimalPeriod
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) : ℕ :=
+  Function.minimalPeriod (semanticAct r) z
+
+/-- Every point returns at its Mathlib minimal period. -/
+theorem semanticPeriodic_minimalPeriod
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) :
+    SemanticPeriodic r z (semanticMinimalPeriod r z) :=
+  Function.isPeriodicPt_minimalPeriod (semanticAct r) z
+
+/-- Periodicity at `n` is divisibility by the minimal period. -/
+theorem semanticPeriodic_iff_minimalPeriod_dvd
+    (r : UnitKernel DkNNRealQ) (z : Vec ℝ) (n : ℕ) :
+    SemanticPeriodic r z n ↔ semanticMinimalPeriod r z ∣ n :=
+  Function.isPeriodicPt_iff_minimalPeriod_dvd
+
+/-- Any finite action order is divisible by every point's minimal period. -/
+theorem semanticMinimalPeriod_dvd_of_finiteOrder
+    {r : UnitKernel DkNNRealQ} {n : ℕ}
+    (h : SemanticFiniteOrder r n) (z : Vec ℝ) :
+    semanticMinimalPeriod r z ∣ n := by
+  rw [← semanticPeriodic_iff_minimalPeriod_dvd]
+  exact (semanticFiniteOrder_iff r n).mp h z
+
+/-- Positive periodicity forces a positive minimal period. -/
+theorem semanticMinimalPeriod_pos
+    {r : UnitKernel DkNNRealQ} {z : Vec ℝ} {n : ℕ}
+    (hn : 0 < n) (h : SemanticPeriodic r z n) :
+    0 < semanticMinimalPeriod r z :=
+  Function.IsPeriodicPt.minimalPeriod_pos hn h
+
 /-
 [TODO: semantic-cf2d/signed-kernel] Source-level `Vec.star` and
 `KernelFamily` require a ring because their core coordinate uses subtraction.
diff --git a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
index d2a41909..0030f637 100644
--- a/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
+++ b/lean/dk_math/DkMath/Analysis/docs/Analysis-Initial-Layer.md
@@ -137,6 +137,7 @@ BridgeNNReal / BridgeReal:
   finite iterates and forward orbits retain the same q2 value
   periodic points use Mathlib IsPeriodicPt
   finite action order makes every level-set point periodic
+  minimal periods divide all known return times and finite action orders
   source-level star and KernelFamily wait for signed DkReal arithmetic
   treat order reflection as a separate heavier task
   compare semantic equality with DkReal.Equiv
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
index 26a53721..5d8092f0 100644
--- a/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-real-analysis-046.md
@@ -90,6 +90,10 @@ SemanticPeriodic
 SemanticLevelPeriodic
 SemanticFiniteOrder
 semanticFiniteOrder_iff
+semanticFiniteOrder_of_dvd
+semanticMinimalPeriod
+semanticPeriodic_iff_minimalPeriod_dvd
+semanticMinimalPeriod_dvd_of_finiteOrder
 ```
 
 The transported kernel now acts on real CF2D vectors and preserves `q2`.
@@ -114,8 +118,15 @@ equivalent to periodicity of the underlying plane point. Finite action order
 means that one iterate is the identity on the whole plane; this makes every
 point of every level set periodic.
 
+The period argument of `SemanticPeriodic` is neither required to be positive
+nor minimal. `semanticMinimalPeriod` uses Mathlib's convention: it is the
+least positive period for a periodic point and zero otherwise. Periodicity is
+equivalent to divisibility by this minimal period. Every point's minimal
+period divides any finite action order, and finite action order propagates to
+all multiples.
+
 The next structural boundary is source-level `Vec.star` and `KernelFamily`.
 Both require signed arithmetic. They should wait for a signed DkReal layer
 rather than forcing subtraction into `DkNNRealQ`. Until then, further work can
-remain on the real side, for example divisibility and minimal-period
-statements. Order reflection remains a separate, heavier task.
+remain on the real side, for example classifying fixed points or finite-order
+actions. Order reflection remains a separate, heavier task.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index ef7c8251..c5259ac3 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -212,6 +212,30 @@ Archive
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
 
+### 2026/06/22 04:09 JST (Minimal periods and finite-order divisibility)
+
+1. 注意点:
+   - `SemanticPeriodic r z n` の `n` は正とも最小とも限らず、角度周期でも
+     ないことを docstring に明記した。
+2. 実施:
+   - finite action order の倍数伝播を証明した。
+   - Mathlib `minimalPeriod` を包む `semanticMinimalPeriod` を追加した。
+   - periodicity と minimal period divisibility の同値を公開した。
+   - 任意の finite action order が全点の minimal period で割り切れることを
+     証明した。
+   - 正周期が存在すれば minimal period が正であることを証明した。
+3. 規約:
+   - periodic point の minimal period は最小正周期。
+   - 非周期点では Mathlib 規約により minimal period は zero。
+4. 結論:
+   - orbit return、period divisibility、finite action order が Mathlib の
+     標準周期 API 上で統一された。
+5. 次の候補:
+   - fixed point / finite-order action の分類。
+   - source-level family は signed DkReal 層まで保留。
+6. 検証:
+   - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
 ### 2026/06/22 03:50 JST (Periodic points and finite action order)
 
 1. 方針:
````
`````

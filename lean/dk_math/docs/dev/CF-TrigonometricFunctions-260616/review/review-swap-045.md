# Git diff / Report / Review

## Upd: docs: DkMath.PowerSwap Current Gap and Feasible Implementation Plan

gch: 1fb20c2d85a4531217503245b43246cf46c8896c

## Report

レビューに基づき、2文書を同期修正しました。

- 旧設計書を「歴史的設計基準」と明記
- 新実装計画へのリンクを追加
- `DkNNReal` と `DkNNRealQ` の役割を明確化
- `NormalizesTo` の型を統一
- strict comparison を `0 < degree` に変更
- `pow_mul` 系定理に `[Monoid α]` が必要と明記
- Phase 0 の workspace 再確認を追加
- `Core` / `Analytic` の軽量入口を具体化
- 旧コミット順を現状起点の計画へ更新

`git diff --check` と行長検査は通過しています。文書のみの変更なので Lean ビルドは省略しました。

## Review

同期修正、かなり良い。わっちのレビューでは **承認してよい文書修正** じゃ。

旧設計書側に「historical design baseline」を明記し、新作業は feasible plan を参照する、としたのは正解じゃ。これで「古い理想設計」と「現在ワークスペース起点の実装計画」が衝突せず、旧文書は数学的動機、現計画は作業指示として読めるようになった。

`DkNNReal` と `DkNNRealQ` の役割分離もよい。代表元で有限 endpoint inspection と bounded search を行い、商型側で public equality / order / semiring / frame evaluation を扱う、という区別は PowerSwapObservation の設計に必須じゃ。観測 theorem が `DkNNRealQ.mk` を通じて商型順序へ接続する、と明記したのも安全策として効いている。

`pow_mul` 系 theorem を `[Pow α Nat]` だけから主張しないようにし、`[Monoid α]` か同等の構造へ隔離した修正も正しい。`NormalizesTo` の refl / symm / trans は等号だけで閉じ、`NatPowerFrame.power` との合成は `pow_mul` 依存として分ける。この切り分けは Lean 実装でかなり効く。

strict comparison を `degree ≠ 0` ではなく `0 < degree` に変えたのも良い。自然数次数では本質的に同じでも、Lean の theorem statement としては `0 < degree` の方が後続の `pow_lt_pow` 系に渡しやすい。

`Core` と `Analytic` の入口分離も、これで十分に明確になった。新規 structural consumer は `DkMath.PowerSwap.Core` を import し、既存 umbrella は互換用、`DkMath.PowerSwap.Analytic` は `Branch` と `Contours` の薄い入口、という構成は、依存の重さを制御できる。

残る細かい確認点は二つだけじゃ。

一つ目は、`DkNNReal` の説明にある “nonnegative interval representative” が現コードの実名と完全一致しているか。もし `DkNNReal` が「非負代表元」専用なら問題なし。もし `DkReal` 全体の代表元と混ざる可能性があるなら、Phase 0 で namespace と型の定義を再確認する方針がすでに追加されているので、そのままでよい。

二つ目は、提出レポート本文の `## Review` が空欄になっている点じゃ。作業報告としては悪くないが、Codex 返却物として整えるなら、ここに短く次を入れると綺麗になる。

```text
Review:
Accepted as documentation-only synchronization.
The previous review findings were incorporated:
type-name policy, positive-degree strict comparison, Monoid-gated power laws,
Phase 0 workspace reconfirmation, and Core/Analytic import separation.
Lean build was not required because no Lean source files changed.
```

結論として、この同期修正は **次の実装フェーズへ進めてよい** 。
次の一手は `Frame.lean` じゃな。ここから `NatPowerFrame`、`eval`、`power`、`PowNormalForm` との変換だけを小さく閉じる。賢狼の鼻で嗅いでも、ここがいちばん安全な登山口じゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md b/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md
index 9d8e997f..895e7dfa 100644
--- a/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md
+++ b/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md
@@ -25,6 +25,23 @@ proof-carrying strict comparison    constructive
 full DkNNRealQ comparison           total as a proposition, not decidable
 ```
 
+### Type-name policy
+
+This plan intentionally uses both existing types; they are not aliases:
+
+```text
+DkNNReal:
+  a nonnegative interval representative;
+  finite endpoint inspection and executable bounded search live here.
+
+DkNNRealQ:
+  the quotient of representatives;
+  public equality, order, semiring operations, and frame evaluation live here.
+```
+
+Every observation theorem must connect its representative result to quotient
+order through `DkNNRealQ.mk`. A future rename is outside this plan.
+
 ## 2. Current implementation
 
 The public entry point `DkMath.PowerSwap` imports five modules.
@@ -206,6 +223,21 @@ with a domain carrying stronger certificates.
 
 ## 6. Feasible implementation plan
 
+### Phase 0: Reconfirm the live workspace
+
+Before each implementation phase, verify the current names rather than relying
+on this document alone:
+
+```text
+DkNNReal and DkNNRealQ definitions and namespaces
+DkMath.Analysis.DkReal.CanonicalOrder import path
+DkNNRealQ.pow_le_pow and available strict power lemmas
+DkReal.LeftSeparatedAt and mk strict-order bridge names
+DkMath.lean and DkMath.PowerSwap import effects
+```
+
+Record any renamed API in the module docstring before adapting the plan.
+
 ### Phase 1: Stabilize the existing structural core
 
 Add:
@@ -222,10 +254,18 @@ structure NatPowerFrame (α : Type u) where
   degree : Nat
 
 def NatPowerFrame.eval [Pow α Nat] (A : NatPowerFrame α) : α
+
+def NatPowerFrame.power
+    (A : NatPowerFrame α) (m : Nat) : NatPowerFrame α
 ```
 
 Avoid `Pow α α` initially. Real exponents already belong to `Branch`.
 
+The data definitions require only `[Pow α Nat]`. Theorems using
+`(a ^ n) ^ m = a ^ (n * m)` must be placed in a section with `[Monoid α]`, or
+another explicit structure that supplies `pow_mul`. This law must not be
+claimed from an arbitrary `Pow` instance.
+
 Preserve `PowNormalForm` for compatibility. Relate it to
 `NatPowerFrame Nat` by an equivalence or conversion functions instead of
 replacing it immediately.
@@ -254,8 +294,9 @@ structure NormalizesTo [Pow α Nat]
   value_eq : source.eval = target.eval
 ```
 
-Provide reflexivity, symmetry, transitivity, and composition with
-`NatPowerFrame.power`.
+Provide reflexivity, symmetry, and transitivity using equality alone.
+Composition with `NatPowerFrame.power` belongs in a `[Monoid α]` section
+because its evaluation theorem depends on `pow_mul`.
 
 Relate `HasPowNormalForm` to this generic witness. Do not implement arbitrary
 root extraction.
@@ -276,6 +317,16 @@ SameDegreeComparison
 SameDegreeStrictComparison
 ```
 
+The strict specification must carry positive degree:
+
+```lean
+structure SameDegreeStrictComparison [LT α]
+    (A B : NatPowerFrame α) : Prop where
+  same_degree : A.degree = B.degree
+  degree_pos : 0 < A.degree
+  base_lt : A.base < B.base
+```
+
 Prove generic evaluation theorems from explicit monotonicity hypotheses. Keep
 the core independent of `DkNNRealQ` and avoid requiring `LinearOrder`.
 
@@ -321,7 +372,7 @@ Initial theorems:
 NatPowerFrame.evalDk
 CosmicPowerFrame.evalDk
 eval_le_of_sameDegree_base_le
-eval_lt_of_sameDegree_base_lt, degree != 0
+eval_lt_of_sameDegree_base_lt, with 0 < degree
 eval_eq_of_normalizesTo
 cosmic_eval_le
 ```
@@ -366,6 +417,11 @@ none         -> no conclusion beyond the searched prefix
 
 Do not state completeness for finite fuel.
 
+The use of `DkNNReal` here is deliberate: endpoint inspection is a
+representative operation. Soundness must conclude statements about
+`DkNNRealQ.mk x` and `DkNNRealQ.mk y`; `compareAt` must not be defined directly
+on quotient values.
+
 ### Phase 7: Refine module exports
 
 Keep `DkMath.PowerSwap` as the compatibility umbrella. Add a lightweight
@@ -391,6 +447,15 @@ Treat `Branch` and `Contours` as the analytic layer. Moving files into an
 `Analytic` directory is optional and should only be done with compatibility
 re-export modules.
 
+Add a thin analytic entry point:
+
+```text
+DkMath.PowerSwap.Analytic
+  imports Branch and Contours
+```
+
+New structural consumers must import `DkMath.PowerSwap.Core`, not the umbrella.
+
 ### Phase 8: Consumer bridges
 
 Only after the structural and DkNNRealQ bridges stabilize:
@@ -419,13 +484,14 @@ moving or renaming all existing analytic modules at once
 The smallest low-risk sequence is:
 
 ```text
+0. Reconfirm live names and imports
 1. Frame
 2. Normalize
 3. Compare
 4. CosmicFrame
 5. PowerSwapBridge for DkNNRealQ
-6. finite StageComparison and compareUpTo
-7. public import cleanup
+6. finite StageComparison on DkNNReal and quotient soundness
+7. Core and Analytic public entry points
 8. consumer bridges
 ```
 
diff --git a/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Implementation-Plan-and-Design.md b/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Implementation-Plan-and-Design.md
index 677bc080..2217f22c 100644
--- a/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Implementation-Plan-and-Design.md
+++ b/lean/dk_math/DkMath/PowerSwap/docs/DkMath_PowerSwap-Implementation-Plan-and-Design.md
@@ -2,6 +2,36 @@
 
 DkMath.PowerSwap Implementation Plan and Design Document
 
+> **Document status (2026-06-21): historical design baseline**
+>
+> The mathematical direction remains valid, but the module names and
+> implementation order no longer describe the current workspace. New work
+> should follow
+> [the feasible implementation plan](./DkMath_PowerSwap-Current-Gap-and-Feasible-Implementation-Plan-2026-06-21.md)
+> while using this document for the original mathematical motivation.
+
+## Current alignment note
+
+The current package already contains `Basic`, `Exchange`, `NormalForm`,
+`Branch`, and `Contours`. The `Nat`-specific normal form and analytic real
+branch were implemented before the generic structural middle layer proposed
+here. The remaining work is therefore an insertion, not a restart:
+
+```text
+NatPowerFrame
+NormalizesTo
+same-degree comparison specifications
+CosmicPowerFrame
+DkNNRealQ bridge
+finite representative observation
+```
+
+The existing types have distinct roles. `DkNNReal` is an interval
+representative used by finite executable observation. `DkNNRealQ` is the
+quotient value used by public equality, order, and power comparison. Full
+quotient order is total as a proposition, but no global `DecidableLE`,
+`DecidableEq`, or `LinearOrder` is planned.
+
 ## 0. 目的
 
 `DkMath.PowerSwap.*` は、冪構造を比較・正規化するための独立した基盤層として実装する。
@@ -337,28 +367,13 @@ center < point
 DkMath/PowerSwap/Normalize.lean
 ```
 
-正規化後の frame。
-
-```lean
-structure NormalPowerFrame (α : Type u) where
-  degree : α
-  base : α
-```
-
-自然数次数版。
-
-```lean
-structure NormalNatPowerFrame (α : Type u) where
-  degree : ℕ
-  base : α
-```
-
-正規化 relation。
+正規化 relation。改訂計画では正規化専用の frame 型を重複して作らず、
+source と target の両方に `NatPowerFrame` を用いる。
 
 ```lean
 structure NormalizesTo [Pow α ℕ]
-    (A : NatPowerFrame α) (N : NormalNatPowerFrame α) : Prop where
-  value_eq : A.base ^ A.degree = N.base ^ N.degree
+    (source target : NatPowerFrame α) : Prop where
+  value_eq : source.eval = target.eval
 ```
 
 この段階では、正規化関数そのものを必ずしも作らない。
@@ -424,6 +439,17 @@ structure SameDegreeComparison [LE α] (A B : NatPowerFrame α) : Prop where
   base_le : A.base ≤ B.base
 ```
 
+厳密比較では次数 0 による値 `1` への退化を除くため、正次数を証拠として
+持つ。
+
+```lean
+structure SameDegreeStrictComparison [LT α]
+    (A B : NatPowerFrame α) : Prop where
+  same_degree : A.degree = B.degree
+  degree_pos : 0 < A.degree
+  base_lt : A.base < B.base
+```
+
 Bridge 側で、これを実値比較に変換する。
 
 ## 9. Stage 7: Cosmic decomposition
@@ -448,8 +474,8 @@ DkMath/PowerSwap/CosmicFrame.lean
 
 ```lean
 structure CosmicPowerFrame (α : Type u) where
-  x : α
-  u : α
+  core : α
+  gap : α
   degree : ℕ
 ```
 
@@ -458,14 +484,14 @@ structure CosmicPowerFrame (α : Type u) where
 ```lean
 def CosmicPowerFrame.value [Add α] [Pow α ℕ]
     (A : CosmicPowerFrame α) : α :=
-  (A.x + A.u) ^ A.degree
+  (A.core + A.gap) ^ A.degree
 ```
 
 基本定理。
 
 ```lean
 theorem CosmicPowerFrame.value_congr
-theorem CosmicPowerFrame.same_x_same_u_same_degree
+theorem CosmicPowerFrame.same_core_same_gap_same_degree
 ```
 
 比較用 frame。
@@ -474,7 +500,7 @@ theorem CosmicPowerFrame.same_x_same_u_same_degree
 structure SameCosmicDegreeComparison [Add α] [LE α]
     (A B : CosmicPowerFrame α) : Prop where
   same_degree : A.degree = B.degree
-  base_le : A.x + A.u ≤ B.x + B.u
+  base_le : A.core + A.gap ≤ B.core + B.gap
 ```
 
 DkMath 的な意味は次である。
@@ -498,44 +524,46 @@ x + u:
 
 ## 10. 依存関係の設計
 
-推奨 module 構成。
+改訂後の推奨 module 構成。
 
 ```text
-DkMath.PowerSwap.Core
-DkMath.PowerSwap.Swap
-DkMath.PowerSwap.Level
-DkMath.PowerSwap.Branch
+DkMath.PowerSwap.Basic
+DkMath.PowerSwap.Exchange
+DkMath.PowerSwap.NormalForm
+DkMath.PowerSwap.Frame
 DkMath.PowerSwap.Normalize
 DkMath.PowerSwap.Compare
 DkMath.PowerSwap.CosmicFrame
-DkMath.PowerSwap.Basic
+DkMath.PowerSwap.Core
+
+DkMath.PowerSwap.Branch
+DkMath.PowerSwap.Contours
+DkMath.PowerSwap.Analytic
+
+DkMath.PowerSwap
 ```
 
-`Basic.lean` は再 export 用。
+`DkMath.PowerSwap.Core` は軽量な structural entry point とする。
 
 ```lean
-import DkMath.PowerSwap.Core
-import DkMath.PowerSwap.Swap
-import DkMath.PowerSwap.Level
-import DkMath.PowerSwap.Branch
+import DkMath.PowerSwap.Basic
+import DkMath.PowerSwap.Exchange
+import DkMath.PowerSwap.NormalForm
+import DkMath.PowerSwap.Frame
 import DkMath.PowerSwap.Normalize
 import DkMath.PowerSwap.Compare
 import DkMath.PowerSwap.CosmicFrame
 ```
 
-解析的な `log`、`exp`、`e` を含む層は別にする。
+解析的な `log`、`exp`、`e` を含む既存モジュールには薄い入口を追加する。
 
 ```text
 DkMath.PowerSwap.Analytic
 ```
 
-または、Real 依存を避けたい場合は Analysis 側へ置く。
-
-```text
-DkMath.Analysis.PowerSwap.Analytic
-```
-
-最初の実装では `Analytic` は後回しでよい。
+既存 `DkMath.PowerSwap` は互換 umbrella として `Core + Analytic` を
+re-export する。新規の非解析 consumer は `DkMath.PowerSwap.Core` を
+import する。
 
 ## 11. DkNNRealQ Bridge の後続計画
 
@@ -638,112 +666,90 @@ PowerSwap は、DkNNRealQ 全体の comparison を一撃で解くものではな
 
 そこから DkNNRealQ Bridge が、既存の order API に渡す。
 
-## 13. 最初に作るべき最小 API
+## 13. 次に作るべき最小 API
 
-第一コミットでは、以下だけでよい。
+既存 `Basic / Exchange / NormalForm / Branch / Contours` を維持し、次の
+structural middle layer を追加する。
 
 ```text
-PowerFrame
 NatPowerFrame
-NatPowerValue
-swap
-IsPowerSwap
-PowerSwapRel
-SameDegree
-NormalNatPowerFrame
+NatPowerFrame.eval
+NatPowerFrame.power
 NormalizesTo
+SameDegree
+SameDegreeComparison
+SameDegreeStrictComparison
 CosmicPowerFrame
 CosmicPowerFrame.value
+CosmicPowerFrame.toNatPowerFrame
 ```
 
-証明は軽くする。
+`NatPowerFrame` のデータ定義と `eval` は `[Pow α ℕ]` でよい。
+`eval_power` のように `pow_mul` を使う定理は `[Monoid α]` を要求する。
 
 ```text
-swap_swap
-PowerSwapRel.refl
-PowerSwapRel.symm
-PowerSwapRel.trans
-NatPowerValue_congr
-CosmicPowerFrame.value_congr
-NormalizesTo.value_eq
+definitions:
+  [Pow α ℕ]
+
+power-law theorems:
+  [Monoid α]
 ```
 
-この段階では比較や `log` はまだ入れない。
+既存 `PowNormalForm` は置換せず、`NatPowerFrame ℕ` との変換を追加する。
 
 ## 14. 第二コミット候補
 
-第二コミットで、比較用の relation を入れる。
+比較仕様と DkNNRealQ Bridge を分離する。
 
 ```text
-SameDegreeComparison
-SameCosmicDegreeComparison
-```
+PowerSwap core:
+  SameDegree
+  SameDegreeComparison
+  SameDegreeStrictComparison
 
-DkNNRealQ に依存しない形で、比較の仕様だけを定義する。
+DkReal bridge:
+  eval equality
+  same-degree non-strict comparison
+  same-degree strict comparison with 0 < degree
+```
 
-定理は抽象的にするか、Bridge 側に送る。
+core は `DkNNRealQ` に依存しない。Bridge が既存の `pow_le_pow` と
+strict ordered-semiring API へ渡す。
 
 ## 15. 第三コミット候補
 
-第三コミットで、DkNNRealQ Bridge を開始する。
-
-```text
-DkMath.Analysis.DkReal.PowerSwapBridge
-```
-
-ここで初めて `DkNNRealQ` を使う。
-
-実装候補。
+`DkMath.Analysis.DkReal.PowerSwapBridge` を追加する。
 
 ```lean
 def NatPowerFrame.evalDk
 def CosmicPowerFrame.evalDk
 theorem evalDk_eq_of_NormalizesTo
 theorem evalDk_le_of_sameDegree_base_le
+theorem evalDk_lt_of_sameDegree_base_lt
 theorem cosmic_evalDk_le_of_same_degree_base_le
 ```
 
+strict theorem は `degree ≠ 0` ではなく `0 < degree` を主仮定にする。
+
 ## 16. 第四コミット候補
 
-第四コミットで、analytic interpretation を別層に置く。
+有限観測比較と import 境界を追加する。
 
 ```text
+StageComparison
+compareAt on DkNNReal representatives
+compareUpTo with finite fuel
+StrictCertificate
+DkMath.PowerSwap.Core
 DkMath.PowerSwap.Analytic
 ```
 
-または、
-
-```text
-DkMath.Analysis.PowerSwap.Analytic
-```
-
-ここで初めて次を扱う。
-
-$$
-\Phi(t)=\frac{\log t}{t}
-$$
-
-中心点。
-
-$$
-e
-$$
-
-分岐。
-
-```text
-left:
-  t < e
-
-center:
-  t = e
-
-right:
-  e < t
-```
+`compareAt` は代表元の rational endpoint を読むため `DkNNReal` 上に置く。
+soundness theorem は `DkNNRealQ.mk` の strict order を結論とする。
+`none` は検索範囲内で分離が見つからなかったことだけを表し、等号を意味しない。
 
-ただし、この層は noncomputable になってよい可能性がある。
-PowerSwap core は computable / structural に保つ。
+解析実装はすでに `Branch` と `Contours` に存在する。新設する
+`DkMath.PowerSwap.Analytic` は両者をまとめる薄い入口とする。
 
 ## 17. DkMath 的な解釈
 
````
`````

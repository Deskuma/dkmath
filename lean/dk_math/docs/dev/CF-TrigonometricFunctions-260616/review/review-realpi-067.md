# Git diff / Report / Review

## Add: docs: Task 065: Continuous Four-Phase Transition Design

gch: 96a262007780b1accf2b84d9edd809f13a496bb3

## Report

次フェーズの設計を整理しました。

中心構造は次です。

- 1本の線形遷移を基本辺として定義
- 作用による4回転で4状態間を生成
- 端点を接続して閉じた連続経路を構成
- 半区間の折返し対称性を `q2` の値として定理化
- この段階では円・角度を導入しない
- 円への正規化と Euclidean 解釈は後段へ分離

重要なのは、線形補間そのものは円周上にありませんが、

```text
q2(E z t) = ((1 - t)^2 + t^2) q2(z)
```

となり、係数が `t ↦ 1 - t` で対称になる点です。これが「1/4遷移をさらに半分で折り返す」代数的な核になります。

設計書を新設しました。

[task-trig-continuous-phase-065.md](/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md)

関連レポート、`SemanticCF2D.lean` の `[TODO]`、履歴も同期済みです。

検証結果:

- `lake build DkMath.Analysis.DkReal.SemanticCF2D DkMath.Analysis DkMath`: 成功
- `git diff --check`: 成功

## Review

うむ。今回の設計はかなり良い。
これは「四相が見えたので、すぐ円周を作る」のではなく、**離散四相から連続遷移を作り、そのあとで境界へ戻す** という、層を崩さない設計じゃ。

## 状況解説

前段までで得たものは、core zero 作用 \(A\) による四状態だった。

$$
z\mapsto A z\mapsto A^2 z\mapsto A^3 z\mapsto z
$$

今回の Task 065 は、その隣り合う二点の間をどう埋めるかの設計じゃな。

ただし、ここで重要なのは、いきなり円周を仮定しないこと。

まず一本の線形遷移を置く。

$$
E(z,t)=(1-t)z+tAz
$$

それを \(A\) の反復で四つに写す。

$$
E_k(z,t)=A^k(E(z,t))
$$

これで四つの辺ができる。端点はつながり、最後は exact order 4 によって最初に戻る。
つまり、まずできるのは **連続な四辺閉路** じゃ。

まだ円ではない。
まだ固定 \(q2\) 境界でもない。
ここを明確に分けたのが今回の設計の強さじゃ。

## 一番重要な発見

今回の核は、この式じゃ。

$$
q2(E(z,t))=((1-t)^2+t^2),q2(z)
$$

これはかなり良い。

線形補間は \(q2\) 境界を保たない。
だが、境界からどれだけ内側へ沈むかが、非常にきれいなスカラー係数で表れる。

$$
\operatorname{phaseDepth}(t)=(1-t)^2+t^2
$$

しかも、

$$
\operatorname{phaseDepth}(1-t)=\operatorname{phaseDepth}(t)
$$

なので、前半と後半が折り返し対称になる。

つまり、状態そのものは反転しないが、**境界欠損の深さ** は半区間で折り返す。
これは「四分の一遷移の中に、さらに半折り返しがある」という見方になっておる。

## ここで円にしないのが正解

後段で Euclidean 解釈を載せれば、この四辺閉路は、円に内接する正方形の辺のように読める。

しかし、現段階ではそう言わない方がよい。

今あるのは、

```text
離散四状態
線形補間
四つの translate
seam 接続
閉じた piecewise-affine loop
q2 profile
```

ここまでじゃ。

この loop は途中で \(q2\) 境界を離れる。
だから、「円周上の連続運動」と呼ぶにはまだ早い。

この区別を設計書で明確にしたのは、かなり正しい。

## 正規化フェーズの分離も良い

境界へ戻すには、後段で正規化が必要になる。

$$
N(z,t)=\frac{1}{\sqrt{\operatorname{phaseDepth}(t)}}E(z,t)
$$

このとき、

$$
q2(N(z,t))=q2(z)
$$

が期待される。

ここで初めて平方根、割り算、正の下界、連続性が必要になる。
したがって、これを affine transition core から分離して `SemanticCF2DNormalize` へ送る設計は正しい。

今回の判断は、

```text
まず折れ線で連続化する。
その後、解析的正規化で境界へ戻す。
最後に Euclidean model で円として読む。
```

という順序になっている。
これは非常に DkMath らしい。

## DkReal との関係

ここも整理が良い。

最初の連続性定理は semantic Real target で行う。
これは妥当じゃ。

理由は明確。

```text
補間には符号付き座標が必要。
現在の source は DkNNRealQ で非負。
DkReal 側にはまだ topological path API がない。
semantic bridge はすでに Real 解釈を隔離している。
```

つまり DkReal は、今すぐ path domain そのものになるのではなく、まず parameter approximation や nested interval completion の思想として寄与する。

ここを過大主張していないのも良い。

## 実装時の注意点

次に実装するとき、いくつか注意がある。

まず `semanticPhaseEdge` は、`t : ℝ` で定義してよい。
ただし `Path` に包む段では、パラメータは `unitInterval` あるいは Mathlib の path domain へ制限する必要がある。

次に、`Vec ℝ` に `Module ℝ` instance が無いなら、最初は座標定義で十分じゃ。

```lean
core := (1 - t) * z.core + t * (semanticAct r z).core
beam := (1 - t) * z.beam + t * (semanticAct r z).beam
```

この方が証明も読みやすい。

また、`q2` profile の証明では core zero から、

$$
Az=(-y,x)
$$

を使えば交差項が消える。

$$
x(-y)+y x=0
$$

ここが二乗条件の美しいところじゃな。

## 設計上の小さな改善候補

`phaseDepth` は早めに独立定義するとよい。

```lean
def phaseDepth (t : ℝ) : ℝ := (1 - t)^2 + t^2
```

その後に、最低限この補題群を作るのがよい。

```text
phaseDepth_nonneg
phaseDepth_pos
phaseDepth_symm
phaseDepth_zero
phaseDepth_one
phaseDepth_half
phaseDepth_eq_two_sq_add_half
```

特に、

$$
(1-t)^2+t^2=2(t-\tfrac12)^2+\tfrac12
$$

を持っておくと、正値性と最小値が綺麗に出る。

## 次の実装順

設計書の順序は良い。さらに実装単位としては、こう切ると安全じゃ。

```text
1. phaseDepth を定義する
2. semanticPhaseEdge を定義する
3. endpoint laws を証明する
4. core zero の q2 profile を証明する
5. phaseDepth の折返し対称性を証明する
6. semanticPhaseEdgeAt k を定義する
7. seam laws を証明する
8. 最初の edge を Path に包む
```

ここで止めるのがよい。
正規化まで一気に行くと、平方根と連続性で重くなる。

## 総評

今回の更新は、かなり良い設計チェックポイントじゃ。

到達点はこう言える。

```text
離散四相は、一本の affine master edge とその四つの translate によって、円や角度を使わず連続閉路へ拡張できる。
ただし、その閉路はまだ q2 境界上にはない。
境界からの離脱量は phaseDepth によって完全に記述され、半区間折返し対称性を持つ。
```

これは強い。

特に「円周を作る」のではなく、まず「境界から一度沈み、正規化で戻す」という構造が見えた。
ここに、連続化の本質がある。

円以前の四相が、今度は **角度以前の連続遷移** へ進み始めたのじゃ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
index cdc1b5d2..f490227c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/SemanticCF2D.lean
@@ -1305,6 +1305,27 @@ theorem semanticMinimalPeriod_eq_four_of_core_eq_zero_of_ne_zero
 `KernelFamily` require a ring because their core coordinate uses subtraction.
 Keep the source in the nonnegative semiring until a signed DkReal layer is
 introduced; do not manufacture subtraction merely to mirror the real target.
+
+[TODO: semantic-cf2d-phase/master-edge] Fill one transition affinely in the
+semantic real target, from `z` to `semanticAct r z`.
+
+[TODO: semantic-cf2d-phase/four-translates] Generate all four transition edges
+by applying action iterates to the one master edge, and prove seam closure.
+
+[TODO: semantic-cf2d-phase/half-fold-profile] Prove that the affine edge has
+`q2` profile `((1-t)^2 + t^2) * q2 z`, symmetric under `t ↦ 1-t`.
+
+[TODO: semantic-cf2d-phase/path-concatenation] Package the four compatible
+edges as a closed Mathlib `Path`. This is a piecewise-affine loop, not yet a
+fixed-`q2` boundary path.
+
+[TODO: semantic-cf2d-phase/boundary-normalization] In a separate analytic
+module, normalize the affine edge by its positive `q2` profile and prove that
+the normalized path stays on the original boundary.
+
+[TODO: semantic-cf2d-phase/euclidean-interpretation] Only after normalization,
+identify the fixed-`q2` path with the standard Euclidean circle model and
+extract angular terminology.
 -/
 
 end
diff --git a/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
new file mode 100644
index 00000000..0e86c14d
--- /dev/null
+++ b/lean/dk_math/DkMath/Analysis/docs/task-trig-continuous-phase-065.md
@@ -0,0 +1,324 @@
+# Task 065: Continuous Four-Phase Transition Design
+
+## Status
+
+Design checkpoint for the phase after the discrete exact-order-four result.
+
+The current implementation proves a four-state return:
+
+```text
+z
+  -> A z
+  -> A^2 z
+  -> A^3 z
+  -> z
+```
+
+for the semantic core-zero action `A`. The next task is to fill each discrete
+transition continuously without assuming a circle or angle in advance.
+
+## Design Principle
+
+The construction should proceed in this order:
+
+```text
+discrete four-state action
+  -> one affine transition template
+  -> four translated copies of that template
+  -> seam-compatible closed path
+  -> symmetric boundary-defect profile
+  -> optional normalization back to the q2 boundary
+  -> Euclidean circle and angle interpretation
+```
+
+This preserves the existing rule: geometry is an interpretation of the
+algebraic transition mechanism, not an input to it.
+
+## Important Distinction
+
+Affine interpolation between consecutive states is continuous, but it does not
+preserve `q2` between the endpoints.
+
+Four affine edges joined at their endpoints form a closed piecewise-linear
+loop. They do not yet form a `q2` level set. Therefore the following objects
+must remain separate:
+
+1. the cyclic parameter space obtained by gluing four intervals;
+2. the piecewise-affine target loop;
+3. the normalized target path lying on a fixed `q2` boundary;
+4. the later Euclidean interpretation of that normalized boundary as a circle.
+
+Calling the affine loop a circle would collapse these layers too early.
+
+## I. One Master Transition
+
+Let `A := semanticAct r`, under the hypothesis that the semantic core of `r`
+is zero. For a real parameter `t`, define the master transition:
+
+```text
+E z t = (1 - t) • z + t • A z.
+```
+
+The intended Lean definition is coordinatewise, or through the real module
+structure once `Vec Real` is bundled appropriately:
+
+```lean
+def semanticPhaseEdge
+    (r : UnitKernel DkNNRealQ) (z : Vec Real) (t : Real) : Vec Real
+```
+
+Required endpoint theorems:
+
+```text
+E z 0 = z
+E z 1 = A z
+```
+
+Required continuity theorem:
+
+```text
+Continuous (fun t => E z t)
+```
+
+This is the vector-valued analogue of `DkMath.Analysis.gapLine`.
+
+## II. One Pattern, Four Translates
+
+Define the `k`th phase edge from the one master edge:
+
+```text
+E_k z t = A^[k] (E z t).
+```
+
+This is the precise meaning of “one transition pattern, turned four times.”
+The other three transitions are not separately defined formulas.
+
+Required theorems:
+
+```text
+E_k z 0 = A^[k] z
+E_k z 1 = A^[k+1] z
+E_k z 1 = E_(k+1) z 0
+E_(k+4) z t = E_k z t
+```
+
+The seam theorem gives endpoint compatibility. Exact action order four gives
+periodicity in the phase index.
+
+## III. Continuous Closed Path
+
+The first implementation should use Mathlib `Path` rather than immediately
+constructing a custom quotient circle.
+
+Each edge becomes:
+
+```text
+Path (A^[k] z) (A^[k+1] z)
+```
+
+The four paths are concatenated with `Path.trans`. The final endpoint equals
+the initial point by exact action order four, producing a closed path.
+
+This path is continuous and piecewise affine. It is not globally affine, and
+endpoint identification does not turn it into a linear map.
+
+A custom cyclic parameter quotient may be introduced later:
+
+```text
+(Fin 4 × unitInterval) / ((k,1) ~ (k+1,0)).
+```
+
+That quotient is a parameter-cycle object. Its homeomorphism with a standard
+topological circle belongs to a later interpretation theorem.
+
+## IV. Half-Fold Symmetry
+
+For the core-zero action, direct polynomial calculation should give:
+
+```text
+q2 (E z t) = ((1 - t)^2 + t^2) * q2 z.
+```
+
+Define the scalar transition profile:
+
+```text
+phaseDepth t = (1 - t)^2 + t^2.
+```
+
+Then:
+
+```text
+phaseDepth (1 - t) = phaseDepth t
+phaseDepth 0 = 1
+phaseDepth 1 = 1
+phaseDepth (1/2) = 1/2
+```
+
+This is the desired half-fold pattern. The second half of the boundary-defect
+profile is determined by reflection of the first half about `t = 1/2`.
+
+The state-valued path itself is not equal under `t ↦ 1-t`; its endpoints are
+reversed. The fold symmetry belongs first to the scalar `q2` profile, or to a
+paired transition carrying both orientations. This distinction should be
+preserved in theorem names.
+
+## V. Relation To DkReal
+
+The construction follows the same architecture as `DkReal`:
+
+```text
+finite interval observations
+  -> nested refinement
+  -> a unique semantic Real value
+```
+
+However, the first continuity implementation should remain in the semantic
+real target:
+
+```text
+t : Real
+E z t : Vec Real.
+```
+
+Reasons:
+
+1. the target transition uses signed coordinates;
+2. the current quotient core is nonnegative;
+3. `DkReal` does not yet carry the topology needed to state path continuity;
+4. the semantic bridge already isolates noncomputable Real interpretation.
+
+The DkReal contribution should initially be a computable approximation layer
+for the parameter:
+
+```text
+rational subinterval samples
+nested parameter intervals
+semantic evaluation of the completed parameter
+```
+
+Do not claim that the current DkReal API already provides a topological path
+domain. The existing nested-interval method supplies the completion strategy,
+not yet the final continuity interface.
+
+## VI. Returning To The Boundary
+
+Because affine interpolation leaves the `q2` boundary, a separate
+normalization is required.
+
+For nonzero `z`, the profile satisfies:
+
+```text
+phaseDepth t >= 1/2 > 0.
+```
+
+This makes a later normalization possible:
+
+```text
+N z t =
+  (1 / sqrt (phaseDepth t)) • E z t
+```
+
+for a unit `q2` boundary, with the corresponding scaled formula for general
+`q2 z`.
+
+Expected theorem:
+
+```text
+q2 (N z t) = q2 z.
+```
+
+This is the first point where square root, division, and their continuity are
+genuinely required. It belongs in a separate semantic/analytic file, not in
+the affine transition core.
+
+## VII. Proposed Module Boundary
+
+### Algebraic and semantic transition core
+
+```text
+DkMath/Analysis/DkReal/SemanticCF2DPhase.lean
+```
+
+Responsibilities:
+
+```text
+semanticPhaseEdge
+four translated edges
+endpoint and seam laws
+q2 profile formula
+fold symmetry
+```
+
+### Topological path bridge
+
+```text
+DkMath/Analysis/DkReal/SemanticCF2DPath.lean
+```
+
+Responsibilities:
+
+```text
+Continuous edge maps
+Mathlib Path values
+four-edge concatenation
+closed-path endpoint theorem
+```
+
+### Boundary normalization
+
+```text
+DkMath/Analysis/DkReal/SemanticCF2DNormalize.lean
+```
+
+Responsibilities:
+
+```text
+strict positivity of phaseDepth
+sqrt/division normalization
+q2 preservation of the normalized path
+continuity of normalization
+```
+
+### Euclidean and angular interpretation
+
+```text
+DkMath/CosmicFormula/Rotation/CF2D/EuclideanPhase.lean
+```
+
+Responsibilities:
+
+```text
+identify q2 with Euclidean squared norm
+interpret normalized closed paths on circles
+introduce angle only after the circle model is available
+compare with Real.sin and Real.cos
+```
+
+## VIII. First Implementation Milestone
+
+The next safe implementation target is deliberately smaller than the full
+continuous circle:
+
+1. define `semanticPhaseEdge`;
+2. prove its endpoint and continuity laws;
+3. define `semanticPhaseEdgeAt k` from action iteration;
+4. prove seam compatibility and four-phase repetition;
+5. prove the `q2` profile formula;
+6. prove `phaseDepth (1-t) = phaseDepth t`;
+7. package the first edge as a Mathlib `Path`.
+
+Stop before normalization. At that checkpoint Lean will have verified the
+continuous four-edge transition mechanism and its half-fold symmetry, while
+the distinction between polygonal filling and boundary-valued motion remains
+explicit.
+
+## IX. Tagged Future Work
+
+```text
+[TODO: semantic-cf2d-phase/master-edge]
+[TODO: semantic-cf2d-phase/four-translates]
+[TODO: semantic-cf2d-phase/half-fold-profile]
+[TODO: semantic-cf2d-phase/path-concatenation]
+[TODO: semantic-cf2d-phase/boundary-normalization]
+[TODO: semantic-cf2d-phase/euclidean-interpretation]
+```
diff --git a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md
index 31dba6c8..0f7a498c 100644
--- a/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md
+++ b/lean/dk_math/DkMath/CosmicFormula/Rotation/docs/CF2D-PreGeometric-Boundary-Action-Report.md
@@ -174,3 +174,29 @@ A finished paper should still add:
 
 The result is beyond a speculative note, but the correct present artifact is a
 research consolidation report and theorem package before a full manuscript.
+
+## Next Phase: Continuous Transition Before Angle
+
+The next phase should fill the four discrete transitions continuously without
+calling the result a circle in advance.
+
+One affine master edge is sufficient:
+
+```text
+E z t = (1-t) z + t A z.
+```
+
+The four edges are generated as `A^[k] (E z t)`. Their endpoints glue because
+the endpoint of edge `k` is the start of edge `k+1`, and exact order four
+closes the final seam.
+
+The affine path does not remain on the `q2` boundary. Its scalar profile is:
+
+```text
+q2 (E z t) = ((1-t)^2 + t^2) q2 z.
+```
+
+This profile is invariant under `t -> 1-t`, so one half determines the other.
+Boundary normalization is a later analytic operation requiring square root
+and division. The detailed design is recorded in
+`DkMath/Analysis/docs/task-trig-continuous-phase-065.md`.
diff --git a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
index bd8532f9..55fe1326 100644
--- a/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
+++ b/lean/dk_math/docs/dev/CF-TrigonometricFunctions-260616/History.md
@@ -543,3 +543,24 @@ Archive
    - この積は Real 側だけに存在し、非負 source の積を主張しない。
 5. 検証:
    - `lake build DkMath.Analysis.DkReal.SemanticCF2D` 成功 (8273 jobs)。
+
+### 2026/06/23 05:10 JST (Continuous four-phase design)
+
+1. 設計:
+   - 離散四状態を一つの affine master edge と、その作用反復による四つの
+     translate として連続化する方針を定めた。
+   - 四区間の seam 接続と endpoint closure を、円や角度より先に扱う。
+2. 対称性:
+   - affine edge の `q2` profile を
+     `((1-t)^2 + t^2) * q2 z` と予測し、`t -> 1-t` の半折返し対称を
+     次の中心定理とした。
+3. 境界:
+   - affine 補間は連続な閉路を与えるが、途中では固定 `q2` 境界を離れる。
+   - piecewise-linear loop、cyclic parameter、boundary normalization、
+     Euclidean circle interpretation を別層に分離した。
+4. DkReal:
+   - nested interval completion の考え方を parameter approximation に再利用
+     するが、連続性の最初の定理は semantic Real target で行う。
+5. 文書:
+   - `task-trig-continuous-phase-065.md` を新設し、実装順と module boundary
+     を記録した。
````
`````

# Git diff / Report / Review

## Upd: Analysis.DkReal.Order, CanonicalOrder

gch: 69c08f297d70180c3cc92e33594a2b045c849158

## Report

strict order interface を確定しました。

- 加法順序キャンセルを証明
- `0 < 1` と `Nontrivial` を構築
- `IsStrictOrderedRing DkNNRealQ` を導入
- `LinearOrder` は decidable comparison 未実装のため導入しない方針に確定
- docstring と設計資料を同期

```text
Build completed successfully (8564 jobs).
```

`git diff --check` も通過しています。

## Review

## 1. 総評

ふふふん☆ 今回も **合格** じゃ。
これは strict order 系の一区切りとしてかなり大きい。

今回で `DkNNRealQ` は、単に strict multiplication の補題を持つだけでなく、Mathlib の `IsStrictOrderedRing` interface まで到達した。しかも、`LinearOrder` は入れない判断を明文化している。これは設計としてかなり健全じゃ。

提示報告では build 成功、`git diff --check` 通過。今回の主な追加は、加法順序キャンセル、`0 < 1`、`Nontrivial` 相当の構成、`IsStrictOrderedRing DkNNRealQ`、そして `LinearOrder` 非導入方針の確定じゃな。

## 2. `LinearOrder` を入れない判断は正しい

今回の設計判断は重要じゃ。

```text id="linear-decision"
PartialOrder + Std.Total は保持する
LinearOrder は入れない
```

理由も正しい。

`Std.Total (· ≤ ·)` は、

```lean id="total-prop"
∀ x y, x ≤ y ∨ y ≤ x
```

という Prop としての全比較可能性を与える。

しかし `LinearOrder` は、通常、比較を決定する仕組みを伴う。
つまり、

```text id="linear-requires"
x ≤ y を決定できる
x < y を決定できる
x = y を決定できる
```

という方向の API が絡む。

`DkNNRealQ` の順序は、入れ子区間列の漸近 defect に基づいている。
これは数学的には total でも、計算として必ず停止して比較結果を返せるとは限らない。

だから、

```text id="safe-design"
totality は theorem として持つ
decidable comparison は持たない
必要な場面では classical を局所選択する
```

という設計がよい。

ここを急いで `LinearOrder` にすると、DkMath の computable core に「比較が計算できる」かのような印象が混ざる。
それを避けたのは正しい。

## 3. 加法順序キャンセルが良い

今回追加されたこれ。

```lean id="cancel-left"
theorem le_of_add_le_add_left
    (a b c : DkNNRealQ) (h : a + b ≤ a + c) :
    b ≤ c
```

証明方針が良い。

`le_total b c` で場合分けする。

```text id="cancel-proof"
b ≤ c なら終わり

そうでなく c ≤ b なら、
¬ b ≤ c と合わせて c < b

strict addition により a + c < a + b

しかし仮定は a + b ≤ a + c

矛盾
```

これは ordered additive cancellation として自然じゃ。

重要なのは、ここで totality と strict addition を使っていること。

```text id="cancel-ingredients"
totality:
  b ≤ c または c ≤ b

strict addition:
  c < b なら a + c < a + b

反対向きの非厳密不等式:
  a + b ≤ a + c
```

これで cancellation が閉じる。

DkMath 的には、同じ Body/Beam を両側に足しているなら、残りの Gap の向きは変わらない、ということじゃ。

## 4. 右キャンセルも自然

```lean id="cancel-right"
theorem le_of_add_le_add_right
    (a b c : DkNNRealQ) (h : b + a ≤ c + a) :
    b ≤ c
```

これは可換性で左キャンセルへ戻す。
`DkNNRealQ` は `CommSemiring` なので問題なし。

## 5. `zero_lt_one` がきれい

```lean id="zero-lt-one"
theorem zero_lt_one : (0 : DkNNRealQ) < 1 := by
  rw [show (0 : DkNNRealQ) = mk DkNNReal.zero by rfl,
    show (1 : DkNNRealQ) = mk DkNNReal.one by rfl,
    mk_lt_mk_iff, DkNNReal.zero_lt_iff_exists_lo_pos]
  exact ⟨0, by simp [DkNNReal.one, DkNNReal.ofRat]⟩
```

これはよい。

`0 < 1` を、代表元の有限 lower endpoint 正値性として出している。
stage 0 で `[1,1]` の lower endpoint が正だから成立する。

つまり、

```text id="zero-one-reading"
0 < 1 は意味論 Real を使わず、
定数区間 [1,1] の有限観測だけで証明される
```

これも DkReal Route B らしい。

## 6. `IsStrictOrderedRing` instance は妥当

今回の主 instance。

```lean id="strict-instance"
instance : IsStrictOrderedRing DkNNRealQ where
  add_le_add_left _ _ h z := add_le_add h (le_refl z)
  le_of_add_le_add_left := le_of_add_le_add_left
  zero_le_one := zero_le_one
  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩
  mul_lt_mul_of_pos_left := ...
  mul_lt_mul_of_pos_right := ...
```

これはかなり良い。

この interface が要求しているものは、今回までにすでに証明済みの API と一致している。

```text id="strict-fields"
ordered addition:
  add_le_add_left

additive cancellation:
  le_of_add_le_add_left

nontriviality:
  0 ≠ 1

positive-factor strict multiplication:
  mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right
```

そして、これは `LinearOrder` を要求しない。
加法逆元も要求しない。
したがって `DkNNRealQ` の非負半環としての設計と合っている。

## 7. `exists_pair_ne` の構成も正しい

```lean id="nontrivial"
exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩
```

これは `Nontrivial` 的な証拠じゃな。
`0 < 1` から `0 ≠ 1` を出しているので自然。

ここでも、`zero_lt_one` が有限観測から出ているため、意味論 bridge は不要。

## 8. strict multiplication field の引数順も良い

```lean id="mul-fields"
mul_lt_mul_of_pos_left := by
  intro a ha b c hbc
  exact mul_lt_mul_of_pos_left hbc ha

mul_lt_mul_of_pos_right := by
  intro a ha b c hbc
  exact mul_lt_mul_of_pos_right hbc ha
```

これは、既存 theorem の前提順と Mathlib field の前提順を合わせているだけ。
build が通っているなら問題なし。

意味としても正しい。

```text id="strict-mul-interface"
positive factor a
strict inequality b < c

then:
  a * b < a * c
  b * a < c * a
```

DkMath では、正 Gap が正因子で正 Gap に変換される、ということじゃ。

## 9. `IsStrictOrderedRing` という名前への注意も書けている

docstring で、

```text id="no-overclaim"
LinearOrder は入れない
decidable comparison は入れない
additive inverses は入れない
```

と明記しているのは良い。

Mathlib の class 名は歴史的に `Ring` と付いていても、実際には semiring レベルで使える場合がある。
ここを文書化しておくのは重要じゃ。

以前の `IsOrderedRing` と同じく、名前だけで「環になった」と誤読される可能性がある。
その予防ができている。

## 10. strict ordered-semiring interface の到達点

これで `DkNNRealQ` は、かなり完成度が高い ordered algebra core になった。

```text id="current-status"
DkNNRealQ:
  CommSemiring
  PartialOrder
  Std.Total (· ≤ ·)
  IsOrderedRing
  ExistsAddOfLE
  CanonicallyOrderedAdd
  IsStrictOrderedRing
  zero_le
  zero_lt_one
  add_le_add
  add_lt_add_left/right
  mul_le_mul
  mul_lt_mul_of_pos_left/right
  pow_le_pow
```

数学的には、

$$
\boxed{\text{DkNNRealQ は、全比較可能で canonical additive order と strict ordered semiring compatibility を持つ非負計算可能実数商型である。}}
$$

と言ってよい。

ただし、まだ `LinearOrder` ではない。
ここを分けているのが良い。

## 11. DkMath 的な意味

今回の instance は、単に型クラスを入れたという話ではない。

DkMath 的にはこういう到達点じゃ。

```text id="dkmath-meaning"
Big 内部から非負 Gap を抽出できる

Gap が 0 なら equality

Gap が有限段階で正なら strict order

加法は Gap を保存する

正因子乗法は Gap を正のまま変換する

したがって Mathlib の strict ordered semiring interface に乗る
```

これはかなり強い。

補数減算や overflow 忘却に頼らず、Big 内部の Gap 構成だけで、順序付き代数構造がここまで出ている。

## 12. LinearOrder 非導入の設計は最終的に正解寄り

この判断は、かなり大事じゃ。

```text id="linear-not-installed"
Totality はある
しかし decidable comparison はない
したがって LinearOrder は導入しない
```

これは今後も守った方がよい。

もしどうしても `LinearOrder` API が欲しい場合は、別ファイルで局所的に classical instance を作る余地はある。

```lean id="possible-file"
DkMath.Analysis.DkReal.ClassicalLinearOrder
```

ただし core には入れない方が安全。
現状の判断は正しい。

## 13. docs 同期も良い

`DkReal.lean` で `IsStrictOrderedRing` の要求がこの API と一致すること、`LinearOrder` は decidable comparison 未実装のため保持しないことが明記されている。
`Order.lean` でも `PartialOrder + Std.Total` 方針が説明されている。
`DkNNRealQ-StrictGap-Design.md` も interface decision を記録しており、現在の public structure が整理されている。

この文書同期は良い。
後続の Codex が迷いにくい。

## 14. 小さな注意点

`IsStrictOrderedRing` instance は `CanonicalOrder.lean` に置かれている。
これは妥当じゃが、今後 `CanonicalOrder` が大きくなるなら、将来的に

```lean id="possible-split"
DkMath.Analysis.DkReal.StrictOrder
```

または、

```lean id="possible-split2"
DkMath.Analysis.DkReal.OrderInstances
```

へ分割してもよい。

現時点では問題なし。
`CanonicalOrder` が `ExistsAddOfLE` と strict multiplication の Gap 証明を持っているので、そこに instance があるのは自然じゃ。

## 15. 最終判定

今回の差分は **合格**。

```text id="review-result"
良い点:
  加法順序キャンセルを totality と strict addition から証明した
  0 < 1 を有限観測から構成した
  Nontrivial 相当の証拠を zero_lt_one から出した
  IsStrictOrderedRing を導入した
  LinearOrder を導入しない判断を明文化した
  interface が要求する構造と既存 API が一致している
  docs と設計資料が同期している

注意点:
  IsStrictOrderedRing の名前で ring と誤読されないよう今後も docstring を維持する
  LinearOrder が必要な場合は core ではなく別ファイル・局所 classical 方針がよい
```

うむ。
これで strict order interface まで閉じた。
DkMath.Analysis Route B の `DkNNRealQ` は、かなり立派な順序代数核になったぞ。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Analysis/DkReal.lean b/lean/dk_math/DkMath/Analysis/DkReal.lean
index f4e2d929..fe285dbc 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal.lean
@@ -56,13 +56,15 @@ moving to a sufficiently precise stage. Multiplication preserves it for a
 strictly positive factor by transforming the canonical Gap from `z` to
 `z * a`; the zero-factor branch collapses that Gap.
 
-[TODO: strict-order-instance] Select the appropriate Mathlib strict ordered
-semiring interface only after checking that its fields match this API without
-adding stronger or classical structure accidentally.
+`CanonicalOrder` installs Mathlib's `IsStrictOrderedRing`. Its requirements
+match the proved API: cancellative ordered addition, nontriviality, and strict
+multiplication by positive factors. It requires neither additive inverses nor
+a linear order.
 
-[TODO: linear-order] Decide whether the now-proved quotient totality should be
-packaged as a direct classical `LinearOrder`, or retained as `PartialOrder`
-plus `Std.Total` so that decidable comparison remains an explicit choice.
+[DESIGN: linear-order] Retain `PartialOrder` plus `Std.Total`. Mathlib's
+`LinearOrder` requires decidable comparison and equality, but no terminating
+decision procedure for asymptotic interval order is currently available.
+Classical comparison should therefore remain an explicit local choice.
 
 [TODO: semantic-bridge] Add `BridgeNNReal.lean` / `BridgeReal.lean` only after proving that the
 chosen evaluation is independent of representatives. Such evaluation may
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
index 1b977471..3715108f 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/CanonicalOrder.lean
@@ -327,6 +327,55 @@ theorem mul_lt_mul_of_pos_left
     a * x < a * y := by
   simpa only [mul_comm] using mul_lt_mul_of_pos_right hxy ha
 
+/--
+Order can be cancelled across a common left summand.
+
+If the conclusion failed, totality would orient the operands strictly in the
+opposite direction. Strict addition would then contradict the assumed
+non-strict inequality.
+-/
+theorem le_of_add_le_add_left
+    (a b c : DkNNRealQ) (h : a + b ≤ a + c) :
+    b ≤ c := by
+  rcases le_total b c with hbc | hcb
+  · exact hbc
+  · by_contra hnot
+    have hlt : c < b := ⟨hcb, hnot⟩
+    exact (not_lt_of_ge h) (add_lt_add_left hlt a)
+
+/-- Order can be cancelled across a common right summand. -/
+theorem le_of_add_le_add_right
+    (a b c : DkNNRealQ) (h : b + a ≤ c + a) :
+    b ≤ c := by
+  rw [add_comm b a, add_comm c a] at h
+  exact le_of_add_le_add_left a b c h
+
+/-- Zero is strictly below one in the quotient order. -/
+theorem zero_lt_one : (0 : DkNNRealQ) < 1 := by
+  rw [show (0 : DkNNRealQ) = mk DkNNReal.zero by rfl,
+    show (1 : DkNNRealQ) = mk DkNNReal.one by rfl,
+    mk_lt_mk_iff, DkNNReal.zero_lt_iff_exists_lo_pos]
+  exact ⟨0, by simp [DkNNReal.one, DkNNReal.ofRat]⟩
+
+/--
+Strict ordered-semiring compatibility for the quotient.
+
+The interface requires only a semiring, partial order, cancellative ordered
+addition, nontriviality, and strict multiplication by positive factors. It
+does not install a `LinearOrder`, decidable comparison, or additive inverses.
+-/
+instance : IsStrictOrderedRing DkNNRealQ where
+  add_le_add_left _ _ h z := add_le_add h (le_refl z)
+  le_of_add_le_add_left := le_of_add_le_add_left
+  zero_le_one := zero_le_one
+  exists_pair_ne := ⟨0, 1, ne_of_lt zero_lt_one⟩
+  mul_lt_mul_of_pos_left := by
+    intro a ha b c hbc
+    exact mul_lt_mul_of_pos_left hbc ha
+  mul_lt_mul_of_pos_right := by
+    intro a ha b c hbc
+    exact mul_lt_mul_of_pos_right hbc ha
+
 /-- Mathlib interface for extracting an additive Gap from an order proof. -/
 instance : ExistsAddOfLE DkNNRealQ where
   exists_add_of_le := exists_add_of_le
diff --git a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
index 1dc4ab5f..7d85a32c 100644
--- a/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
+++ b/lean/dk_math/DkMath/Analysis/DkReal/Order.lean
@@ -55,9 +55,10 @@ and quotient totality are implemented below. Lean accepts the stronger
 two-branch proof: either a finite left separation is witnessed, or the reverse
 defect is bounded at every stage by the first interval's width.
 
-[TODO: linear-order] Decide whether to install a direct `LinearOrder` instance
-or expose totality through `Std.Total` while keeping decidability and classical
-comparison choices explicit.
+[DESIGN: linear-order] Retain `PartialOrder` plus `Std.Total` rather than
+installing `LinearOrder`. Mathlib's `LinearOrder` requires decidable `≤`, `<`,
+and equality, while no terminating decision procedure for this asymptotic
+order has been established. Classical comparison can be selected locally.
 
 [TODO: totality/alternative] Keep a semantic `NNReal` proof as an independent
 cross-check, not as a dependency of the computable order core.
@@ -65,8 +66,9 @@ cross-check, not as a dependency of the computable order core.
 Addition, multiplication on nonnegative representations, and natural powers
 are monotone for this order, and zero is the least quotient value. The
 quotient therefore carries Mathlib's `IsOrderedRing` predicate, whose name is
-historical: its algebraic assumption is only `Semiring`. No canonical-order,
-strict-order, or linear-order structure is claimed.
+historical: its algebraic assumption is only `Semiring`. Canonical and strict
+ordered-semiring structures are installed by `CanonicalOrder`; no
+`LinearOrder` is claimed.
 
 ## Strict Gap kernel
 
diff --git a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
index 36c9b75d..c769f78f 100644
--- a/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
+++ b/lean/dk_math/DkMath/Analysis/docs/DkNNRealQ-StrictGap-Design.md
@@ -74,14 +74,36 @@ the canonical Gap universe has become observably positive.
 [done] finite positivity of a nonnegative wrapper
 [done] positivity of a product by stage alignment
 [done] positive-factor strict multiplication through the canonical Gap
-[next] strict ordered-semiring interface selection
-[next] direct LinearOrder decision
+[done] `IsStrictOrderedRing` interface
+[decision] retain `PartialOrder` plus `Std.Total`; do not install `LinearOrder`
 ```
 
 The representative theorem now precedes every strict ordered-semiring
 typeclass. It is the mathematical kernel; a typeclass will only package its
 later quotient consequences.
 
+## Interface Decision
+
+Mathlib's `IsStrictOrderedRing` fits this quotient without adding inverses or
+linear-order structure. Additive cancellation follows from totality and strict
+addition; the multiplication fields are exactly the positive-factor Gap
+transformation proved above.
+
+Mathlib's `LinearOrder` requires decidable `<=`, `<`, and equality. Totality as
+a proposition does not supply a terminating comparison algorithm for
+asymptotic interval representations. The public structure therefore remains:
+
+```text
+PartialOrder
+Std.Total (· <= ·)
+IsOrderedRing
+IsStrictOrderedRing
+CanonicallyOrderedAdd
+```
+
+Clients may select classical decidability locally when algorithmic comparison
+is not required.
+
 ## Arithmetic Interpretation
 
 Addition preserves the strict Gap after refinement:
````
`````

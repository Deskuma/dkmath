# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 23326ca36bf566be0151da3471c58193ca386d53

## Report

Implemented and verified.

Added in [PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1418):

- `SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`

Added report:

- [report-petal-279.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-279.md)

Verification passed:

- `lake build DkMath.Collatz.PetalBridge.PressureState`
- `lake build DkMath.Collatz.PetalBridge`
- `git diff --check`

What is now established as fact: for any `SourcePressureForwardPairComparisonState L W W'`, the boundary corridor can be used as one bundled dichotomy:

```lean
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    (r + W.val + 1 = r + (W'.val - 1) ∨
      r + W.val + 1 < r + (W'.val - 1))
```

So both corridor endpoints are nonpositive, and the corridor is either a contact corridor with one shared boundary index or a genuine gap corridor with two ordered nonpositive boundary endpoints. This still does not prove that every interior index of a strict corridor is nonpositive.

現在、以下のことが事実として確立されています。任意の `SourcePressureForwardPairComparisonState L W W'` に対して、境界コリドーは一つのまとまった二分法として扱うことができます。

```lean
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
(r + W.val + 1 = r + (W'.val - 1) ∨
r + W.val + 1 < r + (W'.val - 1))
```

したがって、コリドーの両端点は非正であり、そのコリドーは、境界インデックスを一つ共有する「接触コリドー（contact corridor）」か、あるいは順序付けられた二つの非正の境界端点を持つ「真のギャップコリドー（genuine gap corridor）」のいずれかとなります。ただし、これだけでは、厳密なコリドー（strict corridor）の内部インデックスがすべて非正であることまでは証明されません。

## Review

## 判定

採用。
`FPC` の boundary corridor が、符号つきの contact/gap 分岐として一つに束ねられた。

追加：

```lean id="fp3s4b"
SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt
```

これで `SourcePressureForwardPairComparisonState L W W'` から、

```lean id="pg2w7j"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    (r + W.val + 1 = r + (W'.val - 1) ∨
      r + W.val + 1 < r + (W'.val - 1))
```

が直接取れる。`boundary_corridor_surface` と `boundary_corridor_eq_or_lt` を束ねる薄い theorem として、目的通りじゃ。

## 実装レビュー

証明は非常に良い。

```lean id="uxynxg"
rcases h.boundary_corridor_surface with ⟨hnextL, hprevR, _hle⟩
exact ⟨hnextL, hprevR, h.boundary_corridor_eq_or_lt⟩
```

既存 API から必要な成分だけを取り出し、算術分岐を添えている。
新しい主張を混ぜていないので安全。

今回の theorem は、証明力を増やすというより **caller-facing surface の整理** じゃな。後段で corridor 分岐を扱うとき、毎回

```text id="g1y6ab"
非正端点を取る
順序分岐を取る
それらを組み直す
```

という作業をしなくて済む。

## 数学的意味

これで、二つの正中心の間は次の局所形として読める。

```text id="x0sow2"
left positive center
  ↓
left next boundary <= 0
  ↓
contact or gap corridor
  ↓
right previous boundary <= 0
  ↓
right positive center
```

そして corridor は二通り。

```text id="i3zkmc"
contact:
  left next boundary = right previous boundary

gap:
  left next boundary < right previous boundary
```

これは、正 pulse が連続して詰まるのではなく、非正 boundary を介してしか次の正中心へ進めない、という局所構造をかなり見やすくしている。

## 注意点

ここも report の注意通りでよい。

まだ言っていない：

```text id="n0r5jm"
strict gap corridor 内の全 index が非正
全 positive center の大域列構造
任意 witness の網羅
window 全体の disjointness
Collatz 収束
```

言えているのは、明示された `FPC` の二中心について、**非正端点つき corridor が contact/gap に分岐する** ところまでじゃ。

## 現在の到達点

```text id="ay447j"
FPC
  -> two positive centers
  -> no immediate successor contact
  -> nonpositive corridor endpoints
  -> contact-or-gap corridor split
  -> sign-bundled contact-or-gap surface
```

局所 Core API としては、かなり整ってきた。

## 次に攻める定理

次は report の通り、無理に増やさず caller が必要になってからでよい。
ただし、次 checkpoint を進めるなら、分岐後の projection を二つ作るのが自然。

接触側：

```lean id="er6bdl"
theorem SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (hcontact : r + W.val + 1 = r + (W'.val - 1)) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0
```

gap 側：

```lean id="qj9i02"
theorem SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (hgap : r + W.val + 1 < r + (W'.val - 1)) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
        r + W.val + 1 < r + (W'.val - 1)
```

## Codex 指示

```text id="y0qpav"
Goal:
  Add optional branch-specific projections from
  SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt.

Add only thin projection theorems in PressureState.lean.

Suggested contact-case projection:

  theorem SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W')
      (hcontact : r + W.val + 1 = r + (W'.val - 1)) :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0

Suggested strict-gap projection:

  theorem SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos
      {n : OddNat} {k r : ℕ}
      {L : List (SourcePressureLocalIslandWitness n k r)}
      {W W' : SourcePressureLocalIslandWitness n k r}
      (h : SourcePressureForwardPairComparisonState L W W')
      (hgap : r + W.val + 1 < r + (W'.val - 1)) :
      SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
        SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
          r + W.val + 1 < r + (W'.val - 1)

Use:
  h.boundary_corridor_surface_eq_or_lt

Proof shape:
  rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, _hsplit⟩
  exact ...

Do not claim that every interior index of a strict corridor is nonpositive.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

ここから先は、増やす theorem を絞るのがよい。
`boundary_corridor_surface_eq_or_lt` が compact branch point として十分使えるので、次の本命 caller が出るまで、projection は最小限でよい。

このまま続ければ、いずれ

```text id="l6ckor"
positive pulse の最大詰め込み密度
非正 corridor による局所 spacing
局所 spacing から大域 Big への橋
```

へ接続できるはずじゃ。局所 Core は、着実に形になっている。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index f9ca219b..70d137a2 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1408,6 +1408,25 @@ theorem SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt
     h.left_next_boundary_le_right_previous_boundary
   omega
 
+/--
+Sign-bundled contact-or-gap split for the boundary corridor.
+
+Both corridor endpoints are nonpositive, and the corridor is either the contact
+case where those endpoints coincide, or the genuine gap case where the left
+next boundary lies strictly before the right previous boundary.
+-/
+theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W') :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        (r + W.val + 1 = r + (W'.val - 1) ∨
+          r + W.val + 1 < r + (W'.val - 1)) := by
+  rcases h.boundary_corridor_surface with ⟨hnextL, hprevR, _hle⟩
+  exact ⟨hnextL, hprevR, h.boundary_corridor_eq_or_lt⟩
+
 set_option linter.style.longLine false in
 /--
 Value-level form of the corridor split.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-279.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-279.md
new file mode 100644
index 00000000..13972e95
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-279.md
@@ -0,0 +1,76 @@
+# Report: petal-279
+
+## Goal
+
+Bundle the boundary corridor signs with the contact-or-gap split.
+
+## Implemented
+
+Added:
+
+- `SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`
+
+This theorem combines:
+
+- `SourcePressureForwardPairComparisonState.boundary_corridor_surface`
+- `SourcePressureForwardPairComparisonState.boundary_corridor_eq_or_lt`
+
+## Established Fact
+
+For any concrete forward pair comparison state
+
+```lean
+h : SourcePressureForwardPairComparisonState L W W'
+```
+
+Lean now proves:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+  ∧ (r + W.val + 1 = r + (W'.val - 1)
+      ∨ r + W.val + 1 < r + (W'.val - 1))
+```
+
+## What Can Be Concluded
+
+The boundary corridor between a forward pair's two positive centers is now
+available as one sign-bundled dichotomy:
+
+- both corridor endpoints are nonpositive;
+- either those endpoints coincide, giving a contact corridor;
+- or the left endpoint lies strictly before the right endpoint, giving a
+  genuine gap corridor.
+
+This is a stronger caller-facing surface than the plain arithmetic split,
+because the nonpositive endpoint signs are carried through the same theorem.
+
+## Guardrails
+
+This still does not say every interior point of a strict corridor is
+nonpositive.  It also does not assert global coverage, uniqueness of all
+positive centers, arbitrary window disjointness, or Collatz termination.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureState
+lake build DkMath.Collatz.PetalBridge
+```
+
+Final whitespace gate:
+
+```text
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next theorem should probably be added only if a caller needs it:
+
+- contact-case projection: shared nonpositive boundary;
+- strict-gap projection: two ordered nonpositive endpoints.
+
+For now, `boundary_corridor_surface_eq_or_lt` is the compact branch point.
````
`````

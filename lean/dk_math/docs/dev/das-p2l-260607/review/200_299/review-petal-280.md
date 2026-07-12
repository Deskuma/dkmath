# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureState

gch: 8c2fd9676a633f2471c44b7b330ae39e4f5e6af0

## Report

実装完了です。

[PressureState.lean](/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean:1437) に以下を追加しました。

- `SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos`
- `SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos`

これで、contact branch では共有境界の両表現が非正、strict-gap branch では左右 endpoint が非正かつ strict order を持つ、という endpoint-only の事実が取り出せます。内部 corridor 全点の非正性や大域的な Collatz 終了性は主張していません。

[report-petal-280.md](/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-280.md:1) も新規作成しました。

検証済み:

```text
lake build DkMath.Collatz.PetalBridge.PressureState
lake build DkMath.Collatz.PetalBridge
git diff --check
```

`git status` 上の変更は `PressureState.lean` と新規 `report-petal-280.md` です。

## Review

## 判定

採用。
`boundary_corridor_surface_eq_or_lt` から、contact branch / strict-gap branch それぞれの endpoint projection が切り出された。

追加：

```lean id="kx6h6n"
SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos
SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos
```

これで contact 側では、

```lean id="l6a6iq"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0
```

strict-gap 側では、

```lean id="tbh0qq"
SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
  SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
    r + W.val + 1 < r + (W'.val - 1)
```

が直接取れる。endpoint-only projection として設計境界を守っている。

## 実装レビュー

よい。
どちらも `boundary_corridor_surface_eq_or_lt` から endpoint signs を取り出すだけで、内部 corridor の非正性などを混ぜていない。

特に contact 側で `_hcontact` を branch data として受け取っているが、証明では使わない構成も妥当じゃ。
これは「この theorem は contact branch 内で呼ぶための surface であり、符号自体は既存 surface から来る」という読みになる。

## 数学的意味

これで corridor 分岐後の局所像が、呼び出し側から扱いやすくなった。

```text id="jj8vys"
contact branch:
  shared boundary endpoint is nonpositive

strict-gap branch:
  left endpoint <= 0
  right endpoint <= 0
  left endpoint < right endpoint
```

つまり、`FPC` の正中心間には必ず非正 corridor endpoint があり、その corridor が接触型でも gap 型でも、後段は branch ごとの最小情報をすぐ受け取れる。

## 注意点

今回も主張は適切に絞られている。

まだ言っていない：

```text id="zofgsp"
strict-gap corridor 内部の全 index が非正
contact equality による margin 式の rewrite 済み正規形
positive center 列全体の構造
global coverage
Collatz termination
```

ここを広げていないのが良い。

## 現在の到達点

```text id="x62y50"
FPC
  -> sign-bundled contact-or-gap split
  -> contact branch endpoint signs
  -> strict-gap branch endpoint signs + strict order
```

局所 corridor API は、かなり完成に近い。
次からは caller が必要になるまで、むやみに theorem を増やさず、使用箇所を見ながら進める段階じゃな。

## 次に攻めるなら

小さく進めるなら、contact branch で right previous boundary を contact equality により left next boundary へ rewrite した theorem が候補。

```lean id="rdax52"
theorem SourcePressureForwardPairComparisonState.contact_corridor_left_next_nonpos
    {n : OddNat} {k r : ℕ}
    {L : List (SourcePressureLocalIslandWitness n k r)}
    {W W' : SourcePressureLocalIslandWitness n k r}
    (h : SourcePressureForwardPairComparisonState L W W')
    (hcontact : r + W.val + 1 = r + (W'.val - 1)) :
    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0
```

ただしこれは既に `contact_corridor_shared_nonpos` の左成分なので、急がなくてよい。
本命は、次の caller が corridor split を使い始める箇所を作ることだと思う。

## Codex 指示

```text id="u8bw89"
Goal:
  Do not expand the corridor API further unless a concrete caller needs it.

Recommended next step:
  Start a downstream caller theorem that consumes
  SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt,
  contact_corridor_shared_nonpos, or strict_gap_corridor_endpoints_nonpos.

If a tiny projection is needed, add only aliases/projections, not stronger claims.

Guardrails:
  Do not claim all interior indices of a strict corridor are nonpositive.
  Do not claim global positive-center uniqueness.
  Do not claim arbitrary window disjointness.
  Do not claim Collatz termination.

Build:
  lake build DkMath.Collatz.PetalBridge.PressureState
  lake build DkMath.Collatz.PetalBridge
  git diff --check
```

## 次の狙い

ここからは `PressureState` 内で surface を増やすより、**この corridor surface を使う次層**へ進むのがよさそうじゃ。
局所 Core はかなり整った。次は Beam、つまりこの局所 corridor が pressure pulse 列や大域 Big へどう伝播するかを見る段階に入れる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
index 70d137a2..6117b7d8 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureState.lean
@@ -1427,6 +1427,43 @@ theorem SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or
   rcases h.boundary_corridor_surface with ⟨hnextL, hprevR, _hle⟩
   exact ⟨hnextL, hprevR, h.boundary_corridor_eq_or_lt⟩
 
+/--
+Contact-corridor projection.
+
+When the corridor endpoints coincide, the shared boundary is represented by
+two syntactic index expressions, and both are nonpositive.  The contact equality
+is accepted as branch data; this theorem only projects the endpoint signs.
+-/
+theorem SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W')
+    (_hcontact : r + W.val + 1 = r + (W'.val - 1)) :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 := by
+  rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, _hsplit⟩
+  exact ⟨hnextL, hprevR⟩
+
+/--
+Strict-gap corridor projection.
+
+In the genuine gap branch, both corridor endpoints remain nonpositive and the
+left endpoint is strictly before the right endpoint.  This does not assert
+anything about every interior index of the corridor.
+-/
+theorem SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos
+    {n : OddNat} {k r : ℕ}
+    {L : List (SourcePressureLocalIslandWitness n k r)}
+    {W W' : SourcePressureLocalIslandWitness n k r}
+    (h : SourcePressureForwardPairComparisonState L W W')
+    (hgap : r + W.val + 1 < r + (W'.val - 1)) :
+    SourcePressureMarginInt n k (r + W.val + 1) ≤ 0 ∧
+      SourcePressureMarginInt n k (r + (W'.val - 1)) ≤ 0 ∧
+        r + W.val + 1 < r + (W'.val - 1) := by
+  rcases h.boundary_corridor_surface_eq_or_lt with ⟨hnextL, hprevR, _hsplit⟩
+  exact ⟨hnextL, hprevR, hgap⟩
+
 set_option linter.style.longLine false in
 /--
 Value-level form of the corridor split.
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-280.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-280.md
new file mode 100644
index 00000000..22ad6db6
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-280.md
@@ -0,0 +1,88 @@
+# Report: petal-280
+
+## Goal
+
+Add branch-specific projections from
+`SourcePressureForwardPairComparisonState.boundary_corridor_surface_eq_or_lt`.
+
+## Implemented
+
+Added two thin projection theorems in
+`DkMath.Collatz.PetalBridge.PressureState`:
+
+- `SourcePressureForwardPairComparisonState.contact_corridor_shared_nonpos`
+- `SourcePressureForwardPairComparisonState.strict_gap_corridor_endpoints_nonpos`
+
+## Established Facts
+
+For any
+`h : SourcePressureForwardPairComparisonState L W W'`, the contact branch
+
+```lean
+r + W.val + 1 = r + (W'.val - 1)
+```
+
+projects the two syntactic endpoint signs:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+```
+
+The strict-gap branch
+
+```lean
+r + W.val + 1 < r + (W'.val - 1)
+```
+
+projects both endpoint signs and preserves the strict order:
+
+```lean
+SourcePressureMarginInt n k (r + W.val + 1) <= 0
+  ∧ SourcePressureMarginInt n k (r + (W'.val - 1)) <= 0
+  ∧ r + W.val + 1 < r + (W'.val - 1)
+```
+
+## What Can Be Concluded
+
+The corridor split now has branch-specific caller-facing surfaces:
+
+- contact branch: the shared corridor boundary is nonpositive under both
+  endpoint expressions;
+- strict-gap branch: both corridor endpoints are nonpositive and strictly
+  ordered.
+
+This is enough for downstream callers to branch without reopening
+`boundary_corridor_surface_eq_or_lt`.
+
+## Guardrails
+
+These theorems are endpoint-only projections.  They do not prove that every
+interior index of a strict corridor is nonpositive.
+
+They also do not assert global coverage, uniqueness, arbitrary window
+disjointness, or Collatz termination.
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
+Final gate:
+
+```text
+git diff --check
+```
+
+## Next Branch Prediction
+
+The next branch should be driven by caller demand.  Natural small follow-ups are:
+
+- contact branch: rewrite the right previous boundary sign through the contact
+  equality;
+- strict-gap branch: introduce a named `BoundaryStrictGapCorridor` predicate
+  only if repeated callers need to carry this package.
````
`````

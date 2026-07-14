# Git diff / Report / Review

## Upd: DkMath.Collatz.PetalBridge.PressureDecay

gch: f07d4aa40847ad0ebf466f9523d8d7d401e56715

## Report

cp236 実装完了です。

`PressureDecay.lean` に generic な finite local Big bounds を3本追加しました。

```lean
sourcePressureMarginInt_le_two_mul_window
neg_window_le_sourcePressureMarginInt
sourcePressureMarginInt_bounds_window
```

これで任意の `SourcePressureMarginInt n k r` について、

```text
-k ≤ margin ≤ 2k
```

が使えるようになりました。これは点ごとの有限高さの箱で、伝播・coverage・witness aggregation・Collatz 収束は主張していません。

検証済みです。

```text
lake build DkMath.Collatz.PetalBridge.PressureDecay
lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
lake build DkMath.Collatz.PetalBridge.PressureBeam
lake build DkMath.Collatz.PetalBridge
git diff --check
```

対象 pressure 範囲の `sorry/admit` grep も該当なしです。レポートは `lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-236.md` に追加しました。

## Review

## 結論

**採用。これは局所 Big の箱が立った。**
cp236 は、かなり良い checkpoint じゃ。

追加 theorem は 3 本。

```lean id="sb6ayz"
sourcePressureMarginInt_le_two_mul_window
neg_window_le_sourcePressureMarginInt
sourcePressureMarginInt_bounds_window
```

これで任意の `SourcePressureMarginInt n k r` について、

```text id="h1j6sd"
-k ≤ margin ≤ 2k
```

が使える。
これはまさに **点ごとの finite local Big bound** じゃ。伝播でも coverage でもなく、各 pressure depth の高さを有限観測窓 `k` で包む箱ができた。

## 実装レビュー

実装は薄く、良い。

`SourcePressureMarginInt` は定義上、

```lean id="ec2sxh"
(2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
  (orbitWindowRetentionMassPow2 n k r : ℤ)
```

なので、

```text id="v5hgx6"
continuation ≤ k
retention ≤ k
```

を使えば、すぐに

```text id="by166t"
margin ≤ 2k
-k ≤ margin
```

が出る。

実装でも既存の

```lean id="hbpnxi"
orbitWindowContinuationSiblingMassPow2_le_window
orbitWindowRetentionMassPow2_le_window
```

を使い、`omega` で閉じている。
新しい数学的主張を増やしすぎず、既存 API の当然の帰結を正しい層 `PressureDecay.lean` に置いた。配置もよい。

## 数学的意味

cp235 で得たものは、local pulse の符号形だった。

```text id="eumg5l"
非正 -> 正 -> 非正
```

cp236 で得たものは、その符号形が起きる pressure margin の値域。

```text id="lovv3j"
-k ≤ M(j) ≤ 2k
```

つまり、局所 pulse は無限に高く跳ねるわけではなく、有限観測窓 `k` の箱の中で起きる。

DkMath 語彙ではこうじゃ。

```text id="ndnf0n"
Core:
  SourcePressureMarginInt の有限高さ箱

True Beam:
  positive pulse height は最大 2k

Boundary / False Beam:
  nonpositive side も -k より下には落ちない

Gap:
  net drop / jump size / propagation はまだ未支配
```

ここまで来て、ようやく **local Big = finite height box** と呼べるものが Lean theorem として立った。

## 注意点

今回の bound は点ごとじゃ。

まだ言っていないことは多い。

```text id="kjbj2k"
連続する pulse が何個あるか
正領域の run がどれだけ続くか
net drop がどれだけ跳ねるか
window が時間方向へどう伝播するか
任意軌道が下降するか
```

これらは未証明。
だから report の「これは点ごとの finite local Big bound」という説明は正しい。

## 次の分岐判断

report は次候補として 2 つ挙げている。

```text id="towp2s"
1. cp235 sign transition と [-k, 2k] bounds を bundle する
2. SourcePressureNetDropInt / RetentionDropInt / ContinuationDropInt の有限 bound を調べる
```

わっちの判断では、**次は 2 が本命** じゃ。

理由は、cp236 は「高さの箱」。
次に欲しいのは「ジャンプ幅の箱」。

すでに式は見えている。

```text id="my4jpf"
RetentionDrop = R(j) - R(j+1)
ContinuationDrop = C(j) - C(j+1)
NetDrop = RetentionDrop - 2 * ContinuationDrop
```

各 mass が `0..k` に入るなら、

```text id="ae6num"
-k ≤ RetentionDrop ≤ k
-k ≤ ContinuationDrop ≤ k
```

そして、

```text id="zq1drm"
-3k ≤ NetDrop ≤ 3k
```

が期待できる。

これは cp235 の

```text id="xh5sn3"
M(j+1)=M(j)+NetDrop(j)
```

に対する **有限ジャンプ Big** じゃ。

## 次の Codex 指示

```text id="p9113u"
Checkpoint: petal-237

Primary Goal:
  Establish finite local jump bounds for retention drop, continuation drop, and
  net drop.

Context:
  cp236 added pointwise finite local Big bounds for margins:

    -k ≤ SourcePressureMarginInt n k r ≤ 2k

  This bounds pressure height at each depth.

  The next foundational target is the finite jump bound for:

    SourceRetentionDropInt
    SourceContinuationDropInt
    SourcePressureNetDropInt

  These control how far the local pressure margin can move in one adjacent
  pressure step.

Key expected estimates:
  Since retention and continuation masses are each natural counts bounded by
  the finite window `k`, their adjacent differences should lie in:

    -k ≤ SourceRetentionDropInt n k r ≤ k
    -k ≤ SourceContinuationDropInt n k r ≤ k

  Since:

    SourcePressureNetDropInt
      = SourceRetentionDropInt - 2 * SourceContinuationDropInt

  the net drop should satisfy:

    -3k ≤ SourcePressureNetDropInt n k r ≤ 3k

Strategic Branch Goals:

  Branch A: direct retention/continuation drop bounds
    Inspect definitions of:

      SourceRetentionDropInt
      SourceContinuationDropInt

    and existing window bounds:

      orbitWindowRetentionMassPow2_le_window
      orbitWindowContinuationSiblingMassPow2_le_window

    If direct, add:

      theorem sourceRetentionDropInt_le_window
          (n : OddNat) (k r : ℕ) :
          SourceRetentionDropInt n k r ≤ (k : ℤ)

      theorem neg_window_le_sourceRetentionDropInt
          (n : OddNat) (k r : ℕ) :
          - (k : ℤ) ≤ SourceRetentionDropInt n k r

      theorem sourceRetentionDropInt_bounds_window
          (n : OddNat) (k r : ℕ) :
          - (k : ℤ) ≤ SourceRetentionDropInt n k r ∧
            SourceRetentionDropInt n k r ≤ (k : ℤ)

    and the analogous three theorems for:

      SourceContinuationDropInt

    Add fewer names if there is already a preferred style in the file.

  Branch B: net-drop bound follows cleanly
    If Branch A succeeds, add:

      theorem sourcePressureNetDropInt_le_three_mul_window
          (n : OddNat) (k r : ℕ) :
          SourcePressureNetDropInt n k r ≤ 3 * (k : ℤ)

      theorem neg_three_mul_window_le_sourcePressureNetDropInt
          (n : OddNat) (k r : ℕ) :
          - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r

      theorem sourcePressureNetDropInt_bounds_window
          (n : OddNat) (k r : ℕ) :
          - (3 * (k : ℤ)) ≤ SourcePressureNetDropInt n k r ∧
            SourcePressureNetDropInt n k r ≤ 3 * (k : ℤ)

    This is the finite local jump Big bound.

  Branch C: equivalent bounds already exist
    If retention/continuation/net-drop bounds already exist under other names,
    do not duplicate them.

    Report the theorem names and add only aliases if they significantly improve
    caller readability.

  Branch D: cast friction makes all bounds noisy
    If Nat-to-Int coercions make proofs verbose, use proof-local helper `have`s
    and `omega`.

    Do not introduce a broad coercion API in this checkpoint.

  Branch E: too many theorem names
    If adding all nine theorem names feels too much, prioritize bundled bounds:

      sourceRetentionDropInt_bounds_window
      sourceContinuationDropInt_bounds_window
      sourcePressureNetDropInt_bounds_window

    Individual one-sided theorems can be skipped if not needed by callers.

Implementation rules:
  - Use #check, #print, and scratch lemmas.
  - Put generic bounds near the definitions in `PressureDecay.lean`.
  - Prefer generic bounds over seed-specific wrappers.
  - Do not bundle cp235 sign transition with bounds in this checkpoint unless
    it is literally one line and clearly useful.
  - Add no theorem about propagation or global behavior.

Guardrails:
  Do not add:
    - propagation;
    - list-wide coverage;
    - witness-family aggregation;
    - canonical witness selection;
    - arbitrary target transport;
    - overlap repair;
    - disjointness;
    - Collatz convergence;
    - global Big bounds.

Verification:
  lake build DkMath.Collatz.PetalBridge.PressureDecay
  lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
  lake build DkMath.Collatz.PetalBridge.PressureBeam
  lake build DkMath.Collatz.PetalBridge
  no-sorry grep over inspected pressure files
  git diff --check

Report requirements:
  - State which Branch was taken.
  - Show exact theorem statements.
  - Explain that margin bounds are finite height bounds, while net-drop bounds
    are finite jump bounds.
  - Classify results as True Beam / Boundary / False Beam / Gap.
  - Predict whether the next branch should combine cp235 sign transition with
    height/jump boxes.
```

## 待ち構え

次に期待するのはこれ。

```text id="sehtn4"
SourcePressureMarginInt:
  height box [-k, 2k]

SourcePressureNetDropInt:
  jump box [-3k, 3k]
```

この二つがそろうと、

```text id="3tnfdf"
局所 pulse は有限高さの箱にあり、
隣接遷移も有限ジャンプ幅の箱にある
```

と言える。

そこまで行けば、次に初めて

```text id="gj0mrg"
cp235 sign transition
+
height bound
+
jump bound
```

を bundle する価値が出る。

## 総合判断

cp236 は成功。
局所 Big の第一実体、`[-k, 2k]` の finite height box ができた。

次は net drop の `[-3k, 3k]`。
高さの箱から、ジャンプの箱へ進む。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
index c1ce02e7..688be983 100644
--- a/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
+++ b/lean/dk_math/DkMath/Collatz/PetalBridge/PressureDecay.lean
@@ -40,6 +40,54 @@ noncomputable def SourcePressureMarginInt
   (2 * orbitWindowContinuationSiblingMassPow2 n k r : ℤ) -
     (orbitWindowRetentionMassPow2 n k r : ℤ)
 
+/--
+Finite local Big upper bound for source pressure margin.
+
+The margin is `2 * continuation - retention`.  Since continuation mass is
+bounded by the finite observation window `k` and retention is nonnegative, the
+margin cannot exceed `2 * k`.  This is a pointwise height bound only; it does
+not propagate pressure signs or cover a family of windows.
+-/
+theorem sourcePressureMarginInt_le_two_mul_window
+    (n : OddNat) (k r : ℕ) :
+    SourcePressureMarginInt n k r ≤ 2 * (k : ℤ) := by
+  have hcont :
+      orbitWindowContinuationSiblingMassPow2 n k r ≤ k :=
+    orbitWindowContinuationSiblingMassPow2_le_window n k r
+  unfold SourcePressureMarginInt
+  omega
+
+/--
+Finite local Big lower bound for source pressure margin.
+
+The most negative case occurs when continuation contributes no positive mass
+and retention is as large as the finite window.  This is still only a
+pointwise window-height bound, not a global descent or convergence statement.
+-/
+theorem neg_window_le_sourcePressureMarginInt
+    (n : OddNat) (k r : ℕ) :
+    - (k : ℤ) ≤ SourcePressureMarginInt n k r := by
+  have hret :
+      orbitWindowRetentionMassPow2 n k r ≤ k :=
+    orbitWindowRetentionMassPow2_le_window n k r
+  unfold SourcePressureMarginInt
+  omega
+
+/--
+The source pressure margin always lies in the finite local Big box
+`[-k, 2k]`.
+
+This combines the two pointwise window bounds above.  It deliberately says
+nothing about propagation, coverage, witness aggregation, or Collatz
+convergence.
+-/
+theorem sourcePressureMarginInt_bounds_window
+    (n : OddNat) (k r : ℕ) :
+    - (k : ℤ) ≤ SourcePressureMarginInt n k r ∧
+      SourcePressureMarginInt n k r ≤ 2 * (k : ℤ) :=
+  ⟨neg_window_le_sourcePressureMarginInt n k r,
+    sourcePressureMarginInt_le_two_mul_window n k r⟩
+
 /--
 Integer-valued retention drop across adjacent pressure depths.
 
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-236.md b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-236.md
new file mode 100644
index 00000000..5d0ce652
--- /dev/null
+++ b/lean/dk_math/docs/dev/das-p2l-260607/review/report-petal-236.md
@@ -0,0 +1,116 @@
+# report-petal-236
+
+## Checkpoint
+
+`petal-236`
+
+## Result
+
+Implemented Branch A.
+
+The first finite local Big box for source pressure margins is now available at
+the generic `PressureDecay` layer.
+
+## Added Theorems
+
+```lean
+theorem sourcePressureMarginInt_le_two_mul_window
+    (n : OddNat) (k r : ℕ) :
+    SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)
+```
+
+```lean
+theorem neg_window_le_sourcePressureMarginInt
+    (n : OddNat) (k r : ℕ) :
+    - (k : ℤ) ≤ SourcePressureMarginInt n k r
+```
+
+```lean
+theorem sourcePressureMarginInt_bounds_window
+    (n : OddNat) (k r : ℕ) :
+    - (k : ℤ) ≤ SourcePressureMarginInt n k r ∧
+      SourcePressureMarginInt n k r ≤ 2 * (k : ℤ)
+```
+
+## Meaning
+
+By definition:
+
+```text
+SourcePressureMarginInt n k r
+  = 2 * continuation - retention
+```
+
+The existing finite window bounds provide:
+
+```text
+continuation ≤ k
+retention ≤ k
+```
+
+Therefore every pointwise source-pressure margin lies in:
+
+```text
+[-k, 2k]
+```
+
+This is a finite local Big bound.  It is not propagation, not list coverage,
+not aggregation of witness families, and not a global Collatz statement.
+
+## Branch D Decision
+
+No seed-specific wrapper was added in this checkpoint.
+
+The generic bounds are cleaner and apply to every pressure depth.  A future
+wrapper can combine:
+
+```lean
+exists_sourcePressureBeamPulse_witness_center_margin_signs_of_seed
+sourcePressureMarginInt_bounds_window
+```
+
+to say that the three centered pulse margins all live inside the finite local
+box `[-k, 2k]`.  That wrapper should be added only if a caller needs the bundled
+surface.
+
+## Beam Classification
+
+- True Beam: positive pulse height is now bounded above by `2k`.
+- Boundary / False Beam: nonpositive margins are still bounded below by `-k`.
+- Core: the margin-height box is generic and independent of witness selection.
+- Gap: no net-drop bound, local Big upper estimate, propagation, or convergence
+  has been claimed yet.
+
+## Verification
+
+Passed:
+
+```text
+lake build DkMath.Collatz.PetalBridge.PressureDecay
+lake build DkMath.Collatz.PetalBridge.PressureBeam.Pulse
+lake build DkMath.Collatz.PetalBridge.PressureBeam
+lake build DkMath.Collatz.PetalBridge
+git diff --check
+```
+
+No `sorry` or `admit` was found in the requested pressure-file grep scope.
+
+Known unrelated warning still appears during builds:
+
+```text
+DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:152:6:
+declaration uses `sorry`
+```
+
+## Next Branch
+
+The next natural branch is either:
+
+1. Bundle cp235 sign transition with the new `[-k, 2k]` margin bounds for the
+   three involved depths.
+2. Inspect `SourcePressureNetDropInt`, `SourceRetentionDropInt`, and
+   `SourceContinuationDropInt` for analogous finite local bounds.
+
+The second branch is likely more foundational: net-drop bounds would turn
+local pulse transitions into bounded finite jumps, not just bounded pointwise
+heights.
````
`````

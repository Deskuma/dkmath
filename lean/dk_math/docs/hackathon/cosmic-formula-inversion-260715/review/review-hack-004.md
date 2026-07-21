# Git diff / Report / Review

## hack: cp-004

gch: 4aecc862f61e6d00e3ab991575b519da689d8ede

## Report

Checkpoint `hack-004` completed.

Implemented the concrete verified demo in [Demo.lean](/lean/dk_math/DkMath/Hackathon/Demo.lean):

- Four fixed definitions
- Product, coprimality, boundary, factorization, and primality facts
- Freshness of `13` and `17` via the general exclusion theorem
- Square completion via `cosmicCompletion`

Updated only the formal-alignment tables in:

- [DEMO_CONTRACT.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md)
- [VISUAL_STORYBOARD.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md)

Report: [report-hack-004.md](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-004.md)

Verification:

- Demo build passed: `3287/3287`
- No `sorry`, `admit`, or `axiom` in `DkMath/Hackathon`
- `git diff --check` passed
- Fixed values match the contract
- No projection, DkReal, Manim, or later-checkpoint work begun

Next action: Wise Wolf review of `hack-004`.

## Review

# hack-004 状況分析・レビュー

## 判定

**ACCEPT — checkpoint `hack-004` を受理。**

これで Formal MVP は閉じた。

```text
FinitePrimeEscape
+
CosmicCompletion
+
Concrete Demo
=
FORMAL_MVP_SECURED
```

固定値、一般定理の再利用、公開 theorem 名、形式層と映像層の対応表まで揃っておる。`Demo.lean` の build は `3287/3287`、Hackathon 層に `sorry`・`admit`・`axiom` はない。

## 実装レビュー

### 二本の一般定理が Demo で合流した

`demo_thirteen_fresh` と `demo_seventeen_fresh` は、有限集合の直接計算だけで freshness を済ませず、

```lean
prime_dvd_product_add_coprime_not_mem
```

を明示的に利用している。

また、

```lean
demo_cosmic_completion
```

は `ring` で再証明せず、

```lean
cosmicCompletion demoP demoU
```

をそのまま特殊化している。

したがって Demo は単なる数値検算ではない。

```text
general theorem
→ fixed public instance
```

という Formal Demo の役割を正しく果たしておる。

### 公開 API の形も良い

定義は四つだけ。

```lean
demoPrimeSet
demoP
demoU
demoBoundary
```

定理は映像と説明で必要になる九つだけ。

```lean
demo_product
demo_coprime
demo_boundary
demo_factorization
demo_thirteen_prime
demo_seventeen_prime
demo_thirteen_fresh
demo_seventeen_fresh
demo_cosmic_completion
```

Body・Gap・Big の数値定義や巨大な bundle theorem を増やさなかった判断も良い。映像側では数値を表示できるが、Lean API に不要な展示用構造を持ち込んでいない。

### Freshness proof の自立性

二つの freshness proof は `demo_coprime` や `demo_product` を経由せず、その場で具体算術を閉じている。

これは重複ではあるが、問題ではない。

```text
demo_* 補題を多段 rewrite する構成
```

よりも、

```text
一般 theorem の適用点が明瞭
具体 arithmetic は norm_num
```

という現在の方が、録画やコード表示では理解しやすい。

### Formal–Visual alignment が確定した

`DEMO_CONTRACT.md` には fully qualified declaration name が入り、`VISUAL_STORYBOARD.md` も全項目が `verified` になった。

これで Manim 側は theorem 名や値を推測する必要がない。

```text
visual object
↔ Lean declaration
↔ build gate
```

の対応が固定された。

## 現在地点

ここで一度、正式に名前を凍結してよい。

```text
PUBLIC_THEOREM_NAMES = FROZEN
FORMAL_MVP = SECURED
```

既知良好状態として commit を残す地点でもある。commit 操作自体は、これまでどおりぬしの管理領域じゃ。

次に Projection へ進むこともできるが、hackathon の完成物として現在欠けている最大要素は映像である。

したがって順序は、

```text
Formal MVP
→ Visual MVP
→ Integrated Demo
→ optional Projection stretch
```

が安全かつ強い。

まず Manim の中心場面を完成させる。今回は Codex の現場判断を尊重し、scene 分割・クラス設計・animation 手法までは固定しない。

## 次の Codex Instructions

````md
# Checkpoint hack-008a — Manim Visual Prototype

## Session Class

```text
VISUAL
```

## Goal

Create the first working Manim prototype for the verified Cosmic Formula demo.

The prototype must communicate the central transition:

```text
S = {2, 3, 5, 7}
→ P = 210
→ u = 11
→ Body + Gap
→ completed square with boundary 221
→ 221 = 13 × 17
→ 13 and 17 outside S
```

Use the accepted Lean declarations and fixed values as the source of mathematical truth.

Choose the scene architecture, object structure, transitions, and implementation details that you judge most effective.

## Required Reading

Read:

```text
VISUAL_STORYBOARD.md
DEMO_CONTRACT.md
report-hack-004.md
DkMath/Hackathon/Demo.lean
this instruction
```

Inspect the repository for existing visual conventions or Manim infrastructure before deciding the source layout.

## Permitted Work

You may create and edit visual source and supporting files under:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/
```

You may also create:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-008a.md
```

If the repository clearly has a better established location for Manim sources, use it and explain the decision in the report.

Do not edit the accepted Lean theorem modules.

## Required Result

Produce a renderable prototype containing at least:

```text
the finite prime set
the product P = 210
the offset u = 11
the Body and square Gap
the completed boundary P + u = 221
the factorization 221 = 13 × 17
the freshness comparison
```

A Lean verification panel is welcome if it fits naturally, but it is not required for this first prototype.

The geometry may be schematic. Exact numerical scaling is not required.

The mathematical values and meanings must match `Demo.lean`.

## Shared Data

Keep the fixed numerical values in one shared configuration rather than duplicating them independently across scenes.

Beyond that requirement, choose the Python and Manim structure yourself.

## Verification

Run the relevant Manim render command and record:

```text
the exact command
Manim version
Python environment
render result
output path
duration
resolution
```

Also run:

```bash
git diff --check
git status --short
```

## Report

Write `report-hack-008a.md` containing:

```text
status
files created or changed
visual architecture chosen
source-directory decision
scene sequence
shared-data design
render command and result
output artifact
differences from the storyboard
visual limitations
recommended next visual step
first genuine obstruction
stop confirmation
```

## Stopping Rule

Stop after the first coherent rendered prototype.

Do not continue into narration, final editing, projection, DkReal, or submission packaging.

When several visual approaches are possible, exercise your own judgment and explain the chosen design rather than waiting for detailed direction.

## Final Instruction

Build the visual prototype, render it, write `report-hack-008a.md`, and stop for Wise Wolf review.
````

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Hackathon/Demo.lean b/lean/dk_math/DkMath/Hackathon/Demo.lean
index 64eeea5b..8a1e317a 100644
--- a/lean/dk_math/DkMath/Hackathon/Demo.lean
+++ b/lean/dk_math/DkMath/Hackathon/Demo.lean
@@ -3,3 +3,71 @@ Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
 Released under MIT license as described in the file LICENSE.
 Authors: D. and Wise Wolf.
 -/
+
+import DkMath.Hackathon.FinitePrimeEscape
+import DkMath.Hackathon.CosmicCompletion
+
+namespace DkMath.Hackathon
+
+open scoped BigOperators
+
+/-- The fixed finite prime reference set used by the public demonstration. -/
+def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}
+
+/-- The product of the fixed finite prime reference set. -/
+def demoP : ℕ := 210
+
+/-- The fixed coprime completion offset. -/
+def demoU : ℕ := 11
+
+/-- The fixed completed boundary `demoP + demoU`. -/
+def demoBoundary : ℕ := 221
+
+theorem demo_product :
+    ∏ p ∈ demoPrimeSet, p = demoP := by
+  norm_num [demoPrimeSet, demoP]
+
+theorem demo_coprime :
+    Nat.Coprime demoP demoU := by
+  norm_num [demoP, demoU, Nat.Coprime]
+
+theorem demo_boundary :
+    demoP + demoU = demoBoundary := by
+  norm_num [demoP, demoU, demoBoundary]
+
+theorem demo_factorization :
+    demoBoundary = 13 * 17 := by
+  norm_num [demoBoundary]
+
+theorem demo_thirteen_prime :
+    Nat.Prime 13 := by
+  norm_num
+
+theorem demo_seventeen_prime :
+    Nat.Prime 17 := by
+  norm_num
+
+theorem demo_thirteen_fresh :
+    FreshPrimeFactor demoPrimeSet demoBoundary 13 := by
+  refine ⟨demo_thirteen_prime, by norm_num [demoBoundary], ?_⟩
+  apply prime_dvd_product_add_coprime_not_mem
+      (S := demoPrimeSet) (u := demoU)
+  · norm_num [demoPrimeSet, demoU, Nat.Coprime]
+  · exact demo_thirteen_prime
+  · norm_num [demoPrimeSet, demoU]
+
+theorem demo_seventeen_fresh :
+    FreshPrimeFactor demoPrimeSet demoBoundary 17 := by
+  refine ⟨demo_seventeen_prime, by norm_num [demoBoundary], ?_⟩
+  apply prime_dvd_product_add_coprime_not_mem
+      (S := demoPrimeSet) (u := demoU)
+  · norm_num [demoPrimeSet, demoU, Nat.Coprime]
+  · exact demo_seventeen_prime
+  · norm_num [demoPrimeSet, demoU]
+
+theorem demo_cosmic_completion :
+    demoP * (demoP + 2 * demoU) + demoU ^ 2 =
+      (demoP + demoU) ^ 2 := by
+  exact cosmicCompletion demoP demoU
+
+end DkMath.Hackathon
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md
index 99924f99..8822aa19 100644
--- a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md
@@ -991,17 +991,17 @@ This table must be updated after implementation.

 | Demo element | Required formal anchor | Final name |
 |---|---|---|
-| finite set | definition | pending |
-| product equals `210` | theorem | pending |
-| coprimality | theorem | pending |
-| boundary equals `221` | theorem | pending |
-| factorization | theorem | pending |
-| `13` prime | theorem | pending |
-| `17` prime | theorem | pending |
-| `13` fresh | theorem | pending |
-| `17` fresh | theorem | pending |
-| Cosmic completion | theorem | pending |
-| successful verification | build gate | pending |
+| finite set | definition | `DkMath.Hackathon.demoPrimeSet` |
+| product equals `210` | theorem | `DkMath.Hackathon.demo_product` |
+| coprimality | theorem | `DkMath.Hackathon.demo_coprime` |
+| boundary equals `221` | theorem | `DkMath.Hackathon.demo_boundary` |
+| factorization | theorem | `DkMath.Hackathon.demo_factorization` |
+| `13` prime | theorem | `DkMath.Hackathon.demo_thirteen_prime` |
+| `17` prime | theorem | `DkMath.Hackathon.demo_seventeen_prime` |
+| `13` fresh | theorem | `DkMath.Hackathon.demo_thirteen_fresh` |
+| `17` fresh | theorem | `DkMath.Hackathon.demo_seventeen_fresh` |
+| Cosmic completion | theorem | `DkMath.Hackathon.demo_cosmic_completion` |
+| successful verification | build gate | `lake build DkMath.Hackathon.Demo` |

 No `pending` value may remain in the final demo contract.

diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md
index 02978897..a699755a 100644
--- a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md
@@ -1912,16 +1912,16 @@ This table must be finalized after the Lean theorem surface is accepted.

 | Visual element | Formal declaration | Status |
 |---|---|---|
-| `S = {2, 3, 5, 7}` | `demoPrimeSet` | pending |
-| product equals `210` | `demo_product` | pending |
-| `Coprime 210 11` | `demo_coprime` | pending |
-| Body + Gap = Big | `cosmicCompletion` | pending |
-| concrete completion | `demo_cosmic_completion` | pending |
-| boundary equals `221` | `demo_boundary` | pending |
-| `221 = 13 × 17` | `demo_factorization` | pending |
-| `13` fresh | `demo_thirteen_fresh` | pending |
-| `17` fresh | `demo_seventeen_fresh` | pending |
-| successful verification | actual build gate | pending |
+| `S = {2, 3, 5, 7}` | `demoPrimeSet` | verified |
+| product equals `210` | `demo_product` | verified |
+| `Coprime 210 11` | `demo_coprime` | verified |
+| Body + Gap = Big | `cosmicCompletion` | verified |
+| concrete completion | `demo_cosmic_completion` | verified |
+| boundary equals `221` | `demo_boundary` | verified |
+| `221 = 13 × 17` | `demo_factorization` | verified |
+| `13` fresh | `demo_thirteen_fresh` | verified |
+| `17` fresh | `demo_seventeen_fresh` | verified |
+| successful verification | `lake build DkMath.Hackathon.Demo` | passed |

 No row may remain `pending` in the final storyboard used for rendering.

diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-004.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-004.md
new file mode 100644
index 00000000..e1184bb9
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-004.md
@@ -0,0 +1,185 @@
+# Report — Checkpoint hack-004
+
+## Status
+
+```text
+COMPLETED
+```
+
+## Session Metadata
+
+```text
+Checkpoint: hack-004
+Session class: IMPLEMENTATION
+Model: GPT-5 Codex
+End: 2026/07/15 08:10 JST
+```
+
+## Primary Goal
+
+Create the fixed public Lean demonstration combining finite-set prime escape
+and Cosmic Formula square completion with the accepted values
+`S = {2,3,5,7}`, `P = 210`, `u = 11`, and boundary `221 = 13 * 17`.
+
+## Files Changed
+
+- `DkMath/Hackathon/Demo.lean`
+- `docs/hackathon/cosmic-formula-inversion-260715/DEMO_CONTRACT.md`
+- `docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md`
+- `docs/hackathon/cosmic-formula-inversion-260715/report-hack-004.md`
+
+The two existing documents were changed only in their formal-alignment tables.
+
+## Definitions Added
+
+```lean
+def demoPrimeSet : Finset ℕ := {2, 3, 5, 7}
+def demoP : ℕ := 210
+def demoU : ℕ := 11
+def demoBoundary : ℕ := 221
+```
+
+No optional Body, Gap, or Big definitions and no bundled demo structure were
+added.
+
+## Theorems Added
+
+- `demo_product`
+- `demo_coprime`
+- `demo_boundary`
+- `demo_factorization`
+- `demo_thirteen_prime`
+- `demo_seventeen_prime`
+- `demo_thirteen_fresh`
+- `demo_seventeen_fresh`
+- `demo_cosmic_completion`
+
+All required public names were retained.
+
+## Exact General Theorems Reused
+
+Both concrete freshness proofs explicitly apply:
+
+```lean
+prime_dvd_product_add_coprime_not_mem
+```
+
+with the fixed `demoPrimeSet` and `demoU`. Direct finite-set membership
+computation is not used as the freshness proof.
+
+The concrete square-completion theorem directly specializes:
+
+```lean
+cosmicCompletion demoP demoU
+```
+
+It is not reproved by `ring` or numerical normalization.
+
+## Concrete Automation Used
+
+`norm_num` proves only fixed arithmetic facts:
+
+- the finite product is `210`;
+- `210` and `11` are coprime;
+- `210 + 11 = 221`;
+- `221 = 13 * 17`;
+- `13` and `17` are prime;
+- each fixed prime divides the relevant boundary expression.
+
+The accepted general theorem layers provide the structural freshness and
+Cosmic completion arguments.
+
+## Imports
+
+```lean
+import DkMath.Hackathon.FinitePrimeEscape
+import DkMath.Hackathon.CosmicCompletion
+```
+
+No additional tactic import was required because the accepted transitive
+imports already expose the concrete arithmetic tactic. No sample or unrelated
+research module was imported.
+
+## Verification
+
+Focused build:
+
+```text
+$ lake build DkMath.Hackathon.Demo
+✔ [3287/3287] Built DkMath.Hackathon.Demo
+Build completed successfully (3287 jobs).
+```
+
+No-sorry check:
+
+```text
+rg -n "\bsorry\b|\badmit\b|\baxiom\b" DkMath/Hackathon
+```
+
+Result: no matches.
+
+Diff validation:
+
+```text
+git diff --check
+```
+
+Result: passed with no output.
+
+`git status --short` and the final diff were inspected. Only the four permitted
+files changed during this checkpoint.
+
+## Formal–Visual Alignment Updates
+
+The `DEMO_CONTRACT.md` alignment table now records the fully qualified final
+Lean declaration names and the actual `lake build DkMath.Hackathon.Demo` gate.
+
+The `VISUAL_STORYBOARD.md` alignment table now marks the implemented
+definitions and theorems as verified and records the successful focused build
+gate. No narration, values, timing, palette, scene design, or mathematical
+claim was changed.
+
+## Mathematical Meaning
+
+The concrete finite set multiplies to `210`; the coprime offset `11` gives the
+boundary `221`, whose prime factors `13` and `17` are both outside the original
+set by the general finite-prime exclusion theorem. Independently, the general
+Cosmic square identity specializes to the same `P = 210` and `u = 11`.
+
+## Meaning Boundary
+
+The demo does not claim:
+
+- uniqueness of a fresh factor;
+- sequence-relative primitive-divisor status;
+- that geometry causes factorization;
+- a formal Euclidean dissection;
+- normalized or inverse projection;
+- DkReal reconstruction;
+- any Manim implementation or submission packaging.
+
+## Public Theorem-Name Freeze Recommendation
+
+Freeze the four demo definition names and nine theorem names after Wise Wolf
+acceptance. They are concise, match the contract and alignment tables, and are
+suitable for OBS recording and later Manim overlays.
+
+## First Genuine Obstruction
+
+```text
+none
+```
+
+## Next Permitted Action
+
+```text
+Wise Wolf review of checkpoint hack-004.
+```
+
+## Stop Confirmation
+
+```text
+The checkpoint stopped after the concrete Demo, alignment tables, and report.
+No projection, inverse projection, DkReal, Manim, submission, or later
+checkpoint work was begun.
+```
````
`````

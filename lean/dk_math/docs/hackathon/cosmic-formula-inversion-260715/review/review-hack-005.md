# Git diff / Report / Review

## hack: cp-005

gch: e98176f79669908fa4b69f76318626f4f966c12c

## Report

Checkpoint `hack-008a` is complete. 👍️

Created and rendered:

- [Manim scene](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/cosmic_formula_scene.py)
- [Shared demo data](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/demo_data.py)
- [Rendered prototype MP4](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4)
- [Checkpoint report](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-008a.md)

Render results:

- Manim Community 0.20.1
- 1280×720, 30 fps
- 15.9 seconds
- H.264
- 19 animations
- Render completed successfully
- `git diff --check` passed
- Accepted Lean modules remain unchanged

Stopped at the requested first coherent visual prototype, ready for Wise Wolf review.

## Review

# hack-008a 状況分析・レビュー

## 判定

**ACCEPT — checkpoint `hack-008a` を受理。**

映像構成は成立しておる。15.9 秒という速いテンポも、単独解説動画としては短いが、**3 分プロモーション映像へ差し込む一場面**としてはむしろ使いやすい。

```text
FORMAL_MVP = SECURED
VISUAL_PROTOTYPE = SECURED
```

これで、数学契約から Lean 実装、具体 Demo、Manim 可視化まで一本につながった。

## 映像レビュー

### 中心構造は明確に見える

映像は次の流れを短時間で正しく通過している。

```text
{2, 3, 5, 7}
→ P = 210
→ u = 11
→ Body + Gap
→ completed boundary 221
→ 221 = 13 × 17
→ 13, 17 ∉ S
→ Lean theorem anchors
```

特に中央の平方完成場面は、色の役割が明確じゃ。

```text
青:
  Body

赤:
  Gap

白い外枠:
  completed Big

紫:
  fresh prime factors

緑:
  Lean verification
```

幾何が模式図であることも副題に明記されており、数値比率どおりの作図ではないことが伝わる。

### 3 分プロモ内では現在のテンポでよい

単独公開動画なら、式を読む時間として各場面に数秒ずつ追加したい。

しかし 3 分プロモでは、周囲にナレーションや Codex・Lean の実写画面が入るため、この 15.9 秒は次の役割を担える。

```text
詳細説明:
  しない

構造の全体像:
  一気に見せる

印象:
  数学が動き、最後に Lean へ着地する
```

したがって、現時点で Manim 本体を作り直す必要はない。

### プロモ編集時の注意点

画面下部の一般 theorem と、最後の Lean anchor 名はやや小さい。全画面表示なら読めるが、他の映像と並べた inset 表示には向かない。

3 分版では、

```text
Manim 部分:
  全画面で使用

Lean の詳細:
  後続の実際のコード画面で見せる
```

という分担がよい。

Manim 内の最終 anchor panel は証明そのものではなく、次の実画面へのブリッジとして機能する。

## 実装レビュー

### shared data 設計は良い

`demo_data.py` は、原始データを次の三つに限定している。

```python
primes
offset
fresh_factors
```

そこから、

```text
product
boundary
Body
Gap
Big
```

を計算している。

さらに assertion で Lean Demo の固定値へ固定しているため、複数 scene 内に数値を手書きして drift する危険が小さい。

これは最終版でも維持すべき構造じゃ。

### Scene 構造も prototype に適している

複数 scene へ細断せず、一つの連続 `Scene` にしたことで、最初の試作として全体の論理経路を検証できた。

単独公開版を後で作る場合には shot 分割や読み時間の追加が有効だが、プロモ素材としては現在の連続性が強い。

### Lean 層は保護された

accepted Lean modules は変更されていない。

Visual layer が downstream に留まり、

```text
Lean theorem
→ Demo constants
→ shared Python data
→ Manim render
```

という依存方向が保たれている。

### 環境面

唯一、後で閉じるべき問題は Manim 環境の再現性じゃ。

今回は一時 venv と `/tmp` に展開した native dependency で render しており、checkpoint は閉じたが、submission reproduction としては未完成である。

これは今すぐ映像を修正する問題ではなく、`hack-010` の packaging で、

```text
Python version
Manim version
native dependencies
setup command
render command
```

を固定すればよい。

なお報告書の「First genuine obstruction」は、厳密には **解決済みの environment obstacle** である。checkpoint を停止させた genuine obstruction ではないため、今後の報告では次のように分けるとよい。

```text
First genuine obstruction:
  none

Resolved environmental issue:
  Manim / Pango / Cairo environment
```

修正必須ではないが、停止規則の語彙としてはこちらが正確じゃ。

## 現在地点

正式 checkpoint 名は `hack-008a` である。外側の `cp-005` は会話・実行回の通番として扱い、プロジェクト記録では `hack-008a` を維持する。

次は Manim の再制作ではなく、**3 分プロモへの統合**へ進む。

```text
Formal theorem
→ Codex process
→ Manim structure reveal
→ Lean build verification
→ future direction
```

この順で、人間・Codex・Lean・Manim の四者を一つの作品へまとめる。

クレジット記録も次回から補正する。

```text
Weekly allowance:
  before / after

Additional credits:
  before / after
```

両者を換算しない。

# 次の Codex Instructions

前回より、目的と境界だけを渡し、編集判断は Codex に委ねる形へ戻す。

````md
# Checkpoint hack-009a — Three-Minute Promo Integration Draft

## Session Class

```text
INTEGRATION
```

## Goal

Create the first coherent draft of the approximately three-minute DkMath hackathon promotional video.

Use the accepted formal MVP and the accepted Manim prototype to present the project as a verifiable AI-assisted mathematical research workflow.

The draft should connect:

```text
human mathematical direction
Codex repository investigation and implementation
Lean verification
Manim visual explanation
future Cosmic Formula inverse projection
```

Exercise your own editorial and technical judgment.

## Accepted Assets

Treat the following as verified source material:

```text
DkMath/Hackathon/FinitePrimeEscape.lean
DkMath/Hackathon/CosmicCompletion.lean
DkMath/Hackathon/Demo.lean

report-hack-001.md
report-hack-002.md
report-hack-003.md
report-hack-004.md
report-hack-008a.md

visual/media/videos/cosmic_formula_scene/720p30/
  CosmicFormulaPrototype.mp4
```

Inspect the available repository and recording assets before choosing the final sequence.

The accepted Manim prototype may be used as-is. Redesign it only if integration exposes a concrete defect.

## Narrative Requirements

The draft must make the following understandable:

```text
1. DkMath is a large Lean mathematical research library.

2. The mathematical contract was fixed before implementation.

3. Codex audited the existing repository and found the smallest missing bridge.

4. Codex implemented the finite prime escape theorem and Cosmic square completion.

5. Lean verified the general theorems and the fixed example.

6. Manim visualizes the shared boundary:
   P + u = 221.

7. The factors 13 and 17 are fresh relative to {2, 3, 5, 7}.

8. Bounded inverse projection is the next research direction.
```

Collatz footage may be used as short secondary evidence of the same workflow when suitable.

If used, include an explicit limitation:

```text
No Collatz convergence claim is made.
```

## Working Area

Create the integration sources and outputs under:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/
```

Write the checkpoint report to:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/
  report-hack-009a.md
```

Keep the accepted Lean and Manim source modules unchanged.

## Required Deliverables

Produce:

```text
an asset inventory
a timed edit outline
a narration or subtitle script
a first integrated video draft when the available assets are sufficient
```

When an essential recording is unavailable, create the strongest draft possible and report the exact missing asset rather than inventing evidence.

The Manim segment should remain full-screen enough for its equations and labels to remain readable.

## Verification

Record:

```text
editing or rendering tools and versions
exact build or render command
output path
duration
resolution
frame rate
audio status
subtitle status
```

Run:

```bash
git diff --check
git status --short
```

Inspect the final diff.

## Resource Recording

Record the two resource meters independently:

```text
Weekly allowance before:
Weekly allowance after:

Additional credits before:
Additional credits after:
```

Do not convert weekly percentage into credits.

## Report

`report-hack-009a.md` should explain:

```text
the editorial structure chosen
the assets used
the role of the Manim prototype
the Codex and Lean evidence shown
the narration structure
any missing footage
technical output metadata
resolved environmental issues
first genuine obstruction, if any
recommended next integration step
stop confirmation
```

## Stopping Rule

Stop after the first coherent integrated draft or after identifying the exact missing asset that prevents one.

Do not begin projection, DkReal implementation, public long-form video production, or final submission packaging.

## Final Instruction

Build the strongest three-minute promo draft supported by the available verified assets, report the result, and stop for review.
````

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-008a.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-008a.md
new file mode 100644
index 00000000..307c3a69
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-008a.md
@@ -0,0 +1,144 @@
+# Checkpoint hack-008a — Manim Visual Prototype
+
+## Status
+
+Complete. The first coherent Manim prototype was implemented and rendered.
+The accepted Lean modules were not changed.
+
+## Files created or changed
+
+- `visual/demo_data.py`
+- `visual/cosmic_formula_scene.py`
+- `visual/manim.cfg`
+- `visual/README.md`
+- `visual/.gitignore`
+- `visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4`
+- `report-hack-008a.md`
+
+## Visual architecture chosen
+
+The prototype is one continuous `Scene`, rather than a collection of separately
+rendered clips. Persistent title treatment and a small color vocabulary connect
+three visual phases:
+
+1. known primes, their product, and the coprime offset;
+2. schematic square completion with separately colored Body and Gap;
+3. factorization, freshness, and a compact Lean-anchor panel.
+
+This gives the first prototype a single readable argument while keeping each
+phase independently refactorable into a later scene or shot.
+
+## Source-directory decision
+
+Repository inspection found the storyboard but no existing Manim source tree,
+configuration, or naming convention. The checkpoint's requested `visual/`
+directory was therefore used. Source, local render configuration, instructions,
+and the retained MP4 live together there; transient Manim text and partial-movie
+caches are ignored.
+
+## Scene sequence
+
+The rendered sequence is:
+
+```text
+S = {2, 3, 5, 7}
+→ P = 2 × 3 × 5 × 7 = 210
+→ u = 11 and gcd(210, 11) = 1
+→ Body = P(P + 2u) = 48720 and Gap = u² = 121
+→ P(P + 2u) + u² = (P + u)²
+→ completed boundary P + u = 221
+→ 221 = 13 × 17
+→ 13, 17 ∉ S
+→ accepted Lean theorem names
+```
+
+## Shared-data design
+
+`visual/demo_data.py` defines one frozen `CosmicDemoData` value. Only the prime
+tuple, offset, and fresh-factor tuple are primitive data. Product, boundary,
+Body, Gap, and completed-square value are computed properties. Module assertions
+pin the computed results to the accepted `Demo.lean` values, preventing scenes
+from silently diverging through duplicated literals.
+
+## Render command and result
+
+Command, run from `visual/`:
+
+```bash
+manim render -qm cosmic_formula_scene.py CosmicFormulaPrototype
+```
+
+- Manim Community: `0.20.1`
+- Python: `3.12.3`
+- Environment: temporary virtual environment
+  `/tmp/dkmath-manim-system-venv`, created with system site packages
+- Result: success; `Rendered CosmicFormulaPrototype`, 19 animations
+- Video codec: H.264
+- Duration: 15.900 seconds
+- Resolution: 1280 × 720
+- Frame rate: 30 fps
+- File size: 678,561 bytes
+
+Because the host lacked Manim and development metadata for its native Pango/Cairo
+dependency, Manim was installed only in the temporary environment. Debian
+development packages were downloaded and extracted under `/tmp`; the host system
+package set was not modified. Rendering emitted non-fatal GLib critical warnings
+from that temporary library arrangement, but exited successfully and produced a
+valid video whose metadata and representative frames were inspected.
+
+## Output artifact
+
+```text
+visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4
+```
+
+The artifact is a 15.9-second 720p render. The source README records the portable
+render invocation.
+
+## Repository checks
+
+- `git diff --check`: passed with no output.
+- `git status --short --untracked-files=all`: reported only the seven new
+  checkpoint files listed above; no accepted Lean module was modified.
+
+## Differences from the storyboard
+
+- The storyboard's nine conceptual scenes are condensed into one continuous
+  15.9-second prototype.
+- Geometry is intentionally schematic: the Body is an L-shaped region and the
+  Gap is its missing corner; lengths are not scaled as 210 and 11.
+- The Lean panel shows accepted declaration names rather than source excerpts.
+- There is no narration, audio, camera motion, or editorial pause structure.
+- The more detailed final comparison layout is reduced to the original set,
+  two highlighted factor tokens, and the freshness implication.
+
+## Visual limitations
+
+- Text pacing is suitable for prototype review, not yet for narrated viewing.
+- The square-completion diagram does not label individual side segments `P` and
+  `u`; it communicates the identity through color and adjacent equations.
+- The theorem implication is presented as supporting text and is not animated
+  term by term.
+- Font selection uses Manim defaults, so typography is not yet submission-grade.
+- The temporary render environment should be replaced by a reproducible project
+  environment before production rendering.
+
+## Recommended next visual step
+
+After review, split the continuous prototype into storyboard-aligned shots and
+refine the square-completion phase first: add explicit `P`/`u` side braces,
+increase reading holds, and synchronize equation terms with their regions. That
+is the highest-value visual refinement before narration or final editing.
+
+## First genuine obstruction
+
+The first genuine obstruction was the absence of an installed Manim executable
+and native build metadata for Pango/Cairo. System package installation was not
+available without administrative credentials. A non-system workaround using a
+temporary virtual environment and development files extracted under `/tmp`
+unblocked the checkpoint without changing the host package set.
+
+## Stop confirmation
+
+Stopped after the first coherent rendered prototype. No narration, final edit,
+projection, DkReal work, or submission packaging was started.
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/.gitignore b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/.gitignore
new file mode 100644
index 00000000..432cc8ee
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/.gitignore
@@ -0,0 +1,3 @@
+__pycache__/
+media/texts/
+media/videos/**/partial_movie_files/
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/README.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/README.md
new file mode 100644
index 00000000..640636ee
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/README.md
@@ -0,0 +1,16 @@
+# Cosmic Formula Manim Prototype
+
+The scene keeps all verified numerical values in `demo_data.py` and presents
+one continuous schematic transition in `cosmic_formula_scene.py`.
+
+From this directory, render the prototype with Manim Community:
+
+```bash
+manim render -qm cosmic_formula_scene.py CosmicFormulaPrototype
+```
+
+The configured output is 1280×720 at 30 fps under `media/videos/`.
+
+The geometry is intentionally schematic. Exact arithmetic is displayed in the
+labels and anchored by `DkMath.Hackathon.Demo`; screen lengths are not drawn to
+the numerical scale of 210, 221, or 232.
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/cosmic_formula_scene.py b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/cosmic_formula_scene.py
new file mode 100644
index 00000000..b1afa9bf
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/cosmic_formula_scene.py
@@ -0,0 +1,221 @@
+"""First coherent Manim prototype for the verified Cosmic Formula demo."""
+
+from manim import (
+    BLUE_B,
+    BLUE_D,
+    DOWN,
+    FadeIn,
+    FadeOut,
+    GOLD,
+    GREEN,
+    GrowFromCenter,
+    LEFT,
+    ORIGIN,
+    Rectangle,
+    ReplacementTransform,
+    RIGHT,
+    Scene,
+    Square,
+    Text,
+    UP,
+    VGroup,
+    WHITE,
+    Write,
+)
+
+from demo_data import DEMO
+
+
+BACKGROUND = "#0B1020"
+KNOWN = BLUE_B
+PRODUCT = "#67E8F9"
+OFFSET = GOLD
+BODY = BLUE_D
+GAP = "#FB7185"
+BOUNDARY = "#F8FAFC"
+FRESH = "#A78BFA"
+MUTED = "#94A3B8"
+
+
+class CosmicFormulaPrototype(Scene):
+    """One continuous schematic journey from finite primes to fresh factors."""
+
+    def construct(self) -> None:
+        self.camera.background_color = BACKGROUND
+
+        title = Text("DkMath · Cosmic Formula Inversion", font_size=34, color=WHITE)
+        title.to_edge(UP)
+        subtitle = Text(
+            "verified arithmetic · schematic geometry",
+            font_size=20,
+            color=MUTED,
+        ).next_to(title, DOWN, buff=0.14)
+        self.play(Write(title), FadeIn(subtitle), run_time=0.8)
+
+        prime_tokens = VGroup(
+            *[self.token(str(prime), KNOWN) for prime in DEMO.primes]
+        ).arrange(RIGHT, buff=0.35)
+        set_label = Text(
+            f"S = {{{', '.join(map(str, DEMO.primes))}}}",
+            font_size=34,
+            color=KNOWN,
+        ).next_to(prime_tokens, DOWN, buff=0.45)
+        self.play(
+            *[GrowFromCenter(token) for token in prime_tokens],
+            Write(set_label),
+            run_time=1.2,
+        )
+        self.wait(0.4)
+
+        product_text = Text(
+            f"P = {' × '.join(map(str, DEMO.primes))} = {DEMO.product}",
+            font_size=38,
+            color=PRODUCT,
+        )
+        self.play(
+            ReplacementTransform(VGroup(prime_tokens, set_label), product_text),
+            run_time=1.1,
+        )
+        offset_text = Text(
+            f"u = {DEMO.offset}    gcd({DEMO.product}, {DEMO.offset}) = 1",
+            font_size=30,
+            color=OFFSET,
+        ).next_to(product_text, DOWN, buff=0.4)
+        self.play(Write(offset_text), run_time=0.8)
+        self.wait(0.5)
+        self.play(FadeOut(product_text), FadeOut(offset_text), run_time=0.5)
+
+        geometry, body_group, gap_square, outer = self.completion_geometry()
+        formula = Text(
+            "Body + Gap = Big",
+            font_size=34,
+            color=WHITE,
+        ).to_edge(LEFT).shift(UP * 1.5 + RIGHT * 0.45)
+        body_formula = Text(
+            f"Body = P(P + 2u) = {DEMO.body}",
+            font_size=25,
+            color=KNOWN,
+        ).next_to(formula, DOWN, aligned_edge=LEFT, buff=0.35)
+        gap_formula = Text(
+            f"Gap = u² = {DEMO.gap}",
+            font_size=25,
+            color=GAP,
+        ).next_to(body_formula, DOWN, aligned_edge=LEFT, buff=0.25)
+        identity = Text(
+            "P(P + 2u) + u² = (P + u)²",
+            font_size=27,
+            color=BOUNDARY,
+        ).next_to(gap_formula, DOWN, aligned_edge=LEFT, buff=0.5)
+
+        self.play(FadeIn(body_group), Write(formula), Write(body_formula), run_time=1.2)
+        self.play(GrowFromCenter(gap_square), Write(gap_formula), run_time=0.9)
+        self.play(FadeIn(outer), Write(identity), run_time=0.9)
+        self.add(geometry)
+
+        boundary_label = Text(
+            f"completed boundary  P + u = {DEMO.boundary}",
+            font_size=27,
+            color=BOUNDARY,
+        ).next_to(outer, DOWN, buff=0.28)
+        numeric = Text(
+            f"{DEMO.body} + {DEMO.gap} = {DEMO.big}",
+            font_size=24,
+            color=MUTED,
+        ).next_to(boundary_label, DOWN, buff=0.18)
+        self.play(Write(boundary_label), FadeIn(numeric), run_time=0.9)
+        self.wait(0.7)
+
+        factorization = Text(
+            f"{DEMO.boundary} = {DEMO.fresh_factors[0]} × {DEMO.fresh_factors[1]}",
+            font_size=46,
+            color=FRESH,
+        )
+        self.play(
+            FadeOut(VGroup(geometry, formula, body_formula, gap_formula, identity,
+                           boundary_label, numeric)),
+            FadeIn(factorization),
+            run_time=0.8,
+        )
+
+        original = Text(
+            f"S = {{{', '.join(map(str, DEMO.primes))}}}",
+            font_size=32,
+            color=KNOWN,
+        ).next_to(factorization, UP, buff=0.65)
+        fresh_tokens = VGroup(
+            *[self.token(str(prime), FRESH) for prime in DEMO.fresh_factors]
+        ).arrange(RIGHT, buff=0.75).next_to(factorization, DOWN, buff=0.6)
+        freshness = Text(
+            f"{DEMO.fresh_factors[0]}, {DEMO.fresh_factors[1]} ∉ S   ·   fresh prime factors",
+            font_size=29,
+            color=FRESH,
+        ).next_to(fresh_tokens, DOWN, buff=0.38)
+        theorem = Text(
+            "prime q | (P + u)  and  gcd(P, u) = 1   ⇒   q ∉ S",
+            font_size=22,
+            color=MUTED,
+        ).next_to(freshness, DOWN, buff=0.42)
+        self.play(Write(original), GrowFromCenter(fresh_tokens), run_time=0.9)
+        self.play(Write(freshness), FadeIn(theorem), run_time=0.9)
+        self.wait(1.0)
+
+        verified = Text(
+            "Verified Lean anchors:\n"
+            "demo_thirteen_fresh · demo_seventeen_fresh\n"
+            "demo_cosmic_completion",
+            font_size=25,
+            line_spacing=1.25,
+            color=GREEN,
+        )
+        self.play(
+            FadeOut(VGroup(factorization, original, fresh_tokens, freshness, theorem)),
+            FadeIn(verified),
+            run_time=0.8,
+        )
+        self.wait(1.0)
+        self.play(FadeOut(VGroup(title, subtitle, verified)), run_time=0.6)
+
+    @staticmethod
+    def token(label: str, color: str) -> VGroup:
+        circle = Square(side_length=0.78, color=color, stroke_width=3)
+        circle.set_fill(color, opacity=0.16)
+        text = Text(label, font_size=30, color=WHITE).move_to(circle)
+        return VGroup(circle, text)
+
+    @staticmethod
+    def completion_geometry() -> tuple[VGroup, VGroup, Square, Square]:
+        center = RIGHT * 3.35 + DOWN * 0.2
+        side = 4.15
+        gap_side = 1.15
+
+        left_body = Rectangle(
+            width=side - gap_side,
+            height=side,
+            color=BODY,
+            stroke_width=0,
+            fill_opacity=0.82,
+        ).move_to(center + LEFT * gap_side / 2)
+        lower_body = Rectangle(
+            width=gap_side,
+            height=side - gap_side,
+            color=BODY,
+            stroke_width=0,
+            fill_opacity=0.82,
+        ).move_to(center + RIGHT * (side - gap_side) / 2 + DOWN * gap_side / 2)
+        body_group = VGroup(left_body, lower_body)
+
+        gap_square = Square(
+            side_length=gap_side,
+            color=GAP,
+            stroke_width=3,
+            fill_opacity=0.9,
+        ).move_to(center + RIGHT * (side - gap_side) / 2 + UP * (side - gap_side) / 2)
+        gap_square.set_fill(GAP, opacity=0.9)
+
+        outer = Square(
+            side_length=side,
+            color=BOUNDARY,
+            stroke_width=5,
+        ).move_to(center)
+        geometry = VGroup(body_group, gap_square, outer).move_to(center)
+        return geometry, body_group, gap_square, outer
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/demo_data.py b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/demo_data.py
new file mode 100644
index 00000000..df3dc1eb
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/demo_data.py
@@ -0,0 +1,44 @@
+"""Shared verified values for the Cosmic Formula Manim prototype."""
+
+from dataclasses import dataclass
+
+
+@dataclass(frozen=True)
+class CosmicDemoData:
+    primes: tuple[int, ...] = (2, 3, 5, 7)
+    offset: int = 11
+    fresh_factors: tuple[int, int] = (13, 17)
+
+    @property
+    def product(self) -> int:
+        result = 1
+        for prime in self.primes:
+            result *= prime
+        return result
+
+    @property
+    def boundary(self) -> int:
+        return self.product + self.offset
+
+    @property
+    def body(self) -> int:
+        return self.product * (self.product + 2 * self.offset)
+
+    @property
+    def gap(self) -> int:
+        return self.offset**2
+
+    @property
+    def big(self) -> int:
+        return self.boundary**2
+
+
+DEMO = CosmicDemoData()
+
+# Keep accidental visual drift from reaching a render.
+assert DEMO.product == 210
+assert DEMO.boundary == 221
+assert DEMO.fresh_factors[0] * DEMO.fresh_factors[1] == DEMO.boundary
+assert DEMO.body == 48720
+assert DEMO.gap == 121
+assert DEMO.big == 48841
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/manim.cfg b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/manim.cfg
new file mode 100644
index 00000000..add6bdee
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/manim.cfg
@@ -0,0 +1,12 @@
+[CLI]
+background_color = #0B1020
+frame_rate = 30
+pixel_width = 1280
+pixel_height = 720
+media_dir = ./media
+video_dir = {media_dir}/videos/{module_name}/{quality}
+images_dir = {media_dir}/images/{module_name}
+tex_dir = {media_dir}/Tex
+partial_movie_dir = {video_dir}/partial_movie_files/{scene_name}
+output_file = CosmicFormulaPrototype
+disable_caching = False
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4 b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4
new file mode 100644
index 00000000..471d7fe0
Binary files /dev/null and b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4 differ
````
`````

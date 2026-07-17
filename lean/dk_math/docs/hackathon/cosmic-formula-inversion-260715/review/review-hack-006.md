# Git diff / Report / Review

## hack: cp-006

gch: 14cb0863ae454d99a342a63934397f760a7265d1

## Report

Checkpoint `hack-009a` is complete. 👍️

Created:

- [Integrated promo draft MP4](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/output/DkMathCosmicPromoDraft01.mp4)
- [Timed edit outline](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/edit-outline.md)
- [Narration/subtitle script](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/narration.srt)
- [Asset inventory](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/asset-inventory.md)
- [Reproducible FFmpeg build](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/build_draft.sh)
- [Checkpoint report](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-009a.md)

Output:

- Duration: 2:54
- Resolution: 1280×720
- Frame rate: 30 fps
- Video: H.264
- Audio: silent review draft
- Subtitles: complete sidecar narration script; editorial text burned in
- Manim prototype: full-screen at 01:48
- `git diff --check`: passed

Codex/Lean recordingsと音声が未提供なので、実在する theorem・report に基づく evidence cards で構成しました。リソースメーターはローカル環境から観測できないため、推測せずその旨をレポートに記録しています。

## Review

# hack-009a レビュー

## 判定

**ACCEPT WITH ONE FORMAL PATCH — 映像構成とナレーション案は受理。**

2分54秒、約1.65 MBという軽量な統合映像として、構成・テンポ・情報量はいずれもプロモ用途に適しておる。静止カードから Manim へ移り、再び Lean の検証結果へ戻る流れも明快じゃ。

## 映像構成

現在の十区分は、そのままでよい。

```text
project
→ contract
→ Codex audit
→ general theorem
→ fixed example
→ Manim
→ Lean verification
→ next research direction
→ research loop
```

ぬしが通して見て問題を感じなかったなら、ここでテンポ調整を再開する必要はない。

これは長編解説ではなく、3分以内で、

> 何を考え、AIが何を調査し、Lean が何を認め、映像が何を説明したか

を見せるプロモじゃ。15.9秒の Manim が速いことも、全体では構造上のアクセントになっている。

## スクリプト

ナレーションは全体として良い。英語も平明で、各カードの表示時間には十分収まる。

特に最後の、

> Human direction sets the contract. Codex investigates and implements. Lean verifies. Manim communicates.

は、今回の作品全体を正しく閉じておる。

ただし、公開前に直すべき箇所が一つある。

### 必須修正：prime 仮定が画面上から落ちている

`timeline.ass` の監査カードには、現在こうある。

```text
q ∣ (∏ p ∈ S, p) + u  ∧  Coprime P u  ⇒  q ∉ S
```

これだけでは命題は成立しない。実際の定理には、

```lean
Nat.Prime q
```

が必要じゃ。

画面では、例えば次のように二行に分ければ読みやすい。

```text
Nat.Prime q  and  q ∣ P + u
Nat.Coprime P u   ⇒   q ∉ S
```

前段で `P` が集合積として定義されているため、この表示で十分正確である。

ナレーション側はすでに、

> a prime dividing product plus offset

と言っているため正しい。修正対象は主に burned-in theorem card じゃ。

### 推奨する語句調整

第7ナレーションの、

> Body plus square Gap completes the boundary P plus u

は意味は通じるが、数式上は Body と Gap の和が `P + u` そのものになるようにも聞こえる。

次の方が正確じゃ。

> Body plus the square Gap completes a square whose boundary is P plus u, and two hundred twenty-one factors as thirteen times seventeen.

また、第4ナレーションの、

> audited the existing repository and reports

は、

> audited the existing repository and its reports

の方が自然である。

それ以外の修正は不要。

## 実装・パッケージ評価

良い点は、架空の Codex 操作映像や Lean terminal を作らず、実在する theorem 名と report による evidence card を選んだことじゃ。

```text
simulation of evidence:
  なし

actual declarations:
  あり

actual build reports:
  あり

accepted Manim render:
  あり
```

`build_draft.sh` も、既存の Manim MP4 と FFmpeg だけで再構成できる。Manim の一時環境を統合動画の再生成条件にしなかった判断も良い。

この時点で、次は再設計ではなく**数学的表示の補正と提出物への固定**である。

## 次の Codex Instructions

今回は Codex の編集判断を尊重し、目的と必要な修正だけを渡す。

````md
# Checkpoint hack-010a — Submission-Ready Promo Package

## Goal

Turn the accepted three-minute integration draft into a submission-ready promo package.

Preserve the accepted editorial structure, approximate 2:54 duration, and full-screen Manim segment. The current pacing has been reviewed and accepted.

Exercise your own judgment on the final file organization, caption packaging, and concise submission documentation.

## Required Accuracy Corrections

Correct the theorem card so that the displayed finite-escape implication includes the required primality hypothesis.

A readable form is:

```text
Nat.Prime q  and  q ∣ P + u
Nat.Coprime P u   ⇒   q ∉ S
```

Also refine the narration wording:

```text
"the existing repository and reports"
→
"the existing repository and its reports"
```

and:

```text
"Body plus square Gap completes the boundary P plus u"
→
"Body plus the square Gap completes a square whose boundary is P plus u"
```

Equivalent wording is acceptable when it preserves the exact mathematics and timing.

## Accepted Inputs

Use the accepted Lean modules, reports, Manim prototype, promo sources, and `DkMathCosmicPromoDraft01.mp4`.

Do not invent collaboration recordings, terminal output, theorem results, or research claims that are not present in the repository.

## Deliverables

Produce:

- the corrected final promo MP4;
- the final narration/subtitle file;
- the reproducible build script;
- a concise submission package containing:
  - project title;
  - short description;
  - mathematical result demonstrated;
  - AI-assisted workflow;
  - Lean verification evidence;
  - visual explanation;
  - limitations and future direction;
  - build and reproduction instructions;
  - final asset inventory.

Place the package under the existing hackathon documentation tree in a clear submission-oriented directory.

## Final Checks

Verify:

- exact duration, resolution, frame rate, codec, and file size;
- the corrected prime hypothesis is visible;
- the Manim segment remains readable at full screen;
- the narration timing remains valid;
- all referenced Lean declaration names are exact;
- the video makes no projection or Collatz theorem claim;
- the package rebuilds from its documented command;
- `git diff --check` passes.

Record weekly allowance and additional credits separately when observable. Do not infer either meter.

## Report

Write `report-hack-010a.md` with:

- files changed;
- accuracy corrections;
- final editorial decisions;
- final video metadata;
- submission text produced;
- reproducibility result;
- remaining external tasks, such as human narration or upload;
- first genuine obstruction, if any;
- stop confirmation.

## Stopping Rule

Stop when the corrected promo and submission-ready package are complete.

Do not begin new projection, DkReal, Collatz, or long-form video implementation during this checkpoint.

## Final Instruction

Complete the accuracy pass and submission package, report the result, and stop for final review.
````

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/.gitignore b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/.gitignore
new file mode 100644
index 00000000..da6eb420
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/.gitignore
@@ -0,0 +1,2 @@
+output/*.mp4
+!output/DkMathCosmicPromoDraft01.mp4
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/README.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/README.md
new file mode 100644
index 00000000..58ec1f80
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/README.md
@@ -0,0 +1,13 @@
+# Three-minute promo integration draft
+
+Build from this directory or any working directory:
+
+```bash
+bash build_draft.sh
+```
+
+The build uses FFmpeg to render timed evidence cards and inserts the accepted
+Manim prototype full-screen from 01:48. The output is a silent review copy;
+`narration.srt` is the narration/subtitle script for recording and later caption
+authoring.
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/asset-inventory.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/asset-inventory.md
new file mode 100644
index 00000000..6d4703fa
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/asset-inventory.md
@@ -0,0 +1,39 @@
+# Promo asset inventory
+
+## Accepted formal sources
+
+- `DkMath/Hackathon/FinitePrimeEscape.lean`
+- `DkMath/Hackathon/CosmicCompletion.lean`
+- `DkMath/Hackathon/Demo.lean`
+
+These provide the general escape theorem, square-completion identity, and fixed
+`{2, 3, 5, 7}`, `210`, `11`, `221`, `13`, `17` demonstration.
+
+## Accepted process evidence
+
+- `report-hack-001.md`: contract and repository investigation
+- `report-hack-002.md`: finite prime escape implementation
+- `report-hack-003.md`: Cosmic completion implementation
+- `report-hack-004.md`: fixed Lean demo
+- `report-hack-008a.md`: visual prototype and render evidence
+
+## Accepted moving image
+
+- `../visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4`
+  (15.9 seconds, 1280x720, 30 fps, H.264, silent)
+
+## Available integration material
+
+- Actual Lean declaration names and short source excerpts
+- Actual checkpoint sequence and verified build outcomes
+- The Manim prototype at full 720p resolution
+- Project design documents describing bounded inverse projection
+
+## Missing assets
+
+- No screen recording of the human/Codex repository session
+- No Lean editor or terminal recording
+- No recorded narration, music, or sound effects
+- No inverse-projection animation (future research, not an accepted result)
+- No Collatz footage selected; therefore no Collatz claim appears in this draft
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/build_draft.sh b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/build_draft.sh
new file mode 100644
index 00000000..d2430bcb
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/build_draft.sh
@@ -0,0 +1,26 @@
+#!/usr/bin/env bash
+set -euo pipefail
+
+here="$(cd "$(dirname "$0")" && pwd)"
+manim="$here/../visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4"
+output="$here/output/DkMathCosmicPromoDraft01.mp4"
+
+mkdir -p "$here/output"
+
+ffmpeg -y \
+  -f lavfi -i "color=c=0x0B1020:s=1280x720:r=30:d=174" \
+  -i "$manim" \
+  -filter_complex \
+  "[0:v]ass='$here/timeline.ass'[cards];\
+   [1:v]scale=1280:720,format=yuva420p,\
+   fade=t=in:st=0:d=0.4:alpha=1,\
+   fade=t=out:st=15.5:d=0.4:alpha=1,\
+   setpts=PTS+108/TB[visual];\
+   [cards][visual]overlay=0:0:eof_action=pass:enable='between(t,108,124)'[video]" \
+  -map "[video]" \
+  -c:v libx264 -preset medium -crf 18 -pix_fmt yuv420p \
+  -r 30 -t 174 -movflags +faststart \
+  "$output"
+
+printf '%s\n' "$output"
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/edit-outline.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/edit-outline.md
new file mode 100644
index 00000000..1a3b9b63
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/edit-outline.md
@@ -0,0 +1,17 @@
+# Timed edit outline — draft 1
+
+| Time | Duration | Picture | Editorial purpose |
+|---|---:|---|---|
+| 00:00-00:12 | 12 s | Project title and workflow line | Establish the proposition |
+| 00:12-00:30 | 18 s | DkMath library card | Place the work in a large Lean research repository |
+| 00:30-00:48 | 18 s | Mathematical contract card | Show that the target was fixed before coding |
+| 00:48-01:08 | 20 s | Repository-audit card | Explain Codex's smallest-bridge investigation |
+| 01:08-01:30 | 22 s | General Lean theorem card | Show the finite escape theorem and square completion |
+| 01:30-01:48 | 18 s | Fixed demo declarations | Connect general theorem to accepted values |
+| 01:48-02:04 | 16 s | Accepted Manim prototype, full screen | Visualize the shared boundary and fresh factors |
+| 02:04-02:25 | 21 s | Verification result card | State exactly what Lean verified |
+| 02:25-02:43 | 18 s | Bounded inverse projection card | Mark the next research direction without overclaiming |
+| 02:43-02:54 | 11 s | Closing workflow card | Summarize human + Codex + Lean + Manim |
+
+Total target duration: 2 minutes 54 seconds.
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/narration.srt b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/narration.srt
new file mode 100644
index 00000000..3efd7bc3
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/narration.srt
@@ -0,0 +1,40 @@
+1
+00:00:00,000 --> 00:00:12,000
+DkMath asks a practical question: can human mathematical direction, AI-assisted implementation, formal verification, and visual explanation form one research workflow?
+
+2
+00:00:12,000 --> 00:00:30,000
+DkMath is a large Lean mathematical research library. This hackathon slice does not replace that library; it adds a deliberately small, reviewable bridge inside it.
+
+3
+00:00:30,000 --> 00:00:48,000
+Before implementation, the mathematical contract fixed a finite prime set, its product, a coprime offset, the boundary, and the meaning of a fresh prime factor.
+
+4
+00:00:48,000 --> 00:01:08,000
+Codex audited the existing repository and reports, then identified the smallest missing bridge: prove that a prime dividing product plus offset cannot belong to the original finite set.
+
+5
+00:01:08,000 --> 00:01:30,000
+The implementation adds a general finite prime escape theorem and the algebraic Cosmic completion identity. Lean checks the hypotheses, divisibility argument, and completed square.
+
+6
+00:01:30,000 --> 00:01:48,000
+The fixed demonstration chooses S equals two, three, five, seven; P equals two hundred ten; and u equals eleven. Their shared boundary is two hundred twenty-one.
+
+7
+00:01:48,000 --> 00:02:04,000
+Manim now presents the same accepted data visually: Body plus square Gap completes the boundary P plus u, and two hundred twenty-one factors as thirteen times seventeen.
+
+8
+00:02:04,000 --> 00:02:25,000
+Lean verifies that thirteen and seventeen are prime divisors of the boundary and are outside the starting set. The animation explains a theorem-backed result; it does not create the evidence.
+
+9
+00:02:25,000 --> 00:02:43,000
+The next research direction is bounded inverse projection: search backward from observable boundaries under explicit finite bounds. It is a direction, not a theorem claimed by this draft.
+
+10
+00:02:43,000 --> 00:02:54,000
+Human direction sets the contract. Codex investigates and implements. Lean verifies. Manim communicates. That is the DkMath research loop.
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/output/DkMathCosmicPromoDraft01.mp4 b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/output/DkMathCosmicPromoDraft01.mp4
new file mode 100644
index 00000000..56437d70
Binary files /dev/null and b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/output/DkMathCosmicPromoDraft01.mp4 differ
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/timeline.ass b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/timeline.ass
new file mode 100644
index 00000000..c905aba8
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/promo/timeline.ass
@@ -0,0 +1,43 @@
+[Script Info]
+ScriptType: v4.00+
+PlayResX: 1280
+PlayResY: 720
+ScaledBorderAndShadow: yes
+
+[V4+ Styles]
+Format: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding
+Style: Title,DejaVu Sans,48,&H00F8FAFC,&H000000FF,&H000B1020,&H00000000,-1,0,0,0,100,100,0,0,1,1,0,8,70,70,70,1
+Style: Body,DejaVu Sans,30,&H00F8FAFC,&H000000FF,&H000B1020,&H00000000,0,0,0,0,100,100,0,0,1,1,0,5,100,100,40,1
+Style: Code,DejaVu Sans Mono,25,&H0067E8F9,&H000000FF,&H000B1020,&H00000000,0,0,0,0,100,100,0,0,1,1,0,5,90,90,40,1
+Style: Footer,DejaVu Sans,20,&H0094A3B8,&H000000FF,&H000B1020,&H00000000,0,0,0,0,100,100,0,0,1,1,0,2,50,50,30,1
+
+[Events]
+Format: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text
+Dialogue: 0,0:00:00.00,0:00:12.00,Title,,0,0,0,,DkMath · Verifiable Research in Motion
+Dialogue: 0,0:00:00.00,0:00:12.00,Body,,0,0,0,,human direction  →  Codex  →  Lean  →  Manim
+Dialogue: 0,0:00:00.00,0:00:12.00,Footer,,0,0,0,,Cosmic Formula Inversion · integration draft
+Dialogue: 0,0:00:12.00,0:00:30.00,Title,,0,0,0,,1 · A Lean research library
+Dialogue: 0,0:00:12.00,0:00:30.00,Body,,0,0,0,,DkMath is a large, evolving mathematical research repository.\NThis promo follows one small theorem path inside the real library.
+Dialogue: 0,0:00:12.00,0:00:30.00,Code,,0,0,0,,DkMath/Hackathon/FinitePrimeEscape.lean\NDkMath/Hackathon/CosmicCompletion.lean\NDkMath/Hackathon/Demo.lean
+Dialogue: 0,0:00:30.00,0:00:48.00,Title,,0,0,0,,2 · Contract before implementation
+Dialogue: 0,0:00:30.00,0:00:48.00,Body,,0,0,0,,The mathematical target was fixed first:\Na finite set S, product P, coprime offset u, and boundary P + u.
+Dialogue: 0,0:00:30.00,0:00:48.00,Code,,0,0,0,,FreshPrimeFactor S n q :=\N  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
+Dialogue: 0,0:00:48.00,0:01:08.00,Title,,0,0,0,,3 · Codex audits the repository
+Dialogue: 0,0:00:48.00,0:01:08.00,Body,,0,0,0,,Existing APIs and reports were inspected.\NThe smallest missing bridge became one explicit theorem.
+Dialogue: 0,0:00:48.00,0:01:08.00,Code,,0,0,0,,prime_dvd_product_add_coprime_not_mem\N\Nq ∣ (∏ p ∈ S, p) + u  ∧  Coprime P u  ⇒  q ∉ S
+Dialogue: 0,0:01:08.00,0:01:30.00,Title,,0,0,0,,4 · Lean verifies the general bridge
+Dialogue: 0,0:01:08.00,0:01:30.00,Code,,0,0,0,,theorem exists_fresh_prime_factor ... :\N  ∃ q, FreshPrimeFactor S (P + u) q\N\Ntheorem cosmicCompletion (P u : ℕ) :\N  P * (P + 2 * u) + u ^ 2 = (P + u) ^ 2
+Dialogue: 0,0:01:08.00,0:01:30.00,Footer,,0,0,0,,General theorem surface · checked by Lean
+Dialogue: 0,0:01:30.00,0:01:48.00,Title,,0,0,0,,5 · One accepted fixed example
+Dialogue: 0,0:01:30.00,0:01:48.00,Code,,0,0,0,,S = {2, 3, 5, 7}     P = 210     u = 11\NP + u = 221           221 = 13 × 17
+Dialogue: 0,0:01:30.00,0:01:48.00,Body,,0,0,0,,The same values are shared by Demo.lean and the visual prototype.
+Dialogue: 0,0:02:04.00,0:02:25.00,Title,,0,0,0,,6 · Explanation backed by proof
+Dialogue: 0,0:02:04.00,0:02:25.00,Code,,0,0,0,,demo_thirteen_fresh\Ndemo_seventeen_fresh\Ndemo_cosmic_completion
+Dialogue: 0,0:02:04.00,0:02:25.00,Body,,0,0,0,,Lean verifies 13 and 17 are fresh relative to {2, 3, 5, 7}.\NManim communicates the result; it is not the source of truth.
+Dialogue: 0,0:02:25.00,0:02:43.00,Title,,0,0,0,,7 · Next: bounded inverse projection
+Dialogue: 0,0:02:25.00,0:02:43.00,Body,,0,0,0,,Search backward from observable boundaries under explicit finite bounds.\NThis is the next research direction — not a theorem claimed here.
+Dialogue: 0,0:02:25.00,0:02:43.00,Code,,0,0,0,,verified finite bridge  →  bounded candidates  →  future projection
+Dialogue: 0,0:02:43.00,0:02:54.00,Title,,0,0,0,,DkMath · one research loop
+Dialogue: 0,0:02:43.00,0:02:54.00,Body,,0,0,0,,Human direction sets the contract.\NCodex investigates and implements. Lean verifies. Manim communicates.
+Dialogue: 0,0:02:43.00,0:02:54.00,Footer,,0,0,0,,First integration draft · silent · review copy
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-009a.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-009a.md
new file mode 100644
index 00000000..a82fbb98
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-009a.md
@@ -0,0 +1,189 @@
+# Checkpoint hack-009a — Three-Minute Promo Integration Draft
+
+## Status
+
+Complete. A coherent 2-minute-54-second integration draft was built from actual
+Lean evidence, accepted checkpoint reports, and the accepted Manim prototype.
+The accepted Lean and Manim source modules were not changed.
+
+## Editorial structure chosen
+
+The draft uses a proof-backed research-loop structure:
+
+```text
+project context
+→ contract before code
+→ Codex repository audit
+→ general Lean bridge
+→ fixed verified example
+→ full-screen Manim explanation
+→ proof/visual distinction
+→ bounded inverse projection as future work
+```
+
+Timed evidence cards carry the parts for which no screen recording exists. They
+show real paths, declaration names, theorem statements, and accepted values
+rather than simulated editor or terminal footage.
+
+## Assets used
+
+Formal evidence:
+
+- `DkMath/Hackathon/FinitePrimeEscape.lean`
+- `DkMath/Hackathon/CosmicCompletion.lean`
+- `DkMath/Hackathon/Demo.lean`
+
+Process evidence:
+
+- `report-hack-001.md`
+- `report-hack-002.md`
+- `report-hack-003.md`
+- `report-hack-004.md`
+- `report-hack-008a.md`
+
+Moving image:
+
+- `visual/media/videos/cosmic_formula_scene/720p30/`
+  `CosmicFormulaPrototype.mp4`
+
+`promo/asset-inventory.md` records the complete used/missing inventory, and
+`promo/edit-outline.md` records the timed ten-part edit.
+
+## Role of the Manim prototype
+
+The accepted 15.9-second prototype is inserted at 01:48, scaled to the complete
+1280x720 frame. It is not reduced to picture-in-picture, so its equations and
+labels retain their accepted readability. It supplies the visual transition
+from the finite set through Body + Gap and boundary 221 to fresh factors 13 and
+17. The following card explicitly restores the evidentiary hierarchy: Lean is
+the source of verification; Manim communicates the result.
+
+## Codex and Lean evidence shown
+
+The Codex section states the repository-audit outcome and shows the smallest
+missing bridge by its real declaration name:
+`prime_dvd_product_add_coprime_not_mem`.
+
+The Lean sections show short versions of the accepted theorem surfaces:
+
+- `FreshPrimeFactor`
+- `exists_fresh_prime_factor`
+- `cosmicCompletion`
+- `demo_thirteen_fresh`
+- `demo_seventeen_fresh`
+- `demo_cosmic_completion`
+
+The draft does not present an invented Codex session recording or a fabricated
+Lean terminal. Its evidence cards are traceable to the accepted repository
+files.
+
+## Narration structure
+
+`promo/narration.srt` contains a complete ten-cue narration/subtitle script
+timed to the edit. It explains DkMath, contract-first design, Codex's audit, the
+two general Lean results, the fixed example, the Manim boundary, freshness, and
+bounded inverse projection. The output draft is intentionally silent, so this
+script is a sidecar production plan rather than an embedded subtitle stream.
+
+The video itself uses burned-in editorial text and code evidence on every card.
+The Manim interval uses its own burned-in labels.
+
+## Missing footage
+
+No Codex interaction recording, Lean editor/terminal recording, recorded voice,
+music, or inverse-projection animation was available. The strongest honest draft
+therefore uses evidence cards for the first two and leaves the future projection
+as a carefully limited direction. No Collatz footage was used, so no Collatz
+claim or convergence disclaimer is needed in the cut.
+
+## Build command and tools
+
+Exact command, run from `promo/`:
+
+```bash
+bash build_draft.sh
+```
+
+The script's integration renderer is:
+
+- FFmpeg `6.1.1-3ubuntu5`
+- libass `0.17.1`
+- libx264, H.264 High profile
+- DejaVu Sans and DejaVu Sans Mono through Fontconfig
+
+The accepted embedded visual was previously rendered with Manim Community
+`0.20.1`. This integration build does not invoke Manim or Python.
+
+## Technical output metadata
+
+- Output: `promo/output/DkMathCosmicPromoDraft01.mp4`
+- Render result: success, exit status 0
+- Duration: 174.000 seconds (02:54)
+- Resolution: 1280x720
+- Frame rate: 30 fps
+- Video: H.264, `yuv420p`
+- File size: 1,650,079 bytes
+- Audio status: silent; no audio stream
+- Subtitle status: timed narration sidecar in `promo/narration.srt`; editorial
+  evidence and labels are burned into the video; no embedded subtitle stream
+
+A nine-frame contact sheet sampled every 20 seconds was inspected. It confirmed
+the chapter cards, real theorem identifiers, full-screen Manim insertion, future
+direction limitation, and final workflow card.
+
+## Resource meters
+
+The local Codex workspace exposes no API or file containing the two UI resource
+meters. They cannot be inferred from token usage, and weekly percentage was not
+converted into credits.
+
+```text
+Weekly allowance before: not observable in the local execution environment
+Weekly allowance after: not observable in the local execution environment
+
+Additional credits before: not observable in the local execution environment
+Additional credits after: not observable in the local execution environment
+```
+
+## Resolved environmental issues
+
+The project-level `/venv` exists and uses Python
+3.12.3, but does not currently contain Manim. No new Manim render was needed:
+the checkpoint explicitly accepts the existing MP4, and FFmpeg can integrate it
+directly. This avoided modifying either the project environment or the accepted
+visual source.
+
+The prior prototype's temporary Manim environment is therefore not a dependency
+of `promo/build_draft.sh`; only FFmpeg plus the retained accepted MP4 are needed.
+
+## First genuine obstruction
+
+The first genuine integration obstruction was the absence of human/Codex and
+Lean-session recordings, followed by the absence of recorded narration. It did
+not prevent a coherent evidence-based review draft, but it prevents this cut
+from honestly showing the live collaboration and from functioning as a finished
+audio-led promo.
+
+## Recommended next integration step
+
+Review timing and wording first. Then record one concise human/Codex repository
+sequence, one Lean build/editor sequence, and the narration against
+`promo/narration.srt`. Replace the corresponding static evidence cards while
+retaining the full-screen accepted Manim interval. Only after that editorial
+pass should music, sound design, and final submission packaging begin.
+
+## Repository verification
+
+- `bash -n promo/build_draft.sh`: passed.
+- Trailing-whitespace scan over `promo/` and this report: passed.
+- `git diff --check`: passed with no output.
+- `git status --short --untracked-files=all`: reported only the nine new
+  checkpoint deliverables under `promo/` and `report-hack-009a.md`.
+- The final source/report set and output metadata were inspected; no accepted
+  Lean or Manim source file was modified.
+
+## Stop confirmation
+
+Stopped after the first coherent integrated draft. No projection or DkReal
+implementation, public long-form production, or final submission packaging was
+started.
````
`````

# Git diff / Report / Review

## hack: cp-007

gch: b6a85016bc2eb967c7e127fe93a53f508e4b0997

## Report

Checkpoint `hack-010a` is complete. 👍️

Submission package:

- [Final promo MP4](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/output/DkMathCosmicPromoFinal.mp4)
- [Submission README](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/README.md)
- [Final narration/subtitles](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/narration.srt)
- [Final asset inventory](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/ASSET_INVENTORY.md)
- [Reproducible build](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/build_submission.sh)
- [Checkpoint report](/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-010a.md)

Corrections verified:

- The theorem card now visibly includes `Nat.Prime q`.
- Both requested narration passages were corrected.
- Manim remains full-screen at 01:48.
- Duration remains exactly 2:54.
- 1280×720, 30 fps, H.264.
- Final size: 1,652,906 bytes.
- Declaration names match the Lean sources.
- No projection or Collatz theorem claim is made.
- Rebuild succeeded.
- `git diff --check` passed.

Remaining external work is limited to human narration, optional authentic recordings/audio, and upload.

## Review

# hack-010a 状況分析・レビュー

## 判定

**ACCEPT — checkpoint `hack-010a` を受理。**

数学表示の修正、最終映像、再生成スクリプト、ナレーション、提出用説明、資産来歴まで揃った。

```text
FORMAL MVP          = complete
VISUAL MVP          = complete
PROMO INTEGRATION   = complete
SUBMISSION PACKAGE  = complete
```

リポジトリ内で行う主要制作は、これで実質的に閉じておる。

## 修正確認

前回指摘した prime 仮定が、表示上も正しく復元された。

```text
Nat.Prime q  and  q ∣ P + u
Nat.Coprime P u   ⇒   q ∉ S
```

これで映像カードと実際の Lean theorem の意味が一致した。

ナレーションも、

```text
the existing repository and its reports
```

および、

```text
Body plus the square Gap completes a square
whose boundary is P plus u
```

へ直されている。平方の面積と境界長を混同する余地がなくなった。

## パッケージ設計

`promo/` をレビュー用 draft として残し、`submission/` に corrected final を独立配置した判断は良い。

```text
promo/
  accepted integration history

submission/
  final reproducible deliverable
```

これにより、どちらが提出対象か曖昧にならない。

最終映像も、

```text
duration:    2:54
resolution:  1280 × 720
frame rate:  30 fps
codec:       H.264
size:        1,652,906 bytes
```

で維持され、Manim は 01:48 から全画面表示されている。

## 再現性

最終映像は、

```bash
bash build_submission.sh
```

で再生成できる。

依存も、

```text
FFmpeg
libass
libx264
Fontconfig
DejaVu fonts
accepted Manim MP4
```

に限定されており、以前の一時 Manim 環境を要求しない。

これは提出物として強い。映像の生成環境と数学映像の生成環境が分離され、最終編集だけを軽量に再現できる。

## 公開主張の監査

提出 README の数学記述も正確じゃ。

- `S` は一般の有限集合として述べられている。
- `q` の primality が明示されている。
- freshness は有限集合相対である。
- primitive prime divisor とは主張していない。
- bounded inverse projection は将来方向とされている。
- Collatz の証明主張はない。
- Manim を証拠ではなく説明層として位置づけている。

つまり、

```text
Lean:
  verifies

Manim:
  communicates
```

という証拠階層が最後まで維持された。

## 現在の残作業

残っているものは研究実装ではなく、外部公開作業じゃ。

```text
human narration
optional music
optional authentic recordings
platform form entry
upload
```

音声がないため、厳密には **repository-complete / publication-pending** の状態である。

ただし、焼き込みテキストだけでも映像内容は読めるため、無音 master 自体は有効な完成物じゃ。

## 次の進行判断

もう新しい数学や映像を追加する段階ではない。

最後に一度だけ、リポジトリ全体の完了状態を文書へ反映し、提出者が迷わない handoff を作れば、Hackathon branch を閉じられる。

その後、Codex の週次余力を Collatz へ戻せる。

# 次の Codex Instructions

今回は最終整理なので、Codex に文書構成と確認方法を任せる。

````md
# Checkpoint hack-010b — Final Handoff and Project Closure

## Goal

Close the Cosmic Formula Inversion hackathon work inside the repository.

Review the accepted formal, visual, promo, and submission artifacts, then leave a concise final handoff that allows the human author to narrate, upload, and submit without reopening the implementation history.

Use your own judgment to make the final repository state clear and economical.

## Accepted State

The following work is accepted:

```text
hack-001   repository audit
hack-002   finite prime escape
hack-003   Cosmic square completion
hack-004   fixed verified demo
hack-008a  Manim prototype
hack-009a  integrated promo draft
hack-010a  corrected submission package
```

The accepted final video is:

```text
submission/output/DkMathCosmicPromoFinal.mp4
```

## Work

Update the project status documents so that they accurately show:

```text
formal MVP complete
visual prototype complete
promo integration complete
submission package complete
external publication tasks remaining
```

Create a final handoff document containing:

```text
the verified mathematical result
the final Lean declarations
the final video and build command
the submission document locations
artifact provenance
remaining human actions
the exact point at which future inverse-projection work should resume
```

Include checksums for the final submitted artifacts when useful.

Preserve the accepted mathematical claims and final assets. Do not reopen completed implementation merely for stylistic cleanup.

## Verification

Confirm that:

```text
the focused Lean Demo build succeeds
the final submission video rebuild succeeds
the final declaration names are exact
the final video metadata matches the accepted report
the submission documents point to existing assets
git diff --check passes
```

Record the actual commands and outcomes.

## Deliverables

Create:

```text
FINAL_HANDOFF.md
report-hack-010b.md
```

and make only the minimal status updates needed in the existing planning and checkpoint documents.

Choose their precise placement according to the established project structure.

## Resource Record

When visible, record independently:

```text
Weekly allowance before / after
Additional credits before / after
```

Do not infer or convert either meter.

## Stopping Rule

Stop when the repository clearly communicates that the hackathon implementation and package are complete and only external human publication actions remain.

Do not begin inverse projection, DkReal, Collatz, or a new visual production pass.

## Final Instruction

Complete the final handoff, verify the accepted deliverables, write the closure report, and stop.
````

この `hack-010b` が閉じれば、Hackathon 系の Codex 作業はいったん終了でよい。次の実装セッションからは、また Collatz 側の盤面へ戻せるの。

## Diff

`````md
````diff
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-010a.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-010a.md
new file mode 100644
index 00000000..1739b54c
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/report-hack-010a.md
@@ -0,0 +1,157 @@
+# Checkpoint hack-010a — Submission-Ready Promo Package
+
+## Status
+
+Complete. The accepted edit was accuracy-corrected, rebuilt as a final 2:54
+silent promo master, and packaged with final captions, source timeline,
+reproduction script, submission copy, and asset provenance.
+
+## Files changed
+
+Created under `submission/`:
+
+- `README.md`
+- `ASSET_INVENTORY.md`
+- `narration.srt`
+- `timeline.ass`
+- `build_submission.sh`
+- `.gitignore`
+- `output/DkMathCosmicPromoFinal.mp4`
+
+Also created `report-hack-010a.md`. Accepted Lean modules, Manim sources, and
+the accepted integration-draft sources were not modified.
+
+## Accuracy corrections
+
+The finite-escape card now visibly states all material hypotheses:
+
+```text
+Nat.Prime q  and  q ∣ P + u
+Nat.Coprime P u   ⇒   q ∉ S
+```
+
+A frame extracted at 00:55 was inspected at 1280x720 and confirmed that the
+primality hypothesis, divisibility hypothesis, coprimality hypothesis, and
+conclusion are all readable.
+
+The final narration changes:
+
+- `the existing repository and reports` to
+  `the existing repository and its reports`;
+- `Body plus square Gap completes the boundary P plus u` to
+  `Body plus the square Gap completes a square whose boundary is P plus u`.
+
+All displayed Lean declaration names were compared with the accepted modules.
+The names in the package match exactly.
+
+## Final editorial decisions
+
+The reviewed ten-part structure, 174-second duration, and evidence-card pacing
+were preserved. The accepted Manim segment remains at 01:48 and occupies the
+complete 1280x720 frame. A frame at 01:52 confirmed that no picture-in-picture
+scaling or integration overlay reduces its readable area.
+
+The accepted draft remains as a review artifact under `promo/`. The corrected
+master is independently packaged under `submission/`, avoiding ambiguity
+between draft and final deliverables.
+
+The output remains a silent captioned master. Editorial evidence is burned in;
+the final timed narration is supplied as an SRT sidecar for human recording and
+caption authoring.
+
+## Final video metadata
+
+- Path: `submission/output/DkMathCosmicPromoFinal.mp4`
+- Build result: success, exit status 0
+- Duration: 174.000 seconds (02:54)
+- Resolution: 1280x720
+- Frame rate: 30 fps
+- Codec: H.264, High profile, `yuv420p`
+- File size: 1,652,906 bytes
+- Audio: no audio stream
+- Embedded subtitle stream: none
+- Caption status: burned-in editorial text plus final `submission/narration.srt`
+  sidecar
+
+## Submission text produced
+
+`submission/README.md` is the concise submission document. It contains:
+
+- project title and short description;
+- demonstrated finite prime escape and Cosmic completion results;
+- human/Codex/Lean/Manim workflow;
+- exact Lean verification declarations and source modules;
+- role and timing of the visual explanation;
+- limitations and bounded inverse projection as future direction;
+- requirements, exact build command, and expected output;
+- package contents.
+
+`submission/ASSET_INVENTORY.md` separately records final artifacts, verified
+evidence provenance, embedded Manim provenance, accuracy constraints, and
+remaining external assets.
+
+## Reproducibility result
+
+Exact documented command, run from `submission/`:
+
+```bash
+bash build_submission.sh
+```
+
+The command rebuilt the final MP4 successfully using FFmpeg `6.1.1-3ubuntu5`,
+libass `0.17.1`, libx264, Fontconfig, DejaVu fonts, and the accepted Manim MP4.
+The script does not require Python or the project venv.
+
+The narration has ten contiguous cues spanning 00:00:00 through 00:02:54, so its
+timing remains aligned with the unchanged edit duration.
+
+## Claim audit
+
+- The prime hypothesis is visible in the corrected theorem card.
+- Manim remains full-screen and readable.
+- Declaration names match the accepted Lean files.
+- Bounded inverse projection is explicitly future research, not a theorem.
+- No Collatz result or convergence claim appears.
+- No invented collaboration recording, terminal output, or theorem result was
+  added.
+
+## Resource meters
+
+Weekly allowance and additional credits were not observable from the local
+execution environment. Neither value was inferred or converted from another
+meter.
+
+## Remaining external tasks
+
+- Record the human narration using `submission/narration.srt`.
+- Optionally replace selected evidence cards with authentic collaboration and
+  Lean editor footage.
+- Add licensed music or sound design if desired.
+- Supply hackathon-platform metadata and upload the reviewed master.
+
+These are external production or publication tasks; none prevents the current
+silent master from being a reproducible submission package.
+
+## First genuine obstruction
+
+The first remaining obstruction to an audio-finished public promo is the absence
+of recorded human narration. It did not obstruct this checkpoint because the
+accepted format is preserved as a silent captioned master with a complete timed
+narration sidecar.
+
+## Verification
+
+- Video metadata was measured with `ffprobe`.
+- Corrected and Manim frames were extracted with FFmpeg and inspected.
+- The six referenced declaration names were checked against the Lean sources.
+- Projection and Collatz wording was scanned across `submission/`.
+- `bash -n submission/build_submission.sh`: passed.
+- Trailing-whitespace scan over the package and report: passed.
+- `git diff --check`: passed with no output.
+- `git status --short --untracked-files=all`: reported only this report and the
+  seven new submission-package artifacts.
+
+## Stop confirmation
+
+Stopped with the corrected promo and submission-ready package complete. No new
+projection, DkReal, Collatz, or long-form video implementation was started.
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/.gitignore b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/.gitignore
new file mode 100644
index 00000000..ddf771fc
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/.gitignore
@@ -0,0 +1,2 @@
+output/*.mp4
+!output/DkMathCosmicPromoFinal.mp4
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/ASSET_INVENTORY.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/ASSET_INVENTORY.md
new file mode 100644
index 00000000..f295bde8
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/ASSET_INVENTORY.md
@@ -0,0 +1,48 @@
+# Final asset inventory
+
+## Submission artifacts
+
+| Asset | Role | Status |
+|---|---|---|
+| `output/DkMathCosmicPromoFinal.mp4` | 2:54 final silent promo | Generated |
+| `narration.srt` | Final timed narration/subtitle source | Included |
+| `timeline.ass` | Burned-in evidence-card timeline | Included |
+| `build_submission.sh` | Reproducible FFmpeg build | Included |
+| `README.md` | Submission text and reproduction guide | Included |
+
+## Verified source evidence
+
+| Repository asset | Evidence used |
+|---|---|
+| `DkMath/Hackathon/FinitePrimeEscape.lean` | Freshness definition and finite escape theorems |
+| `DkMath/Hackathon/CosmicCompletion.lean` | Completed-square identity |
+| `DkMath/Hackathon/Demo.lean` | Fixed values, factorization, freshness, completion |
+| `report-hack-001.md` through `report-hack-004.md` | Contract, audit, implementation, fixed demo trail |
+| `report-hack-008a.md` | Manim render provenance |
+| `report-hack-009a.md` | Accepted integration structure and metadata |
+
+## Embedded moving-image asset
+
+```text
+../visual/media/videos/cosmic_formula_scene/720p30/
+  CosmicFormulaPrototype.mp4
+```
+
+This accepted 15.9-second, 1280x720, 30 fps H.264 clip is inserted full-screen
+at 01:48. It has no audio stream.
+
+## Accuracy constraints applied
+
+- The finite-escape card explicitly includes `Nat.Prime q`.
+- Freshness is relative to the finite set `{2, 3, 5, 7}`.
+- Bounded inverse projection is labeled as future research, not a theorem.
+- No Collatz theorem or convergence claim appears.
+- No invented collaboration recording or terminal output is included.
+
+## Remaining external assets
+
+- Human narration recording
+- Optional music and sound design with appropriate licensing
+- Optional authentic Codex collaboration and Lean editor recordings
+- Hackathon platform metadata and uploaded media URL
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/README.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/README.md
new file mode 100644
index 00000000..5d8bd5cf
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/README.md
@@ -0,0 +1,96 @@
+# DkMath — Verifiable Research in Motion
+
+## Short description
+
+DkMath demonstrates a contract-first, AI-assisted mathematical research loop:
+human direction fixes a precise target, Codex audits and extends the repository,
+Lean verifies the result, and Manim explains the verified example visually.
+
+## Mathematical result demonstrated
+
+For a finite set `S`, let `P` be the product of its members. If `P` and an
+offset `u` are coprime, then any prime `q` dividing `P + u` cannot be in `S`.
+The demo uses
+
+```text
+S = {2, 3, 5, 7},  P = 210,  u = 11,
+P + u = 221 = 13 × 17,
+```
+
+so both `13` and `17` are fresh relative to `S`. The accompanying algebraic
+identity completes the Cosmic square:
+
+```text
+P(P + 2u) + u² = (P + u)².
+```
+
+## AI-assisted workflow
+
+The mathematical contract was written before implementation. Codex inspected
+the existing repository and its reports, identified the smallest missing bridge,
+implemented the general theorems and fixed demo, and kept the reports aligned
+with verification and visualization artifacts.
+
+## Lean verification evidence
+
+The accepted declarations are:
+
+- `DkMath.Hackathon.prime_dvd_product_add_coprime_not_mem`
+- `DkMath.Hackathon.exists_fresh_prime_factor`
+- `DkMath.Hackathon.cosmicCompletion`
+- `DkMath.Hackathon.demo_thirteen_fresh`
+- `DkMath.Hackathon.demo_seventeen_fresh`
+- `DkMath.Hackathon.demo_cosmic_completion`
+
+They are defined in `DkMath/Hackathon/FinitePrimeEscape.lean`,
+`DkMath/Hackathon/CosmicCompletion.lean`, and `DkMath/Hackathon/Demo.lean`.
+
+## Visual explanation
+
+The 2:54 promo presents the contract and proof evidence as readable cards. At
+01:48, the accepted Manim animation remains full-screen and shows the transition
+from the finite prime set through Body plus the square Gap to the completed
+boundary `P + u = 221`, its factorization, and freshness.
+
+## Limitations and future direction
+
+This silent master contains burned-in editorial text and a timed narration
+sidecar, but no recorded human narration, collaboration footage, or terminal
+capture. It makes no Collatz convergence claim and no inverse-projection theorem
+claim. Bounded inverse projection is identified only as the next research
+direction.
+
+## Build and reproduction
+
+Requirements:
+
+- Bash
+- FFmpeg with libass and libx264
+- DejaVu Sans and DejaVu Sans Mono
+- the accepted Manim MP4 at its repository path
+
+From this directory, run:
+
+```bash
+bash build_submission.sh
+```
+
+Expected output:
+
+```text
+output/DkMathCosmicPromoFinal.mp4
+```
+
+The build renders a 174-second, 1280x720, 30 fps H.264 silent MP4. `timeline.ass`
+is the burned-in editorial timeline; `narration.srt` is the final timed narration
+and caption-authoring source.
+
+## Package contents
+
+- `output/DkMathCosmicPromoFinal.mp4` — final silent captioned promo master
+- `narration.srt` — final timed narration/subtitle file
+- `timeline.ass` — final burned-in editorial timeline
+- `build_submission.sh` — reproducible final build
+- `ASSET_INVENTORY.md` — provenance and package inventory
+- `README.md` — submission description and reproduction guide
+
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/build_submission.sh b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/build_submission.sh
new file mode 100644
index 00000000..afbf225e
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/build_submission.sh
@@ -0,0 +1,26 @@
+#!/usr/bin/env bash
+set -euo pipefail
+
+here="$(cd "$(dirname "$0")" && pwd)"
+manim="$here/../visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4"
+output="$here/output/DkMathCosmicPromoFinal.mp4"
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
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/narration.srt b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/narration.srt
new file mode 100644
index 00000000..0c555c6b
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/narration.srt
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
+Codex audited the existing repository and its reports, then identified the smallest missing bridge: prove that a prime dividing product plus offset cannot belong to the original finite set.
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
+Manim now presents the same accepted data visually: Body plus the square Gap completes a square whose boundary is P plus u, and two hundred twenty-one factors as thirteen times seventeen.
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
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/output/DkMathCosmicPromoFinal.mp4 b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/output/DkMathCosmicPromoFinal.mp4
new file mode 100644
index 00000000..a3ce9202
Binary files /dev/null and b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/output/DkMathCosmicPromoFinal.mp4 differ
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/timeline.ass b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/timeline.ass
new file mode 100644
index 00000000..b37d6014
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/timeline.ass
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
+Dialogue: 0,0:00:00.00,0:00:12.00,Footer,,0,0,0,,Cosmic Formula Inversion · final promo
+Dialogue: 0,0:00:12.00,0:00:30.00,Title,,0,0,0,,1 · A Lean research library
+Dialogue: 0,0:00:12.00,0:00:30.00,Body,,0,0,0,,DkMath is a large, evolving mathematical research repository.\NThis promo follows one small theorem path inside the real library.
+Dialogue: 0,0:00:12.00,0:00:30.00,Code,,0,0,0,,DkMath/Hackathon/FinitePrimeEscape.lean\NDkMath/Hackathon/CosmicCompletion.lean\NDkMath/Hackathon/Demo.lean
+Dialogue: 0,0:00:30.00,0:00:48.00,Title,,0,0,0,,2 · Contract before implementation
+Dialogue: 0,0:00:30.00,0:00:48.00,Body,,0,0,0,,The mathematical target was fixed first:\Na finite set S, product P, coprime offset u, and boundary P + u.
+Dialogue: 0,0:00:30.00,0:00:48.00,Code,,0,0,0,,FreshPrimeFactor S n q :=\N  Nat.Prime q ∧ q ∣ n ∧ q ∉ S
+Dialogue: 0,0:00:48.00,0:01:08.00,Title,,0,0,0,,3 · Codex audits the repository
+Dialogue: 0,0:00:48.00,0:01:08.00,Body,,0,0,0,,Existing APIs and reports were inspected.\NThe smallest missing bridge became one explicit theorem.
+Dialogue: 0,0:00:48.00,0:01:08.00,Code,,0,0,0,,prime_dvd_product_add_coprime_not_mem\N\NNat.Prime q  and  q ∣ P + u\NNat.Coprime P u   ⇒   q ∉ S
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
+Dialogue: 0,0:02:43.00,0:02:54.00,Footer,,0,0,0,,Submission package · silent captioned master
+
````
`````

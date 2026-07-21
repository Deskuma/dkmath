# VIDEO-001 — Breaking Math Verification Three-Minute Demo

## Mission

Produce a complete first-pass English demo video for the separate Devpost project:

```text
Breaking Math Verification
From a breaking mathematical claim to an auditable Lean certificate
```

This is a time-critical production task. Reuse the proven Manim, Kokoro TTS, subtitle, FFmpeg, and validation workflow already present under:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715
```

Do not modify or overwrite the accepted Cosmic Formula video project. Inspect and reuse its local environment, tools, models, conventions, and build ideas from the new Jacobian video directory.

The goal is a complete renderable video package first, not a prolonged design study.

## Repository and Branch

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
hackathon/breaking-math-jacobian-counterexample
```

Work inside a new directory:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/video/
```

Do not create or switch branches. Do not merge or open a pull request.

## Critical Submission Boundary

This is a separate Developer Tools submission, not a continuation of the Cosmic Formula / GN5 / FLT5 submission.

The public video must not make GN5, FLT5, Cosmic Formula, finite-prime escape, or DkMath number theory part of its narrative.

The video subject is:

```text
A reusable verification workflow for independently reconstructing
newly reported mathematical claims as explicit Lean certificates.
```

The Jacobian candidate is the sole public case study.

Do not claim that DkMath discovered the reported formulas. Do not claim that the broader mathematical community has accepted the counterexample. Distinguish these layers:

```text
externally reported candidate formulas
independent DkMath transcription and reconstruction
Lean verification of the exact formalized formulas
broader mathematical review still continuing
```

## First Action — Inspect the Existing Local Production Factory

The repository does not contain every generated or large raw asset. Inspect the actual local working tree before implementing.

At minimum inspect:

```text
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/visual/
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/tts/
lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/submission/
```

Inspect tracked, ignored, and untracked files as necessary. Locate and verify:

```text
venv/bin/manim or the working Manim command
venv/bin/kokoro-tts
Kokoro ONNX model and voice files
ffmpeg
ffprobe
libass support
DejaVu fonts or the fonts used by the accepted video
existing generated Manim media
existing TTS outputs and timing reports
```

Useful accepted references include:

```text
visual/manim.cfg
visual/cosmic_formula_scene.py
tts/build_final_narration.sh
tts/cues.tsv
tts/README.md
tts/FINAL_NARRATION_REPORT.md
submission/timeline.ass
submission/build_submission.sh
submission/build_narrated_promo.sh
```

Use the previous large model files by reference. Do not duplicate or commit model binaries.

Record the discovered executable paths, versions, and reusable assets in the VIDEO-001 report.

## Mathematical Source of Truth

Read the current Lean and documentation before writing screen text or narration:

```text
DkMath/Hackathon/JacobianCounterexample3.lean
DkMath/Hackathon/JacobianCounterexample3/Demo.lean
DkMath/Hackathon/JacobianCounterexample3/Normalized.lean
DkMath/Hackathon/JacobianCounterexample3/VerificationBridge.lean
DkMathTest/Hackathon/JacobianCounterexample3/CheckAxioms.lean
docs/hackathon/jacobian-counterexample-verification-260721/README.md
docs/verification/README.md
```

Every displayed theorem identifier and mathematical statement must match the current branch exactly.

The verified presentation facts include:

```text
F = (P, Q, R)
P = (1 + xy)^3 z + y^2 (1 + xy) (4 + 3xy)
Q = y + 3x (1 + xy)^2 z + 3xy^2 (4 + 3xy)
R = 2x - 3x^2 y - x^3 z

formal determinant of the original map = -2
normalized map F_tilde = (-P/2, Q, R)
formal determinant of the normalized map = 1

three pairwise-distinct explicit points
map to the same target (1/8, 0, 0)
therefore the normalized map is not injective
and has no left inverse
```

Use the exact point definitions from Lean when displaying coordinates. If the coordinate expressions are too large for a readable 720p frame, label them `p0`, `p1`, and `p2`, then show their exact Lean identifiers and the common target instead of shrinking unreadable formulas.

## Video Format

Required final format:

```text
English narration
English burned-in subtitles
strictly less than 180 seconds
preferred final duration: 168–176 seconds
1280 × 720
30 fps
H.264 video
AAC audio
public-video-safe material only
no copyrighted music
```

Use the existing dark visual language where useful, but create an independent title and visual identity. A dark navy background with cyan, violet, white, and one warning/accent color is acceptable.

## Audio-First Timing Rule

Do not begin by forcing narration into an arbitrary fixed timeline.

Use this sequence:

1. Draft the English narration as cue files.
2. Generate every cue at native Kokoro speed.
3. Measure every raw cue with `ffprobe`.
4. Add modest visual breathing room, normally 0.4–1.2 seconds per cue.
5. Compute the complete visual timeline from the measured narration.
6. If the projected total is over 176 seconds, shorten the script before using substantial speed-up.
7. Use `atempo` only for small final corrections, preferably no more than approximately 1.08. Record any exception.
8. Generate the final cue schedule, subtitles, Manim timing data, and video from that accepted measured timeline.

The final build must remain strictly below 180 seconds.

Use the proven Kokoro voice unless local testing reveals a concrete problem:

```text
voice: af_sarah
language: en-us
```

Reuse the accepted normalization target:

```text
loudnorm=I=-16:TP=-1.5:LRA=11
48 kHz mono WAV master
AAC 192 kbps final audio
```

## Starting Narrative

Use the following as a starting script, not as immutable prose. Adjust wording for natural TTS pronunciation, accurate timing, and screen synchronization while preserving the meaning and scope.

### Cue 1 — Cold Open

```text
Yesterday, a concrete candidate counterexample to the Jacobian Conjecture was reported.
But a reported formula is not yet a verified theorem.
```

Screen:

```text
Yesterday:
A candidate counterexample was reported.

Reported is not yet verified.
```

### Cue 2 — The Product Problem

```text
Mathematical claims can spread faster than they can be checked.
Breaking Math Verification turns an external report into exact objects, explicit witnesses, kernel-checked Lean theorems, and a visible trust boundary.
```

Screen flow:

```text
reported claim
    ↓
independent reconstruction
    ↓
explicit witness
    ↓
Lean certificate
    ↓
axiom audit
```

### Cue 3 — Exact Polynomial Map

```text
I independently transcribed the reported three-dimensional polynomial map into Lean.
Its three coordinates are P, Q, and R.
The source formulas remain visible and traceable throughout the verification package.
```

Show `F = (P,Q,R)` and reveal the three formulas one at a time. Keep each formula readable.

### Cue 4 — Formal Jacobian and Normalization

```text
Lean differentiates the multivariable polynomials symbolically and proves that the original formal Jacobian determinant is the constant minus two.
After multiplying the first output coordinate by minus one half, Lean proves that the normalized determinant is exactly one.
```

Visual transformation:

```text
det J(F) = -2
        ↓  normalize first output
F_tilde = (-P/2, Q, R)
        ↓
det J(F_tilde) = 1
```

### Cue 5 — The Central Collision

```text
The decisive global witness is finite and visual.
Lean proves that three pairwise-distinct input points all map to the same normalized target, one eighth, zero, zero.
```

This is the main visual scene. Animate three distinct nodes `p0`, `p1`, `p2` converging through three arrows into one target node:

```text
(1/8, 0, 0)
```

Then display:

```text
p0 ≠ p1
p0 ≠ p2
p1 ≠ p2

F_tilde(p0) = F_tilde(p1) = F_tilde(p2)
```

### Cue 6 — Global Consequence

```text
A map with two distinct inputs and one common output is not injective.
The reusable collision certificate therefore derives non-injectivity and proves that no left inverse can exist.
```

Display exact current theorem names, including the public generic API and the Jacobian adapter. Prefer a code-card presentation with no tiny text.

### Cue 7 — Show the Lean Surface

```text
These are compiled Lean declarations, not screenshots of expected answers.
The focused audit also records the exact foundational axioms used by the public Jacobian certificate.
The generic collision-to-non-injectivity theorem itself depends on no axioms.
```

Show a concise terminal or code-card sequence based on actual output:

```text
#check normalizedJacobianCounterexampleCertificateC
#check normalized_three_point_collision_C
#check normalizedCollisionCertificateC_notInjective
#print axioms ...
```

Do not fabricate terminal output. Generate or copy it from the current build and audit files.

### Cue 8 — GPT-5.6 and Codex Workflow

```text
GPT-5.6 helped analyze the mathematics, design theorem boundaries, and review each checkpoint.
Codex inspected the repository, implemented the Lean modules, ran focused builds, and committed structured reports.
The Git repository became the handoff channel between the two AI workflows.
```

Visual flow:

```text
GPT-5.6
analysis · theorem design · review
        ↓
Git repository
        ↓
Codex
implementation · build · report
        ↓
Lean kernel
```

Briefly show:

```text
BMV-001  architecture
BMV-002  collision certificate
BMV-003  Jacobian adapter
BMV-004  verification contracts
BMV-005  cross-domain engineering validation
BMV-006  public API
```

Do not mention GN5 in the narration or visible list. For BMV-005, the generic label above is sufficient.

### Cue 9 — Honest Scope

```text
The reported candidate is still new, and broader mathematical review will continue.
This project does not replace that process.
It provides a fast, reproducible first verification layer for the exact formulas being discussed.
```

Screen:

```text
Lean verifies the exact formalized formulas.

It does not certify:
historical priority
publication status
peer review
community acceptance
```

### Cue 10 — Closing

```text
Do not trust the headline.
Verify the certificate.
```

End card:

```text
Breaking Math Verification
GPT-5.6 × Codex × Lean 4

From a breaking claim
to an auditable certificate
```

## Visual Direction

The video may be a polished Manim slideshow with one central animated diagram. Do not spend time building unnecessary 3D geometry.

Prioritize these visual moments:

1. The reported-claim-to-certificate pipeline.
2. `det J(F) = -2` transforming to `det J(F_tilde) = 1`.
3. Three distinct input nodes converging to one target node.
4. Real theorem names and audit output.
5. GPT-5.6 → Git → Codex → Lean handoff.

Use mostly:

```text
Text
MathTex when reliable
VGroup
Arrow or CurvedArrow
FadeIn / FadeOut
Write
Transform / ReplacementTransform
Indicate or Circumscribe
```

Do not create text so small that it is technically present but unreadable at 720p. Extract representative frames and inspect them.

If complex LaTeX becomes a render risk, use Unicode-safe `Text` or split formulas across multiple frames rather than delaying the first complete render.

## Recommended Package

Create a minimal reproducible structure similar to:

```text
video/
├── README.md
├── visual/
│   ├── manim.cfg
│   ├── breaking_math_verification_scene.py
│   └── timeline.json          # or another generated timing source
├── tts/
│   ├── narration-en.txt
│   ├── cues.tsv
│   ├── cues/
│   │   ├── 01.txt
│   │   └── ...
│   ├── narration-en.srt
│   ├── build_narration.sh
│   └── output/                # ignored raw/timed WAV files
├── submission/
│   ├── build_submission.sh
│   ├── build_narrated_video.sh
│   ├── timeline.ass           # only if used
│   └── output/
└── VIDEO_REPORT.md
```

Adjust the exact layout when the existing local factory makes a smaller arrangement more reliable.

The end-to-end command should be one obvious script, for example:

```bash
bash lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/video/submission/build_narrated_video.sh
```

That command should regenerate narration, render Manim, burn subtitles, mux audio, and produce the final MP4, or clearly invoke the required substeps in order.

## Source and Artifact Policy

Commit:

```text
all scripts
Manim source
timing sources
English narration
subtitle source
README and reproduction instructions
VIDEO_REPORT.md
small final MP4 if repository policy and GitHub size limits permit
```

Do not commit:

```text
Kokoro model binaries
voice binaries
raw WAV cue files
timed WAV cue files
Manim partial movie cache
large temporary frame dumps
unnecessary duplicate assets
```

Reference the accepted old TTS models from their existing local path.

## Validation

Complete a real first render and validate:

```text
final duration < 180 seconds
1280 × 720
30 fps
H.264
AAC audio
subtitle readability
no clipped formulas or labels
no silent missing cue
no cue overlap
no visible GN5 / FLT5 / Cosmic Formula narrative
all theorem names exact
all public mathematical claims supported by current Lean declarations
```

Use `ffprobe` for media metadata.

Extract and inspect at least these representative frames:

```text
cold open
polynomial formula scene
normalized determinant = 1
three-point collision
Lean theorem / audit card
GPT-5.6–Codex workflow
scope boundary
closing card
```

Record the frame timestamps and inspection result.

If the first complete render has a small readability or synchronization defect, fix it and rebuild once. Do not begin a long aesthetic redesign.

## Build and Claim Audit

The supplied Lean checkpoint is already build-passed. Do not spend the video budget re-proving the project.

Use the current theorem surface and existing reports as source material. Run only focused commands necessary to obtain truthful terminal/audit text for the video and to confirm identifiers.

No new Jacobian mathematics is requested.

## Repository Handoff Protocol

At completion, create:

```text
lean/dk_math/docs/hackathon/jacobian-counterexample-verification-260721/report-jacobian-VIDEO-001.md
```

The report must include:

```text
final commit SHA
changed files
discovered local production environment
final narration duration and cue timing
any atempo factors
final MP4 path
ffprobe metadata
final file size and SHA-256
representative-frame timestamps
render and mux commands
scope/claim audit
known remaining human actions
Outcome A, B, or C
```

Commit and push the complete first-pass package and report.

In the chat response, return only:

```text
commit SHA
final MP4 path
final duration
report path
Outcome
```

Do not paste the long report into chat.

## Outcomes

### Outcome A

A complete, accurate, narrated, subtitle-burned, under-three-minute MP4 and reproducible source package are built and pushed.

### Outcome B

The complete source and build pipeline are pushed, but one external local dependency or final render issue remains. Record the exact blocker and the shortest human command to finish.

### Outcome C

The previous production environment cannot be reused. Preserve the narration, storyboard, and minimal fallback scripts, document the concrete missing dependency, and stop without fabricating a successful video.

## Stopping Rule

Stop after one accurate complete video and, at most, one focused correction pass.

Do not redesign the Jacobian project, add new mathematical claims, modify the first Devpost submission, create a new Devpost project, upload to YouTube, merge, or open a pull request.

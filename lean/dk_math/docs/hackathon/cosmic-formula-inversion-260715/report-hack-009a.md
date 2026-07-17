# Checkpoint hack-009a — Three-Minute Promo Integration Draft

## Status

Complete. A coherent 2-minute-54-second integration draft was built from actual
Lean evidence, accepted checkpoint reports, and the accepted Manim prototype.
The accepted Lean and Manim source modules were not changed.

## Editorial structure chosen

The draft uses a proof-backed research-loop structure:

```text
project context
→ contract before code
→ Codex repository audit
→ general Lean bridge
→ fixed verified example
→ full-screen Manim explanation
→ proof/visual distinction
→ bounded inverse projection as future work
```

Timed evidence cards carry the parts for which no screen recording exists. They
show real paths, declaration names, theorem statements, and accepted values
rather than simulated editor or terminal footage.

## Assets used

Formal evidence:

- `DkMath/Hackathon/FinitePrimeEscape.lean`
- `DkMath/Hackathon/CosmicCompletion.lean`
- `DkMath/Hackathon/Demo.lean`

Process evidence:

- `report-hack-001.md`
- `report-hack-002.md`
- `report-hack-003.md`
- `report-hack-004.md`
- `report-hack-008a.md`

Moving image:

- `visual/media/videos/cosmic_formula_scene/720p30/`
  `CosmicFormulaPrototype.mp4`

`promo/asset-inventory.md` records the complete used/missing inventory, and
`promo/edit-outline.md` records the timed ten-part edit.

## Role of the Manim prototype

The accepted 15.9-second prototype is inserted at 01:48, scaled to the complete
1280x720 frame. It is not reduced to picture-in-picture, so its equations and
labels retain their accepted readability. It supplies the visual transition
from the finite set through Body + Gap and boundary 221 to fresh factors 13 and
17. The following card explicitly restores the evidentiary hierarchy: Lean is
the source of verification; Manim communicates the result.

## Codex and Lean evidence shown

The Codex section states the repository-audit outcome and shows the smallest
missing bridge by its real declaration name:
`prime_dvd_product_add_coprime_not_mem`.

The Lean sections show short versions of the accepted theorem surfaces:

- `FreshPrimeFactor`
- `exists_fresh_prime_factor`
- `cosmicCompletion`
- `demo_thirteen_fresh`
- `demo_seventeen_fresh`
- `demo_cosmic_completion`

The draft does not present an invented Codex session recording or a fabricated
Lean terminal. Its evidence cards are traceable to the accepted repository
files.

## Narration structure

`promo/narration.srt` contains a complete ten-cue narration/subtitle script
timed to the edit. It explains DkMath, contract-first design, Codex's audit, the
two general Lean results, the fixed example, the Manim boundary, freshness, and
bounded inverse projection. The output draft is intentionally silent, so this
script is a sidecar production plan rather than an embedded subtitle stream.

The video itself uses burned-in editorial text and code evidence on every card.
The Manim interval uses its own burned-in labels.

## Missing footage

No Codex interaction recording, Lean editor/terminal recording, recorded voice,
music, or inverse-projection animation was available. The strongest honest draft
therefore uses evidence cards for the first two and leaves the future projection
as a carefully limited direction. No Collatz footage was used, so no Collatz
claim or convergence disclaimer is needed in the cut.

## Build command and tools

Exact command, run from `promo/`:

```bash
bash build_draft.sh
```

The script's integration renderer is:

- FFmpeg `6.1.1-3ubuntu5`
- libass `0.17.1`
- libx264, H.264 High profile
- DejaVu Sans and DejaVu Sans Mono through Fontconfig

The accepted embedded visual was previously rendered with Manim Community
`0.20.1`. This integration build does not invoke Manim or Python.

## Technical output metadata

- Output: `promo/output/DkMathCosmicPromoDraft01.mp4`
- Render result: success, exit status 0
- Duration: 174.000 seconds (02:54)
- Resolution: 1280x720
- Frame rate: 30 fps
- Video: H.264, `yuv420p`
- File size: 1,650,079 bytes
- Audio status: silent; no audio stream
- Subtitle status: timed narration sidecar in `promo/narration.srt`; editorial
  evidence and labels are burned into the video; no embedded subtitle stream

A nine-frame contact sheet sampled every 20 seconds was inspected. It confirmed
the chapter cards, real theorem identifiers, full-screen Manim insertion, future
direction limitation, and final workflow card.

## Resource meters

The local Codex workspace exposes no API or file containing the two UI resource
meters. They cannot be inferred from token usage, and weekly percentage was not
converted into credits.

```text
Weekly allowance before: not observable in the local execution environment
Weekly allowance after: not observable in the local execution environment

Additional credits before: not observable in the local execution environment
Additional credits after: not observable in the local execution environment
```

## Resolved environmental issues

The project-level `/home/deskuma/develop/lean/dkmath/venv` exists and uses Python
3.12.3, but does not currently contain Manim. No new Manim render was needed:
the checkpoint explicitly accepts the existing MP4, and FFmpeg can integrate it
directly. This avoided modifying either the project environment or the accepted
visual source.

The prior prototype's temporary Manim environment is therefore not a dependency
of `promo/build_draft.sh`; only FFmpeg plus the retained accepted MP4 are needed.

## First genuine obstruction

The first genuine integration obstruction was the absence of human/Codex and
Lean-session recordings, followed by the absence of recorded narration. It did
not prevent a coherent evidence-based review draft, but it prevents this cut
from honestly showing the live collaboration and from functioning as a finished
audio-led promo.

## Recommended next integration step

Review timing and wording first. Then record one concise human/Codex repository
sequence, one Lean build/editor sequence, and the narration against
`promo/narration.srt`. Replace the corresponding static evidence cards while
retaining the full-screen accepted Manim interval. Only after that editorial
pass should music, sound design, and final submission packaging begin.

## Repository verification

- `bash -n promo/build_draft.sh`: passed.
- Trailing-whitespace scan over `promo/` and this report: passed.
- `git diff --check`: passed with no output.
- `git status --short --untracked-files=all`: reported only the nine new
  checkpoint deliverables under `promo/` and `report-hack-009a.md`.
- The final source/report set and output metadata were inspected; no accepted
  Lean or Manim source file was modified.

## Stop confirmation

Stopped after the first coherent integrated draft. No projection or DkReal
implementation, public long-form production, or final submission packaging was
started.

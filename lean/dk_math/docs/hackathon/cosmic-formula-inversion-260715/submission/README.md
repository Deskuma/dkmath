# DkMath — Verifiable Research in Motion

## Short description

DkMath demonstrates a contract-first, AI-assisted mathematical research loop:
human direction fixes a precise target, Codex audits and extends the repository,
Lean verifies the result, and Manim explains the verified example visually.

## Mathematical result demonstrated

For a finite set `S`, let `P` be the product of its members. If `P` and an
offset `u` are coprime, then any prime `q` dividing `P + u` cannot be in `S`.
The demo uses

```text
S = {2, 3, 5, 7},  P = 210,  u = 11,
P + u = 221 = 13 × 17,
```

so both `13` and `17` are fresh relative to `S`. The accompanying algebraic
identity completes the Cosmic square:

```text
P(P + 2u) + u² = (P + u)².
```

## AI-assisted workflow

The mathematical contract was written before implementation. Codex inspected
the existing repository and its reports, identified the smallest missing bridge,
implemented the general theorems and fixed demo, and kept the reports aligned
with verification and visualization artifacts.

## Lean verification evidence

The accepted declarations are:

- `DkMath.Hackathon.prime_dvd_product_add_coprime_not_mem`
- `DkMath.Hackathon.exists_fresh_prime_factor`
- `DkMath.Hackathon.cosmicCompletion`
- `DkMath.Hackathon.demo_thirteen_fresh`
- `DkMath.Hackathon.demo_seventeen_fresh`
- `DkMath.Hackathon.demo_cosmic_completion`

They are defined in `DkMath/Hackathon/FinitePrimeEscape.lean`,
`DkMath/Hackathon/CosmicCompletion.lean`, and `DkMath/Hackathon/Demo.lean`.

## Visual explanation

The 2:54 promo presents the contract and proof evidence as readable cards. At
01:48, the accepted Manim animation remains full-screen and shows the transition
from the finite prime set through Body plus the square Gap to the completed
boundary `P + u = 221`, its factorization, and freshness.

## Limitations and future direction

This silent master contains burned-in editorial text and a timed narration
sidecar, but no recorded human narration, collaboration footage, or terminal
capture. It makes no Collatz convergence claim and no inverse-projection theorem
claim. Bounded inverse projection is identified only as the next research
direction.

## Build and reproduction

Requirements:

- Bash
- FFmpeg with libass and libx264
- DejaVu Sans and DejaVu Sans Mono
- the accepted Manim MP4 at its repository path

From this directory, run:

```bash
bash build_submission.sh
```

Expected silent visual master:

```text
output/DkMathCosmicPromoFinal.mp4
```

The build renders a 174-second, 1280x720, 30 fps H.264 silent MP4. `timeline.ass`
is the burned-in editorial timeline; `narration.srt` is the final timed narration
and caption-authoring source.

## Narrated master

After the Kokoro environment has been set up, build the synchronized narrated
master from this directory:

```bash
bash build_narrated_promo.sh
```

This regenerates the visual master, synthesizes the 11 cue narration, normalizes
it, and muxes it as AAC audio. Output:

```text
output/DkMathCosmicPromoFinalNarrated.mp4
```

The selected voice, cue adjustment, verification metadata, and TTS provenance
are documented in `../tts/FINAL_NARRATION_REPORT.md`.

## Package contents

- `output/DkMathCosmicPromoFinal.mp4` — final silent captioned promo master
- `output/DkMathCosmicPromoFinalNarrated.mp4` — final narrated promo master
- `narration.srt` — final timed narration/subtitle file
- `timeline.ass` — final burned-in editorial timeline
- `build_submission.sh` — reproducible final build
- `build_narrated_promo.sh` — reproducible narration and mux build
- `ASSET_INVENTORY.md` — provenance and package inventory
- `README.md` — submission description and reproduction guide

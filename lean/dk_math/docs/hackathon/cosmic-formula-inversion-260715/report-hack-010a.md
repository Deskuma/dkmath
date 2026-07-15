# Checkpoint hack-010a — Submission-Ready Promo Package

## Status

Complete. The accepted edit was accuracy-corrected, rebuilt as a final 2:54
silent promo master, and packaged with final captions, source timeline,
reproduction script, submission copy, and asset provenance.

## Files changed

Created under `submission/`:

- `README.md`
- `ASSET_INVENTORY.md`
- `narration.srt`
- `timeline.ass`
- `build_submission.sh`
- `.gitignore`
- `output/DkMathCosmicPromoFinal.mp4`

Also created `report-hack-010a.md`. Accepted Lean modules, Manim sources, and
the accepted integration-draft sources were not modified.

## Accuracy corrections

The finite-escape card now visibly states all material hypotheses:

```text
Nat.Prime q  and  q ∣ P + u
Nat.Coprime P u   ⇒   q ∉ S
```

A frame extracted at 00:55 was inspected at 1280x720 and confirmed that the
primality hypothesis, divisibility hypothesis, coprimality hypothesis, and
conclusion are all readable.

The final narration changes:

- `the existing repository and reports` to
  `the existing repository and its reports`;
- `Body plus square Gap completes the boundary P plus u` to
  `Body plus the square Gap completes a square whose boundary is P plus u`.

All displayed Lean declaration names were compared with the accepted modules.
The names in the package match exactly.

## Final editorial decisions

The reviewed ten-part structure, 174-second duration, and evidence-card pacing
were preserved. The accepted Manim segment remains at 01:48 and occupies the
complete 1280x720 frame. A frame at 01:52 confirmed that no picture-in-picture
scaling or integration overlay reduces its readable area.

The accepted draft remains as a review artifact under `promo/`. The corrected
master is independently packaged under `submission/`, avoiding ambiguity
between draft and final deliverables.

The output remains a silent captioned master. Editorial evidence is burned in;
the final timed narration is supplied as an SRT sidecar for human recording and
caption authoring.

## Final video metadata

- Path: `submission/output/DkMathCosmicPromoFinal.mp4`
- Build result: success, exit status 0
- Duration: 174.000 seconds (02:54)
- Resolution: 1280x720
- Frame rate: 30 fps
- Codec: H.264, High profile, `yuv420p`
- File size: 1,652,906 bytes
- Audio: no audio stream
- Embedded subtitle stream: none
- Caption status: burned-in editorial text plus final `submission/narration.srt`
  sidecar

## Submission text produced

`submission/README.md` is the concise submission document. It contains:

- project title and short description;
- demonstrated finite prime escape and Cosmic completion results;
- human/Codex/Lean/Manim workflow;
- exact Lean verification declarations and source modules;
- role and timing of the visual explanation;
- limitations and bounded inverse projection as future direction;
- requirements, exact build command, and expected output;
- package contents.

`submission/ASSET_INVENTORY.md` separately records final artifacts, verified
evidence provenance, embedded Manim provenance, accuracy constraints, and
remaining external assets.

## Reproducibility result

Exact documented command, run from `submission/`:

```bash
bash build_submission.sh
```

The command rebuilt the final MP4 successfully using FFmpeg `6.1.1-3ubuntu5`,
libass `0.17.1`, libx264, Fontconfig, DejaVu fonts, and the accepted Manim MP4.
The script does not require Python or the project venv.

The narration has ten contiguous cues spanning 00:00:00 through 00:02:54, so its
timing remains aligned with the unchanged edit duration.

## Claim audit

- The prime hypothesis is visible in the corrected theorem card.
- Manim remains full-screen and readable.
- Declaration names match the accepted Lean files.
- Bounded inverse projection is explicitly future research, not a theorem.
- No Collatz result or convergence claim appears.
- No invented collaboration recording, terminal output, or theorem result was
  added.

## Resource meters

Weekly allowance and additional credits were not observable from the local
execution environment. Neither value was inferred or converted from another
meter.

## Remaining external tasks

- Record the human narration using `submission/narration.srt`.
- Optionally replace selected evidence cards with authentic collaboration and
  Lean editor footage.
- Add licensed music or sound design if desired.
- Supply hackathon-platform metadata and upload the reviewed master.

These are external production or publication tasks; none prevents the current
silent master from being a reproducible submission package.

## First genuine obstruction

The first remaining obstruction to an audio-finished public promo is the absence
of recorded human narration. It did not obstruct this checkpoint because the
accepted format is preserved as a silent captioned master with a complete timed
narration sidecar.

## Verification

- Video metadata was measured with `ffprobe`.
- Corrected and Manim frames were extracted with FFmpeg and inspected.
- The six referenced declaration names were checked against the Lean sources.
- Projection and Collatz wording was scanned across `submission/`.
- `bash -n submission/build_submission.sh`: passed.
- Trailing-whitespace scan over the package and report: passed.
- `git diff --check`: passed with no output.
- `git status --short --untracked-files=all`: reported only this report and the
  seven new submission-package artifacts.

## Stop confirmation

Stopped with the corrected promo and submission-ready package complete. No new
projection, DkReal, Collatz, or long-form video implementation was started.

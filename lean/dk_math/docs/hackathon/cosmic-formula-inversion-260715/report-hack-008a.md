# Checkpoint hack-008a — Manim Visual Prototype

## Status

Complete. The first coherent Manim prototype was implemented and rendered.
The accepted Lean modules were not changed.

## Files created or changed

- `visual/demo_data.py`
- `visual/cosmic_formula_scene.py`
- `visual/manim.cfg`
- `visual/README.md`
- `visual/.gitignore`
- `visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4`
- `report-hack-008a.md`

## Visual architecture chosen

The prototype is one continuous `Scene`, rather than a collection of separately
rendered clips. Persistent title treatment and a small color vocabulary connect
three visual phases:

1. known primes, their product, and the coprime offset;
2. schematic square completion with separately colored Body and Gap;
3. factorization, freshness, and a compact Lean-anchor panel.

This gives the first prototype a single readable argument while keeping each
phase independently refactorable into a later scene or shot.

## Source-directory decision

Repository inspection found the storyboard but no existing Manim source tree,
configuration, or naming convention. The checkpoint's requested `visual/`
directory was therefore used. Source, local render configuration, instructions,
and the retained MP4 live together there; transient Manim text and partial-movie
caches are ignored.

## Scene sequence

The rendered sequence is:

```text
S = {2, 3, 5, 7}
→ P = 2 × 3 × 5 × 7 = 210
→ u = 11 and gcd(210, 11) = 1
→ Body = P(P + 2u) = 48720 and Gap = u² = 121
→ P(P + 2u) + u² = (P + u)²
→ completed boundary P + u = 221
→ 221 = 13 × 17
→ 13, 17 ∉ S
→ accepted Lean theorem names
```

## Shared-data design

`visual/demo_data.py` defines one frozen `CosmicDemoData` value. Only the prime
tuple, offset, and fresh-factor tuple are primitive data. Product, boundary,
Body, Gap, and completed-square value are computed properties. Module assertions
pin the computed results to the accepted `Demo.lean` values, preventing scenes
from silently diverging through duplicated literals.

## Render command and result

Command, run from `visual/`:

```bash
manim render -qm cosmic_formula_scene.py CosmicFormulaPrototype
```

- Manim Community: `0.20.1`
- Python: `3.12.3`
- Environment: temporary virtual environment
  `/tmp/dkmath-manim-system-venv`, created with system site packages
- Result: success; `Rendered CosmicFormulaPrototype`, 19 animations
- Video codec: H.264
- Duration: 15.900 seconds
- Resolution: 1280 × 720
- Frame rate: 30 fps
- File size: 678,561 bytes

Because the host lacked Manim and development metadata for its native Pango/Cairo
dependency, Manim was installed only in the temporary environment. Debian
development packages were downloaded and extracted under `/tmp`; the host system
package set was not modified. Rendering emitted non-fatal GLib critical warnings
from that temporary library arrangement, but exited successfully and produced a
valid video whose metadata and representative frames were inspected.

## Output artifact

```text
visual/media/videos/cosmic_formula_scene/720p30/CosmicFormulaPrototype.mp4
```

The artifact is a 15.9-second 720p render. The source README records the portable
render invocation.

## Repository checks

- `git diff --check`: passed with no output.
- `git status --short --untracked-files=all`: reported only the seven new
  checkpoint files listed above; no accepted Lean module was modified.

## Differences from the storyboard

- The storyboard's nine conceptual scenes are condensed into one continuous
  15.9-second prototype.
- Geometry is intentionally schematic: the Body is an L-shaped region and the
  Gap is its missing corner; lengths are not scaled as 210 and 11.
- The Lean panel shows accepted declaration names rather than source excerpts.
- There is no narration, audio, camera motion, or editorial pause structure.
- The more detailed final comparison layout is reduced to the original set,
  two highlighted factor tokens, and the freshness implication.

## Visual limitations

- Text pacing is suitable for prototype review, not yet for narrated viewing.
- The square-completion diagram does not label individual side segments `P` and
  `u`; it communicates the identity through color and adjacent equations.
- The theorem implication is presented as supporting text and is not animated
  term by term.
- Font selection uses Manim defaults, so typography is not yet submission-grade.
- The temporary render environment should be replaced by a reproducible project
  environment before production rendering.

## Recommended next visual step

After review, split the continuous prototype into storyboard-aligned shots and
refine the square-completion phase first: add explicit `P`/`u` side braces,
increase reading holds, and synchronize equation terms with their regions. That
is the highest-value visual refinement before narration or final editing.

## First genuine obstruction

The first genuine obstruction was the absence of an installed Manim executable
and native build metadata for Pango/Cairo. System package installation was not
available without administrative credentials. A non-system workaround using a
temporary virtual environment and development files extracted under `/tmp`
unblocked the checkpoint without changing the host package set.

## Stop confirmation

Stopped after the first coherent rendered prototype. No narration, final edit,
projection, DkReal work, or submission packaging was started.

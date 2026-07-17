# Cosmic Formula Manim Prototype

The scene keeps all verified numerical values in `demo_data.py` and presents
one continuous schematic transition in `cosmic_formula_scene.py`.

From this directory, render the prototype with Manim Community:

```bash
manim render -qm cosmic_formula_scene.py CosmicFormulaPrototype
```

The configured output is 1280×720 at 30 fps under `media/videos/`.

The geometry is intentionally schematic. Exact arithmetic is displayed in the
labels and anchored by `DkMath.Hackathon.Demo`; screen lengths are not drawn to
the numerical scale of 210, 221, or 232.

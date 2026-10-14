# Gate 001 — compact validation evidence

Origin: `report-001.md` from implementer (Codex Sol);
repository reviewed at commit `fcc57eb884d5fbcdff0c43289b0083eee1f70969`.
This is a compact transcript **reported by the implementer**, not an
independent rerun by the reviewer.

## Source artifact

- Production: `DkMath/FLT/Seven/SevenRamifiedFusionModSixResidues.lean`
- Tests: `DkMathTest/FLT/Seven/SevenRamifiedFusionModSixResidues.lean`
- Exported statements:
  - `Nat.Coprime x y → Nat.ModEq 6 (alternatingCyclotomicSeven x y) 1`
  - `Nat.Coprime D u → Nat.ModEq 6 (GN 7 D u) 1`

## Checked results reported

- Focused Lake build: exit 0.
- Focused Lean test module: exit 0.
- Source code examples include valid primitive cases and explicit
  non-coprime / non-converse counterexamples.
- No changes to the existing allocation receiver definitions.
- No `sorryAx` reported.

```text
'DkMath.FLT.Seven.alternatingCyclotomicSeven_mod_six_of_coprime'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.FLT.Seven.GN_seven_mod_six_of_coprime'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

The full stdout/stderr logs were temporary and are intentionally not
tracked. For replay use the documented repository toolchain and run
the focused build/test plus `#print axioms` on these declarations.

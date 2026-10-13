# Gate 008 verification summary

Provenance: **Codex-reported**, locally executed 2026-10-13; not independently reproduced.
Environment: Lean4.34.1 / Lake5.0.0-src+5045d00. Cwd: `lean/dk_math`.

- `lake build DkMath.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage`: exit **0**.
- `lake env lean DkMathTest/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean` (final tables included): exit **0**, no warning/error.

```text
Build completed successfully (9088 jobs).
```

Actual final test / axiom output:

```text
file: DkMathTest.FLT.Seven.SevenRamifiedFusionGeneralGapModFiveImage
'DkMath.FLT.Seven.centeredSevenSextic_generalGap_no_image_mod_five' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMath.FLT.Seven.nestedAllocation_excluded_of_mod_five_square' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'DkMathTest.FLT.Seven.allocationTwo_modFive_regression' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Universal arbitrary-natural reduction proves no-image under exactly 5∤r and s≡r² mod5. The same chosen-r receiver transport reuses the actual centered equivalence.
Named r=2 regression proves cheap and witness13 sixth-power passage, both exact receiver failures, and failure of the earlier size premise36≤13. Finite image/allowed-s tables are checked in Lean. The zero-gap countermodel shows why the unit premise cannot be erased from the generic natural statement; it is not a positive-divisor allocation.
No all-divisor or packet-existence conclusion is asserted.

Checked source SHA-256:

```text
764b7678ae2f6e2b851cd28cd4a4e606729cec89c39f5c014c8f534f4c762374  DkMath/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean
75daec5d0aa8ab1f6efc3e608bb84f5d5712536e13c1e15920ac0c8fdd2e37ea  DkMathTest/FLT/Seven/SevenRamifiedFusionGeneralGapModFiveImage.lean
```

Full API / residue table / boundaries: [report-008.md](../report-008.md).
Supplied Python discovery is context; it is not the kernel evidence. Raw logs remain disposable. No Git mutation.

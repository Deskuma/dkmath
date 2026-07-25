# FLT7 seven-primary terminal route documents

This directory contains the handoff and implementation documents for the remaining FLT7 work on PR #65.

## Documents

- [STATUS.md](STATUS.md) — proved implementation state, packet hierarchy, and explicit open obligations.
- [ROADMAP.md](ROADMAP.md) — staged route from finite CRT synchronization to terminal exclusion, descent closure, and the final FLT7 target.
- [IMPLEMENTATION_DESIGN.md](IMPLEMENTATION_DESIGN.md) — proposed Lean modules, structures, theorem surfaces, checkpoint boundaries, and the first Codex task.

## Current starting point

The implemented source route currently reaches:

```text
terminal prime q
  → exact original routing depth q^e
  → explicit prime-power orbit
  → column-independent local unit scale
  → finite CRT scale and model reconstruction
  → original-coordinate signed winding
  → universal global coordinate equations and integer equation carries
  → exact 3 x 3 cell prime partition
  → reduction to each exact cell modulus
  → fixed endpoint-row/root-column solution for every cell model
  → row-resolved integral carry decision boundary
```

`AwaySevenBaseTerminalCellwiseFixedSystemObligation` is discharged.  The next
exact obligation is integral arithmetic: combine the nine fixed-system
solutions with coordinate windings, equation carries, and row factorization.
Terminal contradiction, construction of `AwayDescentClosureProvider`, and
recursive descent closure remain unproved.

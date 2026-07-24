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
  → pairwise CRT scale gluing
```

Finite scale gluing, exact modulus coverage, model compatibility, signed integral reconstruction, terminal arithmetic exclusion, and recursive descent closure remain separate proof obligations.

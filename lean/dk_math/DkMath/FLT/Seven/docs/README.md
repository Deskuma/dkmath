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
  → exact cell integer carries from common signed representatives
  → proof that every cell first carry is dependent
  → exact reconstruction seed equivalent to the descent provider
  → proof that a terminal-depth seed/provider is impossible
  → terminal Row-Y / Row-Z ramified chart resolution
  → one primitive common ramified summit
  → exact root-snd depth and ramified cubic factor grid
```

`AwaySevenBaseTerminalCellwiseFixedSystemObligation` is discharged, and
`AwaySevenBaseTerminalCellIntegerCarryPacket.firstCarry_eq` proves that the
nine fixed-system first-coordinate carries contain no new independent
constraint. The carry exploration therefore stops here.
`AwayDescentReconstructionSeed` exposes the exact integral data needed for the
next counterexample, and Lean proves that it is equivalent to
`AwayDescentClosureProvider`. DESCENT-001 therefore ends with Outcome C: the
provider construction interface and strict-drop bridge are complete, while
inhabiting the seed remains open in general. DESCENT-002 gives Outcome D at
terminal depth: a seed or provider would force pivot exponent at least two, so
neither can inhabit the exponent-one branch. TERM-009/010 then exclude Row Sum
and normalize Row Y and Row Z into ramified charts. RAMIFIED-001 unifies those
charts and proves the exact root-snd depth
`5 + 7 * padicValNat 7 gapRoot`, together with the new ramified
linear-cubic-cubic factor grid. This does not yet construct a smaller Fermat
solution. Lifted-branch provider construction, terminal contradiction, and
recursive descent closure remain unproved.

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
  → formal ramified 3 x 3 coprime routing
  → endpoint/root-cubic gap-depth synchronization
  → exact integral and ZMod(7^k) gap-unit bridge
  → coherent unit tower and finite mod-49 seventh-power classifier
  → canonical residual-root one-digit branch selector
  → terminal exact depth 5/6/6 and second-coordinate 2 x 3 routing
  → integral ramified compensation-core receiver
  → canonical 2 x 3 split and exact cubic-gap seventh-shape equivalence
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
solution. RAMIFIED-002 proves both triples nonzero and pairwise coprime,
constructs `RamifiedCubicRoutingPacket`, and synchronizes the endpoint and
root-cubic gap depths. Lifted-branch provider construction, terminal
contradiction, and recursive descent closure remain unproved.
RAMIFIED-003 strengthens the depth equality to a division-free integer
identity and an explicit unit equivalence over every `ZMod (7^k)`. It does
not construct a smaller Fermat solution.
RAMIFIED-004 proves reduction coherence and classifies the seventh-power
branch modulo `49` by the six residues `1, 18, 19, 30, 31, 48`. The common
summit does not yet determine which branch occurs.
RAMIFIED-005 proves that the canonical branch is selected exactly by
`residualRoot = 1` in `ZMod 49`; otherwise the residual root is one of the six
nontrivial principal residues. Higher compatible seventh-root lifting remains
a separate obligation.
RAMIFIED-006 restores the terminal carrier forgotten by the common summit,
proves that `gapRoot` is a seven-unit, and fixes the three ramified depths at
`5, 6, 6`. It proves the exact integer equation `v*S = 7^5*A^7*Q`, its
pairwise-coprime factor ledger, and constructs the resulting 2 x 3 routing
board. The compensation core is now the explicit gcd `gcd(|v|,|Q|)`.
RAMIFIED-007 identifies every abstract routing cell with its canonical gcd
under the source-column pairwise-coprimality hypotheses. It then constructs
the canonical split
`A = X*Y`, `V = 7^5*X^7*C`, `S = Y^7*D`, `Q = C*D` and proves

```text
|R-L| = 7^6 * X^7 * (C*B).
```

The former receiver is equivalent both to this exact cubic-gap seventh-power
shape and to independent seventh powers for `C` and `B`. This is Outcome A.
Producing an internal seventh root of `gapRoot` is the separate
RAMIFIED-008 checkpoint; no descent is claimed here.

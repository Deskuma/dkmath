# FLT7 Unconditional TraceOne Closure

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Base: `develop` at `65642ab38e9110609db407913969c86c786ec662`

## Mission

This campaign specializes the completed generic `DkMath.FLT.Prime` architecture
back to exponent `p = 7` and asks a deliberately narrower question:

```text
Can the new quadratic TraceOne route close FLT7 unconditionally,
without reopening the full historical degree-six/descent tower unless needed?
```

The first target is the ramified branch.  The checked starting route is:

```text
primitive FLT7 counterexample
  -> branch on 7 | (z-y)

ramified branch:
  PrimeAdicFactorPacket 7 (z-y) y x
  -> PrimeTraceOneStrippedIdealPacket
  -> residual = delta^7
  -> exact integer coordinates of delta^7 in TraceOneInt (-2)

away branch:
  7 ∤ (z-y)
  -> z-y = a^7
  -> GTail 7 1 (z-y) y = b^7
  -> separate FLT7 frontier
```

The p=7 class-group obstruction is already discharged structurally through the
existing Euclidean/PID `TraceOneInt (-2)` carrier.  Therefore the ramified
branch now reaches an unconditional exact seventh-power residual for every
existing stripped packet.

## Critical representation boundary

Do **not** silently identify the generic p=7 coordinate packet with the older
specialized FLT7 coordinate package.

The new generic route uses:

```text
PrimeTraceOneCoordinatePacket
P.coord (g+u) u
traceOnePowCoords (-2) m n 7
```

while the specialized FLT7 tower already contains:

```text
cyclotomicSevenToTraceOne z y
seventhPowerFst u v
seventhPowerSnd u v
sevenAxis
```

Both live in `TraceOneInt (-2)`, and the seventh-power coordinate polynomials
are expected to agree with the generic recurrence specialization, but the
parent coordinate packet itself is not yet a checked identification.

The campaign must prove any bridge it uses.

## Success criterion

The campaign may claim FLT7 unconditionality only after both branches of the
primitive counterexample route are closed by kernel-checked theorems and a
public final theorem is derived without a new project axiom or proof hole.

A ramified-only contradiction is an important milestone but is not yet FLT7.

## Working rules

- Lean decides theorem validity.
- No `sorry`, `sorryAx`, `admit`, new `axiom`, or `unsafe` proof shortcut.
- Do not use a hypothetical/completed external FLT7 theorem as a black box.
- Do not identify equal norms with equal TraceOne elements.
- Do not identify the generic p=7 coordinate packet with
  `cyclotomicSevenToTraceOne` without a checked bridge.
- Do not treat the away simultaneous seventh-power split as a contradiction by
  itself.
- Prefer small bridge modules and focused audits before importing large legacy
  FLT7 towers.
- Reuse existing specialized p=7 arithmetic when the dependency is honest and
  does not smuggle in a terminal contradiction.

## Checkpoint workflow

Each checkpoint has:

```text
instruction-NNN.md
report-NNN.md
```

`instruction-000.md` is reconnaissance only.  It determines the exact theorem
surface for the first implementation checkpoint before production code is
changed.

See `ROADMAP.md` for the current campaign sequence.

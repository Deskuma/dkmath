# FLT Prime TraceOne Closure Research

cid: `6aa90db5-7c94-83ee-b8ea-0474639967e6`

Branch: `research/FLT-Prime-TraceOne-Closure-260916-v0`

Base: `develop` at `6ba1fe2ac4a1a346eb8a18db480ab3d518b348e7`

Snapshot used for the initial architecture audit:

```text
__snapshot-dk_math-lean-code-260916-1826.tar.gz
sha256: 1f0b8ee3dd0a9a5f829447eba7656060c1d2e19f085153a19e5040fa63f0dde7
```

## 1. Purpose

This branch continues the research frontier left explicitly open by
`docs/refact/FLT-Prime-Generalization-260911-v0/summary-026.md`.

The previous branch already completed the conditional odd-prime architecture:

```text
PrimeAdicFactorPacket
  -> GTail exact p-adic split
  -> arbitrary-prime QR/QNR TraceOne coordinates
  -> primitive coordinates
  -> prime-discriminant maximal order / Dedekind domain
  -> discriminant-axis strip
  -> conjugate-coprime residual ideals
  -> residual principal ideal = idealRoot^p
  -> [classGroupPTorsionFreeAt]
  -> unit * element^p
  -> unit-sector normalization
```

This branch does **not** restart the old FLT7-to-general-p refactor and does
**not** try to force the old q-adic `2m-global` descent witness.

The new question is narrower:

> Starting from the generic TraceOne endpoint already proved, which remaining
> hypotheses can be discharged by existing DkMath infrastructure, and how can
> the remaining element-power / unit-sector statements be converted into exact
> integer-coordinate obstructions suitable for a final FLT contradiction?

No theorem on this branch may be described as a general proof of FLT unless the
full counterexample-to-contradiction chain is kernel checked without additional
unproved arithmetic hypotheses.

## 2. Current frontier

Phase 26 identified two principal arithmetic obligations:

```text
A. class-group p-torsion / principalization
B. real-branch nonzero unit-sector elimination
```

There are also two integration obligations which should be kept separate from
A and B:

```text
C. p=3 sector/carrier integration
D. generic FLT-counterexample -> PrimeAdicFactorPacket routing / public facade
```

For `p % 4 = 3` and `p >= 7`, the unit sector is already singleton, so B
vanishes and the conditional endpoint is

```text
classGroupPTorsionFreeAt R p
  -> exists delta, residual = delta^p.
```

For `p % 4 = 1`, the current endpoint is

```text
classGroupPTorsionFreeAt R p
  -> exists i : Fin p, exists delta,
       residual = realSectorRep(i) * delta^p.
```

No nonzero real sector has yet been eliminated generically.

## 3. Important new infrastructure from other campaigns

Several modules created after or outside the prime-generalization campaign now
intersect this frontier directly.

### 3.1 General TraceOne lattice landing

`DkMath.Lib.NumberTheory.TraceOneLatticeLanding` proves, for arbitrary
`TraceOneInt s`, an exact divisibility criterion in conjugate-product
coordinates:

```text
beta | alpha
  <->
N(beta) | (alpha * conj beta).fst
and
N(beta) | (alpha * conj beta).snd,
```

under the explicit hypothesis `N(beta) != 0`.

This is a useful receiver for translating element divisibility or sector
relations back into integer arithmetic.

### 3.2 TraceOne power/Core-image landing

`DkMath.Lib.NumberTheory.TraceOnePowerLanding` already contains:

```lean
traceOne_sq_coordinates
traceOne_norm_pow
traceOne_norm_eq_norm_mul_pow_of_eq
traceOne_sq_core_landing_iff
```

The norm layer is already arbitrary-power, but the exact coordinate landing is
currently square-specific. A natural branch target is an arbitrary exponent
coordinate kernel and a `traceOne_pow_core_landing_iff` theorem.

This should be treated as a receiver/criterion layer. It must not fabricate a
power root.

### 3.3 FLT3 / Eisenstein carrier

Production FLT3 defines

```lean
abbrev EisensteinInt := TraceOneInt (-1)
```

and separately provides a concrete Euclidean-domain implementation for
`TraceOneInt (-1)`.

Therefore the Phase-26 p=3 note must be re-audited carefully: the mathematical
carrier is definitionally the same, while the remaining mismatch may only be
that the existing FLT3 unit-sector result is not packaged as the neutral
`UnitPowerSectorSystem` expected by the generic prime facade.

Do not introduce an unnecessary ring equivalence if definitional equality is
already sufficient.

### 3.4 FLT5 / golden carrier

FLT5 uses its own `GoldenInt` structure, while the generic prime route at
`p=5` uses `TraceOneInt 1`.

The multiplication laws encode the same quadratic relation `phi^2 = phi + 1`,
but these are distinct Lean carriers. Any reuse of FLT5 unit information must
therefore be preceded by an explicit audited ring equivalence or adapter.

### 3.5 MultiGauge and old q-adic descent

The MultiGauge audit confirmed that the old FLT q-adic route still lacks an
unconditional provider for the smaller integer stage `g'`. Its `2m-global`
obligation is essentially the hard descent step itself.

This branch should use that result as a negative control:

```text
local residue / gauge transport
  !=
global smaller FLT counterexample.
```

Do not reopen `2m-global` merely to reproduce the same obstruction under new
names.

## 4. Branch strategy

The implementation order is structure-first.

1. Discharge class-group hypotheses when existing ring structure already makes
   them automatic, beginning with neutral reusable lemmas and a p=7 regression.
2. Generalize TraceOne square-coordinate landing to arbitrary natural powers.
3. Feed the generic FLT residual equations into the new power-coordinate
   receiver.
4. Repackage p=3 unit sectors on the generic `TraceOneInt (-1)` carrier if the
   audit confirms this is only an API boundary.
5. Audit the p=5 golden/TraceOne equivalence and reuse specialized fifth-power
   information only through a clean bridge.
6. Study the genuinely arithmetic class-number / p-torsion problem for the
   prime-discriminant quadratic orders.
7. Attack real `Fin p` nonzero sector elimination using exact coordinates,
   norms, residue constraints, and existing FLT packets.
8. Only after the mathematical closure kernel is stable, connect generic FLT
   counterexamples to `PrimeAdicFactorPacket` and export the new route through
   the public FLT facade.

## 5. Architectural rules

Prefer dependency-neutral modules under `DkMath/Lib/NumberTheory` for reusable
class-group and TraceOne algebra. Keep `DkMath/FLT/Prime` as orchestration and
FLT-specific specialization.

Do not make generic library modules import specialized FLT3/5/7 stacks merely
to obtain a regression theorem. Specialized adapters and regressions should
live on the FLT side.

Do not silently turn any of the following into axioms or assumptions hidden
behind structures:

```text
classGroupPTorsionFreeAt R p
all real unit sectors are p-th powers
nonzero real sectors are impossible
PrimeAdicFactorPacket exists for every FLT counterexample
a q-adic local witness has an integer global descent lift
```

## 6. Success criteria

The branch is successful even if it does not close general FLT, provided it
turns the Phase-26 frontier into smaller kernel-checked statements and clearly
classifies any remaining obstruction.

Strong milestones include:

```text
- classGroupPTorsionFreeAt discharged from PID / trivial-class-group structure;
- p=7 generic conditional endpoint made unconditional with respect to class group;
- arbitrary-r TraceOne power coordinates and exact power landing proved;
- p=3 generic sector adapter produced without duplicating the FLT3 ring;
- p=5 carrier equivalence audited and, if justified, implemented;
- class-number criterion isolated as the exact remaining imaginary-branch input;
- real-sector obstruction expressed as explicit integer-coordinate equations.
```

The branch must distinguish clearly between:

```text
PROVED KERNEL
CONDITIONAL ENDPOINT
API / CARRIER BOUNDARY
ARITHMETIC RESEARCH FRONTIER
```

## 7. Initial checkpoint

Start with `instruction-000.md`.

Checkpoint 000 is deliberately conservative: audit the exact class-group API,
add only neutral discharge lemmas justified by existing algebraic structure,
and verify the p=7 route as the first concrete regression.

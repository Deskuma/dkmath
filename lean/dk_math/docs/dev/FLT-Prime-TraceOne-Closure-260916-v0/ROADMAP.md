# FLT Prime TraceOne Closure Roadmap

Branch: `research/FLT-Prime-TraceOne-Closure-260916-v0`

Base: `develop` at `6ba1fe2ac4a1a346eb8a18db480ab3d518b348e7`

The roadmap begins at the exact frontier recorded by
`FLT-Prime-Generalization-260911-v0/summary-026.md`. Checkpoints are ordered so
that reusable algebraic infrastructure is established before FLT-specific
closure attempts.

## FPTC-000 — Class-group discharge audit and p=7 regression

Audit the current `classGroupPTorsionFreeAt` API and Mathlib class-group / PID
interfaces.

Target neutral implications such as:

```text
trivial/subsingleton class group
  -> classGroupPTorsionFreeAt R p

principal ideal ring / Euclidean domain
  -> trivial class group
  -> classGroupPTorsionFreeAt R p
```

Then test the bridge on the existing `TraceOneInt (-2)` Euclidean/PID
infrastructure used by FLT7 and compose it with the generic Phase-26 imaginary
endpoint.

The goal is to remove the explicit class-group hypothesis from the generic
`p=7` residual exact-power endpoint without reusing the specialized FLT7 final
theorem as a black box.

Status: **completed — Outcome A**.

## FPTC-001 — Finite class-group cardinality criterion

If Mathlib's finite class-group API supports it cleanly, prove a neutral
criterion of the conceptual form

```text
gcd(p, |ClassGroup R|) = 1
  -> classGroupPTorsionFreeAt R p.
```

Use the weakest necessary assumptions and avoid introducing a bespoke finite
group theory layer when Mathlib already exposes the needed element-order facts.

This checkpoint should convert the abstract Phase-26 hypothesis into a concrete
class-number target whenever the class group is finite.

Status: **completed — Outcome A**.

## FPTC-002 — Arbitrary-power TraceOne coordinate kernel

Generalize the square-only coordinate theorem in
`TraceOnePowerLanding.lean`.

For `x = <m,n> : TraceOneInt s`, define or characterize exact integer
coordinates

```text
x^r = <A_r(s,m,n), B_r(s,m,n)>
```

with a transparent recurrence induced by

```text
tau^2 = tau + s.
```

Prove the coordinate theorem, base/successor recurrences, and consistency with
the existing square theorem.

Do not add an existential power-root provider.

Status: **completed — Outcome A**.

## FPTC-003 — Arbitrary-power TraceOne landing criterion

Using FPTC-002 and the existing cancellation/lattice infrastructure, prove the
arbitrary-power analogue of `traceOne_sq_core_landing_iff`:

```text
exists gamma, alpha = beta * gamma^r
  <->
exists integer coordinates of gamma whose r-th-power coordinate image matches
(alpha * conj beta) / N(beta),
```

under the explicit nonzero-norm hypothesis on `beta`.

Keep this checkpoint neutral.  Composition with the generic FLT prime endpoint
is deferred to FPTC-004.

Status: **completed — Outcome A**.

## FPTC-004 — Generic imaginary residual coordinate receiver

Compose the Phase-26 theorem

```text
p % 4 = 3, p >= 7
classGroupPTorsionFreeAt R p
  -> residual = delta^p
```

with FPTC-002/003.

Expose exact integer-coordinate equations satisfied by every generic imaginary
branch residual. Check `p=7` and `p=11` as regressions.

This checkpoint should identify the next contradiction target without assuming
that the coordinate equations are already impossible.

Status: **completed — Outcome A**.

## FPTC-005 — p=3 generic Eisenstein sector closure

Re-audit the Phase-26 p=3 boundary with the production facts

```lean
abbrev EisensteinInt := TraceOneInt (-1)
```

and

```lean
eisensteinCubeUnitPowerSectorSystem :
  UnitPowerSectorSystem (TraceOneInt (-1)) 3
```

The sector adapter already exists, so do not duplicate it.  Instead compose the
existing Eisenstein sector system and Euclidean/PID class-group discharge with
the branch-independent generic stripped-ideal sector endpoint at `p = 3`.

Keep the nontrivial unit sector explicit; do not convert a sector-weighted cube
into an exact cube without a checked theorem.

Status: **next**.

## FPTC-006 — p=5 Golden/TraceOne carrier bridge audit

Compare `GoldenInt` with `TraceOneInt 1` exactly at the ring-operation level.

If a clean equivalence is justified, implement it in a dependency-neutral or
FLT5 adapter module and transport only the unit-sector facts needed by the
generic prime route.

Use the specialized FLT5 development as a regression oracle, not as a hidden
proof of the generic theorem.

Status: **planned**.

## FPTC-007 — Prime-discriminant class-number frontier

After FPTC-000/001, formulate the remaining imaginary-branch arithmetic target
in the most concrete form available, ideally involving the class number of the
quadratic order/field associated to `signedPrimeParameter p`.

Audit existing Minkowski machinery from FLT7 and Mathlib before introducing new
bounds.

Possible outcomes:

```text
A. a reusable theorem proves p-torsion-freeness for the required family;
B. a finite/computable criterion is obtained for bounded p;
C. the general class-number statement is identified as a genuine external
   number-theoretic frontier.
```

No unproved class-number claim may be promoted to production.

Status: **research frontier**.

## FPTC-008 — Real `Fin p` sector obstruction

For `p % 4 = 1`, combine:

```text
residual = rep(i) * delta^p
TraceOne lattice landing
arbitrary-power coordinate landing
norm identities
primitive/discriminant-axis conditions
```

and determine which exact coordinate/residue conditions depend on `i`.

The checkpoint goal is first to isolate a machine-checkable obstruction for
`i != 0`, not to assume that all nonzero sectors disappear.

Test `p=5` and `p=13` separately before claiming a uniform theorem.

Status: **research frontier**.

## FPTC-009 — Generic counterexample routing

Audit the remaining front-end gap:

```text
arbitrary odd-prime FLT counterexample
  -> PrimeAdicFactorPacket
```

At present the generic prime architecture begins from the packet rather than
from the public FLT counterexample statement.

Factor existing FLT3/5/7 routing only where the hypotheses genuinely match.
Do not hide a branch assumption inside a constructor.

Status: **planned after closure kernel**.

## FPTC-010 — Public facade and closeout

If the preceding checkpoints justify it:

1. export the stable generic modules through the nearest FLT facade;
2. add p=3/5/7 regression tests;
3. audit axioms and forbidden source patterns;
4. document exactly which exponents/branches are unconditional and which remain
   conditional;
5. write a final branch report.

A closeout document must not call the campaign a proof of general FLT unless
all front-end, class-group, sector, and final-contradiction obligations are
actually closed.

Status: **future**.

## Global stop rules

Stop and report instead of forcing a theorem if:

- `classGroupPTorsionFreeAt` requires a genuinely new number-theoretic theorem
  rather than missing API glue;
- a real-sector elimination argument works only for a fixed exponent;
- the arbitrary-power landing theorem becomes merely a restatement with no
  usable integer-coordinate consumer;
- a proposed p=3 adapter duplicates a definitionally identical carrier;
- a p=5 bridge requires importing the entire FLT5 final theorem into a neutral
  library module;
- generic counterexample routing silently assumes the hard descent conclusion;
- a local q-adic or MultiGauge witness is promoted to a global integer descent
  without a checked provider.

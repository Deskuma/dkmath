# Validation 021

All Lean commands ran from lean/dk_math using Lean 4.34.1.

## Checked source scope

Three production modules have 48 public audit entries:

- FinsetSupportPacking: 21 (18 new, two retained, one refactored)
- OldSupportCapacityCertificate: 8 new
- CoarseTownDeletionCapacity: 19 new

Thus 45 new production declarations and three retained/refactored
production declarations are audited. Seven new regression/calibration
modules have 40 public declarations. The complete manifest has 88 entries,
including definitions, semantic theorems, data equalities, finite decisions,
and all endpoint declarations. The existing facade gained two imports;
raw calibration data remain under DkMathTest.

[Complete declaration manifest](evidence/MANIFEST.md#log-360750ede26140a8)

## Performed builds and dependency audit

- Focused build: all three production modules and all seven new test
  modules passed, 9087 jobs. [Log](evidence/MANIFEST.md#log-e166844069f844f7)
- lake build DkMath.NumberTheory.Legendre passed, 9108 jobs.
  [Log](evidence/MANIFEST.md#log-c41af1cab68c9d6a)
- lake build DkMath passed, 10410 jobs.
  [Log](evidence/MANIFEST.md#log-7f4d5b59bfb12f6a)
- lake build DkMathTest.NumberTheory.LegendreDeletionAxiomAudit passed,
  9125 jobs.
  [Log](evidence/MANIFEST.md#log-2de5eec01f8b42f0)

Every manifest entry has both a check and a print-axioms command. All
resulting dependency sets use only the standard logical axioms propext,
Classical.choice, and Quot.sound, or no axioms. No new endpoint or new
production declaration depends on a proof-hole axiom. In particular,
the provenance conjunction includes the old quotient endpoint as well
as the new deletion endpoint.

The root log retains five existing unrelated proof-hole warnings in
ZsigmondyCyclotomicResearch:147, TriominoCosmicBranchA:4187,
GcdNextResearch:850, CyclotomicPrincipalization:5389, and TriominoFLT:1919.
The existing PacketCross hrs binder warning is also replayed.
No source at these warning locations was changed. The complete new-API
dependency audit supplies the scoped guarantee, not whole-project
proof-hole freedom.

## Large certificate methods and performance

Pure kernel decision, checked rewrites, and symbolic finite set/cardinality
proofs supply the following facts:

- n=1031, S=primeScalesUpTo 10: D.card=216, R.card=216, V.card=432,
  pi(n)=173; the symbolic exact deletion consumer yields the endpoint.
- n=297: the sorted discovered family passes the checker, has 63 seats
  against 62 old primes, and yields the explicit-certificate endpoint.
- n=1031 optional: the sorted discovered family passes the checker and
  has 233 seats against 173 old primes.
- q=11 at 1031: fiber.card=39 and 741 fiber edges imply failure of the
  old edge deficit while the new deletion deficit succeeds.

The 1031 carrier normalizations prove both the geometric seat inventory
and the entire bounded prime inventory. Supplied data are not support
labels. Distinctness of the larger sorted lists uses kernel-checked
adjacent comparisons and transitivity. The full-town list expansion is
checked before the exact production set equality is proved.

Measured whole build behavior:

| Check | elapsed seconds | peak RSS KiB | relevant module times |
|---|---|---|---|
| 1031 coordinate compression | 201.85 | 18325692 | data 173 s, deletion 21 s |
| 1031 final linear expansion | 167.16 | 18325300 | data 138 s, deletion 21 s |
| 297 explicit certificate | 23.50 | 2761828 | checker module 21 s |
| 1031 explicit certificate | 18.41 | 7385024 | checker module 11 s |

These are scoped build observations, with different cached dependencies;
they are not repeated microbenchmarks or a general speedup claim.
The peak of the large data check is about 17.5 GiB and remains a practical
cost of rebuilding that calibration from source. The public symbolic
API and facade do not import these large data proofs.

Direct full-expression reduction and direct large-carrier equality were
interrupted before producing a certificate. They are preserved as attempt
logs, with no mathematical conclusion inferred. The coordinate attempt
completed successfully, and the final linear expansion replaces it in
the source. Closed-carrier strictness proof elaboration first exceeded
recursion/heartbeat limits; symbolic private lemmas fixed that path.
No less-trusted evaluator was introduced.

## Finite and artifact regression checks

Kernel regressions preserve the tiny empty-support family, shared first
endpoints with D.card<E.card, the n=11 edge endpoint, strict deletion/edge
differences at n=6 and n=1031, both required large endpoints, the optional
233-seat endpoint, and a mathematically invalid certificate rejected for
shared old support. Provenance keeps both separately named old and new
1031 proof paths.

The 602-row discovery compares exact left and right deletion unions,
independently reconstructs edges, verifies partitions and actual bounded
fiber disjointness, and compares thresholds with the 020 greedy families.
The artifact checker verifies both imported greedy lists against their
exact discovery input, complete public audit coverage, headers and import
markers, forbidden constructs, neutral import direction, whitespace,
ASCII prose/logs without backslashes, all seventeen report answers, and
the final judgment.

Compiler output logs are converted to plain ASCII notation after builds
finish; successful-build markers, declaration names, axiom names, and
warnings are retained. Empty interrupted-attempt timing files are not
used as performance evidence. The existing earlier logs are unchanged.

The artifact checker passed.
[Checker output](evidence/MANIFEST.md#log-6358d68898dc375f)

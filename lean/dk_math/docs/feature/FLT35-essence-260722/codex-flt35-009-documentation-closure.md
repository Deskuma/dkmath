# Codex instruction: F35-009 FLT3 / FLT5 essence documentation closure

## 0. Context

Repository:

```text
Deskuma/dkmath
```

Branch:

```text
feature/FLT35-essence-260722-v0
```

Read first:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/README.md
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-001.md
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-006.md
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-008a.md
lean/dk_math/docs/feature/FLT35-essence-260722/note-flt5-standalone-v433-lean4web-milestone.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/DkMath/FLT/QuadraticEssence.lean
lean/dk_math/DkMath/FLT/ThreeTraceOneBridge.lean
lean/dk_math/DkMath/FLT/Five/TraceOneBridge.lean
lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
```

Completed checkpoints:

```text
F35-001 investigation and design
F35-002 TraceOneQuadratic core
F35-003 FLT3 bridge
F35-004 FLT5 bridge
F35-005 facade and initial audit
F35-006 standalone manifest and generator
F35-007 fixed v4.29.0 standalone provenance package
F35-008A public/standalone statement and trust audit: Outcome A / PASS
```

External compatibility milestone:

```text
Lean v4.33.0 standalone build: Success
Lean4Web full standalone: PASS
Comparator Live full source: initialization failure
Comparator-minimal theorem bundle: deferred
```

This checkpoint is documentation closure only. Do not change any Lean implementation.

## 1. Goal

Close the FLT3 / FLT5 quadratic-essence feature as a completed, generally shareable result.

Update the feature README so it no longer reads as an implementation roadmap or claims that the completed FLT5 standalone is still missing.

The completed public claim is:

```text
The cubic kernel and quintic kernel are connected to one neutral trace-one quadratic norm family at parameters s = -1 and s = 1.
```

The completed Lean Core is:

```text
GN3 / S0  -> TraceOneInt (-1) norm
GN5       -> TraceOneInt 1 norm
```

Do not claim:

```text
a general odd-prime theorem
an unconditional DkMath-native FLT3 proof
an FLT7 theorem
Comparator Live validation of the full FLT5 source
an axiom-free proof
```

## 2. Required changes

Update:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/README.md
```

Create:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-009.md
```

No other file is required unless a nearby documentation index already contains an explicit list of this feature and must be updated for consistency. Do not create a broad repository README rewrite.

## 3. README status and opening

Change the metadata status from an implementation roadmap to completed.

Recommended form:

```text
- Status: completed
- Completion checkpoint: F35-009
```

At the beginning, add a concise completion summary that states:

1. `TraceOneInt s` is now the neutral coordinate-ring API;
2. FLT3 connects at `s = -1`;
3. FLT5 connects at `s = 1`;
4. the bridges are observational and do not replace either proof tower;
5. the full FLT5 Mathlib-only standalone and its provenance package are fixed;
6. public and standalone FLT5 statements and axiom sets match under v4.29.0;
7. v4.33.0 and Lean4Web compatibility were externally confirmed;
8. Comparator Live minimization remains a separate deferred packaging task.

## 4. Correct outdated statements

Audit the entire README for roadmap-era statements that became false after F35-006 through F35-008A.

In particular, correct every statement equivalent to:

```text
FLT5 full standalone is unfinished
F35-006/F35-007/F35-008 are future work
current standalone consists only of the GN5 seed
public/standalone statement comparison remains pending
axiom audit remains pending
```

Preserve the important distinction:

```text
DkMath.FLT.Five.Standalone
```

is still the small GN5 seed source module, while the completed generated artifact is:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
```

Do not describe the seed module itself as the complete proof.

## 5. Completed module map

Add or update a clear module map:

```text
DkMath.NumberTheory.TraceOneQuadratic
  neutral two-coordinate commutative ring
  conjugation / trace / norm / discriminant
  norm multiplicativity

DkMath.FLT.ThreeTraceOneBridge
  S0_nat -> norm at s = -1
  S0_int -> norm at s = -1
  GN3 gap coordinates -> norm at s = -1
  shifted Eisenstein compatibility

DkMath.FLT.Five.TraceOneBridge
  GoldenInt coordinate map
  goldenNorm -> norm at s = 1
  GoldenNorm -> norm at s = 1
  GN5 square-link coordinates -> norm at s = 1

DkMath.FLT.QuadraticEssence
  public facade importing the two proved specializations
```

Document the dependency direction:

```text
TraceOneQuadratic
      ↑              ↑
FLT3 bridge       FLT5 bridge
      \              /
       QuadraticEssence
```

Retain the prohibition on cross-importing the FLT3 and FLT5 proof towers.

## 6. Public theorem surface

List the completed reusable theorem surface exactly as implemented.

Neutral core:

```text
traceOne_ext
traceOne_tau_sq
traceOne_conj_invol
traceOne_conj_mul
traceOne_mul_conj
traceOne_norm_mul
four_mul_traceOneNorm_eq_discriminant
traceOneNorm_neg_one
traceOneNorm_one
```

FLT3 bridge:

```text
S0_nat_eq_traceOneNorm_negOne
S0_int_eq_traceOneNorm_negOne
GN_three_sub_eq_traceOneNorm_negOne
eisensteinNorm_shift_eq_traceOneNorm_negOne
```

FLT5 bridge:

```text
goldenToTraceOne
goldenNorm_eq_traceOneNorm_one
GoldenNorm_eq_traceOneNorm_one
GN5_eq_traceOneNorm_squareLink
```

Existing endpoints remain unchanged:

```text
DkMath.FLT.FLT3_core
DkMath.FLT.FLT_d3_by_padicValNat
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

## 7. Mathematical result section

Retain and elevate the completed identities:

```text
N_s(a,b) = a^2 + a*b - s*b^2
Delta_s = 1 + 4*s
4*N_s(a,b) = (2*a+b)^2 - Delta_s*b^2
```

Then state the two completed specializations:

```text
s = -1:
N_{-1}(a,b) = a^2 + a*b + b^2
Delta = -3
GN3 / S0 -> N_{-1}

s = 1:
N_1(a,b) = a^2 + a*b - b^2
Delta = 5
GN5 -> N_1 through the proved square coordinates
```

Make clear that this is the extracted common quadratic essence. It is not a single theorem proving both FLT3 and FLT5.

## 8. FLT3 boundary

Preserve the exact distinction:

```text
DkMath.FLT.FLT3_core
```

is an unconditional control route using Mathlib's completed FLT3 theorem.

The DkMath-native valuation route:

```text
DkMath.FLT.FLT_d3_by_padicValNat
```

still receives `hS0_not_sq` and `Nat.Coprime a b` as hypotheses.

Do not describe the DkMath-native route as unconditional. Do not weaken or hide this boundary.

## 9. FLT5 standalone and provenance

Add a concise completed artifact table containing:

```text
Artifact:
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt

Pinned environment:
Lean / Mathlib v4.29.0

Lines:
5981

Bytes:
234552

SHA-256:
400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd

Active import surface:
import Mathlib

Ordered production modules:
33
```

Mention:

```text
deterministic manifest generation
exact-byte isolated build PASS
checksum PASS
production endpoint included exactly once
artifact remains outside the production import graph
```

Link by repository-relative path to:

```text
FLT5#StandAlone-v0.provenance.md
FLT5#StandAlone-v0.lean.build.log
FLT5#StandAlone-v0.audit-v429.log
report-flt35-007.md
report-flt35-008a.md
```

## 10. Statement and trust audit result

Record the F35-008A result precisely:

```text
Outcome A
Final audit result PASS
```

State that these actual declarations matched between public source and fixed standalone:

```text
Fermat5Equation
FLT5Target
flt5Target
fermatFive_no_positive_solution
```

State that separate Lean processes produced equal type output for the checked endpoint declarations.

Record the exact FLT5 endpoint axiom set:

```text
{propext, Classical.choice, Quot.sound}
```

State:

```text
sorryAx: absent
DkMath-defined axioms: absent
active native_decide: absent
active admit: absent
active sorry: absent
```

Do not call the endpoints axiom-free because the standard Lean axioms above are present.

For the quadratic-essence theorem surface, state only that the checked declarations contain no `sorryAx` or DkMath-defined axiom. The detailed per-theorem sets may be linked to `report-flt35-008a.md` rather than duplicated in full.

## 11. v4.33.0 and web boundary

Record the external compatibility milestone separately from the v4.29.0 provenance certificate:

```text
standalone v4.33.0 compatibility derivative: build Success
Lean4Web full standalone: PASS
```

Record the current Comparator Live observation:

```text
Unexpected error initializing verification
No output generated
```

State the observed boundary accurately:

- reducing executable declarations allows Comparator Live to initialize;
- changing comment volume alone does not solve it;
- a declaration-minimal theorem bundle using `theorem_picker` is deferred;
- Comparator Live is not part of the completed Essence API or fixed standalone proof certificate.

Do not present Comparator Live as a mathematical failure.

## 12. Checkpoint roadmap closure

Convert the checkpoint roadmap into a completed table or list:

```text
F35-001 complete
F35-002 complete
F35-003 complete
F35-004 complete
F35-005 complete
F35-006 complete
F35-007 complete
F35-008A complete
F35-008B partial external milestone; Comparator-minimal bundle deferred
F35-009 complete
```

Do not leave the README saying F35-008 or F35-009 are still recommended next steps.

## 13. Definition of Done

Update the Definition of Done to actual final results.

The completed feature must conclude with:

```text
GN3 -> N_{-1}
GN5 -> N_1
```

and identify these as Lean-proved bridge theorems.

The remaining research begins outside this feature:

```text
GN7 -> N_{-2} prediction
```

Do not implement or claim the p=7 identity in this checkpoint.

## 14. General-sharing summary

Add a short section suitable for linking to other Lean users. It should explain:

- what was generalized;
- where the reusable neutral API lives;
- where the FLT3 and FLT5 bridges live;
- which endpoint is unconditional and which native route remains conditional;
- where the standalone proof certificate and audits live;
- what is explicitly not claimed.

Keep it technical and factual. Avoid promotional claims about a general FLT proof.

## 15. Required report

Create `report-flt35-009.md` containing:

- checkpoint and Outcome A, B, or C;
- README status transition;
- outdated statements corrected;
- completed module map;
- public theorem surface documented;
- FLT3 conditional/unconditional boundary documented;
- FLT5 standalone identity documented;
- F35-008A trust result documented;
- v4.33.0 / Lean4Web boundary documented;
- Comparator Live deferred boundary documented;
- files changed;
- verification performed;
- exact final feature status;
- recommended next feature: FLT7 quadratic prediction.

Outcome meanings:

### Outcome A

Documentation now accurately describes the completed implementation, provenance, audits, and remaining boundaries.

### Outcome B

Minor stale or contradictory documentation was found and corrected; the final documentation is accurate.

### Outcome C

A material implementation or audit contradiction is found. Do not mark the feature completed; report the contradiction.

## 16. Verification

Run at minimum:

```bash
cd lean/dk_math

python scripts/audit-flt5-public-standalone.py --check
sha256sum --check \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'

lake build DkMath.FLT.QuadraticEssence
lake build DkMath.FLT.Five

git diff --check
```

Also inspect the final README for stale text equivalent to:

```text
Status: implementation roadmap
FLT5 full standalone is unfinished
F35-008 remains future work
F35-009 remains future work
```

No such stale statement may remain unless quoted explicitly as historical context.

## 17. Strict non-goals

Do not:

- modify any Lean source;
- modify any test Lean source;
- modify the standalone artifact, checksum, provenance, build log, or audit log;
- rerun or alter the v4.33.0 compatibility derivative;
- create the Comparator-minimal bundle;
- run Comparator Live;
- add p=7 code;
- add a general odd-prime theorem;
- alter FLT3 or FLT5 endpoint claims;
- update unrelated repository documentation.

## 18. Commit boundary

One documentation commit is preferred.

Suggested commit message:

```text
Complete FLT3 FLT5 quadratic essence documentation
```

Push to:

```text
feature/FLT35-essence-260722-v0
```

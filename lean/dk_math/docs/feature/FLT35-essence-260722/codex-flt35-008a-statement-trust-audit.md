# Codex instruction: F35-008A public/standalone statement and trust audit

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
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
lean/dk_math/docs/feature/FLT35-essence-260722/note-flt5-standalone-v433-lean4web-milestone.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
lean/dk_math/DkMathTest/FLT/QuadraticEssence.lean
lean/dk_math/DkMathTest/FLT/Five/CheckAxioms.lean
```

Completed facts:

```text
F35-002 TraceOneQuadratic core
F35-003 FLT3 trace-one bridge
F35-004 FLT5 trace-one bridge
F35-005 common facade and initial audit
F35-006 deterministic FLT5 standalone generator
F35-007 fixed v4.29.0 provenance standalone
external v4.33.0 standalone build: Success
Lean4Web full standalone: PASS
```

Comparator Live full-source initialization is deferred because the executable declaration bundle is too large for the current Live frontend. Do not attempt Comparator Live in this checkpoint.

Codex can execute only the repository-pinned Lean/Mathlib v4.29.0 environment. This checkpoint is therefore F35-008A only.

## 1. Goal

Close the remaining local verification obligations before documentation closure:

1. verify that the current public FLT5 endpoint and the fixed v4.29.0 standalone endpoint have the same declaration statement;
2. verify that their public equation definition is the same;
3. run and save formal axiom reports for the public and standalone endpoints;
4. audit the FLT3/FLT5 quadratic-essence theorem surface already exposed by `DkMathTest.FLT.QuadraticEssence`;
5. record the exact trust boundary without changing any proof.

The target endpoint is:

```text
DkMath.FLT.Five.fermatFive_no_positive_solution
```

Also audit its aggregate predecessor:

```text
DkMath.FLT.Five.flt5Target
```

## 2. Strict preservation boundary

Do not modify:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/DkMath/FLT/Five/*.lean
lean/dk_math/DkMath/FLT/ThreeTraceOneBridge.lean
lean/dk_math/DkMath/FLT/QuadraticEssence.lean
lean/dk_math/DkMath/NumberTheory/TraceOneQuadratic.lean
lean/dk_math/lean-toolchain
lean/dk_math/lake-manifest.json
```

Do not regenerate the fixed v4.29.0 artifact.

Its checksum must remain:

```text
400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd
```

No production theorem statement or proof body may change.

## 3. Required new files

Create a deterministic standard-library-only audit script:

```text
lean/dk_math/scripts/audit-flt5-public-standalone.py
```

Create a saved audit log:

```text
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.audit-v429.log
```

Create the checkpoint report:

```text
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-008a.md
```

Temporary `.lean` files must be created outside the repository or in a temporary directory and must not remain tracked.

## 4. Audit-script contract

The script must run from `lean/dk_math` and use Python standard library only.

Recommended interface:

```bash
python scripts/audit-flt5-public-standalone.py --check
python scripts/audit-flt5-public-standalone.py \
  --log 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.audit-v429.log'
```

The script must fail with nonzero exit status on every mismatch or Lean failure.

It must:

1. verify the fixed artifact SHA-256 before all other work;
2. verify the repository executable is Lean v4.29.0;
3. read the current public source:

```text
DkMath/FLT/Five/Basic.lean
DkMath/FLT/Five/Main.lean
```

4. read the fixed standalone artifact;
5. extract and compare the declaration source for:

```text
def Fermat5Equation
abbrev FLT5Target
theorem flt5Target
theorem fermatFive_no_positive_solution
```

6. compare declaration statements, not proof bodies;
7. generate separate public and standalone audit files;
8. run both through `lake env lean`;
9. capture endpoint type output and `#print axioms` output;
10. compare public and standalone endpoint type outputs;
11. compare public and standalone endpoint axiom sets;
12. run the existing quadratic-essence audit target and capture its output;
13. write one complete deterministic log.

Do not compare declarations by theorem name alone.

## 5. Source-statement extraction

The public and standalone declarations share the same namespace but cannot be imported into one environment because the standalone duplicates production declarations. Compare them in separate environments.

For source extraction, locate declaration starts by exact declaration kind and identifier. Extract:

- `Fermat5Equation`: complete definition through its defining expression;
- `FLT5Target`: complete abbreviation statement through its defining proposition;
- `flt5Target`: theorem type only, ending immediately before `:=`;
- `fermatFive_no_positive_solution`: theorem type only, ending immediately before `:=`.

Normalize only syntactically irrelevant formatting:

```text
line endings
trailing whitespace
runs of ordinary whitespace outside comments and string literals
```

Do not unfold, rename, reorder binders, rewrite notation, or simplify propositions.

The script must print and log a SHA-256 for each normalized declaration statement from both sources. Require exact pairwise equality.

Expected logical endpoint shape:

```lean
theorem fermatFive_no_positive_solution
    (x y z : ℕ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    ¬ Fermat5Equation x y z
```

Do not hardcode equality merely from this expected display. The script must compare the actual current source and fixed artifact.

## 6. Public Lean audit file

Generate a temporary file equivalent to:

```lean
import DkMath.FLT.Five.Main

#check @DkMath.FLT.Five.Fermat5Equation
#check @DkMath.FLT.Five.flt5Target
#check @DkMath.FLT.Five.fermatFive_no_positive_solution

#print axioms DkMath.FLT.Five.flt5Target
#print axioms DkMath.FLT.Five.fermatFive_no_positive_solution

example (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ DkMath.FLT.Five.Fermat5Equation x y z :=
  DkMath.FLT.Five.fermatFive_no_positive_solution x y z hx hy hz
```

Markers may be added around each output section so the script can parse the log reliably.

Build it with the pinned project environment.

## 7. Standalone Lean audit file

Create an exact temporary `.lean` copy of:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
```

Append only audit commands corresponding to the public audit file:

```lean
#check @DkMath.FLT.Five.Fermat5Equation
#check @DkMath.FLT.Five.flt5Target
#check @DkMath.FLT.Five.fermatFive_no_positive_solution

#print axioms DkMath.FLT.Five.flt5Target
#print axioms DkMath.FLT.Five.fermatFive_no_positive_solution

example (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ DkMath.FLT.Five.Fermat5Equation x y z :=
  DkMath.FLT.Five.fermatFive_no_positive_solution x y z hx hy hz
```

Do not edit the tracked artifact.

Build the temporary file with the same v4.29.0 environment.

## 8. Type-output comparison

Normalize only path prefixes, diagnostic source positions, and ordinary output whitespace.

Require exact equality between public and standalone `#check` output for:

```text
@DkMath.FLT.Five.Fermat5Equation
@DkMath.FLT.Five.flt5Target
@DkMath.FLT.Five.fermatFive_no_positive_solution
```

If Lean output formatting is too unstable for a clean comparison, keep the source-statement hash comparison as the primary equality certificate and record the precise output difference. Do not falsely claim output equality.

## 9. Axiom/trust audit

Capture the exact `#print axioms` output for public and standalone:

```text
DkMath.FLT.Five.flt5Target
DkMath.FLT.Five.fermatFive_no_positive_solution
```

Require the public and standalone axiom sets to match exactly for each endpoint.

Reject immediately if any endpoint dependency report contains:

```text
sorryAx
DkMath-defined axiom declarations
```

Standard Lean axioms such as the following are not silently rejected:

```text
propext
Quot.sound
Classical.choice
```

Record the exact set actually reported. Do not describe a theorem as “axiom-free” if standard axioms appear.

Additionally inspect executable source, with comments and string literals excluded, for active uses of:

```text
native_decide
admit
sorry
```

An occurrence in prose or a comment is not an active use and must not fail the audit.

Do not infer absence of `native_decide` from `#print axioms`; perform the token audit separately.

## 10. Quadratic-essence audit

Run the existing target:

```bash
lake env lean DkMathTest/FLT/QuadraticEssence.lean
```

Capture and record the `#print axioms` output for:

```text
DkMath.NumberTheory.TraceOneQuadratic.traceOne_norm_mul
DkMath.NumberTheory.TraceOneQuadratic.four_mul_traceOneNorm_eq_discriminant
DkMath.FLT.S0_nat_eq_traceOneNorm_negOne
DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne
DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one
DkMath.FLT.Five.GN5_eq_traceOneNorm_squareLink
```

Reject `sorryAx` or DkMath-defined axioms in these reports.

This audit concerns the extracted quadratic essence only. It does not convert the conditional DkMath-native FLT3 valuation theorem into an unconditional theorem.

## 11. Saved log contract

The saved log must begin with:

```text
checkpoint: F35-008A
repository: Deskuma/dkmath
branch: feature/FLT35-essence-260722-v0
lean_toolchain: leanprover/lean4:v4.29.0
lean_version_output: <actual output>
artifact: DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
artifact_sha256: 400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd
```

Then record:

```text
normalized declaration hashes
statement comparison results
public Lean command and exit status
standalone Lean command and exit status
normalized #check comparison results
public endpoint axiom reports
standalone endpoint axiom reports
axiom-set comparison results
active-token audit result
quadratic-essence audit command, output, and exit status
final result
```

The final result must be exactly one of:

```text
PASS
FAIL_STATEMENT_MISMATCH
FAIL_TYPE_OUTPUT_MISMATCH
FAIL_AXIOM_MISMATCH
FAIL_TRUST_BOUNDARY
FAIL_BUILD
FAIL_ENVIRONMENT
```

## 12. Report contract

Create `report-flt35-008a.md` with:

- date and checkpoint;
- outcome A, B, or C;
- pinned Lean/Mathlib boundary;
- fixed artifact identity and checksum;
- declaration statement hash table;
- public/standalone statement comparison result;
- public/standalone type-output comparison result;
- exact endpoint axiom sets;
- exact quadratic-essence axiom results;
- active `native_decide` / `admit` / `sorry` token result;
- saved log path;
- files changed;
- explicit non-goals;
- F35-009 recommendation.

Use these outcome meanings:

### Outcome A

All statement, type, axiom, token, and build checks pass exactly.

### Outcome B

A tooling or output-normalization defect is found and corrected without changing any proof or statement. All final checks pass.

### Outcome C

A real statement mismatch, axiom mismatch, active unsafe token, environment mismatch, or build failure remains. Do not proceed to documentation closure.

## 13. Verification

Run at minimum:

```bash
cd lean/dk_math

lake env lean --version
sha256sum --check \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'

python scripts/audit-flt5-public-standalone.py --check
python scripts/audit-flt5-public-standalone.py \
  --log 'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.audit-v429.log'

lake build DkMath.FLT.QuadraticEssence
lake build DkMath.FLT.Five

git diff --check
```

Before commit, prove that the fixed artifact and checksum did not change.

## 14. Explicit non-goals

Do not:

- run Comparator Live;
- create the Comparator-minimal theorem bundle;
- edit the v4.33.0 compatibility derivative;
- alter the v4.29.0 provenance artifact;
- change any FLT3 or FLT5 theorem statement;
- change any FLT3 or FLT5 proof;
- add a general odd-prime theorem;
- add the exponent-seven experiment;
- mark the feature README completed;
- perform F35-009.

## 15. Commit boundary

One implementation/audit commit is preferred.

Suggested commit message:

```text
Audit FLT5 public and standalone endpoints
```

Push to:

```text
feature/FLT35-essence-260722-v0
```

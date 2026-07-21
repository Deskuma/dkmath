# Codex instruction: F35-008B standalone-only Lean v4.32+ compatibility

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
lean/dk_math/docs/feature/FLT35-essence-260722/report-flt35-007.md
lean/dk_math/docs/feature/FLT35-essence-260722/note-FLT5-standalone-v429-to-v432-error-log-build-01.txt
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
lean/dk_math/DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
```

The source artifact is the accepted Lean/Mathlib v4.29.0 proof certificate:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
SHA-256: 400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd
```

It is immutable in this checkpoint.

Lean Comparator Live requires Lean/Mathlib v4.32.0 or later. This checkpoint ports only the standalone artifact. Do not perform a repository-wide Lean upgrade.

## 1. Goal

Produce a reproducible compatibility derivative of the v4.29.0 standalone proof that builds with Mathlib-only under Lean/Mathlib v4.32.0 or later.

The theorem statements and mathematical proof route must remain unchanged. Only elaboration/API compatibility repairs are allowed.

Primary minimum target:

```text
Lean v4.32.0
matching Mathlib v4.32.0 environment
```

After the v4.32.0 build passes, also smoke-test v4.33.0 when that environment is locally available. Record the two results separately.

## 2. Strict preservation boundary

Do not modify:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.provenance.md
scripts/generate-flt5-standalone.py
DkMath/FLT/Five/*.lean
DkMath/FLT.lean
DkMath/FLT/Five.lean
lean-toolchain
lake-manifest.json
```

The production repository remains v4.29.0-based.

Before work and before commit, verify the original artifact checksum:

```bash
sha256sum --check \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'
```

## 3. Compatibility derivative and transformation script

Create a deterministic transformation script:

```text
scripts/port-flt5-standalone-v432.py
```

Input:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt
```

Final output after all compatibility errors are closed:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v432-v0.lean.txt
```

The script must:

- use Python standard library only;
- verify the input SHA-256 before transforming;
- apply exact old-block to new-block replacements, not broad regex rewrites;
- require every expected old block to occur exactly once unless an explicit expected count is documented;
- fail on missing or duplicate replacement targets;
- add a compatibility-derivative header recording input artifact SHA-256, target Lean version, and script path;
- preserve `import Mathlib` as the only active import;
- write only an explicitly supplied output path;
- normalize the output to exactly one final newline.

Recommended interface:

```bash
python scripts/port-flt5-standalone-v432.py --check
python scripts/port-flt5-standalone-v432.py --output /tmp/FLT5Standalone-v432.lean
```

During exploration, a temporary editable copy may be used. Once it builds, encode every change in the deterministic script, regenerate from the pristine v4.29 artifact, compare byte-for-byte with the working result, and rebuild the regenerated output.

Do not hand-edit the final tracked derivative.

## 4. First visible error inventory

The first v4.32.0 log exposes 24 blocking errors in three compatibility families.

The warnings at lines 1075, 1082, and 5838 are non-blocking and are not part of the first repair gate.

Do not use generated line numbers as transformation identities. Locate each theorem through the generated `BEGIN GENERATED SOURCE` markers and theorem names.

### Family A: `Nat.gcd` versus `GCDMonoid.gcd`

Visible occurrences: 3.

Representative theorems:

```text
fifth_power_factor_split
SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
GoldenZeroSectorDescentPacket.fifthRoot_power_split
```

The new environment no longer simplifies `Nat.Coprime` directly into the generalized `GCDMonoid.gcd` expected by `exists_eq_pow_of_mul_eq_pow`.

Use the explicit bridge:

```lean
simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
```

Apply the same form to `hcopTH` and `hcopN0H` as appropriate.

Do not replace the generalized theorem or weaken coprimality.

### Family B: explicit `goldenOne` versus ring `1`

Visible occurrences: 3, all inside:

```text
goldenUnit_iff_isUnit
```

The explicit predicate `GoldenUnit` is stated with `goldenOne`, while `isUnit_iff_exists_inv` uses ring `1`. The new simplifier does not reliably bridge the two representations in these `simpa` calls.

Rewrite this theorem using explicit `change`, `calc`, or direct definitional transport. Avoid relying on global simp behavior.

Preferred proof shape:

```lean
/-- The explicit golden-unit predicate agrees with the standard ring predicate. -/
theorem goldenUnit_iff_isUnit {x : GoldenInt} : GoldenUnit x ↔ IsUnit x := by
  constructor
  · rintro ⟨y, hxy, _⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨y, ?_⟩
    change goldenMul x y = goldenOne
    exact hxy
  · intro hx
    rcases isUnit_iff_exists_inv.mp hx with ⟨y, hxy⟩
    have hxy' : goldenMul x y = goldenOne := by
      change x * y = (1 : GoldenInt) at hxy
      exact hxy
    refine ⟨y, hxy', ?_⟩
    calc
      goldenMul y x = goldenMul x y := by
        change y * x = x * y
        exact mul_comm _ _
      _ = goldenOne := hxy'
```

If the exact `change` orientation differs in v4.32.0, keep the same principle: explicitly bridge the two presentations and do not add an unsafe simp loop.

### Family C: `convert` descends into `Dvd` instances

Visible occurrences: 18.

The log reports:

```text
ring_nf made no progress on the goal
```

At the representative site, the actual residual goal is an instance equality such as:

```text
Int.instDvd = semigroupDvd
```

This is not a polynomial identity. `ring` and `ring_nf` must not be used on it.

Affected generated source regions include:

```text
SignedGoldenSectorArithmetic.lean
SignedGoldenZeroSector.lean
SignedGoldenZeroSectorInversion.lean
SignedGoldenZeroSectorFactorization.lean
SignedGoldenZeroSectorDescent.lean
```

Replace the fragile pattern:

```lean
convert dvd_sub h₁ h₂ using 1
all_goals ring
```

or analogous `dvd_add`, `dvd_mul_of_dvd_*`, and transported-divisibility forms with one of these stable shapes.

Simple cancellation:

```lean
simpa only [sub_sub_cancel] using dvd_sub hF hdiff
```

```lean
simpa only [sub_add_cancel] using dvd_add hnormDiff hsq
```

General algebraic transport:

```lean
have hdiv := dvd_sub h₁ h₂
have hEq : sourceExpression = targetExpression := by ring
rw [hEq] at hdiv
exact hdiv
```

Use an explicit equality theorem for the outer expression, then rewrite the divisibility proof. Do not use `convert ... using 1` at a goal whose outer proposition is `Dvd.dvd`.

For a negated target, first prove the exact expression equality and then use `Int.dvd_neg.mp` or `.mpr` explicitly.

Audit every logged Family-C theorem, not just the two memo examples.

## 5. Layered build loop

The first log is only the visible surface. Some errors are masked until earlier declarations elaborate.

Use an iterative loop:

1. apply one compatibility family or a small coherent group;
2. generate a fresh temporary derivative from the pristine input;
3. build under v4.32.0;
4. save the complete log;
5. classify newly exposed errors;
6. continue until the file builds.

Save logs as:

```text
docs/feature/FLT35-essence-260722/
  note-FLT5-standalone-v429-to-v432-error-log-build-02.txt
  note-FLT5-standalone-v429-to-v432-error-log-build-03.txt
  ...
```

Do not overwrite build-01.

Each log should begin with:

```text
Lean version
Mathlib revision if available
input artifact SHA-256
port script Git/worktree hash
exact build command
```

Do not stop merely because all build-01 errors disappear. The gate is a full zero-error v4.32.0 build.

## 6. Semantic invariants

After every generated derivative, verify:

```text
active imports total: 1
active import: Mathlib
active DkMath imports: 0
BEGIN source markers: 33
END source markers: 33
theorem flt5Target declarations: 1
theorem fermatFive_no_positive_solution declarations: 1
```

The following declarations and statements must not be renamed or weakened:

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z

theorem flt5Target : FLT5Target

theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z
```

Compatibility repairs may change proof terms and tactic scripts only.

## 7. Final v4.32 package

Only after a clean v4.32.0 build, track:

```text
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v432-v0.lean.txt
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v432-v0.lean.build.log
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v432-v0.lean.txt.sha256
DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v432-v0.provenance.md
scripts/port-flt5-standalone-v432.py
docs/feature/FLT35-essence-260722/report-flt35-008b-v432.md
```

The provenance document must record:

- immutable input artifact path and SHA-256;
- port script path and blob SHA;
- target Lean version output;
- target Mathlib revision;
- ordered compatibility replacement ledger;
- output SHA-256, line count, and byte count;
- full build command and result;
- statement that the derivative is not the v4.29 provenance original;
- statement that no production DkMath source was modified.

## 8. v4.33 smoke test

After v4.32.0 passes, run the exact regenerated derivative under a v4.33.0 environment when available.

Do not silently edit the v4.32 derivative for v4.33. If another repair is required, add a version-neutral compatibility replacement when it still builds on v4.32; otherwise split a later derivative.

Record the v4.33 result separately in the report.

## 9. Verification

At minimum:

```bash
# In the unchanged v4.29 project checkout
sha256sum --check \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256'
python scripts/port-flt5-standalone-v432.py --check
python scripts/port-flt5-standalone-v432.py \
  --output /tmp/FLT5#StandAlone-v432-v0.lean
python scripts/port-flt5-standalone-v432.py \
  --output /tmp/FLT5#StandAlone-v432-v0-second.lean
cmp \
  /tmp/FLT5#StandAlone-v432-v0.lean \
  /tmp/FLT5#StandAlone-v432-v0-second.lean
```

Then in the isolated v4.32.0 environment:

```bash
lake env lean --version
lake env lean /tmp/FLT5#StandAlone-v432-v0.lean
```

Also verify the original v4.29 artifact and repository remain unchanged:

```bash
git diff --exit-code -- \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt' \
  'DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt.sha256' \
  'DkMath/FLT/Five' \
  'lean-toolchain' \
  'lake-manifest.json'
git diff --check
```

## 10. Outcome branches

### Outcome A

The deterministic derivative builds under v4.32.0, all integrity checks pass, and the original v4.29 artifact remains byte-identical.

Commit the complete compatibility package and report.

### Outcome B

Additional errors emerge after the first visible layer, but all are compatibility-only and can be repaired without changing theorem statements or production sources.

Continue the layered loop until PASS, preserve the intermediate logs, then commit the complete package.

### Outcome C

A required repair would alter a theorem statement, introduce a non-Mathlib dependency, modify production sources, or leave the v4.29 artifact unreproducible.

Do not commit a falsely compatible derivative. Commit only the port harness, layered logs, and an honest blocker report.

## 11. Non-goals

Do not:

- upgrade the repository-wide Lean version;
- modify the v4.29 artifact or checksum;
- modify any production theorem source;
- change FLT5 endpoint statements;
- perform the public-versus-standalone statement audit;
- perform the final `#print axioms` trust audit;
- run or claim Lean Comparator Live acceptance before the local v4.32 build passes;
- add the exponent-seven experiment;
- make a general-prime theorem.

## 12. Commit

One or more focused commits are acceptable because hidden error layers are expected.

Suggested final package commit:

```text
Add FLT5 standalone Lean v4.32 compatibility derivative
```

Push to:

```text
feature/FLT35-essence-260722-v0
```

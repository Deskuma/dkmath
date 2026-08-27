# GWSS-001M Mellin finite-τ-jet / Vandermonde rank — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Implement and audit only the inserted Mellin-rank stage:

```text
GWSS-001M-A  exact finite τ-jet of the Mellin symmetric second-difference kernel
GWSS-001M-B  2-orbit and 3-orbit finite rank certificates
GWSS-001M-C  general finite squared-orbit Vandermonde transfer, only if A/B justify it
GWSS-001M-D  actual Xi-window Mellin-family rank classification
```

Do **not** start GWSS-002 in this assignment.

The current trusted frontier is:

```text
GWSS-000
  VARIABLE-WEIGHT-SOURCE-ALREADY-PRESENT

GWSS-001
  VARIABLE-WEIGHT-RANK-UNRESOLVED

GWSS-001T-A
  ACTUAL-WINDOW-EVEN-POLYNOMIAL-ORBIT-SEPARATION-FOUND

GWSS-001T-B
  MELLIN-FAMILY-RANK-UNRESOLVED
```

The next question is not whether arbitrary even polynomial selectors can read the actual finite Xi window. That is already proved.

The question is whether the **pre-existing zero-configuration-independent Mellin family** carries enough finite parameter rank to separate the actual squared orbits.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
GWSS roadmap and reports read
global objective
current GWSS stage
load-bearing provider boundary
next unresolved Gap
```

Global objective:

```text
zero configuration
  -> independent source
  -> off-critical detector
  -> arithmetic control
  -> centered-coordinate uniqueness
  -> RiemannHypothesis
```

Current stage:

```text
GWSS-001M
```

Load-bearing boundary:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO fixed-Xi defect vanishing provider
NO prime-side sign assumption
NO T -> infinity horizontal decay theorem
NO limit exchange
NO use of the actual zero configuration to define the Mellin family itself
```

The actual-window polynomial selector from GWSS-001T-A is a **rank certificate**, not yet an independent witness family, because its coefficients depend on the actual carrier.

GWSS-001M must therefore audit a family that is already defined independently of the unknown zero configuration.

## 2. Exact source family to audit

Inspect the checked-out definitions and theorem names; do not rely only on this document.

At minimum inspect:

```text
DkMath.Analysis.MellinMultiplicativeApproxIdentity
DkMath.RH.CFBRC.PascalCenteredXiExplicitFormulaHorizontalPairing
DkMath.RH.CFBRC.PascalCenteredXiMellinArithmeticSpecialization
DkMath.RH.CFBRC.PascalCenteredXiActualWindowVariableWeightRankTransfer
```

Important existing objects are expected to include:

```text
centeredMellinBoxApprox
centeredMellinSpectralWeight
centeredMellinSecondDifferenceWeight
pascalCenteredXiMellinSecondDifferenceWeight
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
tendsto_centeredMellinSpectralWeight_centeredMellinBoxApprox_one
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
```

For nonzero `τ`, the exact kernel factor is currently exposed schematically as

```text
K(τ,z) = (exp(τ z) - 2 + exp(-τ z)) / τ^2.
```

The full Mellin weight is this kernel multiplied by the spectral factor

```text
S_ε(z) = centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z.
```

Do not silently replace the full weight by the bare kernel until the spectral factor has been accounted for.

## 3. Independence firewall

The key distinction is:

```text
GWSS-001T-A selector
  coefficients depend on the actual finite Xi carrier

GWSS-001M Mellin family
  parameters ε and τ are chosen independently of the actual zero configuration
```

A successful GWSS-001M theorem must use the second kind of family.

Do not count a theorem as an independent Mellin rank result if it first computes the zero set and then chooses a custom polynomial weight depending on that set.

Using the actual carrier only to **evaluate a fixed/pre-existing family** or to state a finite-rank condition is allowed.

## 4. GWSS-001M-A — exact finite τ-jet

### 4.1 Goal

Formalize the exact low-order even Taylor coefficients of

```text
τ |-> (exp(τ z) - 2 + exp(-τ z)) / τ^2
```

at `τ = 0`, or an equivalent totalized/patched function already present in DkMath.

Do not use an informal Taylor-series comment as a theorem.

### 4.2 Preferred first targets

At minimum obtain exact Lean theorems corresponding to the first three nontrivial even powers:

```text
coefficient / jet order 0  -> z^2
coefficient / jet order 2  -> z^4 / 12
coefficient / jet order 4  -> z^6 / 360
```

The precise normalization may differ if derivatives rather than Taylor coefficients are used. Record the exact normalization in the report.

Acceptable theorem styles include:

```text
iterated derivative at τ = 0
HasDerivAt / HasFDerivAt chain
formal power series coefficient already available in Mathlib
an exact finite difference identity that isolates z^2, z^4, z^6 without an infinite series
```

Prefer the smallest proof surface that compiles cleanly in the pinned toolchain.

### 4.3 Do not overbuild

Do not begin by formalizing a full entire-function Taylor expansion or a general analytic-function power-series library.

If exact low-order derivatives are enough for the 2-orbit / 3-orbit gates, stop there.

### 4.4 Classification for A

Choose one:

```text
MELLIN-LOW-ORDER-JET-FOUND
MELLIN-JET-API-GAP
MELLIN-JET-IMPLEMENTATION-OBSTRUCTION
```

If A is not `MELLIN-LOW-ORDER-JET-FOUND`, stop this assignment and do not start B/C/D.

## 5. GWSS-001M-B — 2-orbit finite rank first

Proceed only after A succeeds.

### 5.1 Squared-orbit coordinates

For two distinct squared-orbit coordinates

```text
q1 = z1^2
q2 = z2^2
```

with

```text
q1 ≠ q2,
```

audit whether two independent Mellin jet coordinates separate them.

The natural low-order matrix is based on powers such as

```text
[q1,   q2]
[q1^2, q2^2]
```

or, if a constant/effective zeroth coordinate is more natural in the implemented normalization,

```text
[1,  1]
[q1, q2].
```

Do not force one matrix shape if the exact implemented jet normalization gives a cleaner equivalent form.

### 5.2 Zero squared-orbit case

Handle `q = 0` explicitly.

Do not hide a factor of `q1*q2` in a determinant theorem and then claim rank for all distinct squared orbits.

Determine from the actual centered-Xi API whether `z = 0` can occur in the finite centered Xi zero carrier. If an existing theorem excludes it, use that theorem and cite it. If not, either:

```text
A. use a rank matrix that remains valid when one q is zero;
B. state the nonzero-squared-orbit hypothesis explicitly;
C. classify zero-orbit handling as a separate API gap.
```

Do not infer zero exclusion merely from classical knowledge of Xi.

### 5.3 Required concrete certificate

Before generalizing, produce at least one focused Lean theorem proving 2-orbit separation from the actual low-order Mellin jet coordinates.

A determinant theorem, linear-independence theorem, or explicit reconstruction theorem is acceptable.

Suggested success label:

```text
MELLIN-2-ORBIT-RANK-FOUND
```

Otherwise classify:

```text
MELLIN-2-ORBIT-RANK-OBSTRUCTION
```

If the 2-orbit gate fails, do not proceed to 3-orbit or general Vandermonde work.

## 6. GWSS-001M-B — then 3-orbit rank

After the 2-orbit certificate, test three distinct squared coordinates.

Prefer a concrete theorem before invoking a general matrix theorem.

Natural coordinates are the first three powers of each squared orbit, with the exact normalization inherited from Part A.

The goal is to verify that the expected finite rank phenomenon survives actual Lean types, coercions, complex scalars, and the chosen normalization.

Success label:

```text
MELLIN-3-ORBIT-RANK-FOUND
```

A failure here is valuable; name the exact obstruction instead of bypassing it with a broad assumption.

## 7. GWSS-001M-C — general finite Vandermonde only after 2/3-orbit success

Do not start this section unless both concrete gates succeeded.

### 7.1 Goal

For a finite list/finset of pairwise distinct squared-orbit coordinates

```text
q_j = z_j^2,
```

formalize enough Vandermonde / power-evaluation rank to conclude that finitely many Mellin jet coordinates separate the finite squared-orbit mass vector.

### 7.2 Reuse Mathlib first

Search the pinned Mathlib source for existing declarations on:

```text
Vandermonde matrices
polynomial evaluation matrices
linear independence of powers
determinant of Vandermonde
Fin n matrices
```

Do not duplicate a general determinant theorem if Mathlib already has it.

### 7.3 Minimal acceptable general theorem

A full abstract matrix-rank library is unnecessary.

It is enough to prove a theorem of the schematic form:

```text
pairwise distinct q_j
  -> equality of the first N suitable power moments
  -> equality of all N orbit masses.
```

or equivalently:

```text
the first N jet evaluation functionals are linearly independent
on N distinct squared-orbit coordinates.
```

Use the exact finite carrier representation that makes the Lean proof smallest and trustworthy.

### 7.4 Source-rank meaning

Do not confuse algebraic rank of the **bare kernel jet** with the full Mellin weight family.

The spectral factor `S_ε(z)` still multiplies each orbit evaluation.

## 8. GWSS-001M-D — spectral-factor transfer to actual Xi window

Use the existing theorem from GWSS-001T-B:

```text
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
```

This gives, for each fixed finite radius `R`, sufficiently small positive `ε` such that

```text
S_ε(z) ≠ 0
```

for every actual Xi zero in the finite carrier.

### 8.1 What nonvanishing does and does not give

Nonvanishing permits pointwise nonzero scaling.

But be careful: the factor `S_ε(z)` depends on `z`, so the transfer is not necessarily a single common scalar multiplication of all columns.

If the rank matrix is multiplied columnwise by nonzero factors, prove explicitly that rank/invertibility is preserved.

Do not merely say "nonzero factor does not matter" without a theorem matching the matrix orientation being used.

### 8.2 Actual-window final target

A successful final theorem should be strong enough to justify one of the following equivalent readings:

```text
for a fixed finite Xi window and suitable small positive ε,
finite Mellin τ-jet data separates all distinct squared-orbit masses
```

or

```text
the restricted Mellin family has full finite evaluation rank modulo z ↔ -z
on the actual Xi window.
```

The family/parameters must remain independent of the unknown zero configuration except for choosing a finite number of evaluation parameters or the finite rank size after the window is fixed.

## 9. Finite τ values are allowed as an alternative to derivatives

If exact derivative/jet implementation becomes disproportionately difficult, an alternative finite-evaluation route is allowed.

For example, for distinct real parameters

```text
τ1, ..., τN,
```

consider the matrix of exact kernel values

```text
K(τ_i, z_j).
```

A successful finite-evaluation theorem must prove invertibility/separation exactly, not numerically.

Do not use floating-point determinant evidence as a load-bearing result.

If a finite-evaluation route is easier than a Taylor-jet route, explain why and keep the same source-independence firewall.

## 10. Positivity and arithmetic-control firewalls remain closed

GWSS-001M is **only** a source-rank stage.

Do not implement or assume:

```text
classical Weil positivity
prime-side positivity
sign of the von Mangoldt term after cancellation
horizontal-term disappearance
T -> infinity
exchange of ε, τ, X, or T limits
RH-equivalent global test-function positivity
```

Even a successful Mellin rank theorem does not prove RH.

## 11. GWSS-002 authorization rule

GWSS-002 remains forbidden during this assignment.

At the end classify GWSS-001M with exactly one primary label:

```text
MELLIN-FAMILY-ACTUAL-WINDOW-RANK-TRANSFER-FOUND
MELLIN-FAMILY-RANK-UNRESOLVED
MELLIN-FAMILY-RANK-OBSTRUCTION
```

Only the first label may authorize a later assignment to begin GWSS-002.

The final response may say:

```text
GWSS-002 is now mathematically eligible for a separate assignment
```

but must not implement it in the same run.

## 12. Recommended focused module

If new Lean code is required, prefer one focused module such as:

```text
DkMath.RH.CFBRC.PascalCenteredXiMellinFiniteJetRankAudit
```

Do not split every derivative order or every matrix size into separate modules.

If a generally reusable analytic lemma belongs naturally under `DkMath.Analysis`, it may be placed there only if it is genuinely generic and small. Avoid unrelated refactoring.

## 13. Required reports

Produce:

```text
0008-GWSS-001M-Mellin-finite-jet-rank-report.md
```

The report must include:

```text
Global objective
Current GWSS stage
Load-bearing boundary
Next unresolved Gap
```

Then record separately:

```text
A. exact τ-jet result
B. 2-orbit result
C. 3-orbit result
D. general finite-rank result, if reached
E. spectral-factor transfer result
F. final GWSS-001M classification
G. whether GWSS-002 is mathematically eligible for a separate assignment
```

## 14. Verification

For every added or modified Lean module run a focused build:

```text
lake build <module>
```

If the public `DkMath.RH` import surface changes, also run:

```text
lake build DkMath.RH
```

Always run:

```text
git diff --check
```

Check that no new:

```text
sorry
admit
axiom placeholder
```

was introduced.

Use `#print axioms` on every new load-bearing theorem. Standard results such as

```text
[propext, Classical.choice, Quot.sound]
```

are acceptable if they arise from ordinary Mathlib infrastructure; record the exact output.

## 15. Drift stop conditions

Stop and report instead of continuing if the work begins turning into:

```text
large general Taylor-series development
large new matrix/rank framework unrelated to this finite problem
new Eta endpoint normalization
completed-zeta reciprocal transport
fixed-Xi defect renaming
classical Weil positivity implementation
T -> infinity work
prime-side sign search
arbitrary numerical determinant experimentation without exact Lean closure
```

The criterion for progress is not module count. It is whether the pre-existing Mellin family is proved to carry independent finite squared-orbit rank on the actual Xi window.

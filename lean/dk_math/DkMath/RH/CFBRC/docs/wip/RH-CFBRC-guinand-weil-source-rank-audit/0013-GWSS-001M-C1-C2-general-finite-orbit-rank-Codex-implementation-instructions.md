# GWSS-001M-C1/C2 general finite-orbit Mellin rank — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue after the successful low-rank finite-`τ` lift.

Implement and audit only:

```text
GWSS-001M-C1  general finite bare-Mellin rank
GWSS-001M-C2  actual Xi-window full squared-orbit rank transfer
```

Do **not** start:

```text
GWSS-002  off-critical witness construction
GWSS-003  arithmetic sign / upper-control audit
GWSS-004  classical Guinand-Weil infrastructure
```

The current trusted frontier is:

```text
GWSS-001T-A
  ACTUAL-WINDOW-EVEN-POLYNOMIAL-ORBIT-SEPARATION-FOUND

GWSS-001M-A
  exact finite Mellin jets FOUND

GWSS-001M-B
  MELLIN-LOW-JET-ACTUAL-WINDOW-RANK-FOUND

GWSS-001M-C0
  FINITE-TAU-LOW-RANK-SEPARATION-FOUND
```

The remaining source-rank question is now genuinely finite-dimensional:

```text
Does the zero-independent Mellin family have full evaluation rank
on every finite set of distinct nonzero squared coordinates?
```

If yes, transfer this rank to the entire finite actual Xi zero window modulo the forced `z ↔ -z` symmetry.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0011 and 0012 read
global objective
current GWSS stage
load-bearing boundary
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
GWSS-001M-C1/C2
```

Load-bearing boundary:

```text
NO RH assumption
NO classical Weil positivity
NO Li criterion
NO fixed-Xi defect vanishing provider
NO T -> infinity horizontal decay provider
NO limit exchange
NO prime-side sign assumption
NO carrier-dependent polynomial selector counted as an independent witness
NO inference from formal Taylor series without an exact Lean theorem
```

The already proved rank-2/rank-3 finite-`τ` theorems are trusted and must be reused rather than duplicated.

## 2. Critical conceptual firewall

There are three different statements. Keep them separate.

### 2.1 Arbitrary even polynomial rank

Already proved using a selector built from the actual finite carrier.

This proves evaluation-map information content but is **carrier-dependent**.

Do not count it as the missing zero-independent source.

### 2.2 Mellin family rank on a prescribed finite coordinate set

This assignment must prove that the pre-existing family

```text
τ |-> complexExpSecondDifferenceKernel τ z
```

or equivalently the fixed-`ε` Mellin family has enough evaluation rank on every finite set of distinct nonzero squared coordinates.

The family itself is independent of the Xi zero configuration.

### 2.3 Actual Xi-window transfer

Only after 2.2 succeeds may the theorem be specialized to one representative per actual Xi squared orbit.

Do not claim point-level separation of `z` and `-z`; even weights cannot distinguish them.

## 3. Preferred proof architecture

Do **not** generalize the explicit 2-by-2 and 3-by-3 scalar determinant expansions by hand.

Use one general finite-dimensional argument.

Before choosing the implementation, inspect the pinned Mathlib surface for:

```text
Matrix.det
Matrix.vandermonde or equivalent Vandermonde determinant support
LinearIndependent
finite evaluation-map rank lemmas
function-space linear independence
basis / dual evaluation lemmas
```

Choose the lowest-complexity route supported by the pinned API.

Preferred routes, in order:

```text
Route A: general Mellin jets -> function linear independence -> finite evaluation basis
Route B: general normalized determinant -> Vandermonde leading coefficient
Route C: custom finite evaluation induction if the relevant Mathlib theorem is absent
```

Do not implement both A and B unless one is required as a helper for the other.

If the pinned API blocks the clean route, record the exact API gap instead of proliferating bespoke determinant code.

## 4. GWSS-001M-C1-A — arbitrary even Mellin jet coefficient

The low-order theorems established the coefficient pattern

```text
z^2
z^4 / 12
z^6 / 360
```

Generalize only as much as required for finite rank.

The expected coefficient of `τ^(2r)` in the bare kernel is

```text
2 * z^(2*r + 2) / (2*r + 2)!
```

or, with `q = z^2`,

```text
2 * q^(r + 1) / (2*r + 2)!
```

A suitable load-bearing theorem may be an arbitrary-order remainder statement such as:

```text
for m >= 0,
  K_τ(z)
    - sum_{r < m} coeff(r,z) * τ^(2r)
  = coeff(m,z) * τ^(2m) + o(τ^(2m))
```

or an equivalent `Tendsto` quotient theorem on a punctured neighborhood.

Requirements:

- derive it from the exact exponential Taylor remainder API already used in `PascalCenteredXiMellinFiniteJetRankAudit`;
- preserve the patched `τ = 0` distinction;
- do not introduce a formal power-series identity unless the needed convergence/remainder theorem is actually proved;
- reuse the existing low-order results when convenient, but C1 must support arbitrary finite orbit count.

Possible classification if this generalization itself fails:

```text
GENERAL-MELLIN-JET-API-GAP
```

If so, stop and document the precise missing theorem.

## 5. GWSS-001M-C1-B — squared-coordinate Vandermonde rank

Let a finite family of centered coordinates be indexed by `Fin n`:

```text
z : Fin n -> ℂ
q j := (z j)^2
```

Assume:

```text
∀ j, q j ≠ 0
Pairwise fun i j => q i ≠ q j
```

The first `n` even Mellin jet coefficient rows are, up to nonzero row scalars,

```text
q_j
q_j^2
...
q_j^n
```

Therefore their determinant is a nonzero scalar times

```text
(∏ j, q_j) * ∏_{i<j} (q_j - q_i)
```

Formalize enough of this statement to prove full coefficient rank.

Preferred theorem shape:

```text
LinearIndependent ℂ
  (fun j : Fin n =>
    fun r : Fin n =>
      2 * (q j)^(r.1 + 1) / ((2 * r.1 + 2)! : ℂ))
```

or an equivalent determinant-ne-zero statement.

Important:

- the hypotheses are on squared coordinates only;
- do not require `z i ≠ z j` separately;
- `q = 0` is already excluded on the actual Xi carrier by B0;
- do not reopen the generic `q = 0` nullspace as a new route obstruction.

Classification:

```text
GENERAL-FINITE-ORBIT-JET-RANK-FOUND
GENERAL-FINITE-ORBIT-JET-RANK-API-GAP
GENERAL-FINITE-ORBIT-JET-RANK-OBSTRUCTION
```

Only the first permits continuation.

## 6. GWSS-001M-C1-C — finite evaluation separation

The target is not merely jet rank. Prove existence of finitely many actual Mellin dilation parameters yielding an invertible evaluation matrix.

For the bare kernel, target a theorem schematically of the form:

```text
∃ τ : Fin n -> ℝ,
  Function.Injective τ / or pairwise distinct if useful
  ∧ Matrix.det (fun i j => complexExpSecondDifferenceKernel (τ i) (z j)) ≠ 0
```

The exact parameter constraints may be weaker if the determinant theorem is sufficient.

### Preferred Route A: linear-independent functions

If C1-B proves that the functions

```text
f_j(τ) = complexExpSecondDifferenceKernel τ (z j)
```

are linearly independent, use finite-dimensional linear algebra to obtain evaluation points `τ_i` with invertible evaluation matrix.

If a generic Mathlib theorem exists, reuse it.

If not, a short induction is acceptable:

```text
n = 0: trivial
n+1:
  choose evaluations separating first n functions
  use linear independence to find one more τ where the remaining Schur-complement / determinant function is nonzero
```

Do not build a large abstract interpolation library.

### Nonzero-τ requirement

Prefer all selected `τ_i ≠ 0`.

If the clean evaluation theorem naturally returns a parameter `0`, do not stop immediately. Since the bare Mellin functions are continuous and C0 already proves genuine nonzero-τ separation in low rank, audit whether the determinant can be perturbed off zero while preserving nonvanishing.

An acceptable general theorem may therefore use:

```text
τ : Fin n -> {t : ℝ // t ≠ 0}
```

or prove existence first in `ℝ` and then a separate nonzero perturbation theorem.

Do not silently use the `τ = 0` branch in a theorem advertised as finite nonzero-τ separation.

### Alternative Route B: normalized determinant

If the determinant asymptotic route is materially simpler in the pinned API, fixed dilation multiples are acceptable:

```text
τ_i(t) = (i+1) * t
```

The expected normalized leading order is

```text
t^(n*(n-1))
```

and the leading coefficient is a nonzero scalar times the product of two Vandermonde factors:

```text
Vandermonde(((i+1)^2)_i)
*
(∏ j, q_j)
*
Vandermonde((q_j)_j)
*
∏_{r<n} 2/(2r+2)!
```

The rank-2 coefficient `3` and rank-3 coefficient `120` must be recovered as special cases conceptually, but no separate reproving of C0 is required.

If this route becomes a large determinant-asymptotics detour, abandon it and use Route A.

### C1 success classification

End C1 with exactly one primary classification:

```text
GENERAL-FINITE-ORBIT-BARE-MELLIN-RANK-FOUND
GENERAL-FINITE-ORBIT-RANK-API-GAP
GENERAL-FINITE-ORBIT-RANK-OBSTRUCTION
```

Only `FOUND` permits C2.

## 7. GWSS-001M-C2-A — actual squared-orbit carrier

Proceed only after C1 `FOUND`.

The actual Xi finite carrier is

```text
pascalCenteredXiZeroDiskFinset R
```

The information quotient forced by evenness is the squared-coordinate image.

A natural carrier is:

```text
(pascalCenteredXiZeroDiskFinset R).image (fun z => z ^ 2)
```

You may introduce a named definition if it materially simplifies the proof.

Required facts:

```text
all q in the squared-orbit carrier satisfy q ≠ 0
carrier elements are distinct by Finset construction
carrier is finite
```

Do not claim the image cardinality equals the original zero count.

Do not assume both `z` and `-z` occur. The squared-orbit carrier is defined by actual points present in the window.

## 8. GWSS-001M-C2-B — representative discipline

The Mellin weight is evaluated on centered coordinates `z`, whereas the orbit carrier is represented by `q = z^2`.

Use one of the following clean approaches:

```text
A. choose one actual representative z for each q in the image finset;
B. prove the relevant spectral factor / Mellin weight is well-defined on squared orbits;
C. formulate C1 directly for an injected representative family whose squares enumerate the orbit carrier.
```

Prefer C if it avoids quotient infrastructure.

If representatives are chosen, prove:

```text
rep q ∈ pascalCenteredXiZeroDiskFinset R
(rep q)^2 = q
Pairwise distinct q -> Pairwise distinct squared representatives
```

Classical choice is acceptable; no new axiom is allowed.

## 9. GWSS-001M-C2-C — spectral-factor transfer

Retain the exact fixed-`ε` Mellin weight:

```text
H_{ε,τ}(z)
  = K_τ(z) * S_ε(z)
```

For every fixed finite actual window, reuse:

```text
eventually_pascalCenteredXiMellinSpectralWeight_ne_zero_on_actual_window
```

Do not replace `S_ε(z)` by `1`.

For a representative family `z_j`, prove the evaluation matrix is obtained from the bare matrix by nonzero column scaling:

```text
MellinMatrix = BareMatrix * diagonal(S_ε(z_j))
```

or directly prove the determinant identity

```text
det MellinMatrix
  = (∏ j, S_ε(z_j)) * det BareMatrix
```

with the exact orientation matching the chosen matrix convention.

This must work for arbitrary finite `n`, not only 2 or 3.

## 10. GWSS-001M-C2-D — full actual-window rank theorem

Target a theorem strong enough to state:

```text
for every finite actual Xi window R,
for every enumeration of one representative per distinct squared orbit,
for sufficiently small positive ε (or for some ε > 0 obtained from the existing eventual theorem),
there exist finitely many Mellin parameters τ_i
such that the Mellin evaluation matrix on those orbit representatives is invertible.
```

A nested-existence theorem is acceptable if cleaner than nested eventuality.

For example:

```text
∃ ε > 0,
  ∃ τ : Fin n -> ℝ,
    det (fun i j =>
      pascalCenteredXiMellinSecondDifferenceWeight ε (τ i) (z j)) ≠ 0
```

with all carrier and distinct-square hypotheses explicit.

Prefer nonzero `τ_i` if C1 supplies them.

The theorem must be about the **pre-existing Mellin family**. Do not use the carrier-dependent polynomial selector from GWSS-001T-A in the load-bearing proof.

## 11. Optional but valuable consequence — orbit-mass recoverability

Only if it follows cheaply from the invertible evaluation matrix, formalize the zero-side interpretation.

For each squared orbit `q`, define its actual multiplicity mass schematically as

```text
μ_R(q)
  = ∑ z in zeroWindow filtered by z^2 = q,
      pascalCenteredXiZeroMultiplicity z
```

Then every even weighted zero moment is a linear combination

```text
moment(τ_i) = ∑_q μ_R(q) * H_{ε,τ_i}(rep q)
```

and invertibility means the finite vector of Mellin moments determines the orbit-mass vector.

This would make the source-rank meaning explicit.

However:

- do not turn this into a large reconstruction API;
- do not claim recovery of `z` versus `-z` separately;
- do not call this an off-critical detector yet;
- stop if it materially expands the module beyond the rank theorem.

## 12. Final classification

If C1 and C2 both close, record:

```text
MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND
```

This means:

```text
on every finite actual Xi window,
the zero-independent Mellin family has full finite evaluation rank
on the distinct squared-orbit quotient forced by evenness.
```

It does **not** mean:

```text
RH proved
Weil positivity proved
prime-side control proved
horizontal term removed
off-critical witness completed
```

If C1 succeeds but C2 fails, use:

```text
GENERAL-BARE-MELLIN-RANK-FOUND
ACTUAL-WINDOW-FULL-RANK-TRANSFER-GAP
```

If a genuine information-theoretic obstruction appears, state it precisely and stop.

## 13. GWSS-002 authorization rule

Do not implement GWSS-002 in this assignment.

If and only if the final classification is

```text
MELLIN-FAMILY-ACTUAL-WINDOW-FULL-RANK-FOUND
```

then the report may state:

```text
GWSS-002 is eligible to start in the next assignment.
```

Do not start it automatically.

The next Gap after a successful C2 should be named:

```text
OFF-CRITICAL-MELLIN-WITNESS-GAP
```

## 14. Suggested implementation shape

Prefer one focused module, for example:

```text
DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralFiniteRankAudit
```

Avoid a chain of one-file-per-helper modules.

A second helper module is acceptable only if the general finite-dimensional linear-algebra theorem is genuinely reusable and would otherwise dominate the RH-specific file.

Suggested report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0014-GWSS-001M-C1-C2-general-finite-orbit-rank-report.md
```

## 15. Verification requirements

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinGeneralFiniteRankAudit
git diff --check
```

If another new module is added, build it explicitly as well.

Run `#print axioms` on the load-bearing general rank theorem and actual-window full-rank theorem.

Allowed standard axioms are the usual foundational ones already seen in this branch, such as:

```text
propext
Classical.choice
Quot.sound
```

Reject:

```text
sorry
admit
new axiom declarations
hidden RH-equivalent providers
```

If a public aggregation import is modified, run the corresponding root build. Otherwise report that it was intentionally unchanged.

## 16. Mandatory final report format

The report must begin with:

```text
Global objective:
zero configuration -> independent source -> off-critical detector -> arithmetic control -> centered-coordinate uniqueness -> RiemannHypothesis

Current GWSS stage:
GWSS-001M-C1/C2

Load-bearing boundary:
<exact providers used and forbidden providers not introduced>

Next unresolved Gap:
<one named Gap>
```

Then report exactly:

```text
C1 arbitrary-jet status
C1 general squared-coordinate rank status
C1 finite-evaluation status
C2 actual squared-orbit carrier status
C2 spectral-factor transfer status
C2 actual-window full-rank status
primary classification
GWSS-002 authorization status
verification
```

## 17. Stop conditions

Stop immediately and report instead of widening scope if any of the following occurs:

```text
arbitrary-order jet requires a missing analytic theorem not cheaply derivable from existing exp remainder API
Mathlib determinant/Vandermonde API causes a large infrastructure detour
finite function independence does not yield finite evaluation separation in the pinned API without substantial new abstract theory
actual squared-orbit representative construction requires quotient infrastructure disproportionate to the theorem
spectral-factor transfer loses well-definedness across z ↔ -z and cannot be repaired by representative formulation
an attempted provider silently uses RH / Weil positivity / horizontal decay / prime-side sign
```

In those cases classify the exact gap. Do not compensate by adding many local modules.

## 18. Mathematical target summary

The expected finite-rank structure is:

```text
K_τ(z)
  = sum_{r>=0} [2 z^(2r+2)/(2r+2)!] τ^(2r)

q_j = z_j^2

jet coefficient matrix
  ~ [q_j^(r+1)]

nonzero q_j + distinct q_j
  -> Vandermonde rank n
  -> Mellin functions linearly independent
  -> finite evaluation points with invertible bare matrix
  -> nonzero spectral-factor column scaling
  -> actual Xi squared-orbit full rank
```

This is the only target of this assignment.

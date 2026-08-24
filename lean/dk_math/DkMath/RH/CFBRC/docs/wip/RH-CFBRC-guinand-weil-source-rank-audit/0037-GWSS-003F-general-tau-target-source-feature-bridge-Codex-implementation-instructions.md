# GWSS-003F general-τ target source-feature bridge — Codex implementation instructions

Date: 2026-08-22

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only from the verified GWSS-003E frontier.

Trusted state:

```text
GWSS-001 source rank                         CLOSED
GWSS-002 finite off-critical Mellin witness CLOSED
GWSS-003A finite arithmetic identity        FOUND
GWSS-003B universal complex-linear phase    NOGO
GWSS-003C first-order homogeneous norm      NOGO
GWSS-003D independent vanishing scale       NOT FOUND
GWSS-003D real/conjugation route            API GAP / cancellation risk
GWSS-003D nonlinear positivity              SOURCE-SIDE CANDIDATE
GWSS-003E fixed-τ=0 polarization            FOUND
GWSS-003E positivity-only dominance         NOGO
GWSS-003E target-witness source bridge      GAP
current primary classification              TARGET-WITNESS-QUADRATICIZATION-BRIDGE-GAP
```

Implement only the next bounded stage:

```text
GWSS-003F-1  expose a nonzero-τ logarithmic-box source feature
GWSS-003F-2  prove the single-basis weight/source averaging identity
GWSS-003F-3  bridge the finite vertical arithmetic source for one nonzero τ
GWSS-003F-4  bridge the finite top-horizontal / whole source for one nonzero τ if feasible
GWSS-003F-5  lift the bridge through a finite synthesized witness Σ cᵢ H_{ε,τᵢ}
GWSS-003F-6  audit exact scalar transport for the GWSS-002 off-critical witness
GWSS-003F-7  record complex fixed-reference polarization with references 1 and I
GWSS-003F-8  select exactly one next-provider classification
```

This stage is a representation/source-interface implementation audit. It is not authorization to prove a new positivity theorem.

Do not start:

```text
GWSS-004 classical Guinand--Weil infrastructure
full Weil positivity criterion
Li criterion
T -> infinity
new zero-avoidance-height theory
new Xi growth theory
new source-rank family
new interpolation family
DkReal shrinking-window uniqueness
RiemannHypothesis deduction
```

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0035 instructions read
0036 report read
PascalCenteredXiMellinWitnessGramPolarizationBridgeAudit.lean read
PascalCenteredXiMellinWitnessQuantitativeHomogeneityAudit.lean read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiMellinArithmeticSpecialization.lean read
PascalCenteredXiPrimeSideQuadraticizationAudit.lean read
PascalCenteredXiFiniteArithmeticExplicitFormula.lean read
PascalCenteredXiExplicitFormulaHorizontalPairing.lean read
global objective
current GWSS stage
load-bearing bridge boundary
next unresolved Gap
```

The branch was 35 commits ahead and 0 behind `develop` immediately before this instruction file was created. Reconfirm the exact repository state; the repository is the source of truth.

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
GWSS-003F
```

Load-bearing boundary:

```text
The current GWSS-002 witness is

h_target(z) = Σ i, c_i * H_{ε,τ_i}(z),

and in the global full-rank construction every selected τ_i is nonzero.

GWSS-003E established that fixed-reference polarization genuinely retains a
linear cross-term, but the existing source-side quadraticization is specialized
to τ = 0.  The missing interface is therefore not yet an information-theoretic
obstruction: first test whether the nonzero-τ canonical Mellin basis itself can
be transported into the same finite source-feature language.
```

Forbidden shortcuts:

```text
assuming a general-τ source feature without proving its averaging identity
silently replacing H_{ε,τ} by the τ=0 quadratic weight
silently replacing the finite arithmetic approximant by the exact zeta RHS
using X -> infinity as an equality
removing the top-horizontal term
assuming synthesized coefficients are real
assuming conjugation-realness of h_target
calling shifted-energy nonnegativity an order theorem
using zeroMoment rewrite as an independent source-side sign theorem
RH
Weil positivity
Li criterion
unproved limit exchange
```

## 2. Exact nonzero-τ kernel already available

Reuse the existing theorem

```lean
pascalCenteredXiMellinSecondDifferenceWeight_eq_kernel_mul
    {ε τ : ℝ} (hτ : τ ≠ 0) (z : ℂ)
```

which gives

```text
H_{ε,τ}(z)
  = K_τ(z) * S_ε(z),

K_τ(z)
  = (exp(τ z) - 2 + exp(-τ z)) / τ²,

S_ε(z)
  = centeredMellinSpectralWeight (centeredMellinBoxApprox ε) z.
```

The Mellin box API already gives the logarithmic average

```text
S_ε(z)
  = (2 ε)^(-1) * ∫_{-ε}^{ε} exp(u z) du
```

for `ε > 0`.

Therefore the first candidate feature is not speculative. For `τ ≠ 0`, audit/prove the exact identity using a minimal definition such as

```text
Φ_{ε,τ}(z,u)
  := K_τ(z) * exp(u z)
```

with

```text
H_{ε,τ}(z)
  = (2 ε)^(-1) * ∫_{-ε}^{ε} Φ_{ε,τ}(z,u) du.
```

Names may follow local conventions. Do not over-generalize beyond what the current bridge needs.

## 3. GWSS-003F-1/2 — single-basis box feature

### F1. Nonzero-τ kernel feature

Prefer a focused reusable definition in a new module, for example:

```text
DkMath/RH/CFBRC/
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

A reasonable surface is:

```lean
noncomputable def pascalCenteredXiMellinGeneralTauBoxKernel
    (τ : ℝ) (z : ℂ) : ℂ := ...

noncomputable def pascalCenteredXiMellinGeneralTauBoxFeature
    (τ : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  pascalCenteredXiMellinGeneralTauBoxKernel τ z *
    Complex.exp ((u : ℂ) * z)
```

Do not add `ε` to the feature unless it is actually needed; the normalized integration interval already carries `ε`.

### F2. Weight averaging theorem

Prove, for `hε : 0 < ε` and `hτ : τ ≠ 0`, an exact theorem of shape

```text
H_{ε,τ}(z)
  = (2 ε)^(-1) * ∫ u in (-ε)..ε, Φ_τ(z,u).
```

This theorem must be obtained from existing kernel factorization and Mellin log-average theorems. It is a representation theorem only.

If this compact theorem fails because an expected Mellin log-average theorem is not public/reusable, stop and classify the exact API gap instead of recreating a large Mellin library.

## 4. GWSS-003F-3 — finite vertical source bridge

The finite arithmetic source at fixed cutoff `X` is the relevant object here. Keep distinct:

```text
finite arithmetic approximant at X
```

and

```text
exact ordinary-zeta RHS / X -> infinity endpoint.
```

Do not identify them.

Reuse the existing right-edge source decomposition from `PascalCenteredXiPrimeSideQuadraticizationAudit.lean` where possible:

```text
verticalAmplitude(W,X,t)
  = finite prime cutoff
    + archimedean correction
    + elementary correction.
```

For one nonzero real `τ`, define only the minimal general-τ vertical box feature required to prove

```text
weighted finite vertical source for H_{ε,τ}
  = (2 ε)^(-1) * ∫ u, aggregatedVerticalFeature(τ,W,X,u).
```

Expected pointwise structure:

```text
Φ_τ(node(t),u) * verticalAmplitude(W,X,t).
```

Preserve the correct contour orientation. If the convenient source surface is deoriented, name that fact explicitly. Do not compare an oriented `I dt` quantity to a deoriented quantity without an exact theorem.

Reuse finite-rectangle integrability/Fubini infrastructure already proved for `τ = 0` whenever it applies abstractly. If the only missing step is continuity of the new kernel on a compact rectangle, prove that locally. Do not rebuild the entire fixed-τ=0 quadraticization stack.

Legitimate partial result:

```text
GENERAL-TAU-VERTICAL-SOURCE-BRIDGE-FOUND
```

provided the top-horizontal/whole bridge is still honestly recorded as missing.

## 5. GWSS-003F-4 — top-horizontal and whole finite surface

The final useful interface must retain the top-horizontal term.

Audit whether the same nonzero-τ box averaging can be applied to the top node

```text
pascalOrdinaryToCentered
  (pascalSymmetricRectangleTopEdge x W.rectangle.T)
```

and the existing centered-Xi negative logarithmic derivative amplitude.

A minimal top feature should have schematic form

```text
Φ_τ(topNode(x),u) * topAmplitude(W,x).
```

Preserve the horizontal orientation exactly.

If the existing fixed-τ=0 code uses a source-derived horizontal symmetrization, do not assume it transfers automatically. Check the exact parity/conjugation facts of `K_τ` for real nonzero `τ` and prove only the compact identities needed.

Success at this stage means an exact finite whole-surface representation for one nonzero `τ`, including:

```text
finite prime cutoff
archimedean correction
elementary correction
top-horizontal contribution.
```

No `T -> infinity` is permitted or needed.

If vertical succeeds but horizontal becomes a substantial new analytic development, stop with the precise horizontal bridge gap rather than expanding scope.

## 6. GWSS-003F-5 — synthesized finite witness

Only after the single-basis bridge exists, lift it through

```lean
pascalCenteredXiMellinWitnessWeight ε τ c
```

where

```text
h_target(z) = Σ i, c_i * H_{ε,τ_i}(z).
```

For the target bridge relevant to GWSS-002, assume/use

```text
∀ i, τ i ≠ 0.
```

This is available in the global full-rank witness construction and avoids reopening the patched `τ = 0` branch.

Define a synthesized source feature by the same finite coefficient combination:

```text
Φ_target(...,u) = Σ i, c_i * Φ_{τ_i}(...,u).
```

Prove finite linearity from existing integral/source APIs rather than by postulating a provider structure.

Required success shape, modulo exact local orientation conventions:

```text
finiteWholeArithmeticSurface(h_target,W,X)
  = normalizedIntegral(Φ_target).
```

The theorem must concern the actual synthesized witness used by GWSS-002, not a new unrelated coefficient family.

## 7. GWSS-003F-6 — off-critical scalar transport

Reuse the GWSS-003C factorization

```text
h_off = qIm * h_mass
```

with real

```text
qIm = targetSquaredOrbit.im.
```

If the synthesized source feature bridge is linear in the witness coefficients, prove the corresponding source-feature factorization

```text
Φ_off = qIm * Φ_mass
```

and, if the whole aggregate has been built,

```text
WholeSource_off = qIm * WholeSource_mass.
```

This is not a contradiction theorem. Its purpose is to certify that the source bridge faithfully transports the same target scalar and is not secretly introducing new information.

If this scalar transport fails, explain exactly which part of the feature construction is nonlinear and whether that failure is genuine new information or only a definition mismatch.

## 8. GWSS-003F-7 — complex fixed-reference polarization

Do not require the synthesized witness or its source feature to be conjugation-real.

The inverse-matrix coefficients are complex. Therefore record the generic complex polarization identities using two fixed references.

For arbitrary `F : ℂ`, prove compact facts of the exact mathematical shape

```text
normSq(F + 1) - normSq(F - 1) = 4 * F.re
normSq(F + I) - normSq(F - I) = 4 * F.im
```

with whatever coercions Lean requires.

Also record the real-scalar version if useful:

```text
q : ℝ

reference 1  -> 4 q * F.re
reference I  -> 4 q * F.im.
```

These are algebraic readout certificates only. They do not supply shifted-energy order.

This avoids reopening the restricted-real witness route merely to use polarization.

## 9. Information firewall

Even if the full target source bridge is found, do not claim RH progress from positivity alone.

The following remain invalid as independent providers:

```text
E_plus >= 0 and E_minus >= 0
therefore E_plus >= E_minus

or

source polarization identity
therefore a sign of the source surface
```

The 003E no-go remains load-bearing.

If the bridge is found, the next unresolved question is whether arithmetic/source structure independently provides one of:

```text
P1: a shifted-energy ordering
P2: shifted-energy equality
P3: a quantitative asymmetric gap
```

for the actual synthesized target witness.

Do not prove or assume P1/P2/P3 in this assignment.

## 10. Required classification

End with exactly one primary classification from:

```text
SYNTHESIZED-WITNESS-WHOLE-SOURCE-BRIDGE-FOUND
GENERAL-TAU-VERTICAL-BRIDGE-FOUND-HORIZONTAL-GAP
TARGET-WITNESS-SOURCE-BRIDGE-REPRESENTATION-GAP
TARGET-WITNESS-QUADRATICIZATION-BRIDGE-OBSTRUCTION
TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP
GWSS-003F-IMPLEMENTATION-API-GAP
```

Use `TARGET-WITNESS-SHIFTED-ENERGY-DOMINANCE-GAP` only if the exact synthesized whole-source bridge, including horizontal compatibility and off-critical scalar transport, is already proved and the remaining missing information is genuinely P1/P2/P3.

Use `SYNTHESIZED-WITNESS-WHOLE-SOURCE-BRIDGE-FOUND` only if the bridge itself is the primary result and a separate dominance decision is deliberately deferred. The report must still name the next Gap.

Use `TARGET-WITNESS-QUADRATICIZATION-BRIDGE-OBSTRUCTION` only for a proved structural incompatibility, not for a difficult Lean proof.

Secondary findings may include:

```text
nonzero-τ weight box averaging: FOUND / GAP
general-τ vertical feature: FOUND / GAP
general-τ horizontal feature: FOUND / GAP
single-basis whole source bridge: FOUND / GAP
finite synthesized source feature: FOUND / GAP
off-critical source scalar transport: FOUND / GAP
complex reference-1 polarization: FOUND
complex reference-I polarization: FOUND
independent shifted-energy dominance: NOT FOUND
```

## 11. GWSS-004 authorization rule

GWSS-004 remains unauthorized in this assignment.

Even if the synthesized whole-source bridge succeeds, stop at the exact source-side dominance Gap. Do not import or formalize classical Guinand--Weil or Weil positivity yet.

A later review may authorize GWSS-004 only if the remaining minimal provider has been identified precisely enough that a bounded classical fragment can be named without importing an RH-equivalent black box.

## 12. Preferred outputs

Preferred focused Lean module:

```text
DkMath/RH/CFBRC/
PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit.lean
```

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0038-GWSS-003F-general-tau-target-source-feature-bridge-report.md
```

Keep the implementation bounded. Reuse existing fixed-τ=0 integrability and source-amplitude infrastructure aggressively, but do not silently inherit τ=0 algebra that fails for nonzero τ.

## 13. Verification

Required focused build:

```bash
./lean-build.sh DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessGeneralTauSourceBridgeAudit
```

Also run:

```bash
git diff --check
```

For load-bearing public theorems, run `#print axioms` or the repository's normal axiom-audit mechanism.

No:

```text
sorry
admit
native_decide
new axiom
RH assumption
Weil criterion
Li criterion
unproved limit exchange
```

Expected standard axiom footprint remains within:

```text
propext
Classical.choice
Quot.sound
```

## 14. Stop condition

Stop after the 0038 report and exactly one primary classification.

Do not start GWSS-004.

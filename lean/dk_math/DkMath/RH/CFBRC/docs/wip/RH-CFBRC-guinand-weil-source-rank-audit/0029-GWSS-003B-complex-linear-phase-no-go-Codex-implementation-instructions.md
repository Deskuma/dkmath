# GWSS-003B complex-linear phase no-go / real-structure compatibility audit — Codex implementation instructions

Date: 2026-08-21

Repository: `Deskuma/dkmath`

Branch: `wip/RH-CFBRC-guinand-weil-source-rank-audit-260820-v0`

## 0. Mission

Continue only after GWSS-003A has closed with:

```text
MELLIN-WITNESS-FINITE-ARITHMETIC-IDENTITY-FOUND-CONTROL-GAP
```

Trusted frontier:

```text
GWSS-001
  canonical Mellin source rank CLOSED

GWSS-002
  exact off-critical detector CLOSED

GWSS-003A
  exact finite arithmetic transport FOUND
  independent arithmetic control NOT FOUND
```

Implement and audit only the next bounded stage:

```text
GWSS-003B-1  expose complex scalar linearity of the finite arithmetic RHS
GWSS-003B-2  prove the universal phase-control no-go on a complex-linear admissible class
GWSS-003B-3  audit whether a smaller real / conjugation-compatible weight class could carry an independent phase theorem
GWSS-003B-4  audit whether the existing off-critical detector can be synthesized inside such a smaller class without losing the detector
GWSS-003B-5  classify whether the next provider must be target-specific quantitative control, a real-structure theorem, or a genuinely nonlinear positivity theorem
```

Do **not** start:

```text
GWSS-004 classical Guinand--Weil infrastructure
full Weil positivity
Li criterion
T -> infinity horizontal-term removal
new zero-avoidance-height theory
new Xi growth theory
RH deduction
DkReal uniqueness
new source-rank family
```

This assignment is a **structure/no-go audit**, not a large analytic estimate project.

## 1. Mandatory orientation before editing

Before any edit, report:

```text
current branch
current HEAD
working-tree status
Lean toolchain
0027 instructions read
0028 report read
PascalCenteredXiMellinWitnessArithmeticControlAudit.lean read
PascalCenteredXiMellinOffCriticalWitnessAudit.lean read
PascalCenteredXiMellinArithmeticSpecialization.lean read
PascalCenteredXiFiniteArithmeticExplicitFormula.lean read
PascalCenteredXiPrimeRightEdgeTransport.lean read
PascalCenteredXiExplicitFormulaHorizontalPairing.lean read
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
GWSS-003B
```

Load-bearing provider boundary:

```text
The off-critical detector already gives a target-dependent admissible weight h
with a nonzero real zeroMoment

  zeroMoment(h)
    = ((z^2).im : ℂ) * orbitMass(z^2)

and hence the finite arithmetic RHS is the nonzero pure-imaginary scalar

  -(2*pi*i) * zeroMoment(h).

Any new contradiction must come from an arithmetic/analytic property of h or
of a restricted admissible class that is proved independently of this zero-side
identity.
```

Forbidden providers:

```text
RH
classical Weil positivity
Li criterion
functional-equation transport promoted as new information
criticalMirror / conjugation merely reindexed as a new source
fixed-Xi defect vanishing
unproved T -> infinity decay
unproved limit exchange
reverse Cauchy--Schwarz / reverse triangle
post-hoc Gram or norm-square positivity without an independent theorem
phase facts obtained by rewriting the already-known zeroMoment
```

## 2. Key structural observation to formalize

The finite arithmetic RHS is linear in the weight.

At the level of the current named object:

```lean
pascalCenteredXiFiniteArithmeticRHS h W
```

and at each individual arithmetic surface, multiplication of a weight by a
complex scalar should multiply the corresponding observable by the same scalar.

This matters because the current admissible contracts

```text
Differentiable ℂ h
PascalCenteredEvenWeight h
```

are closed under multiplication by `Complex.I`.

Therefore a universal phase theorem on the entire complex-linear admissible
class has a strong no-go property.

Conceptually, for a complex-linear functional `F`, if both

```text
F(h).im = 0
F(I * h).im = 0
```

hold, then the second equation says the real part of `F(h)` is zero as well.
Hence `F(h) = 0`.

Similarly, if `F(h).re = 0` for every admissible `h`, applying the claim to
`I * h` forces `F(h).im = 0` and therefore `F(h) = 0`.

This is the main semantic question of GWSS-003B:

```text
Can a nontrivial universal real-axis / imaginary-axis phase theorem coexist
with the current complex-linear admissible weight class?
```

Expected answer: only if the entire functional vanishes on that class, or if
the admissible class is restricted so that multiplication by `I` is no longer
allowed.

Do not assume this conclusion; prove the relevant finite algebra in Lean.

## 3. GWSS-003B-1 — complex scalar linearity

### B1. Weight scaling

Expose compact helper theorems showing that admissibility is preserved by a
complex scalar, at least for the special scalar `Complex.I`.

Preferred shapes:

```lean
theorem pascalCenteredEvenWeight_const_mul
    {h : ℂ -> ℂ} (heven : PascalCenteredEvenWeight h) (a : ℂ) :
    PascalCenteredEvenWeight (fun z => a * h z) := by
  ...
```

and, if needed,

```lean
theorem differentiable_const_mul_weight
    {h : ℂ -> ℂ} (hh : Differentiable ℂ h) (a : ℂ) :
    Differentiable ℂ (fun z => a * h z) := by
  ...
```

Use local private helpers if public names would pollute the API.

### B2. RHS scalar linearity

Prove a focused theorem such as:

```lean
theorem pascalCenteredXiFiniteArithmeticRHS_const_mul
    (a : ℂ) (h : ℂ -> ℂ)
    (W : PascalCenteredXiResidueTransportWindow) :
    pascalCenteredXiFiniteArithmeticRHS (fun z => a * h z) W =
      a * pascalCenteredXiFiniteArithmeticRHS h W := by
  ...
```

Preferred proof route:

```text
unfold named RHS
use interval-integral const-multiplication on each finite term
use top-horizontal integral linearity
ring
```

If integral API friction is large, an alternative proof through the generic
finite explicit formula is **not acceptable as an independent arithmetic
linearity proof** if it rewrites through `zeroMoment`.  The point here is to
expose arithmetic-side linearity directly.

A small local helper for interval integrals is acceptable.

### B3. Zero-moment scalar linearity as comparison only

It is acceptable to also prove:

```text
zeroMoment(a * h) = a * zeroMoment(h)
```

but label it as comparison/bookkeeping.  It must not substitute for B2.

## 4. GWSS-003B-2 — universal phase no-go

### C1. Generic finite complex algebra helper

Prefer first proving a theorem independent of Xi.

For example:

```lean
theorem complex_eq_zero_of_im_eq_zero_and_I_mul_im_eq_zero
    (w : ℂ)
    (h₁ : w.im = 0)
    (h₂ : (Complex.I * w).im = 0) :
    w = 0 := by
  ...
```

or an equivalent theorem using real parts.

A direct `ext <;> simp`/`norm_num`/ring proof is preferred.

### C2. Arithmetic functional no-go: real-valued version

Prove a semantic theorem of the following strength:

```lean
theorem pascalCenteredXiFiniteArithmeticRHS_eq_zero_of_universal_im_zero
    {h : ℂ -> ℂ}
    (hh : Differentiable ℂ h)
    (heven : PascalCenteredEvenWeight h)
    (W : PascalCenteredXiResidueTransportWindow)
    (hphase :
      forall g : ℂ -> ℂ,
        Differentiable ℂ g ->
        PascalCenteredEvenWeight g ->
        (pascalCenteredXiFiniteArithmeticRHS g W).im = 0) :
    pascalCenteredXiFiniteArithmeticRHS h W = 0 := by
  ...
```

Equivalent packaging is acceptable and a more local theorem is preferred if
it avoids quantifying over all functions.

A very compact alternative is:

```text
If RHS(h).im = 0 and RHS(I*h).im = 0,
then RHS(h) = 0.
```

This local two-weight theorem is enough to expose the no-go and may be the
cleanest Lean statement.

### C3. Imaginary-axis version

If cheap, also prove the analogous result for a universal condition

```text
RHS(g).re = 0.
```

Do not overbuild a general theory of complex-linear real-valued functionals.

### C4. Classification meaning

If C1-C3 succeed, state explicitly:

```text
A universal theorem saying that the finite arithmetic RHS always lies on one
fixed real line through the origin is incompatible with a nonzero complex-linear
RHS on an admissible class closed under multiplication by I.
```

This does **not** prove that no target-specific phase theorem can exist.
It only excludes a universal phase restriction on the full complex-linear
admissible class.

## 5. GWSS-003B-3 — real / conjugation-compatible subspace audit

A phase theorem can still be meaningful on a smaller real form not closed
under multiplication by `I`.

Audit the repository for a weight condition resembling one of:

```text
h(conj z) = conj(h z)
h(conj z) = -conj(h z)
real coefficients in a canonical basis
real-valuedness on the imaginary axis / right-edge paired path
```

Do not invent a large new abstraction unless one very small predicate is
clearly useful.

If no suitable predicate exists and a short focused definition helps, a local
candidate is acceptable:

```lean
def PascalCenteredConjugationRealWeight (h : ℂ -> ℂ) : Prop :=
  forall z, h (conj z) = conj (h z)
```

Use the exact Mathlib conjugation syntax available in the pinned toolchain.

### D1. Canonical Mellin basis audit

For real `ε` and real `τ`, audit whether each canonical Mellin basis weight
satisfies the chosen conjugation-real condition.

Do not assume it merely because the parameters are real.

Preferred evidence routes:

```text
centeredMellinBoxApprox has real data
Complex.exp conjugation law
finite real interval integral conjugation law
existing explicit formula for the spectral weight
```

If proving this requires a nontrivial new integration/conjugation library,
stop and classify an API gap instead of broadening the assignment.

### D2. Synthesized witness coefficient audit

The actual GWSS-002 witness uses coefficients obtained from a row of
`Matrix.nonsingInv` and then scaled by `q0.im`.

Audit whether anything in the current proof guarantees those coefficients are:

```text
all real
conjugate-paired
compatible with a real/conjugation-real witness condition
```

Do not infer this from determinant nonvanishing.

If no such theorem exists, say so explicitly.

## 6. GWSS-003B-4 — compatibility of real structure with the detector

This is the most important part after the no-go.

The off-critical detector currently isolates one squared orbit `q0` and returns

```text
q0.im * mass(q0).
```

A conjugation-compatible weight may be unable to isolate one member of a
conjugate pair independently.

Therefore audit, without assuming new zeta symmetry theorems, the following:

```text
1. Does the repository prove that conjugation preserves the actual centered-Xi zero window?
2. Does it prove equality of multiplicities under conjugation?
3. Does conjugation send squared orbit q to conj(q)?
4. If both q and conj(q) are present, what does a conjugation-real weight do to their combined zeroMoment contribution?
5. Can the current detector q.im * mass(q) survive on the restricted real form, or does the pair symmetry force cancellation / loss of single-orbit extraction?
```

Important firewall:

```text
Do not use conjugation as a new independent source.
```

Here conjugation is only being audited as a **restriction on the witness class**
needed for a possible arithmetic phase theorem.

### E1. Minimal abstract countermodel is allowed

If the actual zeta conjugation API is missing, it is acceptable to prove a
small finite two-coordinate model showing the structural tension:

```text
q and conj(q) with equal positive masses
conjugation-real test weight
```

versus

```text
single-orbit antisymmetric detector proportional to q.im.
```

Use such a model only to classify compatibility; do not claim it as an actual
zeta theorem.

### E2. Do not force a conclusion

Possible legitimate outcomes include:

```text
REAL-STRUCTURE-WITNESS-COMPATIBILITY-FOUND
REAL-STRUCTURE-DETECTOR-CANCELLATION-OBSTRUCTION
CONJUGATION-SYMMETRY-API-GAP
```

## 7. Existing prime-side norm majorant — mandatory correction to the 003A inventory

`PascalCenteredXiPrimeRightEdgeTransport.lean` already contains the unconditional
finite vertical majorant

```text
norm_pascalPrimePowerPHZFiniteUpTo_rightEdge_le_verticalMajorant
```

and an integrand domination of schematic form

```text
||primeCutoffIntegrand(h, sigma, X, t)||
  <= ||h(centeredRightEdge)|| * pascalVonMangoldtVerticalMajorant sigma.
```

This is genuine arithmetic-side norm control and must be recorded accurately.

However, audit its exact usefulness for the GWSS-002 witness:

```text
Does it force a phase?                 probably no; prove/audit
Does it force vanishing?               probably no; prove/audit
Is it uniform in X and t?              yes, as stated by the existing theorem
Does the remaining bound depend on h?  yes
Does h depend on target coefficients?  yes
```

The report should correct any over-broad statement from 0028 that there was no
finite norm control at all.  The accurate distinction is expected to be:

```text
finite prime-side norm majorant exists,
but no currently known bound makes it small/zero or phase-restricted strongly
enough to contradict the fixed nonzero detector.
```

Do not rewrite historical reports unless necessary; the new 003B report may
supersede the inventory statement explicitly.

## 8. GWSS-003B-5 — decide the next provider class

At the end, classify which provider class remains mathematically viable.

### Route P — universal complex-linear phase

If the no-go theorem succeeds, classify this route as closed:

```text
UNIVERSAL-COMPLEX-LINEAR-PHASE-PROVIDER-NOGO
```

### Route R — restricted real/conjugation-compatible witness

If the canonical Mellin family and detector can be restricted to a suitable
real form while retaining a nonzero off-critical detector, classify:

```text
REAL-STRUCTURE-MELLIN-WITNESS-PHASE-ROUTE-OPEN
```

and name the exact next missing arithmetic theorem.

If the detector is destroyed or conjugate-pair cancellation is structural,
classify:

```text
REAL-STRUCTURE-DETECTOR-CANCELLATION-OBSTRUCTION
```

### Route Q — target-specific quantitative estimate

If universal phase is closed and real-structure compatibility is unavailable,
but the finite prime majorant or another independent norm theorem could in
principle bound the target witness, classify:

```text
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED
```

Then name the first missing quantity, e.g. coefficient norm / basis-weight
right-edge norm / top-horizontal norm.

### Route N — nonlinear positivity

If the only plausible mechanism left is a quadratic/nonlinear positivity
statement, say so, but do not import it.

Possible classification:

```text
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
```

Only this type of precise conclusion may authorize a later GWSS-004 decision
audit.  Do not start classical Weil theory in this assignment.

## 9. Preferred focused Lean output

Prefer one focused module:

```text
DkMath/RH/CFBRC/PascalCenteredXiMellinWitnessPhaseNoGoAudit.lean
```

Do not modify the existing 003A module unless a tiny reusable lemma clearly
belongs there.

Required report:

```text
docs/wip/RH-CFBRC-guinand-weil-source-rank-audit/
0030-GWSS-003B-complex-linear-phase-no-go-report.md
```

The module should remain compact.  A proof of the complex-linear phase no-go
plus a bounded real-structure audit is preferable to hundreds of lines of
term estimates.

## 10. Stop / success classifications

End with exactly one primary classification from:

```text
UNIVERSAL-COMPLEX-LINEAR-PHASE-PROVIDER-NOGO
REAL-STRUCTURE-MELLIN-WITNESS-PHASE-ROUTE-OPEN
REAL-STRUCTURE-DETECTOR-CANCELLATION-OBSTRUCTION
CONJUGATION-SYMMETRY-API-GAP
TARGET-SPECIFIC-QUANTITATIVE-CONTROL-REQUIRED
NONLINEAR-POSITIVITY-PROVIDER-DECISION-REQUIRED
GWSS-003B-IMPLEMENTATION-API-GAP
```

The report may include secondary findings, especially:

```text
finite prime vertical norm majorant: FOUND
universal full-class phase provider: FOUND or NOGO
canonical Mellin conjugation-realness: FOUND / GAP
synthesized coefficient real-structure: FOUND / NOT FOUND
single-orbit detector compatibility: FOUND / OBSTRUCTED / UNRESOLVED
top-horizontal independent control: still OPEN unless genuinely changed
```

## 11. GWSS-004 authorization rule

GWSS-004 remains unauthorized unless this audit identifies a precise
**nonlinear/classical positivity fragment** as the minimal remaining provider.

Do not authorize GWSS-004 merely because universal phase control fails.

If the result is instead a target-specific quantitative gap, remain within
GWSS-003 and specify the next bounded quantitative theorem.

## 12. Verification

At minimum run:

```text
lake build DkMath.RH.CFBRC.PascalCenteredXiMellinWitnessPhaseNoGoAudit
git diff --check
```

Inspect `#print axioms` for the load-bearing no-go and compatibility theorems.

Requirements:

```text
NO sorry
NO admit
NO native_decide proof shortcut
NO new axiom
```

Expected axiom footprint remains:

```text
propext
Classical.choice
Quot.sound
```

Report any deviation.

## 13. Mandatory report orientation

The 0030 report must state:

```text
global objective
current GWSS stage
load-bearing provider boundary
complex scalar linearity status
universal phase no-go status
finite prime majorant status
canonical Mellin real/conjugation structure status
synthesized coefficient real-structure status
detector compatibility with any restricted real form
top-horizontal status
primary classification
next unresolved Gap
GWSS-004 authorization status
verification
```

## 14. Route-drift firewall

Stop if the assignment begins expanding into any of:

```text
large Gamma estimates
large zeta growth theory
new horizontal zero-avoidance machinery
full Guinand-Weil theorem
full Weil criterion
Li coefficients
DkReal shrinking windows
```

without first changing the primary classification above.

The point of GWSS-003B is to decide **what kind of arithmetic control can even
be logically compatible with the current complex-linear witness framework**.

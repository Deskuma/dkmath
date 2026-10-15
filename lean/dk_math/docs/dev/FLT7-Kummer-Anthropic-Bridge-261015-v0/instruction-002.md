> **Historical instruction — COMPLETE.** The later repository policy forbids committing build logs, raw evidence dumps and disposable probes. Keep only code, useful regression tests and concise mathematical reports.

# instruction-002 — concrete cyclotomic seventh-power unit bridge

Date: 2026-10-15 JST  
Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Lean project root: `lean/dk_math/`  
Research docs: `docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/` (relative to Lean root)  
Gate: **002 / implementation of exactly G1–G3; STOP and report for review**.

## 0. Source of truth, workspace, and Gate-001 cleanup

1. Read repository-root `AGENT.md`, this folder's `README.md`,
   `ROADMAP.md`, `bridge-matrix-001.md`, `report-001.md`,
   `review-001.md` and `evidence/001-axiom-summary.txt`.
2. Confirm `git status --short`, branch and HEAD. Preserve **all** local
   uncommitted work. Refresh the branch from GitHub safely if necessary;
   never hard-reset a dirty workspace.
3. The GitHub repository at its actual checkout HEAD is the DkMath
   canonical source. The Anthropic source is pinned to
   `https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2`.
   Read `P2M/Sol/S_flt_regular.lean`, especially the actual
   `P2MW.S_flt_regular.FltRegular.eq_pow_prime_of_unit_of_congruent`.
4. Correct Gate-001 *narrative source pointers* to use canonical pinned
   upstream URLs/file:line and DkMath paths. Existing research artifacts
   mention temporary comparison copies as if they were in this directory:
   they are **not a persistent input contract**. Preserve historical raw
   command evidence but do not claim such copies can be cloned or are in Git.
   If making a substantive correction to the old report, add an explicitly
   labeled erratum rather than silently altering its original results.
5. Do not specify `LEAN_NUM_THREADS`; Codex chooses build parallelism.

## 1. Goal and existing proof resources

Prove the actual existing proposition
`DkMath.FLT.Seven.DegreeSixKummerUnitLemmaAtSeven`, which currently is
a **definition of a `Prop`**, not a theorem.

Canonical local definitions:

```lean
-- namespace DkMath.FLT.Seven
def DegreeSixUnitCongruentToRationalModSeven
    (u : SevenCyclotomicDegreeSixInt.Ring) : Prop :=
  ∃ m : ℤ, ¬ (7 : ℤ) ∣ m ∧ u - (m : SevenCyclotomicDegreeSixInt.Ring) ∈ sevenIdeal

def DegreeSixKummerUnitLemmaAtSeven : Prop :=
  ∀ u : SevenCyclotomicDegreeSixInt.Ringˣ,
    DegreeSixUnitCongruentToRationalModSeven
      (u : SevenCyclotomicDegreeSixInt.Ring) →
    ∃ v : SevenCyclotomicDegreeSixInt.Ringˣ, u = v ^ 7
```

Reuse; don't reprove:

- `DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicUnitCongruence.lean`:
  `sevenIdeal`, integer congruence and `star_sub_int_mem_sevenIdeal`.
- `.../PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean`:
  `quadraticNormUnit`, `starUnit`, `ofRealUnit`,
  packet-specific norm-one/congruence/square arguments.
- `.../PrimeTraceOneDirectCyclotomicCMTorsionPhase.lean`:
  `relativeNormOneScalarUnitAtSeven_unconditional`,
  a theorem proving a norm-one unit congruent to 1 mod 7 is 1.
- `.../SevenRealCubicUnitClass.lean`:
  `SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero`.
- `.../PrimeTraceOneDirectCyclotomicCMUnitPhase.lean`:
  ring-of-integers equivalence and compatible unit maps.
- `.../PrimeTraceOneDirectCyclotomicChosenTail.lean`,
  `.../PrimeTraceOneDirectCyclotomicUnitCongruence.lean`:
  chosen-factor `Q=γ^7` construction and unit congruence.
- Gate-001 matrix's 17 indexed matches and exact Lean `#check` output.

The general Kummer congruence theorem applies to all units satisfying its
congruence, **not** every unit. The chosen packet already achieves
`L = ramifiedUniformizer * γ^7`; duplicating that proof would yield no
new capability. Do not solve the gate by assuming a chosen packet.

## 2. Target API — three obligations, in this order

Suggested new module:
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`.
Namespace: `DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt`.
Use the narrowest existing import chain (initially
`PrimeTraceOneDirectCyclotomicCMTorsionPhase`), but adjust if required
by real unit classification. Exact declarations may be renamed minimally
to conform to actual source namespaces, recording every change.

### G1 — eliminate the CM-relative phase

```lean
theorem unit_eq_starUnit_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    u = starUnit u := by
  -- real proof only
```

Suggested proof:
from `h` and preservation of integer casts under `star`, prove
`((u : Ring) - star u) ∈ sevenIdeal`. For
`delta = u / starUnit u`, show
`quadraticNormUnit delta = 1` and
`((delta : Ring)-1) ∈ sevenIdeal`. Apply the existing
`relativeNormOneScalarUnitAtSeven_unconditional`; hence `delta=1`.
Avoid assuming `u` is fixed by `star` at the outset.

### G2 — real norm is a seventh power

```lean
theorem exists_normUnit_seventhPower_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    ∃ v : SevenRealCubicIntˣ, quadraticNormUnit u = v ^ 7 := by
  -- real proof only
```

**This is the mathematical bottleneck of Gate 002.** First check the
actual type of `quadraticNormUnit`, the embedding of `ℤ` into the
real-cubic ring, its modulus-7 ideal and exact coordinate projections.
Prove an intermediate congruence
`quadraticNormUnit u ≡ m^2 (mod 7)` by ring-hom compatibility.
Then establish a **genuine** implication from that congruence to
`SevenRealCubic.projectiveLog (Additive.ofMul (quadraticNormUnit u)) = 0`.
Only then apply the existing
`SevenRealCubic.unit_isSeventhPower_iff_projectiveLog_eq_zero`.

Do not infer projective-log vanishing just from a mod-7 norm congruence
without an injectivity / unit-class / coordinate theorem showing it.
An exploratory finite residue calculation may aid design, but is not
the proof. If this implication is false or cannot be obtained from the
existing hypotheses, stop: report the minimal exact gap (and a concrete
counterexample if one exists). A documented Outcome B/C is acceptable.

### G3 — inhabit the existing unit-lemma Prop

```lean
theorem degreeSixKummerUnitLemmaAtSeven :
    DegreeSixKummerUnitLemmaAtSeven := by
  -- combine G1 + G2
```

For a unit `u` satisfying the original scalar congruence:
G1 makes `u = starUnit u`; G2 supplies `v` with
`quadraticNormUnit u = v^7`. Use
`u^2 = (ofRealUnit v)^7`, then the Bézout exponent identity
`(t^4*u⁻¹)^7 = u` (when `t^7=u^2`).
The local `RelativeNormPhase` module contains private implementations
of the square and Bézout argument. They are not automatically accessible
from a new module: either make an appropriately reviewed reusable public
helper in a separate small edit or reproduce only the very small group
calculation; don't duplicate the packet-specific framework.

G3 must use h concretely. Do not assert `∀u:Ringˣ, ∃v, u=v^7`
without congruence. Don't declare this theorem as an axiom or trivially
inhabit the Prop through an unrelated logical implication.

## 3. Tests and audits

- Put the focused production implementation in the indicated module.
  Do not silently import it into a broad FLT7 facade, `DkMath.Lib.*`,
  or the default library during Gate 002; report suggested future wiring.
- Add a small opt-in regression file such as
  `DkMathTest/FLT/Seven/KummerAnthropicBridgeAudit002.lean`.
  Include `#check` for G1–G3, the original existing spec, and a
  typechecked application of G3 to an arbitrary congruent unit (no packet).
- Run focused `lake build` for the new module from `lean/dk_math`, and
  the scratch test through the normal project toolchain. Choose build
  parallelism based on the environment; do not hard-code a thread count.
- `#print axioms` for G1, G2, G3 (if proved), and any exported helpers.
  Required dependency set: subset of
  `[propext, Classical.choice, Quot.sound]`. Record precise failed
  builds too. Avoid new `sorry`, `admit`, `axiom`, vacuous `True`
  targets, classical postulates external to the standard set, and
  imports of finished FLT theorems.
- Compare the final implementation with the Gate-001 matrix and
  `#print axioms` baseline. G1–G3 are not to be marked accepted
  based only on a `#check` of their Prop signatures.

## 4. Stop rule and deliverables

Write in `docs/dev/FLT7-Kummer-Anthropic-Bridge-261015-v0/`
relative to Lean root:

1. `report-002.md`: exact branch/HEAD, source paths:lines, theorem
   statements, proven/blocked status of **each G1/G2/G3**, build commands
   axiom sets, changed files, source-provenance correction
   and any unaddressed obstacle. State Outcome A only for genuinely
   kernel-checked target proofs, otherwise Outcome B/C with evidence.
2. No evidence/log artifacts. Keep local outputs outside Git.
3. The opt-in test module and new implementation source **only if an
   honest proof is obtained**. Don't leave a public theorem with `sorry`.
4. Suggested Gate 003 after verification: a **new research design** for
   the enlarged cyclotomic integer descent state (unit + π-adic exponent),
   not reinvention of a chosen-factor constructor already complete.

**STOP after Gate 002. Do not commit, push, open PR, merge, or begin
Gate 003.** Present all changes and the report for human/Wise Wolf review.

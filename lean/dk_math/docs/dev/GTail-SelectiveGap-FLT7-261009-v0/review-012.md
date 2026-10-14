# Review 012 — typed Eisenstein norm-square receiver

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Decision: **APPROVED — Step 012 COMPLETE / Outcome B**

## Reviewed material

GitHub source inspection of:
- `DkMath/Lib/NumberTheory/GTailSevenNormReadout.lean` (60 lines);
- `DkMath/FLT/Seven/GTailNormReadoutAudit.lean` (35 lines);
- their two direct tests (70 and 32 lines);
- `report-012.md`, `source-inventory-012.md`, and Steps 004–005/010–011 relevant contracts;
- existing `TraceOneQuadratic`, `EisensteinCoordinates`, `EisensteinLatticeLanding` for mathematical ownership and limitation checks.

**Static review only.** The successful final focused builds, Step 011 regressions and six new standard-axiom results are reported by Codex, not independently rerun here.

## Findings

1. `gtailSevenNormCoord a b := eisensteinCoord (a:ℤ) (-(b:ℤ))` is the correct sign convention. The existing `eisensteinCoord a b` produces the **minus** mixed term, while `gtailSevenNormCoord` is literally `⟨a,b⟩ : TraceOneInt (-1)`, whose existing ring norm is the intended **plus** polynomial `a²+ab+b²`.
2. `norm_gtailSevenNormCoord` is an honest integer-norm equality for every natural a,b. The natural/integer cast is explicit.
3. `norm_gtailSevenNormCoord_sq` uses `traceOne_norm_mul` (after `pow_two`), rather than introducing a new ad hoc quartic 'norm'.
4. `dvd_quadratic_iff_dvd_gtailSevenNormCoord` is correct for any natural q, **including q=0**, as an equivalence with integer divisibility of the **norm value**. It does not assert ring-element divisibility, splitting of (q), or an ideal above q.
5. `selectedBody_seven_interior_eq_norm_square` instantiates the generic selected Body theorem at `ℤ` and then substitutes the typed norm-square result. It remains neutral: no Fermat hypotheses or FLT import enters the Lib closure.
6. `focused_gtail_eq_norm_square` casts the already established **natural-valued GTail** product to `ℤ` and rewrites its quadratic-square value. It does not silently replace the natural GTail by an integer re-evaluation. It assumes exactly `Fermat7Equation a b c` and `a+b=c+g`, without positivity, primitivity or a unit assumption.
7. The neutral numeric checks distinguish `norm(eisensteinCoord 5 8)=49` from `norm(gtailSevenNormCoord 5 8)=129`, check the ring-square coordinates `⟨-39,144⟩`, `norm α²=16641`, and selected Body `60573240`. The explicit different norm-one elements are a valid witness of norm **noninjectivity**, but not a proof of a claimed nonsquare-unit obstruction.
8. The zero-coordinate Fermat boundary used to test the conditional owner is satisfiable; it is not a fabricated positive FLT7 solution.
9. Codex recorded final successful builds for all four new targets and both Step 011 regression modules. A single initial neutral-test elaboration issue was repaired without changing the theorem. The one new helper definition has no axiom dependencies; six public theorem printouts use only standard foundations. The new sources contain no placeholders/new axioms/unsafe or FLT closure call. Neutral→FLT dependency remains absent.

## Scope/novelty boundary

This is a **typed norm-value receiver**, not an element-level square factorization. The existing `EisensteinLatticeLanding` already has a precise coordinate criterion for divisibility of one Eisenstein element by another; do not replace it by the false converse `q∣norm α → (q:TraceOneInt(-1))∣α`.

For example, `α=⟨5,8⟩` has `norm α=129`, divisible by 43, but neither coefficient is divisible by 43. The scalar integer 43 therefore does **not** divide α as a ring element. This is the next important boundary to make concrete.

## Step 013 recommendation

Advance to a **neutral mod-q Eisenstein residue evaluation / split-support calibration**, with the new typed norm as input. For prime q dividing `Q=a²+ab+b²` and q∤b, define the ratio `t=-(a:ZMod q)/(b:ZMod q)`; show `t²-t+1=0` and `a+b*t=0`. The conjugate root `1-t` gives the other coordinate `a+b*(1-t)=2a+b`. Under q≠3 and q∤b, prove it is nonzero (or prove the two roots differ); the q=3 ramified repeated-root boundary must be tested explicitly.

For q=43,a=5,b=8 this gives `t=37`, `1-t=7`, zero first evaluation and nonzero conjugate evaluation 18, independently of any Fermat equation. Reuse the existing `TraceOneInt (-1)` multiplication/conjugation APIs and inspect `EisensteinLatticeLanding` for prior overlap.

Only after this satisfiable neutral calibration should a thin FLT7 q-support adapter be considered; it merely represents the prime address more precisely. Do not claim a prime-ideal choice, cyclotomic root packet, unit-power class, or descent without constructing and proving the missing typed maps.

**APPROVED / Outcome B.** No PR, merge or broad façade promotion is authorized.

# Instruction 012 — exact Eisenstein norm readout of the selected seven-tail square

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-011.md`, `report-011.md`, `report-010.md`.
Scope: **Step 012 only — a typed quadratic-ring norm value bridge, not a cyclotomic unit-class or ideal-factorization proof.**

## Mission

Make the previously "Eisenstein norm-shaped" quadratic `Q=a²+ab+b²` a **genuine, well-typed norm value in the ALREADY IMPLEMENTED quadratic ring** `TraceOneInt (-1)`. Prove that the selected seventh interior Body and the conditional FLT7 focused product can be read as `7ab(a+b) * norm(α²)`, for an explicitly chosen integral coordinate α.

We must establish the correct typed receiver, signs and coercions. No new quadratic ring, external number field, false prime-ideal identification, unit extraction, or hypothetical Fermat solution may be introduced. Existing `DkMath.Lib.NumberTheory.EisensteinCoordinates` has the exact multiplicative `TraceOneQuadratic.norm` support; **reuse it**.

This is a meaningful carrier bridge, but the mere equality of scalar norm values is not an algebraic-element square factorization and does not construct a next FLT7 counterexample.

## Phase 0 — inventory and overlap

Inspect actual declarations and signatures in:
- `DkMath.NumberTheory.TraceOneQuadratic`: `TraceOneInt (-1)`, `norm`, `traceOne_norm_mul`, `traceOneNorm_neg_one`, `conj`;
- `DkMath.Lib.NumberTheory.EisensteinCoordinates`: `eisensteinCoord`, `norm_eisensteinCoord`, `norm_eisensteinCoord_mul_sq`;
- `DkMath.Lib.Cosmic.GTailSeven`: `selectedBody_seven_interior` and `add_pow_seven_eq_gap_add_interior`;
- `DkMath.FLT.Seven.GTailBridge`: `gtail_seven_shell` and `gtail_seven_eq_of_fermat7Equation`;
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit` and `GTailPrimeOrderAudit` for existing q-support/order receivers;
- prior reports 010–011 and relevant existing typed cyclotomic/trace-one carrier modules, by **source inspection only**.

Write `source-inventory-012.md` with exact symbols, dependency direction and how this new typed readout differs from existing other-number-field or signed-root packets. Check for an already existing statement with the same norm coordinate/target and adapt rather than duplicate it.

**Critical sign convention:** In `TraceOneInt (-1)`, `norm ⟨m,n⟩ = m²+m*n+n²`. The existing `eisensteinCoord m n = ⟨m,-n⟩`, with `norm_eisensteinCoord m n = m²-m*n+n²`. Thus to represent our **plus-sign** Q via `eisensteinCoord` use

```text
α(a,b) := eisensteinCoord (a:ℤ) (-(b:ℤ))
        = (⟨(a:ℤ),(b:ℤ)⟩ : TraceOneInt (-1)).
```

Do not accidentally use `eisensteinCoord a b`: its norm has the opposite mixed sign.

## Phase 1 — a neutral exact typed norm

Suggested owner: `DkMath/Lib/NumberTheory/GTailSevenNormReadout.lean`, importing only the necessary **neutral** Eisenstein coordinate and seventh GTail modules.

Define a minimal helper for α (or reuse a proven existing helper) and prove, for arbitrary `a b : ℕ`:

```text
norm(α(a,b)) = ((a²+a*b+b² : ℕ) : ℤ)
norm(α(a,b)^2) = (((a²+a*b+b²)^2 : ℕ) : ℤ)
```

Derive the first from existing `norm_eisensteinCoord` (or `traceOneNorm_neg_one`), not an invented Norm. Derive the second from **existing norm multiplicativity** `traceOne_norm_mul`, not just independent degree-four polynomial expansion. Keep the exact carriers visible in Lean signatures. Natural casts and integer products must be proved coherent, not glossed over.

Provide an endpoint relating the natural quadratic divisor to the **integer** norm divisor, e.g. for `q a b : ℕ`:

```text
q ∣ a²+a*b+b²  ↔  (q:ℤ) ∣ norm(α(a,b))
```

The statement means an integer **norm value** divisor, not divisibility of α by an algebraic ring element, not a prime ideal factor, and not an element-level square root. Use existing Mathlib cast/divisibility lemmas.

Boundary tests at (a,b)=(0,0), (1,0), (0,1), (5,8) with Q(5,8)=129. For norm-square, check Q²=16641.

## Phase 2 — selected Body as an actual norm square

Use the already kernel-checked `selectedBody_seven_interior` with `R=ℤ`, and the Phase 1 typed equality to derive:

```text
selectedBody 7 (Finset.Ico 1 7) (a:ℤ) (b:ℤ)
  = 7*(a:ℤ)*(b:ℤ)*((a+b:ℕ):ℤ)*norm(α(a,b)^2)
```

Keep the exact selected Body and its original endpoint/GN convention visible. This is a **neutral theorem** for all natural a,b, with no Fermat premise. Provide a cast-aware statement of the equivalent ordinary seventh-power interior if it adds reuse, but avoid duplicate restatement of every Step 004 theorem.

Numerical regression (5,8): selected interior Body has value 60573240 = 7*5*8*13*16641. Test the actual theorem application and an independent numeric check, rather than only a large simplifier expansion.

## Phase 3 — conditional FLT7 norm readout, no stronger claim

In a narrow owner `DkMath/FLT/Seven/GTailNormReadoutAudit.lean`, importing `GTailBridge` and the neutral Phase 1/2 module (or narrow prime allocation/order if used), prove:

```text
(hEq : Fermat7Equation a b c)
(hsum : a+b=c+g)
⊢ (g:ℤ) * ((GTail 7 1 g c : ℕ):ℤ)
   = 7*(a:ℤ)*(b:ℤ)*((a+b:ℕ):ℤ)*norm(α(a,b)^2)
```

Proof route: **cast** the Step 005 exact natural equation to ℤ, then rewrite its Q² factor with the existing norm-square receiver. No false equality of integer and natural GTail rows, and no import of a Fermat impossibility theorem.

An optional *norm-address q-support adapter* may replace `q∣Q` by `(q:ℤ)∣norm α` in the Step 010 allocation or Step 011 Tail order theorem, using Phase 1's iff. It must be clearly labeled an equivalent input presentation, **not new FLT7 arithmetic**. No q-adic or 21-order proof duplication.

## Phase 4 — norm readout is not reverse reconstruction

**Mandatory countercheck**: exhibit two different elements of `TraceOneInt (-1)` with the **same norm** (e.g. α=⟨1,0⟩ and β=⟨0,1⟩ both norm one, but α≠β) in a kernel-checkable test.

This shows the norm value map loses information. Therefore:
- `norm α = Q` does **not** reconstruct an algebraic element from the scalar Q alone;
- `norm(α²)=Q²` does **not** imply an arbitrary β with norm Q² is an algebraic square or a unit multiple of α²;
- `q∣norm α` does **not** identify a chosen prime ideal above q;
- an integer equality of norms is **not** a proof of a cyclotomic unit-power class, normalized root orientation or a next primitive Fermat packet.

Keep these as distinctions in docs; do not assert a non-square unit theorem without a separate proof.

## Phase 5 — validation, reports and stop

Deliver:
- `DkMath/Lib/NumberTheory/GTailSevenNormReadout.lean`;
- `DkMathTest/NumberTheory/GTailSevenNormReadout.lean`;
- `DkMath/FLT/Seven/GTailNormReadoutAudit.lean`;
- `DkMathTest/FLT/Seven/GTailNormReadoutAudit.lean`;
- `source-inventory-012.md`, `report-012.md`; accurate project `ROADMAP.md` update.

Build just the actual created focused targets, sequentially and incrementally with process-local `LEAN_NUM_THREADS=2`; replay Step 011 neutral/owner tests if practical. Do not run a costly full clean/all-test build.

Log exact theorem signatures, source paths, imports, command/exit codes, known overlapping APIs, the cast/sign audit, public `#print axioms` output, and the noninjective-norm boundary. Check no `sorry`, `admit`, new `axiom`, `unsafe`, FLT impossibility end theorem, or neutral-to-FLT dependency cycle. Leave broad public façade promotion and old unit/Norm research owners untouched.

**Outcome B expected:** an actual typed quadratic-ring norm readout, selected seven-tail norm-square identity and conditional focused norm equality, with no independent new obstruction/descent. **Outcome C:** a wrong sign, cast, carrier or converse statement, with a precise correction/counterexample. **Outcome A** requires a new, independently validated arithmetic obstruction beyond norm presentation alone; this step is **not** designed to force one.

**STOP after Step 012.** No prime ideal splitting, cyclotomic unit-power extraction, q-support aggregate products, constructive descent, FLT7 closure, branch merge or PR.

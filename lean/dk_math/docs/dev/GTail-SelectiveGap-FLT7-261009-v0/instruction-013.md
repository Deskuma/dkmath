# Instruction 013 — Eisenstein norm-prime residue slots and conjugate orientation

Date: 2026-10-10
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisite: `review-012.md`, `report-012.md`, `report-011.md`.
Scope: **Step 013 only. Build a neutral, satisfiable residue-level receiver; do not implement prime ideals, cyclotomic unit classes, next Fermat packets, or descent.**

## Mission

Step 012 proved `Q=a²+a*b+b² = norm(α)` and `Q²=norm(α²)` for `α=gtailSevenNormCoord a b : TraceOneInt (-1)`. The norm map loses information. Step 013 must isolate the **first recoverable extra information at a prime divisor q of Q**:

- The existing ring identity `α * conj α = ofInt (-1) (norm α)` is an **element equality**, not only a norm value.
- Divisibility `q∣norm α` does **not** imply the **scalar ring element** q divides α. Use the exact lattice/coefficient criteria, with a real counterexample.
- When q is prime and divides Q, and b is nonzero modulo q, an explicit root `t=-(a:b)/(b:b)` of the Eisenstein polynomial `t²-t+1` gives an evaluation of α equal to zero modulo q.
- Away from q=3, the conjugate evaluation is **nonzero** and selects a different root. This is a neutral *oriented residue address*. It does **not** yet construct or distinguish prime ideals in a larger cyclotomic ring.

These are stronger structural readouts than a bare scalar norm equality, but they remain satisfiable neutral statements independent of any FLT7 counterexample.

## Phase 0 — existing source audit

Inspect signatures and proofs before editing:
- `DkMath.NumberTheory.TraceOneQuadratic`: `TraceOneInt (-1)`, `mul`, `conj`, `traceOne_mul_conj`, `traceOne_norm_mul` and coordinate projections.
- `DkMath.Lib.NumberTheory.EisensteinCoordinates` and `EisensteinLatticeLanding`, especially the **already existing** element-divisibility coordinate criterion.
- `DkMath.Lib.NumberTheory.TraceOneLatticeLanding` and `traceOne_dvd_imp_norm_dvd_norm`. Prefer existing theorems to new general-purpose duplicates.
- `DkMath.Lib.NumberTheory.GTailSevenNormReadout`, Step 010–011 prime-support/order and focused exact owner.
- Mathlib `ZMod` field casts/division/`RingHom` only as genuinely required.
- Existing narrow Eisenstein residue / root-evaluation modules, if any; search before adding a second implementation.

Create `source-inventory-013.md` with exact reused names, distinguished carriers (ring element, integer norm, field residue), import direction and prime-exception hypotheses.

## Phase 1 — actual conjugation equality and the norm-divisor boundary

Create a small neutral module, suggested `DkMath/Lib/NumberTheory/GTailSevenEisensteinResidue.lean`.

Specialize the **existing** `traceOne_mul_conj` to the Step 012 α and prove an endpoint such as:

```text
α(a,b) * conj (α(a,b))
  = ofInt (-1) (((a²+a*b+b² : ℕ) : ℤ))
```

Optionally give the explicit conjugate-coordinate form `conj(α(a,b))=⟨(a+b:ℤ),-(b:ℤ)⟩` using existing conjugation API; do not invent ring operations.

Using existing `TraceOneLatticeLanding` / `EisensteinLatticeLanding` where suitable, prove the scalar divisibility boundary (or its concrete specialization):

```text
(ofInt (-1) (q:ℤ)) ∣ α(a,b)
  ↔ (q∣a ∧ q∣b)     -- specify Nat/Int carriers in the actual Lean signature
```

This statement concerns **scalar multiplication of an integral lattice element**, not divisibility of its integer norm. If an existing lemma already provides exactly this, use it and supply only the Step 012 adapter.

Mandatory concrete counterexample: q=43,a=5,b=8. Lean should prove `43∣norm α` but `¬(ofInt (-1) 43 ∣ α)`, since 43 does not divide either coordinate. This is compatible with the norm-divisor iff from Step 012. Do not mislabel it as failure of an element divisibility statement with a chosen non-scalar prime factor.

## Phase 2 — canonical root and a zero residue slot

For prime `q`, naturals `a,b` and `q∣a²+a*b+b²` with `¬q∣b`, work in `ZMod q` (instantiate `Fact (Nat.Prime q)` before field division). Define, preferably as a small transparent helper under the instance,

```text
t := -(a : ZMod q) / (b : ZMod q)
evalAt(t, z : TraceOneInt (-1)) :=
  (z.fst : ZMod q) + (z.snd : ZMod q) * t
```

Here the fields are integers, so the casts need to be correct for negative coordinates too.

Prove, in a carrier-accurate sequence:

```text
t² - t + 1 = 0
evalAt(t, α(a,b)) = 0
(1-t)² - (1-t) + 1 = 0
evalAt(1-t, α(a,b)) = (2*a+b : ZMod q)
```

The second expression follows by the chosen t, not from injecting a scalar Norm condition. The final explicit evaluation equals the evaluation of the conjugate α at t, in accord with `conj τ=1-τ`. Reuse mathlib's field/denominator lemmas and the existing integral-coordinate definition. No Fermat equation, prime-ideal abstract type, or q≠3 assumption is needed for the two root equations and first zero slot.

If implementation of a generic \`evalAt\` is needed, prove it respects addition and (when `t²-t+1=0`) multiplication by actual coordinate algebra. A full `RingHom` package is **optional** only if readily checkable without a new large hierarchy. Do not claim an algebra homomorphism merely from a function definition.

## Phase 3 — separate conjugate slots away from q=3

With the hypotheses of Phase 2 and additionally `q≠3`, prove

```text
evalAt(1-t, α(a,b)) ≠ 0
t ≠ 1-t
```

The key identity to reuse or prove is the integer/ZMod polynomial identity

```text
4*(a²+a*b+b²) = (2*a+b)² + 3*b².
```

If q divides Q and `2*a+b`, the identity forces q to divide `3*b²`. Since q is prime and q∤b, it forces q=3. This establishes the **characteristic-three exception** without assuming coprimality of a,b beyond the explicit b-unit condition. The q=3 root can be repeated and both evaluations may vanish.

Do **not** announce a decomposition `(q)=P*Pbar`, PID/UFD, class-group triviality or a preferred prime ideal on the basis of this field evaluation alone. A pair of distinct residue slots is a precursor to such a construction, not a proof of one.

## Phase 4 — concrete nonvacuous calibration and optional GTail adapter

Required actual numeric checks, without Fermat assumptions:

- `q=43, a=5,b=8`: `Q=129=3*43`, `t=37` in ZMod 43, conjugate root `1-t=7`, first evaluation `5+8*37=0` in ZMod 43, other evaluation `5+8*7=18≠0`; also norm α=129 and scalar ring 43 does not divide α.
- `q=3, a=b=1`: `Q=3`, `t=2` in ZMod 3 and `1-t=2`; both evaluations are zero. This tests why q≠3 is needed.
- Boundary b=0: do not use denominator inversion without q∤b. Check at least one harmless ordinary norm/conjugation boundary case.
- If useful, apply the Step 011 neutral third-order theorem to q=43 independently. This must not be treated as a new Fermat result.

**Optional very thin owner adapter**: from Step 010's primitive pair and q∣Q derive q∤b, then invoke the neutral residue theorem, or restate the Step 011 Tail branch in the explicitly chosen slot notation. Create an FLT owner file only if this adds a real typed connection and compiles through narrow direct imports. No other FLT hypothesis is required for the neutral residue theorem.

## Validation, reporting and stop

Required neutral production/test:
- `DkMath/Lib/NumberTheory/GTailSevenEisensteinResidue.lean`
- `DkMathTest/NumberTheory/GTailSevenEisensteinResidue.lean`

Optional narrow FLT adapter and test, **only if justified**.

Required documentation:
- `source-inventory-013.md`;
- `report-013.md` with exact public theorem signatures, all hypotheses, proof dependencies, numeric examples, limitations, failed/repair attempts and classification;
- update `ROADMAP.md` with a truthful post-012 state.

Run sequential incremental focused builds with process-local `LEAN_NUM_THREADS=2` for actual new targets and Step 012 regression, recording command, exit code, axiom audit of all public endpoints, exact cyclic dependency scan and forbidden placeholder/unsafe scan. Avoid full all-test build or unrelated Legendre optimization. Do not modify the established TraceOne ring, old lattice kernels, Step 010–012 theorem statements, public facades or root driver merely to make the new proof convenient.

**Outcome B expected:** element-level conjugation, scalar-vs-norm divisibility distinction and a well-typed residue-slot orientation away from q=3, without ring-ideal/cyclotomic receiver or descent. **Outcome C** for a failed split condition, carrier mismatch or missing unit premise; record the smallest counterexample/corrected contract. **Outcome A** only for a genuinely new independently compared arithmetic obstruction, not for constructing a residue coordinate.

**STOP after Step 013.** Do not assert a prime ideal, class/unit extraction, norm-to-element square reconstruction, unconditional FLT7 result, PR or branch merge.

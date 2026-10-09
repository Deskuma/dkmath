# Instruction 016 — ramified three in the existing Eisenstein order: test P²=(3)

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-015.md`, `report-015.md`, `source-inventory-015.md`
Scope: **Step 016 only; neutral, characteristic-three ramified ideal calculation.** No FLT7 closure, cyclotomic carrier transport, class-number/UFD theorem or next counterexample/descent.

## Mission

Step 015 proved for a prime q with **two separated roots** of `t²-t+1=0`:

```text
P_t ⊓ P_(1-t) = (q)
P_t * P_(1-t) = (q)
```

where `P_t` is the checked `RingHom.ker` in the **actual integral** `R=TraceOneInt (-1)`. At q=3, the root `t=2` equals its conjugate. Step 015 exhibited `P ⊓ P=P ≠ (3)`. This counterexample does **not** settle `P²=(3)`; no inference of failure is licensed.

Evaluate the **separate ramified product candidate** in `R`, with checked element and ideal equalities:

```text
τ = tau (-1)           -- τ²=τ-1
π = 1+τ
P = eisensteinResidueIdeal (2 : ZMod 3) ht2
π² = ofInt (-1) 3 * τ
τ*(1-τ)=1
proposed:  P = Ideal.span {π}
proposed:  P*P = eisensteinScalarIdeal 3
```

The algebraic identities can be checked directly; the **ideal equalities remain proof targets** until Lean checks both inclusions. Do not assert them from norm(π)=3 or from a single finite example.

## Phase 0 — exact source and overlap audit

Inspect:
- `DkMath.Lib.NumberTheory.GTailSevenSplitIdeal`, `GTailSevenResidueIdeal`, `GTailSevenEisensteinResidue`;
- `DkMath.NumberTheory.TraceOneQuadratic` for the actual `tau`, `ofInt`, `norm`, `conj`, `mul` and coordinate lemmas;
- existing `DkMath.Lib.NumberTheory.TraceOneLatticeLanding` for `traceOne_dvd_iff_norm_dvd_mul_conj_coordinates`, especially the nonzero norm prerequisite;
- `EisensteinLatticeLanding` and any preexisting ramified-prime principal-ideal results (inspect to avoid duplication);
- Mathlib current `Ideal.span_singleton` membership and ideal-product-of-singletons theorems. **Do not guess an API name; verify by source or `#check`.**

Write `source-inventory-016.md` identifying exact reused source theorem signatures, the characteristic-three root proof, and the minimal import closure. No broad `DkMath.FLT.Seven` or degree-seven cyclotomic ideals in a neutral module.

## Phase 1 — explicit ramified generator and unit

Choose a minimal local/reusable definition for `π : TraceOneInt (-1)`, such as `1 + tau (-1)`. With the ring's *existing* product prove:

```text
π = ⟨1,1⟩
norm π = 3
π * π = ofInt (-1) 3 * tau (-1)
tau (-1) * (1-tau (-1)) = 1
```

Optionally prove `(1-tau (-1))*tau (-1)=1` explicitly or use commutativity. This supplies the *actual integral witness* that τ is a unit (no global PID/UFD infrastructure necessary). Verify the sign: this `TraceOneInt (-1)` model uses `τ²=τ-1`, not `τ²=-τ-1` under a different generator convention.

Prove q=3 root `ht2 : (2:ZMod 3)^2-2+1=0` from computation. Show `π∈P`, and `π²∈(3)`, then also scalar 3 is divisible by π² **using τ's explicit inverse**. This is the key two-way generator comparison.

## Phase 2 — identify the *entire* kernel with a principal ideal

Core target for every arbitrary signed `z : TraceOneInt (-1)`:

```text
z ∈ P  ↔  π ∣ z.
```

This is stronger than `π∈P` and is essential for a principal-kernel equality. Suggested sound route:

1. Kernel membership is `(z.fst : ZMod 3)+2*(z.snd : ZMod 3)=0`, equivalent to the integer coordinate condition `3∣z.fst-z.snd`.
2. `conj π = ⟨2,-1⟩` and `norm π=3`; `z*conj π` has coordinates `2*z.fst+z.snd` and `-z.fst+z.snd`.
3. The two coordinates are both divisible by 3 precisely when `3∣z.fst-z.snd` (their difference is `3*z.fst`). Reuse `traceOne_dvd_iff_norm_dvd_mul_conj_coordinates` with the **explicit normπ≠0** premise to turn those coordinate divisors into `π∣z`, or directly construct an integral quotient if that makes a smaller proof.
4. Convert the element divisibility iff into the checked ideal equality:

```text
P = Ideal.span {π}
```

using ideal extensionality and `Ideal.mem_span_singleton`, for **all signed integral elements**, not just α(a,b).

If the existing lattice theorem's carrier/sign conventions differ, correct the coordinate translation. Do not bypass it with an unproved norm-to-element divisibility converse.

## Phase 3 — prove or precisely block the ramified product

After the principal-kernel equality compiles, use Mathlib's correct **ideal multiplication** API to show:

```text
P*P = Ideal.span {π²}.
```

Then establish `Ideal.span {π²} = eisensteinScalarIdeal 3` by mutual integral element divisibility:

```text
π² = 3*τ          so 3 ∣ π²
3 = π²*(1-τ)      so π² ∣ 3.
```

Check `3` is the embedded scalar `ofInt (-1) 3`, not a norm value or an ordinary integer ideal in `ℤ`.

An alternative direct proof `P*P≤(3)` and `(3)≤P*P` is acceptable if the principal ideal product API is awkward, but BOTH directions must be kernel checked. No invocation of Step 015 `Ideal.mul_eq_inf_of_coprime` is allowed: **P and P are not comaximal**.

If a proposed equality cannot be checked with available mathematics, stop at the strongest honest preceding theorem and report Outcome C for the blocked inference. Do not insert axioms, placeholders, fabricated unit instances or assumed prime-ideal relations.

## Phase 4 — negative and positive calibrations

Mandatory Lean regressions:
- q=3, t=2, the common kernel P; `π=⟨1,1⟩`, `norm π=3`, `π∈P`, `π∉(3)`, showing `P∩P=P ≠(3)`;
- if proved, `P²=(3)`, side by side with `P∩P≠(3)`. They are mathematically compatible because P is not comaximal with itself;
- verify nonzero/signed generic witnesses `⟨-2,1⟩` or `⟨-43,86⟩` as appropriate after checking actual mod3 membership; use `⟨-2,1⟩` (evaluation -2+2=0), and verify π-divisibility through the new generic theorem;
- the generator identity `π²=3τ` and inverse identity `τ(1-τ)=1` by direct ring operations;
- q=43 split identity remains the Step 015 result; do not conflate it with q=3 ramification. Replay Step 015 test target unchanged.

Optional q=5 inert no-root check may be inherited from Step 015; do not expand to full decomposition classification.

## Phase 5 — deliverables and guarded stop

Suggested neutral owner and test:
- `DkMath/Lib/NumberTheory/GTailSevenRamifiedThreeIdeal.lean`
- `DkMathTest/NumberTheory/GTailSevenRamifiedThreeIdeal.lean`

Docs:
- `source-inventory-016.md`
- `report-016.md`
- truthful post-015 `ROADMAP.md` section, preserving historical distinctions.

Build sequential, incremental and low-memory:

```text
LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenRamifiedThreeIdeal
LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenRamifiedThreeIdeal
LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenSplitIdeal
```

Use actual target names if the source paths differ; log every final exit code and intermediate repair. Print axioms of **all new public definitions and theorems**, audit import cycles/neutral→FLT direction, no `sorry`, `admit`, added `axiom`, `unsafe`, `exfalso`/FLT impossibility endpoint, and `git diff --check`/new-file whitespace. Keep numeric checks small, with no expensive full 683-test run. Do not touch previous Step 010–015 statements, root driver, old carrier definitions, facades, or Legendre performance code.

### Outcomes

- **Outcome B (expected):** checked ramified principal kernel and its square equals the scalar (3), while the intersection counterexample remains true; no new FLT7 obstruction/descent.
- **Outcome C:** a false sign/generator/quasi-principal inference or blocked equality, with the smallest typed counterexample or missing lemma. Report partial completed theorems honestly.
- **Outcome A:** only if a genuinely new independently validated FLT7 necessary obstruction is obtained and compared to prior work; a classical ramified ideal identity alone is B.

**STOP after Step 016.** No q-adic ideal valuation theory, q-general cyclotomic transfer, unproved norm-square converse, FLT7 packet reconstruction, PR or branch merge.

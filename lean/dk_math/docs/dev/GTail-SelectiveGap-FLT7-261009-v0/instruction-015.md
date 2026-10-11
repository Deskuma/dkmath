# Instruction 015 — split scalar-prime ideal factorization in the existing Eisenstein ring

Date: 2026-10-10
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-014.md`, `report-014.md`, `source-inventory-014.md`.
Scope: **Step 015 only: neutral split-prime ideal intersection and, if supported by checked APIs, ideal product. No cyclotomic transfer, FLT7 closure or descent.**

## Mission and mathematical statement

For the **existing** integral `TraceOneInt (-1)` ring, Step 014 constructed an actual maximal ideal
`P_t = ker (eisensteinResidueRingHom t ht)` whenever q is prime and `t : ZMod q` obeys `t²-t+1=0`.

The next step is to formalize the missing **two-slot coordinate reconstruction**. Given two *distinct* conjugate roots `t` and `1-t`, prove that belonging to both evaluation kernels is equivalent to divisibility of **both integral coordinates by the scalar q**. Use this to prove the ideal intersection formula:

```text
P_t ⊓ P_(1-t) = Ideal.span {ofInt (-1) (q:ℤ)}.
```

Then, as a **separately checked gate**, use distinct maximal ideals/comaximality and a genuine Mathlib `Ideal` product/inf theorem to derive:

```text
P_t * P_(1-t) = Ideal.span {ofInt (-1) (q:ℤ)}.
```

This is a legitimate **conditional split-prime factorization in the degree-two Eisenstein ring**. It is **not** a factorization in the seventh cyclotomic carrier, not a class-number/unique-factorization theorem, and not a lift of scalar q-support into an FLT7 prime-ideal packet.

Do not assume every prime q admits such a root. Do not apply distinctness at q=3.

## Phase 0 — inventory of exact existing contracts

Inspect actual definitions and theorem names before editing:
- `DkMath.Lib.NumberTheory.GTailSevenResidueIdeal` (RingHom, ker, maximality, root conjugation, membership iff, orientation).
- `DkMath.Lib.NumberTheory.GTailSevenEisensteinResidue` (coordinate evaluation and char-three distinction).
- `DkMath.NumberTheory.TraceOneQuadratic` (`ofInt`, `TraceOneInt.fst/snd`, `traceOne_ext`).
- `DkMath.Lib.NumberTheory.TraceOneLatticeLanding`, `EisensteinLatticeLanding` (existing scalar versus element-level divisibility).
- Current Mathlib `Ideal.span`, `Ideal.mem_span_singleton`, `Ideal.inf`, `Ideal.IsMaximal`, comaximal/sup and `Ideal.mul_eq_inf` or whichever names are actually available. **Discover exact theorem names by Lean `#check` or library source; examples here are not guaranteed API names.**
- `DkMath.NumberTheory.TraceOneResidueType` (for carrier overlap), and prior reports 012–014.

Write `source-inventory-015.md`: precise import plan, generic-versus-specialized theorem boundaries, root-existence and characteristic-three issues, and overlap with any existing typed splitting lemma. Do not import heavy FLT7/cyclotomic owners into this neutral module.

## Phase 1 — prove root separation, not just name it

For prime q, `t : ZMod q` with `ht : t²-t+1=0`, prove the split condition from **q≠3**:

```text
q ≠ 3 → t ≠ 1-t.
```

One valid argument uses the characteristic-independent polynomial identity
`4*(t²-t+1) = (2*t-1)²+3`. If `t=1-t`, then `2*t-1=0`, so `3=0` in ZMod q. Since q is prime, this forces q=3, contradiction.

Alternatively, expose a main API parameterized by `htdiff : t ≠ 1-t`, with a checked q≠3 adapter. Do not accidentally require q≠7; the characteristic-three distinction is the relevant exception.

At q=3, `t=2` is a repeated root. This is a **required negative boundary** for the proposed product decomposition, not a special-case afterthought.

## Phase 2 — neutral arbitrary-coordinate two-slot reconstruction

Let `z : TraceOneInt (-1)`. Given q prime, ht root and htdiff as above, prove the iff:

```text
z ∈ P_t ∧ z ∈ P_(1-t)
  ↔ (q:ℤ) ∣ z.fst ∧ (q:ℤ) ∣ z.snd.
```

Proof path:
1. Rewrite both memberships through the *already proved* `mem_eisensteinResidueIdeal_iff`, obtaining `(z.fst:ZMod q)+(z.snd:ZMod q)*t=0` and the same at `1-t`.
2. Subtract; `(z.snd:ZMod q)*(t-(1-t))=0`.
3. q prime makes the codomain a field; htdiff makes the second factor nonzero. Hence `z.snd` casts to zero, and then `z.fst` casts to zero.
4. Convert zero ZMod integer casts into **integer coordinate divisibility**, not merely natural divisibility. Prove the converse from those two divisors by direct evaluation.

Do not restrict z to nonnegative natural coordinates: the ideal equality requires **every element of the integral ring**, including negative fst/snd.

Prove a small exact scalar-coordinate criterion, or reuse an existing general lemma:

```text
ofInt (-1) (q:ℤ) ∣ z  ↔
  (q:ℤ) ∣ z.fst ∧ (q:ℤ) ∣ z.snd.
```

The Step 013 `scalar_dvd_gtailSevenNormCoord_iff` concerns only natural α(a,b); it is **not a substitute** for the arbitrary integral z lemma. Use the explicit pair quotient when needed.

## Phase 3 — actual ideal intersection, then product

Define the scalar principal ideal `I_q` using the **existing ring**:

```lean
Ideal.span ({ofInt (-1) (q : ℤ)} : Set (TraceOneInt (-1)))
```

or a standard equivalent `Ideal.span_singleton`, with no newly invented ring of integers.

Use the membership characterization of principal ideals, Phase 2's scalar-coordinate iff, and extensionality to prove:

```text
P_t ⊓ P_(1-t) = I_q.
```

A direct proof may be easier than invoking a broad principal ideal factorization theorem. Ensure ideal equality is proved for all elements, not just the chosen α(a,b).

**Only after intersection compiles**, prove:
- q prime and ht + htdiff imply both P ideals are maximal (Step 014 already provides this).
- P_t and P_(1-t) are distinct. A compact proof can use `tau(-1)`, whose two evaluations are t and 1-t, or the difference between `tau(-1)-ofInt(-1) t` (if a compatible integral lift of t is chosen). Better: use maximality plus the fact that the two ring homomorphisms have different values on tau; verify kernel equality would imply equality of these surjective quotient evaluations, or construct a direct kernel membership witness. You **may not infer different kernels solely from different homomorphism values** without a proof.
- Distinct maximal ideals are comaximal, then their **ideal product equals intersection** by an existing theorem. Source-check all hypotheses and theorem orientations.

A simpler independent direct argument proving P_t + P_(1-t)=⊤ by explicitly constructing a Bezout combination may be preferable if it avoids a large ideal hierarchy, but must actually exhibit the ideal membership witnesses.

The last product equality is an **optional success gate**: if available ideal infrastructure makes it disproportionately costly, stop after the exact intersection theorem and document the smallest verified missing lemma; mark Step 015 PARTIAL/Outcome B or C as appropriate. Do not insert a new axiom or claim an unproved product equality.

## Phase 4 — mandatory split/ramified calibration

Satisfiable numerical checks using *bundled* ideals, not unbundled evaluations alone:

### Split q=43

Roots t=37, 1-t=7 satisfy the relation and are distinct. Prove the concrete equalities if Phase 3 succeeds:

```text
P37 ⊓ P7 = I_43
P37 * P7 = I_43               -- only if product theorem is proved
P37 ⊔ P7 = ⊤                  -- only if comaximality is proved
```

Check:
- α=⟨5,8⟩ is in P37 but not P7, thus not in I_43.
- Scalar element 43 is in both P37 and P7 and generates I_43; scalar 43 does **not** divide α.
- A signed-coordinate element such as z=⟨-43,86⟩ belongs to both kernels and to I_43.
- At least one actual ideal membership proof uses the new generic reconstruction lemma, not only finite `decide`.

### Ramified q=3 — counterexample to an overstrong assertion

At root t=2=1-t, P_t=P_(1-t). Take z=⟨1,1⟩, with norm(z)=3:
- z lies in the common kernel.
- scalar element 3 does not divide z (coordinates 1,1).
- hence P_t ⊓ P_(1-t) **is not** I_3.

This refutes the intersection/product formula when distinctness is removed. Do **not** conclude that the correct ramified decomposition is something specific such as P²=(3) without its own proof.

### Inert boundary

Do not create roots for q that lack solutions to `t²-t+1=0` in ZMod q. If convenient, prove/verify an inert example q=5 by checking no t exists; the main theorem already requires a root argument and should not need this test to compile.

## Phase 5 — validation / classification

Suggested neutral module + test:
- `DkMath/Lib/NumberTheory/GTailSevenSplitIdeal.lean`
- `DkMathTest/NumberTheory/GTailSevenSplitIdeal.lean`

Required docs:
- `source-inventory-015.md`
- `report-015.md` with exact theorem signatures, mathematical prerequisites, demonstrated equality scope and identified unsolved statements;
- a truthful post-014 `ROADMAP.md` entry; preserve historical reports and ledgers.

Build incrementally, sequentially and with process-local `LEAN_NUM_THREADS=2`:

```text
LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenSplitIdeal
LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenSplitIdeal
LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenResidueIdeal
```

Record each actual final exit status, earlier repair attempts, `#print axioms` for each new public declaration, absence of sorry/admit/new axiom/unsafe/false-elimination shortcuts, and minimal import graph without neutral→FLT cycles. Do not run full `DkMathTest`, change unrelated Legendre proofs, expose a new facade or merge branch.

**Outcome B expected** if the exact split ideal intersection and optionally its comaximal product decomposition are kernel checked, without FLT7 contradiction/descent. **Outcome C** if a hoped-for equality is false or needs an omitted distinctness/unit/carrier assumption; report the counterexample or exact missing lemma, without concealing partial success. **Outcome A** requires an independently verified new FLT7 obstruction, not the classical split-prime identity alone.

**STOP after Step 015.** No cyclotomic-prime transport, class group, unit-power extraction, arbitrary norm-square-to-square inversion, primitive Fermat packet, FLT7 closure, PR or merge.

# FLT prime-generalization Phase 25 — stripped TraceOne residual to ideal p-th power

## Goal

Phase 24 closed the arbitrary-prime primitive-coordinate bridge at the normalized FLT endpoint:

```text
PrimeAdicFactorPacket
  -> PrimeTraceOneCoordinatePacket
  -> prime_packet_coordinate_isCoprime
```

Phase 21 already supplies the exponent-independent downstream TraceOne kernel:

```text
coordinate coprime + axis terminal
  -> span(w) and span(conj w) are coprime ideals
```

and Phase 15 supplies the neutral Dedekind-domain extraction:

```text
I ⟂ J, I*J = K^p
  -> ∃ A, I = A^p.
```

This phase must connect those GREEN layers without adding a class-group hypothesis.  The target is the first production theorem/packet proving that the **axis-stripped arbitrary-prime TraceOne residual generates a nonzero ideal p-th power**.

Expected final status:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
PGEN-PRIME-TRACEONE-IDEAL-POWER-GREEN
```

Do not prove principalization, class-group p-torsion-freeness, unit-sector elimination, regular-prime theory, or FLT.

---

## A. Pin the exact existing APIs first

Create a focused audit file under:

```text
DkMathTest/FLT/Prime/PrimeTraceOneStrippedIdealApiAudit.lean
```

Pin the exact checkout-local signatures for at least:

- `PrimeAdicFactorPacket`
- `PrimeAdicPowerSplit`
- `primeAdicPowerSplit_of_packet`
- `PrimeAdicPowerSplit.residual_eq`
- `PrimeAdicPowerSplit.prime_not_dvd_b`
- `PrimeTraceOneCoordinatePacket`
- `PrimeTraceOneCoordinatePacket.coord`
- `PrimeTraceOneCoordinatePacket.coord_norm_eq`
- `prime_packet_coordinate_isCoprime`
- `PrimeDiscriminantPacket`
- `discr_signedPrimeParameter`
- `signedPrimeDiscriminant_natAbs`
- `PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow`
- `ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal`
- `traceOne_mul_conj`
- `traceOneRat_no_rational_root`
- `traceOneRat_isDedekindDomain`
- `exists_eq_pow_of_isCoprime_mul_eq_pow`
- the pinned principal-ideal multiplication/power lemmas actually used (`Ideal.span`, singleton span multiplication, powers, and nonzero-divisor membership).

Do not guess Mathlib theorem names.  Record the exact usable declarations in `report-025.md`.

---

## B. Add the signed-prime `PrimeDiscriminantPacket` adapter

The repeated parameter is

```text
s_p := signedPrimeParameter p
```

with

```text
discr s_p = signedPrimeDiscriminant p,
natAbs (signedPrimeDiscriminant p) = p.
```

Add a small reusable production adapter at the narrowest non-circular location, for example in a new neutral module or in an existing TraceOne prime-discriminant module:

```lean
def signedPrimeDiscriminantPacket
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    PrimeDiscriminantPacket p (signedPrimeParameter p)
```

or an equivalent theorem/definition.

It must be proved from the existing Phase-12/4 declarations; do not duplicate discriminant arithmetic.

---

## C. Promote the Nat/Int GTail-shell bridge if needed

Phase 24 currently has a private helper in `PrimeTraceOneCoordinateCoprime.lean` converting

```text
GTail p 1 g u
```

to the integer `GTailCyclotomicShell` at `(g,u)`.

Phase 25 needs the same equality to turn the coordinate packet norm into

```text
natAbs(norm parent) = p * b^p.
```

If that helper is still private, promote/refactor it into a neutral reusable theorem in the lowest suitable GTail/cyclotomic module.  Suggested shape:

```lean
theorem natCast_GTail_one_eq_GTailCyclotomicShell
    {p g u : ℕ} (hg : g ≠ 0) :
    ((GTail p 1 g u : ℕ) : ℤ) =
      GTailCyclotomicShell p (g : ℤ) (u : ℤ)
```

Exact naming is flexible.  Avoid duplicate proof bodies in the FLT module.

---

## D. Neutral lemma: coordinate coprimality survives one axis stripping

For general `s : ℤ`, multiplication by

```text
discrAxis s = ⟨-1, 2⟩
```

is an integral linear transformation of the two coordinates.  If

```text
x = discrAxis s * y
```

and the coordinates of `x` are coprime, then the coordinates of `y` are coprime.

Add a neutral theorem, preferably in `TraceOneDiscriminantAxis.lean` or `TraceOneConjugateCoprime.lean`:

```lean
theorem coordinate_isCoprime_of_eq_discrAxis_mul
    {s : ℤ} {x y : TraceOneInt s}
    (hxy : x = discrAxis s * y)
    (hx : IsCoprime x.fst x.snd) :
    IsCoprime y.fst y.snd
```

or an equivalent orientation.

A direct Bézout proof is preferred.  Do not introduce Euclidean/GCD structure.

The coordinate formulas are expected to reduce to integer linear combinations; prove them from the existing multiplication definitions rather than postulating them.

Add a small neutral regression for several `s` values.

---

## E. Neutral lemma: norm p-th power gives a principal-ideal product p-th power

For any TraceOne element `r` with

```text
norm r = k^p,
```

prove the principal-ideal identity needed by Phase 15:

```text
span{r} * span{conj r} = (span{(k : TraceOneInt s)})^p.
```

Implement this as a reusable neutral theorem, with an exact Lean shape determined by the pinned `Ideal.span` API.  Conceptually:

```lean
theorem span_mul_span_conj_eq_pow_of_norm_eq_pow
    {s : ℤ} [CommRing ...] ...
    {r : TraceOneInt s} {k : ℤ} {p : ℕ}
    (hNorm : norm r = k ^ p) :
    Ideal.span ({r} : Set (TraceOneInt s)) *
      Ideal.span ({conj r} : Set (TraceOneInt s)) =
    (Ideal.span ({(k : TraceOneInt s)} : Set (TraceOneInt s))) ^ p
```

The proof should use the existing identity

```text
r * conj r = (norm r : TraceOneInt s)
```

and principal-ideal multiplication/power functoriality.

Do not use UFD/PID/GCD assumptions.

---

## F. Construct the stripped residual from an actual FLT-side packet

Work in a new production module, suggested path:

```text
DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean
```

Input should include:

```lean
P0 : PrimeAdicFactorPacket p g u x
P  : PrimeTraceOneCoordinatePacket L p ζ hζ
```

with the existing cyclotomic-extension assumptions on `L, ζ`.

Let

```text
parent := P.coord (g+u) u
split  := primeAdicPowerSplit_of_packet P0
```

Use Phase 24 to obtain:

```text
IsCoprime parent.fst parent.snd.
```

Use `split.residual_eq` and the packet norm equality to prove the exact Phase-21 stripping input:

```text
natAbs (norm parent) = p * split.b^p
```

and use:

```text
split.prime_not_dvd_b
```

for the no-extra-p condition.

Then apply:

```text
signedPrimeDiscriminantPacket
PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
```

to obtain a residual `r` satisfying:

```text
parent = discrAxis (signedPrimeParameter p) * r
norm r ≠ 0
¬ discrAxis (signedPrimeParameter p) ∣ r
∃ k : ℤ, norm r = k^p.
```

Do not reprove the axis-depth argument.

---

## G. Prove the stripped residual coordinates are primitive

Apply the neutral Part-D theorem to the Phase-24 parent-coordinate result and the stripping equation:

```text
IsCoprime r.fst r.snd.
```

This is the exact input required by Phase 21.

Then instantiate the odd-prime TraceOne domain/Dedekind structure using the existing Phase-17 machinery.  Follow the already working local-instance pattern from `TraceOnePrimeUnitSectors.lean`; do not install a new global field/domain instance.

Apply:

```text
ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
```

to obtain:

```text
IsCoprime (Ideal.span {r}) (Ideal.span {conj r}).
```

This should require no `GCDMonoid` or Euclidean theorem.

---

## H. Extract the ideal p-th power

Combine:

```text
IsCoprime (span r) (span (conj r))
```

with the Part-E principal-ideal product identity, then apply:

```lean
exists_eq_pow_of_isCoprime_mul_eq_pow
```

from Phase 15.

Required endpoint:

```lean
∃ I : Ideal (TraceOneInt (signedPrimeParameter p)),
  Ideal.span ({r} : Set _) = I ^ p
```

Strengthen this, if cheap, to carry the nonzero condition required by Phase 15/16 principalization:

```lean
∃ I : Ideal (TraceOneInt (signedPrimeParameter p)),
  I ∈ (Ideal (TraceOneInt (signedPrimeParameter p)))⁰ ∧
  Ideal.span ({r} : Set _) = I ^ p
```

The nonzero proof should come from `norm r ≠ 0`, hence `r ≠ 0`, and the positive exponent `p > 0`; do not assume it.

---

## I. Preferred production packet

If it keeps the downstream API clean, package Parts F-H into a structure such as:

```lean
structure PrimeTraceOneStrippedIdealPacket (...) : Type where
  adicSplit : PrimeAdicPowerSplit p g u x
  parent : TraceOneInt (signedPrimeParameter p)
  residual : TraceOneInt (signedPrimeParameter p)
  axis_eq : parent = discrAxis (signedPrimeParameter p) * residual
  parent_coordinate_coprime : IsCoprime parent.fst parent.snd
  residual_coordinate_coprime : IsCoprime residual.fst residual.snd
  residual_norm_ne_zero : norm residual ≠ 0
  residual_axis_terminal : ¬ discrAxis (signedPrimeParameter p) ∣ residual
  residual_norm_pow : ∃ k : ℤ, norm residual = k ^ p
  residual_conj_ideal_coprime :
    IsCoprime (Ideal.span ({residual} : Set _))
      (Ideal.span ({conj residual} : Set _))
  idealRoot : Ideal (TraceOneInt (signedPrimeParameter p))
  idealRoot_nonzero : idealRoot ∈ (Ideal _)⁰
  residual_span_eq : Ideal.span ({residual} : Set _) = idealRoot ^ p
```

Exact field names/types may be adjusted to avoid redundant data.  A theorem-only endpoint is acceptable if a packet adds no value, but remember that Phase 26 will consume the residual, its ideal root, the nonzero proof, and the span-power equality.

Do not put class-group or unit-sector hypotheses in this packet.

---

## J. Regressions

Add focused probes for:

```text
p=3  : generic bridge compiles without claiming the p=3 unit sector is singleton
p=5  : TraceOneInt 1 stripped ideal-power endpoint
p=7  : compare/replay against the existing specialized Seven residual route
p=11 : TraceOneInt (-3) imaginary carrier endpoint
p=13 : TraceOneInt 3 real carrier endpoint
```

These are architecture regressions only.  Do not claim FLT for p=11 or p=13.

For p=7, compare the generic output shape with the existing `SevenQuadraticResidualPacket` / conjugate-coprime route when practical, but do not require definitional equality of witnesses.

---

## K. Axiom and source audit

Add:

```text
DkMathTest/FLT/Prime/PrimeTraceOneStrippedIdealAxiomAudit.lean
```

Print axioms for all new public neutral and FLT-side endpoints.  Expected inherited dependencies are only the standard foundational axioms already seen in this branch (`propext`, `Classical.choice`, `Quot.sound`) unless Mathlib exposes another standard dependency; record the exact output.

Fresh source scan over Phase-25 production/test files must contain no:

```text
sorry
sorryAx
admit
explicit axiom
unsafe
```

Do not attribute the pre-existing `ZsigmondyCyclotomicResearch.lean` warning to this phase.

---

## L. Focused validation

At minimum build:

```text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMath.NumberTheory.TraceOneConjugateCoprime
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.NumberTheory.CyclotomicQRCommonPrimeSupport
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateCoprime
lake build DkMath.Lib.NumberTheory.IdealPowerFactor
lake build DkMath.FLT.Prime.PrimeTraceOneStrippedIdeal
lake build DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealApiAudit
lake build DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealProbe
lake build DkMathTest.FLT.Prime.PrimeTraceOneStrippedIdealAxiomAudit
lake build DkMath.FLT.Seven
git diff --check
```

Adjust only for actual final module names.

---

## M. Report and stop boundary

Create:

```text
docs/refact/FLT-Prime-Generalization-260911-v0/report-025.md
```

Report exact statuses.  Preferred success classification:

```text
PGEN-PRIME-TRACEONE-STRIPPED-IDEAL-BRIDGE-GREEN
PGEN-PRIME-TRACEONE-IDEAL-POWER-GREEN
```

If the bridge stops earlier, classify the smallest precise blocker rather than adding a receiver assumption.

Explicit non-goals:

- no `classGroupPTorsionFreeAt` proof;
- no principalization;
- no class-number theorem;
- no regular-prime theorem;
- no unit-sector elimination;
- no general FLT theorem.

If GREEN, the next mathematical frontier is no longer cyclotomic-coordinate primitivity.  It is the actual supply of the class-group `p`-torsion condition and, on the real branch, elimination of the nonzero `Fin p` unit sectors.

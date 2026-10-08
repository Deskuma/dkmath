# Prime reappearance / cyclotomic layer addresses — Findings 003

2026-10-04. Lean / Mathlib `v4.34.1`.
Branch `research/GapFocusing-ExponentGauge-Ultra-261004-v0`.
Initial HEAD `0d34556bd`; initial working tree clean.
User request: read and carry out [instruction-003](instruction-003.md).
The proposed address ray and moire interpretation are questions to test,
not assumptions to put in a structure.

## Checkpoint 01 — source inventory

- General homogeneous cyclotomic evaluation already exists as
  `DkMath.CFBRC.cyclotomicShiftedEval n x u`, using the actual natural-degree
  homogenization. At `x=a-b,u=b` it is the homogeneous value `Phi_n(a,b)`.
  Reuse this definition rather than introduce a second value formalism.
- `DkMath.CosmicFormula.GTailCyclotomicHomEval` is the prime-index degree
  `p-1` shell and is not a substitute for general composite-index evaluation.
- Mathlib `Polynomial.isRoot_cyclotomic_prime_pow_mul_iff_of_charP`
  already identifies roots of `Phi_(q^k*m)` in characteristic `q` with
  primitive `m`-th roots, when `q` does not divide `m`.
  This supplies an exact route to the predicted address law, including `q=2`.
- Existing `DkMath.Zsigmondy.PrimitivePrimeDivisor` concerns the full
  difference `a^n-b^n` at all positive lower degrees, not merely the
  address set restricted to indices greater than one.
- Mathlib LTE treats odd primes and `q=2` separately. No generic integer
  cyclotomic-value valuation theorem was found in the initial source audit.

## Initial work allocation

Parallel proof work: characteristic-prime address classification; homogeneous
power-difference order / primitive characterization; LTE and layer valuations.
The main thread is proving coefficient-map and residue-root bridges for the
existing homogeneous evaluator, then will combine these results.

## Initial mathematical obligation

Prove that divisibility of the integral homogeneous evaluation is equivalent
to a root of `Phi_n` at `a*b⁻¹` in `ZMod q`, with `q∤b`. Combine the generic
root classification with order positivity from `q∤a,b`. Preserve degree one
when discussing first appearance: an address set with `n>1` can omit the
true order-one first appearance.

## Checkpoint 02 — multiplicative order bridge checked

`PrimeOrder` proves integral power-difference divisibility iff the residue
ratio's order divides the exponent, assuming only `q∤b` and primality.
For natural subtraction `b≤a` is retained. Nonvanishing of both coordinates
gives positive order dividing `q-1`; no coordinate gcd assumption is needed.
The scalar residue order is identified with the order of the corresponding
actual unit. The existing primitive-prime predicate is equivalent to order
equal to the positive exponent under the same denominator/subtraction boundary.

## Checkpoint 03 — full address law and first appearance checked

`CyclotomicAddress` and `HomogeneousAddress` compiled. For `q∤b`, every
positive homogeneous cyclotomic index satisfies

```text
q | Phi_n(a,b)  iff  exists k, n=orderOf(a*b^(-1) mod q)*q^k.
```

The scalar zero-ratio case is included as order zero and has no positive
address. The theorem includes `q=2`, and does not require `q∤n`.
Away from `q` in the degree, only the order itself can occur.
`FirstLayerAppearance` includes all positive indices; it is equivalent to
order equal to the index and to the existing natural primitive-prime predicate
under the explicit transport hypotheses.

The set `primeLayerAddresses` deliberately uses `n>1`. If the order exceeds
one, its least element is the order. If the order is one, its least element
is `q`; this is a reappearance of degree one and is not globally primitive.
Multiplication of any address by `q` produces a strictly larger address.

## Checkpoint 04 — valuation profile checked within explicit scope

`LayerValuation` supplies odd-prime LTE along `r*q^k` for power differences,
and the separate characteristic-two correction. At unit anchor and order-one
base, odd prime-power cyclotomic layers have valuation one; at prime two the
first layer retains `v_2(a+1)` while subsequent powers have valuation one.
This is not yet the general homogeneous layer valuation profile for arbitrary
order `r`. Divisibility classification does not supply that multiplicity claim.

## Checkpoint 05 — coordinate boundary classified

`CyclotomicBoundary` proves the zero-anchor value `a^totient(n)` and the
remaining cases at positive degrees. If `q|b`, divisibility of the layer is
equivalent to `q|a`. Thus a prime dividing only one coordinate has an empty
address set; a prime dividing both has every `n>1` as its address. This is
the exact boundary outside the nonvanishing order-ray law.

## Checkpoint 06 — support map and counterexample boundaries

`layerPrimeSupport a b n` is the actual set of rational primes dividing the
homogeneous value. `primeLayerAddresses` is its nontrivial-index incidence
fiber. The calibration `Phi_2(2,1)=Phi_6(2,1)=3` gives a formally noninjective
support map. In characteristic three, `Phi_6=Phi_2^2`, explaining the common
root as a genuine polynomial reduction, not equality of characteristic-zero
layer indices.

The order-one boundary has a checked counterexample to a naive Zsigmondy
reinterpretation: for `(a,b,q)=(4,1,3)`, degree 3 is the least `n>1` address,
yet 3 is not primitive at degree 3 because it already divides the linear layer.
The existing primitive definition is also vacuous at degree 0; all new
primitive-order equivalences explicitly retain positive degree.

## Checkpoint 07 — first-layer load strengthened

At the unit anchor, if the residue order is the positive index `n` and the
integer power difference is nonzero, the cyclotomic layer's `padicValInt`
equals that of the full difference `a^n-1`. All proper divisor factors have
valuation zero by the address classification. This gives the actual first
load without imposing a bound. General homogeneous later-layer loads remain
outside the checked valuation scope.

## Checkpoint 08 — Outcome A and final validation complete

Outcome A is selected for the complete reappearance/first-appearance framework,
including both coordinate degeneracies. The combined production/facade and
regression build passed (10372 jobs). The final audit target passed separately
(8966 jobs). All 53 production and 29 named regression declarations have actual
printed dependency lists using only standard axioms or no axioms. All ten new
Lean files had zero forbidden-token matches. One anonymous calibration compiled.

The main build's five existing `sorry` warnings are recorded separately from
the new declarations' dependency closure. Three existing Zsigmondy existence
endpoints were re-audited and retain their original sufficient hypotheses.
See [report-003](report-003.md) and [validation-003](validation-003.md).

## Next mathematical obligation

Instruction 003 is complete within the reported Outcome A classification.
The remaining individual-layer valuation question is to extract the load of
general homogeneous `Phi_(r*q^k)(a,b)` from a full divisor-product valuation,
handling the characteristic-two first layer separately. It is not supplied by
the checked address law or by complete power-difference LTE alone.

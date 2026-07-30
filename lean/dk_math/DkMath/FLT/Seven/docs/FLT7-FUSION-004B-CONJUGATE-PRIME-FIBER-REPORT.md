# FLT7-FUSION-004B conjugate-prime fibre completion report

Date: 2026-07-30

Execution mode: NORMAL

Active phase: N1

Starting commit: `0306290d8d2a3d57102b078dc15513712313b75c`

Ending commit: this N1 checkpoint commit

## Completed Lean facts

For every canonical `CyclotomicLinearPrimeAddress a`, Lean proves:

```text
a.quotientAddress.ratio != a.quotientAddress.ratio⁻¹

a.evalKernel * a.conjugateEvalKernel
  <= a.realPrimeFiberIdeal

a.realPrimeFiberIdeal
  = a.evalKernel * a.conjugateEvalKernel

a.ConjugatePrimeFiberProductEqualityObligation
```

The public theorem names are:

- `ratio_val_ne_inv`;
- `conjugatePrimeProduct_le_realPrimeFiberIdeal`;
- `realPrimeFiberIdeal_eq_conjugateProduct`;
- `conjugatePrimeFiberProductEqualityObligation_holds`.

They are implemented in
`SevenRamifiedFusionCyclotomicConjugatePrimePair.lean`, which is already
imported by the public `DkMath.FLT.Seven` facade.

## Proof route

N1 closes by Route N1-D, the explicit componentwise calculation.

An element of the product ideal belongs to both conjugate kernels. Writing it
in the concrete quadratic pair model gives the two residue equations

```text
eval(re) + ratio * eval(im) = 0
eval(re) + ratio⁻¹ * eval(im) = 0.
```

If `ratio = ratio⁻¹`, its square is one. Together with `ratio^7 = 1` this
would force `ratio = 1`, contradicting the existing nontriviality theorem.
The difference of the two equations therefore forces `eval(im) = 0`, and the
first equation then gives `eval(re) = 0`.

Finally,

```text
x = ofReal x.re + zeta * ofReal x.im
```

shows directly that `x` belongs to the extension of the common real-cubic
kernel. Combining this reverse containment with the previously proved forward
containment gives exact fibre equality.

This route requires no quotient-cardinality comparison, full cyclotomic
integer ring, PID, or class-number machinery.

## New or changed modules

- Changed:
  `SevenRamifiedFusionCyclotomicConjugatePrimePair.lean`
- Added:
  `FLT7-FUSION-004B-CONJUGATE-PRIME-FIBER-REPORT.md`
- Updated execution memos:
  `FLT7-FUSION-004B-ULTRA-ROADMAP.md`,
  `FLT7-FUSION-004B-CONJUGATE-PRIME-FIBER.md`,
  `FLT7-FUSION-004B-CODEX-EXECUTION-INSTRUCTIONS.md`

## Exact remaining obligation

The local conjugate-prime fibre has no remaining obligation.

The next distinct frontier, reserved for an explicitly selected N2 run, is the
finite global oriented factorization launchpad. This N1 checkpoint does not
begin that construction.

The stage still does not claim:

- that the degree-six carrier is the full ring of integers;
- PID or class number one for that carrier;
- element-level seventh-power extraction;
- a primitive additive Fermat chart;
- strict decrease;
- descent closure;
- FLT7.

## Outcome

Outcome A: the requested exact equality was proved directly.

Next recommended execution mode and phase:

```text
NORMAL / N2
```

This recommendation is not activation; operator review and selection are
required before N2 begins.

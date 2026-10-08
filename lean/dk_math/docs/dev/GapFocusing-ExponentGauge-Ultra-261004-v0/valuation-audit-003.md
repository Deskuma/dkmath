# Instruction 003 — valuation audit

## Source/API checkpoint

The complete homogeneous evaluator already exists as
`DkMath.CFBRC.cyclotomicShiftedEval n (a-b) b` in
`DkMath/CFBRC/CyclotomicProduct.lean`. It homogenizes the integer cyclotomic
polynomial at its natural degree, using Mathlib `Polynomial.homogenize`.
This is the reusable value object for arbitrary layers. Its existing field
formula is `cyclotomicShiftedEval_eq_cyclotomicEval_div_mul_pow`.

`DkMath.CosmicFormula.GTailCyclotomicHomEval p Φ x u` is a different, earlier
finite coefficient evaluation at prescribed homogeneous degree `p-1`.
Its prime-index shell bridge is useful for GN, but is not the general
natural-degree homogeneous evaluator. No duplicate evaluator was introduced.
The unit-anchor results use the existing neutral
`DkMath.Lib.NumberTheory.cyclotomicEval`.

The following current Mathlib APIs were inspected directly:

| File/API | Scope and explicit assumptions |
| --- | --- |
| `NumberTheory/Multiplicity.lean`, `padicValNat.pow_sub_pow` | Odd prime `q`, `b<a`, `q ∣ a-b`, `q ∤ a`, nonzero exponent. Gives `v_q(a^n-b^n)=v_q(a-b)+v_q(n)`. |
| Same file, `padicValNat.pow_two_sub_pow` | `b<a`, `2 ∣ a-b`, `2 ∤ a`, nonzero even exponent. Gives `v₂(a^n-b^n)+1=v₂(a+b)+v₂(a-b)+v₂(n)`. |
| `RingTheory/Polynomial/Cyclotomic/Basic.lean`, `cyclotomic_prime_pow_eq_geom_sum` | Prime-power cyclotomic polynomial as a geometric sum over any commutative ring. |
| Same file, `cyclotomic_prime_pow_mul_X_pow_sub_one` | Exact factorization for adjacent prime-power exponents over any commutative ring. |
| `RingTheory/Polynomial/Cyclotomic/Expand.lean` | Characteristic-prime layer identities and root propagation; these classify divisibility but do not provide characteristic-zero multiplicities. |
| `NumberTheory/Padics/PadicVal/Basic.lean`, `padicValNat.mul`, `.prime_pow` | Additivity for nonzero natural products and prime-power valuation. |

The inspected Mathlib cyclotomic evaluation and expansion modules do not
contain a ready theorem giving the valuation of every homogeneous layer along
an arbitrary order ray. Divisibility/root statements alone cannot supply it.

## Checked general LTE checkpoint

`DkMath/NumberTheory/GapFocusing/LayerValuation.lean` proves
`padicValNat_pow_sub_pow_mul_prime_pow`. For prime odd `q`, `b<a`, `r≠0`,
`q∤a`, and `q ∣ a^r-b^r`, every `k` satisfies

```text
v_q(a^(r*q^k) - b^(r*q^k)) = v_q(a^r-b^r) + k.
```

No coordinate coprimality is needed beyond these explicit hypotheses.
This is a valuation formula for the **complete power difference**, not for
one selected cyclotomic factor.

At `q=2`, `padicValNat_pow_sub_pow_mul_two_pow_succ` separately proves,
under `b<a`, `r≠0`, `2∤a`, `2 ∣ a^r-b^r`,

```text
v₂(a^(r*2^(k+1)) - b^(r*2^(k+1)))
  = v₂(a^r+b^r) + v₂(a^r-b^r) + k.
```

The sum term is required; silently substituting `q=2` into odd-prime LTE
would erase this correction.

## Checked individual-layer checkpoint

`padicValInt_cyclotomicEval_eq_pow_sub_one_of_orderOf_eq` gives the general
unit-anchor first-address formula. For any integer `a`, prime `q`, positive
index `n`, `orderOf (a : ZMod q)=n`, and `a^n-1≠0`,

```text
v_q(Φ_n(a)) = v_q(a^n-1).
```

This theorem applies to an arbitrary fundamental address, including `n=1`.
The proof uses the exact cyclotomic divisor product and the checked address law
to show that every proper divisor factor has zero `q`-valuation. It preserves
the full first-layer load and asserts no upper bound on that load.

The same production file proves exact individual-layer formulas for prime-power
indices on the unit anchor:

- `padicValNat_cyclotomicEval_prime_pow_eq_one`: for an odd prime `q`,
  `1<a`, `q∤a`, `q ∣ a-1`, every layer `Φ_(q^(k+1))(a)` has valuation `1`.
- `padicValNat_cyclotomicEval_two`: for every natural `a`, the first layer
  satisfies `v₂(Φ₂(a))=v₂(a+1)`.
- `padicValNat_cyclotomicEval_two_pow_succ_eq_one`: if `1<a`, `2∤a`,
  `2 ∣ a-1`, every layer `Φ_(2^(k+2))(a)` has valuation `1`.

The proof extracts the prime-power geometric sum from the existing evaluator,
uses its exact power-difference factorization, then applies LTE to two
successive exponents. Nonzero conditions are proved before valuation additivity.
The assumptions `q∤a` and `q ∣ a-1` are both stated explicitly; their conjunction
is mathematically redundant in the first formula but safe and usable.

These results give genuine infinite families, including the exceptional first
`2`-layer. They do not yet prove that every later homogeneous layer at an
arbitrary fundamental address `r>1` has valuation one. For that further theorem,
one must extract individual factor loads from a complete divisor-product
valuation, using the checked address law and handling `q=2` separately.

## Primitive multiplicity checkpoint

`DkMathTest/NumberTheory/GapFocusingLayerValuation.lean` keeps the calibrations
visible using the actual evaluators:

- `Φ₂(2)=3` and `Φ₆(2)=3`, both carrying `3`-adic valuation `1`.
- `Φ₂(3)=4` has `2`-adic valuation `2`, while every later `2`-power layer at
  `a=3` has valuation `1`.
- `cyclotomicShiftedEval 3 (2:ℤ) 3 = Φ₃(5,3)=49`.
- `DkMath.Zsigmondy.PrimitivePrimeDivisor 5 3 3 7`, and the same homogeneous
  layer has `7`-adic valuation `2`.

The final example disproves the inference “primitive prime implies valuation
one.” It also lies in a first-address layer with `7∤3`; excluding primes
dividing the index does not impose a first-layer load-one bound.

The earlier checked `ZsigmondyCyclotomicSquarefree` API only obtains an upper
bound from an explicit squarefree GN hypothesis; the `NoLift` route requires
its explicit no-square-divisibility hypothesis. The legacy unconditional
research endpoints in `ZsigmondyCyclotomicResearch` and `GcdNextResearch`
must not enter production dependencies. This implementation imports neither.

## Verification checkpoint

Production `LayerValuation` built successfully with eight public theorems.
The regression target `DkMathTest.NumberTheory.GapFocusingLayerValuation`
also built successfully (8952 jobs), printing dependencies of all eight production and eight calibration
declarations. Each dependency list contains
only `propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`.
Evidence is in `logs/build-layer-valuation-003.txt`. Final combined validation
is recorded by the parent task in `validation-003.md`.

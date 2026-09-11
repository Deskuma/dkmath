# FLT prime-generalization Phase 21 — generic TraceOne conjugate-coprime bridge

## Scope and outcome

This report records the bounded implementation requested by
`instruction-021.md`.  The exponent-independent TraceOne conjugate-coprime
kernel is now implemented.  The arbitrary-prime Phase-13 coordinate
primitivity theorem remains an explicit bridge obligation and is not asserted
by receiver assumptions.

The phase statuses are:

~~~text
PGEN-TRACEONE-CONJUGATE-COPRIME-KERNEL-GREEN
PGEN-PRIME-COORDINATE-COPRIME-CYCLOTOMIC-BRIDGE-MISSING
~~~

No FLT theorem, class-group torsion-freeness theorem, class-number theorem, or
sector elimination was added.

## A. Neutral algebra separated from the p=7 proof

The p=7 declarations in `DkMath/FLT/Seven/PrimitiveCoordinateCoprime.lean`
were separated into the following neutral production declarations in
`DkMath/NumberTheory/TraceOneDiscriminantAxis.lean`:

~~~lean
sub_conj_eq_snd_mul_discrAxis
discrAxis_mul_sub_tau_mul_sub_conj
common_divisor_dvd_discrAxis_of_coordinate_coprime
~~~

They use only the `TraceOneInt s` ring operations, `tau`, `conj`, the
discriminant axis, and coordinate Bézout.  The specialized p=7 polynomial
coordinate theorem remains in the p=7 namespace.

## B. Generic discriminant-axis primality

`DkMath/NumberTheory/TraceOneConjugateCoprime.lean` adds:

~~~lean
discrAxis_ne_zero_of_packet
PrimeDiscriminantPacket.prime_discrAxis
~~~

For a `PrimeDiscriminantPacket p s` and an explicit
`IsDomain (TraceOneInt s)` instance, primality is proved from

~~~text
discrAxis s ∣ x  <->  p ∣ natAbs (norm x)
norm (x*y) = norm x * norm y.
~~~

The nonzero and nonunit fields of the pinned `Prime` API are discharged from
the packet norm and the same divisibility equivalence.  No global domain
instance is installed.

## C. Principal axis ideal

The same production module adds

~~~lean
PrimeDiscriminantPacket.discrAxis_span_isMaximal
~~~

It obtains primality of `Ideal.span {discrAxis s}` from the prime element,
proves the principal ideal is nonzero, and applies
`Ideal.IsPrime.isMaximal` with `Ring.DimensionLEOne`.  A Dedekind carrier
supplies both the domain and one-dimensional hypotheses; no PID/UFD theorem
is introduced.

## D. Ideal-level conjugate coprimality

The public kernel is:

~~~lean
ideal_isCoprime_span_conj_of_coordinate_coprime_of_axis_terminal
~~~

Given `IsCoprime w.fst w.snd`, `¬ discrAxis s ∣ w`, a prime-discriminant
packet, and the domain/one-dimensional carrier hypotheses, the proof puts the
axis into

~~~text
Ideal.span {w} ⊔ Ideal.span {conj w}
~~~

using the two neutral coordinate identities and Bézout.  Maximality of the
axis ideal then rules out the non-top sum: that case would put `w` in the axis
ideal and contradict terminality.  The result is the required ideal
coprimality, without introducing a `GCDMonoid`.

## E. Conditional one-axis stripping and norm p-th power

The production module also adds:

~~~lean
PrimeDiscriminantPacket.exists_terminal_discrAxis_mul_of_natAbs_norm_eq_prime_mul_pow
~~~

Under the explicit input

~~~text
natAbs (norm x) = p * c^p
p ∤ c,
~~~

the theorem returns one axis factor, a nonzero axis-terminal residual, and an
integer `k` with `norm residual = k^p`.  The real-branch sign is absorbed by
`(-c)^p` using oddness of `p`.  This is the neutral normalization endpoint;
it intentionally does not claim that the Phase-13 polynomial coordinates
provide the input equality.

## F. Phase-13 primitive-coordinate audit

`DkMathTest/FLT/Prime/TraceOneConjugateCoprimeApiAudit.lean` pins the current
source APIs, including:

~~~lean
GTail_one_eq_GTailCyclotomicShell_of_ne_zero
exists_prime_traceOne_coordinates
PrimeAdicPowerSplit.residual_eq
~~~

The existing `exists_prime_traceOne_coordinates` theorem provides existential
integer polynomials `AZ`, `SZ` and only the norm equality to
`GTailCyclotomicShell`.  It does not provide

~~~text
Nat.Coprime z y -> IsCoprime (eval AZ z y) (eval SZ z y).
~~~

The current checkout also has no resultant/Bezout theorem for these
Phase-13 coordinate polynomials and no cyclotomic QR/QNR theorem that
transports endpoint primitivity through the polynomial realization.  Thus the
smallest honest current blocker is
`PGEN-PRIME-COORDINATE-COPRIME-CYCLOTOMIC-BRIDGE-MISSING`.  This is an audit
result, not a claim that the mathematical bridge is false.

## G. Conditional Phase-15 boundary

The GREEN kernel can be applied once a Phase-13 or other upstream source
supplies coordinate coprimality and axis terminality for the stripped residual.
The implemented endpoint stops at the terminal residual and the ideal
coprimality theorem.  The Phase-15 ideal p-th-power composition is not claimed
because the arbitrary-prime primitive-coordinate bridge is still open.

## H. Regressions

`DkMathTest/FLT/Prime/TraceOneConjugateCoprimeProbe.lean` checks:

~~~text
p=3   generic ideal carrier
p=5   TraceOneInt 1 common-divisor kernel and one-axis norm normalization
p=7   specialized cyclotomic coordinate shape through the generic kernel
p=11  TraceOneInt -3 prime-axis API
p=13  TraceOneInt 3 ideal-coprimality API
~~~

`DkMathTest/FLT/Prime/TraceOneConjugateCoprimeAxiomAudit.lean` prints the
axiom dependencies of the neutral identities, axis primality, maximality,
ideal coprimality, and one-axis normalization theorem.

## I. Focused validation

The following commands were run successfully from `lean/dk_math`:

~~~text
lake build DkMath.NumberTheory.TraceOneDiscriminantAxis
lake build DkMath.NumberTheory.TraceOneQuadraticField
lake build DkMath.NumberTheory.CyclotomicQRTraceOneBridge
lake build DkMath.FLT.Prime.AdicPowerSplit
lake build DkMath.NumberTheory.TraceOneConjugateCoprime
lake build DkMathTest.FLT.Prime.TraceOneConjugateCoprimeApiAudit
lake build DkMathTest.FLT.Prime.TraceOneConjugateCoprimeProbe
lake build DkMathTest.FLT.Prime.TraceOneConjugateCoprimeAxiomAudit
lake build DkMath.FLT.Seven
git diff --check
~~~

The fresh Phase-21 focused log has no non-sorry warning lines.  The existing
repository test log separately records the unrelated pre-existing warning
`DkMath/NumberTheory/ZsigmondyCyclotomicResearch.lean:147`.

No new `sorry`, `sorryAx`, `admit`, `axiom`, `unsafe`, or
`NumberField.discr` occurrence was added in the Phase-21 production and test
files.

## J. Non-goals

This phase does not prove the arbitrary-prime primitive-coordinate theorem,
does not infer it from the norm shell, does not prove class-group
p-torsion-freeness or unit-sector elimination, and does not establish FLT.

# FLT7TC-000 — Exact p=7 TraceOne closure reconnaissance

## Outcome

```text
Outcome B — the ramified generic endpoint is checked, but the
generic-parent-to-specialized-coordinate bridge is absent.
```

The p=7 generic `PrimeTraceOne` route already reaches an unconditional exact
seventh-power residual.  The recurrence-coordinate receiver is also checked.
The existing specialized p=7 arithmetic can consume the recurrence power
after one small coordinate bridge.  It cannot yet consume the provenance of
the generic parent: the current packet API exposes only a norm identity for
an arbitrary `PrimeTraceOneCoordinatePacket`, and the stripped packet does not
retain a field identifying its `parent` with `P.coord (g + u) u`.

This is a reconnaissance report only.  No production Lean file was changed.

## Scope and source boundary

The attached `instruction-000.md` is treated as the bounded checkpoint
contract, separate from the user's request to read, reason, and implement.
That contract permits only this report as a persistent artifact.  The
campaign README and roadmap explicitly make this checkpoint read-only and
defer production bridges to FLT7TC-001/002.

The relevant source/build project is `lean/dk_math`, under Lean 4.34.

## Q1. Exact p=7 endpoint

### Coordinate endpoint

`DkMath.FLT.Prime.exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven`
in
`DkMath/FLT/Prime/PrimeTraceOneCoordinateReceiver.lean:87-106` has the
following complete type, with the displayed local typeclass assumptions:

```lean
theorem exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    ∃ m n : ℤ,
      Q.residual.fst =
        (traceOnePowCoords (signedPrimeParameter 7) m n 7).1 ∧
      Q.residual.snd =
        (traceOnePowCoords (signedPrimeParameter 7) m n 7).2
```

The theorem calls the generic receiver with `p = 7`, proves `7 ≤ 7` and
`7 % 4 = 3`, and supplies the already checked
`classGroupPTorsionFreeAt_traceOneNegTwo_seven`.  The latter proves

```lean
classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
```

by `classGroupPTorsionFreeAt_of_isPrincipalIdealRing 7`, in
`DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean:22-25`.
The endpoint normalizes `signedPrimeParameter 7` to `-2`, so its carrier is
`TraceOneInt (-2)`.

There is no caller-supplied class-group premise in the p=7 coordinate
endpoint.

### Element-level seventh-power endpoint

The separately exposed element theorem is
`DkMath.FLT.Prime.exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven`
in
`DkMath/FLT/Prime/PrimeTraceOneClassGroupClosure.lean:29-55`:

```lean
theorem exists_eq_pow_of_primeTraceOneImaginaryStrippedIdealPacket_seven
    {L : Type*} [Field L] [Algebra ℚ L]
    {g u x : ℕ} [Fact (Nat.Prime 7)]
    [IsCyclotomicExtension {7} ℚ L]
    {ζ : L} {hζ : IsPrimitiveRoot ζ 7}
    (P0 : PrimeAdicFactorPacket 7 g u x)
    (P : PrimeTraceOneCoordinatePacket L 7 ζ hζ)
    (Q : PrimeTraceOneStrippedIdealPacket L P0 P) :
    let : IsDomain (TraceOneInt (signedPrimeParameter 7)) := by
      rw [show signedPrimeParameter 7 = -2 by
        norm_num [signedPrimeParameter, signedPrimeDiscriminant]]
      infer_instance
    ∃ delta : TraceOneInt (signedPrimeParameter 7),
      Q.residual = delta ^ 7
```

Its dependency chain is:

```text
P0
  -> primeAdicPowerSplit_of_packet P0
  -> p=7 adic split and prime_not_dvd_b
P0, P
  -> parent := P.coord (g+u) u
  -> terminal residual and axis_eq
Q
  -> Q.residual_span_eq, Q.idealRoot_nonzero
  -> traceOnePrimeImaginary_exists_eq_pow_of_span_eq_pow
  -> classGroupPTorsionFreeAt (TraceOneInt (-2)) 7
  -> delta with Q.residual = delta^7
delta equality
  -> traceOne_pow_core_landing_iff with beta = 1 and r = 7
  -> exact recurrence coordinates
```

The p=7 class-group step is structural and Euclidean/PID-based.  No
specialized FLT7 contradiction is called.

## Q2. `PrimeTraceOneStrippedIdealPacket` invariant surface

The structure is in
`DkMath/FLT/Prime/PrimeTraceOneStrippedIdeal.lean:35-59`.
Its fields are:

| field | content | p=7 consumer status |
|---|---|---|
| `adicSplit` | `PrimeAdicPowerSplit p g u x` | Natural-number front-end data; useful for recovering the exact p=7 gap/residual shape, but not a pure `TraceOneInt (-2)` fact. |
| `parent` | `TraceOneInt (signedPrimeParameter p)` | Generic parent element; at p=7 it is in `TraceOneInt (-2)`, but its provenance is not stored in the structure. |
| `residual` | `TraceOneInt (signedPrimeParameter p)` | Main p=7 arithmetic consumer. |
| `axis_eq` | `parent = discrAxis (signedPrimeParameter p) * residual` | Main scale-axis relation; needs the checked p=7 adapter `discrAxis (-2) = sevenAxis`. |
| `parent_coordinate_coprime` | `IsCoprime parent.fst parent.snd` | Relevant only to parent-side arithmetic or construction audits; not enough to identify the parent polynomial. |
| `residual_coordinate_coprime` | `IsCoprime residual.fst residual.snd` | Direct consumer.  Together with `7 ∣ residual.snd`, it gives `7 ∤ residual.fst`; with the seventh-power equality it also feeds the existing root-primitivity theorem. |
| `residual_norm_ne_zero` | `norm residual ≠ 0` | Direct nonzero/normalization invariant. |
| `residual_axis_terminal` | `¬ discrAxis (...) ∣ residual` | Direct terminality invariant; via the p=7 discriminant packet it gives 7-unit norm. |
| `residual_norm_pow` | `∃ k : ℤ, norm residual = k ^ p` | Used in the ideal-power construction; redundant for the root-side norm calculation after `residual = delta^7`. |
| `residual_conj_ideal_coprime` | coprimality of the principal residual and conjugate ideals | Ideal-level input to `residual_span_eq`; not itself a coordinate contradiction. |
| `idealRoot` | an ideal of `TraceOneInt (signedPrimeParameter p)` | Principalization/class-group input only. |
| `idealRoot_nonzero` | `idealRoot ∈ (Ideal R)⁰` | Required by the class-group closure theorem. |
| `residual_span_eq` | `Ideal.span {residual} = idealRoot ^ p` | Exact ideal-power input to the p=7 principalization theorem. |

The structure parameters `P0` and `P` are parameters, not fields.  In
particular, there is no field of the form

```lean
parent_eq_coord : parent = P.coord (g + u : ℤ) (u : ℤ)
```

The constructor proof locally defines `parent` to be that coordinate at
`PrimeTraceOneStrippedIdeal.lean:137-139`, but the equality is not retained
in the packet type.  This matters in Q6.

### p=7 `adicSplit` specialization

`PrimeAdicPowerSplit` is defined in
`DkMath/FLT/Prime/AdicPowerSplit.lean:71-81`.  At `p = 7` its relevant
fields become:

```lean
a_pos              : 0 < a
b_pos              : 0 < b
coprime_a_b        : Nat.Coprime a b
gap_eq             : g = 7 ^ 6 * a ^ 7
residual_eq        : GTail 7 1 g u = 7 * b ^ 7
distinguished_eq   : x = 7 * a * b
prime_not_dvd_b    : ¬ 7 ∣ b
```

`input` remains the original `PrimeAdicFactorPacket 7 g u x`, whose fields
are natural-number facts: `prime`, `odd`, `gap_pos`, `distinguished_pos`,
`coprime_gap_unit`, `prime_dvd_gap`, and
`factor_eq : g * GTail 7 1 g u = x ^ 7`.

Thus `adicSplit` still mentions the original `(g,u,x)` world.  The fields
`parent`, `residual`, all axis/norm/coordinate facts, and the ideal fields live
in `TraceOneInt (-2)` after p=7 normalization.  The only link back to the
original coordinate packet is construction-local; it is not a packet
invariant.

## Q3. Generic recurrence versus explicit seventh-power coordinates

The generic side is checked by
`DkMath.Lib.NumberTheory.traceOne_pow_coordinates` in
`DkMath/Lib/NumberTheory/TraceOnePowerLanding.lean:47-58`:

```lean
(⟨m, n⟩ : TraceOneInt s) ^ r =
  ⟨(traceOnePowCoords s m n r).1,
   (traceOnePowCoords s m n r).2⟩
```

The specialized side is checked by
`DkMath.FLT.Seven.traceOne_pow_seven_eq` in
`DkMath/FLT/Seven/SeventhPowerCoordinates.lean:27-44`:

```lean
(⟨m, n⟩ : TraceOneInt (-2)) ^ 7 =
  ⟨seventhPowerFst m n, seventhPowerSnd m n⟩
```

No direct theorem with either of the following exact target shapes was found:

```lean
(traceOnePowCoords (-2) m n 7).1 = seventhPowerFst m n
(traceOnePowCoords (-2) m n 7).2 = seventhPowerSnd m n
```

Therefore these are missing bridge lemmas, not missing mathematics.  The
minimal proof compares the two checked descriptions of the same element
`(⟨m,n⟩ : TraceOneInt (-2)) ^ 7`, using `congrArg TraceOneInt.fst` and
`congrArg TraceOneInt.snd`.  It should not re-expand the seventh power a
second time.

The minimal import boundary for that bridge is:

```text
DkMath.Lib.NumberTheory.TraceOnePowerLanding
DkMath.FLT.Seven.SeventhPowerCoordinates
```

No generic FLT packet, historical FLT7 tower, or final contradiction is
needed.  `signedPrimeParameter 7 = -2` is the separate small normalization
already used by the p=7 endpoint.

After this bridge and that normalization, the generic receiver can be
rewritten exactly as:

```lean
∃ m n,
  Q.residual.fst = seventhPowerFst m n ∧
  Q.residual.snd = seventhPowerSnd m n
```

This is only a residual-root coordinate statement.  It does not identify
`Q.parent` with `cyclotomicSevenToTraceOne`.

## Q4. Axis terminality and root-side 7-unit norm

The generic axis theorem is
`PrimeDiscriminantPacket.discrAxis_dvd_iff_prime_dvd_natAbs_norm` in
`DkMath/NumberTheory/TraceOneDiscriminantAxis.lean:242-255`.
For the p=7 packet at `s = -2` it gives:

```lean
discrAxis (-2) ∣ Q.residual ↔
  7 ∣ Int.natAbs (norm Q.residual)
```

The needed p=7 equality is not a named adapter in the current source, but it
is a checked two-line equality:

```lean
example : discrAxis (-2) = sevenAxis := by
  rw [discrAxis_eq, sevenAxis_eq]
```

The generic and specialized definitions both reduce to `⟨-1, 2⟩`; they
should not be treated as silently definitionally equal in a consumer theorem.
The existing compatibility audit records this exact adapter in
`DkMathTest/FLT/Prime/TraceOneDiscriminantAxisCompatibility.lean:27-39`.

Consequently, without new mathematics:

```text
Q.residual_axis_terminal
  -> ¬ discrAxis (-2) ∣ Q.residual
  -> ¬ 7 ∣ Int.natAbs (norm Q.residual)
  -> ¬ (7 : ℤ) ∣ norm Q.residual.
```

The final presentation uses the standard `Int.natCast_dvd` conversion.  The
specialized alternative is
`sevenAxis_dvd_iff_seven_dvd_norm` in
`DkMath/FLT/Seven/AxisDivisibility.lean:76-80`, together with
`sevenAxis_norm` from `DkMath/NumberTheory/TraceOneQuadratic.lean`.

Now let

```lean
hdelta : Q.residual = delta ^ 7
```

be supplied by the p=7 element endpoint.  The neutral theorem
`DkMath.Lib.NumberTheory.traceOne_norm_pow` gives

```text
norm Q.residual = norm delta ^ 7.
```

If `7 ∣ norm delta`, primality gives `7 ∣ norm delta ^ 7`, hence
`7 ∣ norm Q.residual`, contradicting the terminal result.  Therefore the
current checked surface also yields:

```lean
¬ (7 : ℤ) ∣ norm delta
```

No root-side positivity or primitive-root assumption is used in this step.
The role of `sevenAxis_norm : norm sevenAxis = 7` and norm multiplicativity
is the same specialized one-layer calculation; the generic discriminant
packet already supplies the more neutral route.

## Q5. Consequences of the explicit factorization

Assume Q3's coordinate bridge and Q4's root norm result.  The following
classification is exact:

| target | status | reason |
|---|---|---|
| `7 ∣ Q.residual.snd` | immediate | `seventhPowerSnd_eq_seven_mul` in `SeventhPowerCoordinates.lean:51-54`, followed by the Q3 equality. |
| `¬ 7 ∣ seventhPowerSndCore m n` | immediate | `seven_not_dvd_seventhPowerSndCore_of_norm` in `SeventhPowerCoordinates.lean:95-109`, using `¬ 7 ∣ norm delta`. |
| `49 ∣ Q.residual.snd ↔ 7 ∣ n` | immediate | `fortyNine_dvd_seventhPowerSnd_iff` in `SeventhPowerCoordinates.lean:111-126`, with the root norm hypothesis. |
| `Q.residual.fst mod 7 = m + 4*n` | immediate in `ZMod 7`; small presentation adapter for integer `%` | The checked theorem is `seventhPowerFst_mod_seven` in `SeventhPowerCoordinates.lean:68-78`. It gives `(seventhPowerFst m n : ZMod 7) = m + 4*n`; an `Int.emod` statement is not the theorem's current surface. |
| `¬ 7 ∣ Q.residual.fst` | immediate | From `Q.residual_coordinate_coprime` and `7 ∣ Q.residual.snd`, since a prime dividing both coordinates contradicts `IsCoprime`. Axis terminality is not needed. |

The companion theorem
`seventhPowerSnd_mod_seven` in `SeventhPowerCoordinates.lean:80-85`
also records the second-coordinate congruence directly in `ZMod 7`.

### Does primitivity descend from `delta^7` to `delta`?

Yes, for the exact specialized carrier, an existing theorem already proves
it:

```lean
coordinates_isCoprime_of_pow_seven_coordinates_isCoprime
    (root : TraceOneInt (-2))
    (hpow : IsCoprime (root ^ 7).fst (root ^ 7).snd) :
    IsCoprime root.fst root.snd
```

It is in
`DkMath/FLT/Seven/SevenBaseTerminalRamifiedQuadraticInnerRoot.lean:34-74`.
With `hdelta` and `Q.residual_coordinate_coprime`, `hpow` is obtained by
rewriting the residual coordinates.  Thus root-coordinate primitivity need
not be assumed silently.

This theorem is not part of the neutral generic `Prime` API.  Its current
import boundary is the specialized ramified inner-root module (which itself
imports the specialized ramified tower).  Reusing it is mathematically
honest for a p=7 consumer, but a small neutral gcd-power lemma would be a
cleaner dependency if the next checkpoint wants to avoid that tower.

## Q6. Parent-coordinate provenance boundary

### What the generic packet actually proves

`PrimeTraceOneCoordinatePacket` is the structure in
`DkMath/NumberTheory/CyclotomicQRTraceOneBridge.lean:294-318`.
It stores `RZ`, `SZ`, `AZ`, the map/Gauss/half-relation certificates, and
the norm identity.  Its coordinate evaluation is:

```lean
P.coord z y =
  ⟨MvPolynomial.eval ![z, y] P.AZ,
   MvPolynomial.eval ![z, y] P.SZ⟩
```

The only exposed evaluation theorem is:

```lean
P.coord_norm_eq z y :
  norm (P.coord z y) = GTailCyclotomicShell p (z - y) y
```

The existential constructor
`exists_prime_traceOne_coordinate_packet` at
`CyclotomicQRTraceOneBridge.lean:340-373` proves only `Nonempty` of this
packet.  It does not provide a canonical p=7 constructor, a uniqueness
theorem, or an orientation/sign/conjugation/permutation theorem.

### What the specialized package proves

`DkMath.FLT.Seven.cyclotomicSevenToTraceOne` is the explicit pair

```lean
⟨cyclotomicSevenFst z y, cyclotomicSevenSnd z y⟩
```

in `DkMath/FLT/Seven/QuadraticBridge.lean:19-45`.  Its checked norm relation
is

```lean
cyclotomicSeven z y =
  norm (cyclotomicSevenToTraceOne z y)
```

The specialized API also proves divisibility, coordinate coprimality, and
seventh-power formulas for this explicit pair.  Those theorems do not mention
`PrimeTraceOneCoordinatePacket` or `P.coord`.

The p=7 generic and specialized surfaces therefore currently meet only at a
norm level, after the separate `GTailCyclotomicShell`/`GN` normalization.
There is no checked theorem establishing any of:

```text
P.coord (g+u) u = cyclotomicSevenToTraceOne (g+u) u
P.coord (g+u) u = conj (cyclotomicSevenToTraceOne (g+u) u)
P.coord (g+u) u = ± cyclotomicSevenToTraceOne (g+u) u
an exact coordinate permutation/orientation equivalence
```

Equality of the two norms is not enough to infer any of these element
relations.

There is a second, independent provenance loss: the definition of
`PrimeTraceOneStrippedIdealPacket` has `parent` as an unconstrained field
except for `axis_eq` and coprimality.  The constructor happens to set it to
`P.coord (g+u) u`, but an arbitrary `Q` accepted by
`exists_powCoords_of_primeTraceOneImaginaryStrippedIdealPacket_seven` carries
no theorem recovering that equality.

### Exact missing bridge

The next checkpoint therefore needs one of the following checked designs:

1. a canonical p=7 `PrimeTraceOneCoordinatePacket` plus an exact equality to
   `cyclotomicSevenToTraceOne`;
2. a proved sign/conjugation/orientation relation strong enough for the
   intended obstruction; or
3. an explicit provenance field/constructor theorem for `parent`, together
   with an obstruction proved invariant under the remaining orientation.

The existing `SevenAdicCounterexamplePacket.toPrimeAdicFactorPacket` in
`DkMath/FLT/Seven/SevenAdicPowerSplit.lean:16-25` bridges only the natural
`PrimeAdicFactorPacket`; it does not solve this TraceOne coordinate problem.
Likewise, the specialized
`SevenQuadraticSeventhPowerPacket` packages
`cyclotomicSevenToTraceOne = sevenAxis * root ^ 7`, but it is constructed from
the specialized quadratic residual packet, not from an arbitrary generic
`PrimeTraceOneCoordinatePacket`.

## Current frontier and non-claims

The strongest checked ramified data are:

```text
Q.residual = delta^7
Q.residual = ⟨seventhPowerFst m n, seventhPowerSnd m n⟩
¬ 7 ∣ norm delta
IsCoprime delta.fst delta.snd        (using the existing specialized theorem)
7 ∣ Q.residual.snd
¬ 7 ∣ seventhPowerSndCore delta.fst delta.snd
49 ∣ Q.residual.snd ↔ 7 ∣ delta.snd
¬ 7 ∣ Q.residual.fst
```

These facts do not yet give a contradiction.  In particular, this checkpoint
does not claim:

```text
generic parent = cyclotomicSevenToTraceOne
generic parent has specialized p=7 coordinates
ramified branch is contradictory
away branch is contradictory
unconditional FLT7
```

The immediate implementation target is the small recurrence-to-explicit
coordinate bridge (FLT7TC-001).  The parent provenance/orientation bridge is
the separate, materially stronger FLT7TC-002 frontier.

## Validation performed

The source-level audit used the exact declarations listed above and the
existing compatibility audit for `discrAxis (-2) = sevenAxis`.  The report
was the only persistent file added in this checkpoint; no production Lean
source or test source was edited.

The focused build from `lean/dk_math` passed for:

```text
lake build DkMath.FLT.Prime.PrimeTraceOneCoordinateReceiver
lake build DkMath.FLT.Prime.PrimeTraceOneClassGroupClosure
lake build DkMath.FLT.Seven.SeventhPowerCoordinates
lake build DkMath.FLT.Seven.AxisDivisibility
lake build DkMathTest.FLT.Prime.TraceOneDiscriminantAxisCompatibility
lake build DkMathTest.FLT.SevenSeventhPowerCoordinates
```

The combined replay completed successfully (`9139` jobs).  The existing
TraceOne/axis linter warnings were non-fatal.  `git diff --check` passed for
tracked changes, and `git diff --no-index --check /dev/null report-000.md`
reported no whitespace diagnostics for the new untracked report.

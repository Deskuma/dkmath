# FLT7 prime-generalization Lean probe report 000

## Scope and dependency surface

The attached inventory and instruction were treated as the bounded stage
contract. This report covers only the requested probe. The FLT7 proof tower
was not modified.

The probe is
`DkMathTest.FLT.Prime.GeneralizationProbe`.
Its source imports only:

- `DkMath.Lib.Cosmic.GTailBoundary`
- `DkMath.Lib.Cosmic.GTailCongruence`
- `DkMath.Lib.NumberTheory.PadicValNat`

There is no source import from `DkMath.FLT.Seven`.

## Probe A — exact r=1 boundary gcd

Compiled statements:

```lean
theorem gcd_GN_eq_gcd_of_one_le
    {d g u : ℕ} (hd : 1 ≤ d) (hcop : Nat.Coprime g u) :
    Nat.gcd g (GTail d 1 g u) = Nat.gcd g d

theorem gcd_GN_prime_eq_gcd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u) :
    Nat.gcd g (GTail p 1 g u) = Nat.gcd g p

theorem gcd_GN_prime_eq_one_of_not_dvd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u)
    (hpg : ¬ p ∣ g) :
    Nat.gcd g (GTail p 1 g u) = 1

theorem gcd_GN_prime_eq_prime_of_dvd
    {p g u : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    Nat.gcd g (GTail p 1 g u) = p
```

Classification: `PGEN-GREEN`.

The exact gcd theorem already follows from
`DkMath.CosmicFormula.gcd_GTail_eq_gcd_choose`; primality is not needed
there. The minimal arithmetic condition is `1 ≤ d`, needed because the
theorem is at `r = 1`. Primality is needed only for the branch dichotomy
`gcd g p = 1` or `p`.

This is the direct general replacement for the current FLT7 gcd branch
lemmas, without expanding the degree-seven Pascal row.

## Probe B — prime divisibility address

Compiled statement:

```lean
theorem prime_dvd_GN_iff_dvd_gap
    {p g u : ℕ} (hp : Nat.Prime p) :
    p ∣ GTail p 1 g u ↔ p ∣ g
```

Classification: `PGEN-GREEN`.

The minimal assumption is `Nat.Prime p`; no coprimality, positivity of `g`
or `u`, or endpoint ordering is required. The reverse direction uses the
existing mod-`p` collapse. The forward direction was checked from the finite
prime Pascal row: all terms before the terminal term are divisible by `p`,
while the terminal term is `g^(p-1)` modulo `p`. This row helper is currently
probe-local; no missing reusable core theorem was needed for the probe,
although extracting that helper into `DkMath.Lib.Cosmic` would be a
reasonable later API cleanup.

The theorem includes `p = 2`. The probe also checks the concrete instance
`2 ∣ GTail 2 1 g u ↔ 2 ∣ g`.

Relative to FLT7, this is the direct prime-exponent form of
`seven_dvd_GN_seven_sub_iff`; the probe uses the already normalized gap `g`
instead of reconstructing it as `a - b`.

## Probe C — sharpened prime-row mod-p² congruence

Compiled statement:

```lean
theorem GN_modEq_head_mod_sq_of_odd_prime_dvd_x_probe
    {p : ℕ} (g u : ℕ)
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hpg : p ∣ g) :
    GTail p 1 g u ≡ p * u ^ (p - 1) [MOD p ^ 2]
```

Classification: `PGEN-GREEN`.

The proof is a direct specialization of
`GTail_modEq_head_mod_sq_of_prime_dvd_x` with `r = 1`. The real condition is
`2 < p`, represented in the requested statement by `3 ≤ p`. Therefore the
existing `5 ≤ p` convenience theorem is unnecessarily strong for this
statement. No production API was changed in this phase.

This is the generic counterpart of the mod-`49` front-half input used by the
FLT7 valuation route.

## Probe D — exact odd-prime residual valuation

Compiled statement:

```lean
theorem padicValNat_GN_prime_eq_one_of_dvd_gap
    {p g u : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (hcop : Nat.Coprime g u)
    (hpg : p ∣ g) :
    padicValNat p (GTail p 1 g u) = 1
```

Classification: `PGEN-GREEN` on the stated odd-prime range;
`PGEN-BOUNDARY` at `p = 2`.

The minimal assumptions of the compiled theorem are exactly prime `p`,
`3 ≤ p`, primitive endpoint coprimality, and `p ∣ g`. The proof obtains
`p ∣ GTail` from Probe B, obtains `p ∤ u` from coprimality, obtains
`p^2 ∤ GTail` from Probe C, and converts the two divisibility facts using the
lower `PadicValNat` API.

The boundary witnesses also compile:

```lean
GTail 2 1 2 1 = 4
padicValNat 2 4 = 2
```

Thus the exact-one conclusion cannot be extended to `p = 2`. This is a
genuine prime-boundary issue, not a seven-specific obstruction. Relative to
FLT7, the result replaces the cyclotomic/`TraceOneInt (-2)` valuation bridge
for the front-half residual.

## Probe E — generic power-factor split

Compiled statement:

```lean
theorem power_factor_split
    {d a b x : ℕ}
    (hcop : Nat.Coprime a b)
    (hbody : a * b = x ^ d) :
    (∃ u : ℕ, a = u ^ d) ∧ (∃ v : ℕ, b = v ^ d)
```

Classification: `PGEN-GREEN`.

No assumption on `d` is required by Lean, including no positivity or
primality assumption. The proof is the current Mathlib
`exists_eq_pow_of_mul_eq_pow` route after converting natural coprimality to a
unit gcd. This is a generic factor-splitting lemma, not prime-exponent
mathematics. It is the direct general replacement for
`seventh_power_factor_split`.

## Probe F — valuation conservation for p-th-power products

Compiled statement:

```lean
theorem padicValNat_carrier_shape_of_mul_eq_prime
    {p carrier residual distinguished : ℕ}
    (hp : Nat.Prime p)
    (hc0 : carrier ≠ 0)
    (hr0 : residual ≠ 0)
    (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ p)
    (hrVal : padicValNat p residual = 1) :
    ∃ m : ℕ,
      padicValNat p carrier = (p - 1) + p * m
```

Classification: `PGEN-GREEN`.

The compiled proof needs exactly the displayed prime and nonzero hypotheses,
the product equality, and residual valuation one. It does not need `3 ≤ p`;
the valuation-conservation statement is valid at `p = 2`. The natural-number
normal form is `(p - 1) + p * m`; the intermediate identity used by the proof
is `padicValNat p carrier = p * padicValNat p distinguished - 1`.

This is the generic replacement for
`padicValNat_carrier_shape_of_mul_eq_seventh` and depends only on valuation
conservation, not on the degree-seven field layer.

## Probe G — divisibility consequence

Compiled statement:

```lean
theorem prime_pow_sub_one_dvd_carrier
    {p carrier residual distinguished : ℕ}
    (hp : Nat.Prime p)
    (hc0 : carrier ≠ 0)
    (hr0 : residual ≠ 0)
    (hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ p)
    (hrVal : padicValNat p residual = 1) :
    p ^ (p - 1) ∣ carrier
```

Classification: `PGEN-GREEN`.

This follows from Probe F through
`DkMath.Lib.NumberTheory.padicValNat_le_iff_dvd`; no hand-built divisibility
argument is used. It is the generic replacement for the FLT7 conclusion
`7^6 ∣ gap`.

## Axiom and build audit

The new probe contains no `sorry` and introduces no axiom. The source has
`#print axioms` checks for the main A–G theorems. Every checked theorem has
only the ordinary project-accepted surface:

```text
propext, Classical.choice, Quot.sound
```

No checked theorem depends on `sorryAx`.

Focused builds:

```text
lake build DkMathTest.FLT.Prime.GeneralizationProbe  -- passed, 8660 jobs
lake build DkMath.FLT.Seven                         -- passed, 8809 jobs
```

The second command is a regression build; no FLT7 production source was
changed.

## Phase-1 decision

Proceeding to phase 1 is justified for the odd-prime front half, with the
following explicit boundary:

- Probe B is valid for every prime, including `p = 2`.
- Probes C and D require `p ≥ 3`; Probe D is false at `p = 2`.
- Probes E–G are generic arithmetic/valuation results and do not establish a
  global FLT theorem.

The expected `PrimeAdicPowerSplit` normal form is therefore a justified next
target, but it was not implemented here. The first seven-specific frontier
remains downstream of this probe, at the `TraceOneInt (-2)`, axis-depth,
real-cubic, and degree-six ramified layers. Those layers were intentionally
left untouched under the phase-0 non-goals.

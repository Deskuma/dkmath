# FLT7TC-005R48 — Common-prime residue-one strengthening

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `astra-002-report.md`
- `DkMathTest/FLT/SevenQuotientPrimeAstra02Scratch.lean`
- `PrimeTraceOneDirectRealCubicCommonPrimeKummer.lean`
- `PrimeTraceOneDirectRealCubicSquareIdealSupport.lean`
- `PrimeTraceOneDirectRealCubicSquareGaloisSupport.lean`
- `PrimeTraceOneDirectRealCubicResidueSupport.lean`
- `PrimeTraceOneDirectRealCubicOrbitSplit.lean`
- `SevenRealCubicAxisDrop.lean`

Astra-002 has already kernel-checked the second breakthrough:

```text
q prime
q | C
----------------
q % 7 = 1
```

for the current `DirectOrbitCanonicalCommonFactorPacket`.

R48 is a focused promotion checkpoint.  Promote that bridge to production,
with the original current provenance retained.  Do not mix calibration
exclusion, degree-six phase lifting, reciprocity, or new Kummer theory into
this checkpoint.

## Part A — production module

Create:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicCommonPrimeResidueOne.lean
```

Preferred import:

```lean
import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeKummer
```

This is acceptable because the scratch already passes on that surface and the
new theorem strengthens the existing common-prime residue support without
changing the older API.

Namespace:

```text
DkMath.FLT.Seven.SevenRealCubic
```

## Part B — neutral quotient-evaluation lemma

Promote a neutral theorem equivalent to the Astra scratch:

```lean
theorem quotient_eval_mod_seven_one
    {q : ℕ} (hq : q.Prime) (h7 : (7 : ZMod q) ≠ 0)
    (f : SevenRealCubicInt →+* ZMod q)
    (x y : SevenRealCubicInt)
    (hcop : IsCoprime x y)
    (hzero : f (seventhQuotient x y) = 0) :
    q % 7 = 1
```

Naming may be prefixed for the direct-orbit namespace if repository style
requires it.

The proof must retain the Astra route:

1. use the exact factorization
   `x^7 - y^7 = (x-y) * seventhQuotient x y`;
2. from `f(seventhQuotient x y)=0`, derive
   `f x ^ 7 = f y ^ 7`;
3. use `IsCoprime x y` to show both evaluations are nonzero;
4. prove `f x != f y`;
5. if they were equal, the seventh quotient would evaluate to
   `7*(f y)^6`, contradicting `h7` and nonzero `f y`;
6. define the nontrivial unit
   `tau = f x / f y`;
7. prove `tau^7 = 1` and `tau != 1`;
8. conclude `orderOf tau = 7`;
9. use the finite-field unit-group order to obtain
   `7 | q-1`;
10. conclude `q % 7 = 1`.

Do not appeal to the older `q % 7 = 1 ∨ 6` theorem to choose a branch.

## Part C — common-norm-prime theorem

Promote the current-provenance theorem for an arbitrary
`DirectOrbitSquareRefinementPacket p`:

```lean
theorem common_norm_prime_mod_seven_one
    {x y z q : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (t : DirectOrbitSquareRefinementPacket p)
    (hq : q.Prime)
    (hqR : q ∣ Int.natAbs (norm t.gapSquareRoot))
    (hqS : q ∣ Int.natAbs (norm t.quotientSquareRoot)) :
    q % 7 = 1
```

Use the exact Astra construction:

1. choose the quotient-side prime ideal from
   `directOrbitSquareRefinement_exists_distinct_prime_ideals`;
2. use complete splitting and inertia degree one;
3. identify its residue field with `ZMod q`;
4. define
   `f : SevenRealCubicInt →+* ZMod q`;
5. prove `f t.quotientSquareRoot = 0`;
6. use the quotient-core/root factorization to get
   `f (directOrbitQuotient p) = 0`;
7. prove `7 != 0` in `ZMod q` from `q != 7`;
8. invoke Part B with
   `x = rotateEquiv p.rho`,
   `y = p.rho`,
   and the checked original-root coprimality.

This theorem is stronger than the old `common_norm_prime_mod_seven` theorem.
Do not delete or rewrite the old theorem in R48.

## Part D — canonical common-factor endpoint

Promote the mandatory current endpoint:

```lean
theorem directOrbitCommonPrime_q_mod_seven_one
    {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    {p : DirectRealCubicRootPacket source r}
    (h : DirectOrbitCanonicalCommonFactorPacket p)
    (q : ℕ) (hq : q.Prime) (hqc : q ∣ h.c) :
    q % 7 = 1
```

Use only:

- `directOrbitCommonPrime_dvd_data`;
- Part C.

This is the mandatory R48 public endpoint.

## Part E — prime-support corollary

If clean, expose a theorem expressing the strengthened support directly:

```text
every prime divisor q of h.c satisfies q % 7 = 1.
```

The exact theorem may simply be Part D if no new wrapper is useful.

Optionally prove:

```text
h.c > 1 -> h.c % 7 = 1
```

only if it follows cleanly from existing factorization/product APIs without
adding a large arithmetic detour.

Do not make this optional corollary a blocker for R48.

## Part F — lower-bound audit

As a small audit, determine whether the strengthened support gives a clean
theorem:

```text
h.c > 1 -> 29 <= h.c.
```

This should only be promoted if the proof is short and uses ordinary
prime-divisor existence plus the fact that the first prime congruent to
`1 mod 7` is 29.

Do not introduce a generic prime-enumeration framework merely for this.

If promoted, the existing strict height

```text
h.c * h.u^5 < h.v
```

immediately gives the useful corollary

```text
29 * h.u^5 < h.v.
```

Again: optional, not mandatory.

## Part G — keep the 14th-power/Kummer layer separate

Do not alter the R38 theorem

```text
z^7 = beta*(1+beta)
```

in this checkpoint.

The mathematical consequence of R48 is only that every actual common prime is
now in the `q % 7 = 1` branch.

This removes the previously automatic `q % 7 = 6` branch, but the checked
R38 calibration at `q = 379` shows that the reduced Kummer condition alone
still does not contradict all `q % 7 = 1` primes.

Record this explicitly in the report.

## Part H — cyclic product theorem

Astra also kernel-checked:

```text
R * sigma(R) * sigma^2(R) = -1
```

for the square-twist coefficient ratio.

Do **not** promote it in R48 unless it is literally needed by one of the
mandatory residue-one proofs.

Preferred action: leave it in the Astra scratch for a later character/
degree-six checkpoint.

## Part I — integration

Add the new module to `DkMath.FLT.Seven` facade, preferably after
`PrimeTraceOneDirectRealCubicCommonPrimeKummer` or adjacent to the existing
common-prime modules.

Add:

- focused API audit;
- focused axiom audit;
- R48 client regression.

Update:

- `report-054.md`;
- `ROADMAP.md`.

The client should consume the production theorem rather than duplicate the
Astra scratch proof.

## Hard stops

- No claim that `C > 1` is impossible.
- No claim that every `q ≡ 1 mod 7` fails the Kummer condition.
- No degree-six cyclotomic phase bridge in R48.
- No reciprocity law.
- No character-product contradiction.
- No calibration-exclusion work in this module.
- No successor/descent construction.
- No historical terminal contradiction.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Validation

Run sequentially:

```text
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicCommonPrimeResidueOne
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicCommonPrimeResidueOneR48Scratch.lean
git diff --check
```

Adjust client filenames only to match repository naming conventions and record
the exact commands in the report.

Print axioms for:

- the neutral quotient-evaluation theorem;
- `common_norm_prime_mod_seven_one`;
- `directOrbitCommonPrime_q_mod_seven_one`.

Expected project-level audit:

```text
[propext, Classical.choice, Quot.sound]
```

Run forbidden-source/import scans on all decisive files.

## Report questions

1. Was the neutral quotient-evaluation order-7 argument promoted?
2. Does it derive `q % 7 = 1` without using the old ±1 theorem?
3. Are both evaluated original roots proved nonzero from coprimality?
4. Is inequality of their evaluations proved from the nonvanishing of 7?
5. Is the quotient-side prime chosen from the current square-refinement
   provenance?
6. Is residue-field cardinality exactly q obtained from inertia degree one?
7. Does the canonical theorem retain current `source/r/p/h` provenance?
8. Is every actual prime divisor of `h.c` now forced to `1 mod 7`?
9. Were optional `c > 1 -> c % 7 = 1` / `29 <= c` corollaries added only
   if genuinely cheap?
10. Are facade/API/axiom/client checks green?
11. Is the report explicit that the q=379 local calibration still prevents a
   universal single-prime Kummer contradiction?

## Outcome

- Outcome A — residue-one strengthening is green and cheap support/height
  corollaries are also green.
- Outcome B — the three mandatory residue-one theorems are green; optional
  support/height corollaries are deferred.
- Outcome C — the neutral/order-7 theorem is green but the current
  square-refinement residue-field instantiation is the precise frontier.
- Outcome D — the Astra scratch relies on a hidden assumption not valid in
  production; document the exact gap and stop.

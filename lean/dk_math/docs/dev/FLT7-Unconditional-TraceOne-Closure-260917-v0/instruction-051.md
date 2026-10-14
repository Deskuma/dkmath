# FLT7TC-005R45 — Finite-Hensel depth amplification and the 7^9 correction

Branch: `research/FLT7-Unconditional-TraceOne-Closure-260917-v0`

Authoritative inputs:

- `report-050.md`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean`
- `PrimeTraceOneDirectRealCubicTrivialCommonFactorDeepJet.lean`
- `SevenRealCubicThetaSeventhPower.lean`
- `SevenRealCubicThetaSeventhPowerMod49.lean`
- `SevenRealCubicUnitClass.lean`
- `SevenRamifiedThetaJetLifting.lean`

R44 is green through the exact current-provenance endpoint

```text
W = rho * w^49.
```

The clash audit is negative: neither the non-square coefficient theorem nor
the mixed-sign theorem gives a contradiction.

Do not repeat the mod-49 calculation manually.  The unused theta depth is much
larger: the current quotient remainder has theta depth at least 32, hence it
contains theta depth 30, corresponding to scalar divisibility by `7^10`.

R45 must formalize the neutral finite-Hensel depth rule for seventh powers,
use the full available depth, and strengthen the correction to

```text
W = rho * t^(7^9).
```

This is a finite-depth amplification only.  It is not an infinite descent and
not an FLT7 contradiction.

## Part A — neutral nilpotent-depth predicate

Add a small neutral module, preferred:

```text
DkMath/FLT/Seven/SevenRealCubicThetaSeventhPowerDepth.lean
```

Define

```lean
def ThetaNilpotentDepth (n : ℕ) (x : SevenRealCubicInt) : Prop :=
  (7 : ℤ)^n ∣ thetaLinearInt x ∧
    (7 : ℤ)^n ∣ thetaSquareInt x
```

Naming may differ, but keep the concept neutral.

Add the obvious monotonicity theorem:

```text
m <= n ->
ThetaNilpotentDepth n x ->
ThetaNilpotentDepth m x.
```

Do not introduce a full valuation API.

## Part B — public 7-unit coefficient helpers

The exact formulas are

```text
thetaLinear(x^7)
  = 7 * (B * GB + 7*C^2*GC)

thetaSquare(x^7)
  = 7 * (C * HC + B^2*HB),
```

where

```text
GB = seventhThetaLinearBFactor A B C
HC = seventhThetaSquareCFactor A B C.
```

For `7 ∤ A`, expose or reprove neutral public lemmas

```text
¬ 7 | GB
¬ 7 | HC.
```

The existing proofs in `SevenRamifiedThetaJetLifting.lean` are currently
private; either make minimal public versions there or prove equivalent helpers
in the new neutral module.

Use only the existing mod-seven factor theorems.

## Part C — generic seventh-power depth drop

Prove the key finite-Hensel theorem:

```text
theorem thetaNilpotentDepth_pow_seven_drop
    (x : SevenRealCubicInt) (n : ℕ)
    (hA : ¬ (7 : ℤ) ∣ thetaConstInt x)
    (hdepth : ThetaNilpotentDepth (n+1) (x^7)) :
    ThetaNilpotentDepth n x.
```

A proof by induction on `n` is preferred.

For the successor step:

1. use the weaker output depth and the induction hypothesis to know
   `7^n | B` and `7^n | C`;
2. cancel the leading factor `7` from the exact seventh-power coordinate
   formulas;
3. in the linear quotient,
   `7*C^2*GC` has depth at least `n+1`;
4. hence `7^(n+1) | B*GB`;
5. `GB` is coprime to `7^(n+1)`, so
   `7^(n+1) | B`;
6. in the square quotient, the now stronger `B^2` term has sufficient
   depth;
7. cancel the 7-unit `HC` to obtain
   `7^(n+1) | C`.

Do not prove this by expanding `x^7` from scratch.  Reuse
`thetaLinear_pow_seven`, `thetaSquare_pow_seven`, and the factor APIs.

This theorem is the main neutral R45 result.

## Part D — depth-one unit class closure

For a model unit `u`, prove

```text
ThetaNilpotentDepth 1 (u : SevenRealCubicInt)
  -> projectiveLog (Additive.ofMul u) = 0.
```

Reason:

```text
7 | thetaLinearInt u
7 | thetaSquareInt u
```

give both raw mod-seven nilpotent coordinates zero, and the unit constant
coordinate is nonzero.

Then expose the seventh-power consequence using

```text
unit_isSeventhPower_iff_projectiveLog_eq_zero.
```

## Part E — recursive unit power extraction

Prove the neutral recursive theorem

```text
theorem unit_is_pow_seven_pow_of_inverse_depth
    (u : SevenRealCubicIntˣ) (n : ℕ)
    (hdepth :
      ThetaNilpotentDepth n
        ((u⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt)) :
    ∃ t : SevenRealCubicIntˣ, u = t ^ (7^n).
```

The intended induction is:

- `n=0`: choose `t=u`;
- `n+1`:
  1. depth at least one gives
     `projectiveLog (u⁻¹) = 0`;
  2. extract `r` with `u⁻¹ = r^7`;
  3. set `s = r⁻¹`, so `u = s^7`;
  4. apply Part C to
     `r^7 = u⁻¹` to obtain
     `ThetaNilpotentDepth n r`;
  5. this is the inverse-depth hypothesis for `s`;
  6. recurse on `s`;
  7. combine exponents:
     `7 * 7^n = 7^(n+1)`.

Do not infer any unit is `1`.

This theorem is a finite algebraic extraction theorem, not a completeness or
p-adic convergence theorem.

## Part F — general theta^(3m) to 7^m scalar divisibility

In the paired module or a neutral axis helper, generalize the R42 special
lemmas to:

```text
eisensteinAxis^(3*m) | x
  -> ((7 : ℤ)^m : SevenRealCubicInt) | x.
```

Equivalent `ofInt ((7 : ℤ)^m)` spelling is acceptable.

Use

```text
7 = eisensteinAxis^3 * thetaSevenUnit
```

and the inverse of the unit `thetaSevenUnit^m`.

Do not remove the existing `axis^6 -> 49` and `axis^9 -> 343` API unless
they become simple corollaries and all uses remain green.

## Part G — use theta depth 30 to make the source root scalar to depth 9

The current packet has

```text
eisensteinAxis^32 | directOrbitGap p.
```

Weaken to

```text
eisensteinAxis^30 | directOrbitGap p
```

and apply Part F with `m=10`:

```text
7^10 | directOrbitGap p
```

in the model ring.

Transport to theta coordinates and use the already checked exact formulas

```text
thetaConst(gap)  = -7*C
thetaLinear(gap) = 3*B - 21*C
thetaSquare(gap) = B - 6*C.
```

The constant and square formulas are sufficient to prove

```text
(7 : ℤ)^9 | thetaLinearInt p.rho
(7 : ℤ)^9 | thetaSquareInt p.rho.
```

Suggested arithmetic:

- `7^10 | -7*C` gives `7^9 | C`;
- `7^10 | B - 6*C` and `7^9 | C` give `7^9 | B`.

Expose

```text
ThetaNilpotentDepth 9 p.rho.
```

This is a strengthening of R43's mod-49 source scalarity.

## Part H — source sixth power remains scalar to depth 9

Generalize the R44 structural argument:

from Part G prove

```text
((7 : ℤ)^9 : SevenRealCubicInt) |
  p.rho - ofInt (thetaConstInt p.rho)
```

and then

```text
((7 : ℤ)^9 : SevenRealCubicInt) |
  p.rho^6 - (ofInt (thetaConstInt p.rho))^6.
```

Conclude

```text
ThetaNilpotentDepth 9 (p.rho^6).
```

Avoid an explicit sixth-power coordinate expansion.

## Part I — quotient remainder gives depth 9 for Z^7

R44 already proves

```text
eisensteinAxis^32 |
  Z^7 - p.rho^6.
```

Weaken to theta depth 30 and use Part F:

```text
((7 : ℤ)^10 : SevenRealCubicInt) |
  Z^7 - p.rho^6.
```

Hence both theta nilpotent coordinates of the difference have depth 10.

Combine with Part H to prove

```text
ThetaNilpotentDepth 9 (Z^7).
```

Expose this as a current-provenance theorem.

## Part J — drop one seventh-power depth: Z has depth 8

R44 already proves that the theta constant of `Z` is nonzero modulo seven.

Translate this to

```text
¬ 7 | thetaConstInt Z.
```

Apply Part C to Part I with `n=8`:

```text
ThetaNilpotentDepth 8 Z.
```

No separate mod-343 polynomial expansion is allowed.

## Part K — transfer depth 8 from Z to v inverse

Recall exactly

```text
Z = (v⁻¹ : SevenRealCubicInt) * (V : SevenRealCubicInt)^2.
```

Prove exact integer-coordinate scalar multiplication formulas:

```text
thetaLinearInt Z =
  thetaLinearInt (v⁻¹) * V^2

thetaSquareInt Z =
  thetaSquareInt (v⁻¹) * V^2.
```

R44 gives

```text
¬ 7 | V.
```

Therefore `V^2` is coprime to `7^8`.  Cancel it from the two divisibility
statements in Part J and obtain

```text
ThetaNilpotentDepth 8
  ((v⁻¹ : SevenRealCubicIntˣ) : SevenRealCubicInt).
```

Do not call `V` a global algebraic unit; only integer coprimality is used.

## Part L — amplify the unit correction from 7^2 to 7^9

Apply Part E with `n=8`:

```text
∃ t : SevenRealCubicIntˣ, v = t^(7^8).
```

Combine with the exact R41 correction

```text
W = rho * v^7
```

to prove

```text
W = rho * t^(7^9).
```

Use the symbolic exponent `7^9`; do not hard-code the decimal numeral.

This is the mandatory R45 current-provenance endpoint.

## Part M — provenance-preserving wrapper

Provide a theorem for the current `C = 1` canonical packet, using the same
R41 root `v`, that returns at least

```text
ThetaNilpotentDepth 8 (v⁻¹)
v = t^(7^8)
W = rho * t^(7^9)
quotientCore = thetaSevenUnit * Z^7.
```

Retain the existing R44 wrapper unchanged.

## Part N — clash audit only

After Part L/M is green, inspect existing checked theorems only.

1. Does `W = rho * t^(7^9)` now clash with the R27 non-square theorem?
   Remember `7^9` is still odd.
2. Does the much higher odd power determine a forbidden real-sign pattern?
3. Is there already a checked unit-height bound strong enough to exclude such
   a high power?
4. Does any existing binary-cubic/Thue theorem classify the trace-plane
   norm-one units strongly enough to use the new exponent?

Do not start Baker theory, a new Thue solver, or an Archimedean unit-equation
project in R45.

## Hard stops

- This is finite Hensel amplification, not infinite Hensel lifting.
- Do not claim arbitrary depth beyond what theta^32 supplies.
- Do not infer that a `7^9`-th power is trivial.
- Do not infer a contradiction from odd-power parity.
- Do not call the integer scalar `V` a global algebraic unit.
- No hidden terminal/cyclotomic contradiction imports.
- No successor/descent claim.
- No FLT7 conclusion without an independent checked clash.
- No `sorry`, `sorryAx`, `admit`, `unsafe`, or project `axiom`.

## Preferred implementation

Preferred new neutral file:

```text
DkMath/FLT/Seven/SevenRealCubicThetaSeventhPowerDepth.lean
```

Keep generic finite-Hensel lemmas there.

Continue current-provenance instantiations in:

```text
DkMath/FLT/Seven/PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet.lean
```

Update:

- `DkMath.FLT.Seven` facade;
- focused API checks for the neutral and paired modules;
- axiom audits;
- `R45Scratch`;
- `report-051.md`;
- `ROADMAP.md`.

## Report questions

1. Was a neutral `ThetaNilpotentDepth` predicate added?
2. Was the generic seventh-power depth-drop theorem proved?
3. Was the recursive unit theorem
   `inverse depth n -> 7^n-th power` kernel-checked?
4. Was the general `theta^(3m) -> 7^m` scalar divisibility theorem proved?
5. Did the source root reach nilpotent depth 9?
6. Did `p.rho^6` retain nilpotent depth 9?
7. Did the quotient remainder give nilpotent depth 9 for `Z^7`?
8. Did the neutral depth-drop theorem give nilpotent depth 8 for `Z`?
9. Was depth 8 transported to `v⁻¹` using only `7 ∤ V`?
10. Was `v = t^(7^8)` proved?
11. Was `W = rho*t^(7^9)` proved?
12. Did any independent existing theorem turn this into an actual
    contradiction?

## Outcomes

- Outcome A — the amplified correction clashes with an existing independent
  invariant and yields an actual contradiction.
- Outcome B — neutral finite-Hensel depth amplification is green and the
  current C=1 branch reaches
  `W = rho * t^(7^9)`; no contradiction yet.
- Outcome C — `ThetaNilpotentDepth 8 Z` is green, but transfer to
  `v⁻¹` / recursive unit extraction is the precise frontier.
- Outcome D — source and quotient high-depth transport are green, but the
  generic seventh-power depth-drop theorem is the precise frontier.
- Outcome E — the neutral finite-Hensel depth theorem itself is the precise
  frontier.

## Validation

At minimum:

```text
lake build DkMath.FLT.Seven.SevenRealCubicThetaSeventhPowerDepth
lake build DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJet
lake build DkMath.FLT.Seven
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetApi
lake build DkMathTest.FLT.SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetAxiom
lake env lean DkMathTest/FLT/SevenPrimeTraceOneDirectRealCubicTrivialCommonFactorPairedDeepJetR45Scratch.lean
git diff --check
```

Add focused API/axiom checks for the neutral depth module if repository
conventions warrant it.

Print axioms for:

- `thetaNilpotentDepth_pow_seven_drop`;
- `unit_is_pow_seven_pow_of_inverse_depth`;
- `theta^(3m) -> 7^m` divisibility;
- source depth 9;
- `Z^7` depth 9;
- `Z` depth 8;
- `v⁻¹` depth 8;
- `v = t^(7^8)`;
- `W = rho*t^(7^9)`.

Run forbidden-source/import scans on all decisive files.

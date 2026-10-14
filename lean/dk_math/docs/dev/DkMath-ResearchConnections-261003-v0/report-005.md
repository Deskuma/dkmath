# DRC-005 — General prime-shell finite Hensel API

## Outcome A

The prime-shell root/roots-of-unity correspondence, nonramified simplicity,
unique next digit at every positive finite depth, finite-depth root existence,
and exact divisibility depth are kernel-checked for arbitrary prime degree.
The base-unit and distinct-prime hypotheses are explicit. The ramified root
sector is stated separately. No mathematical novelty claim is made.

## Audit and scope

- Branch: `research/DkMath-ResearchConnections-261003-v0`.
- Initial HEAD: `a4fc51ec94c6387b2e72e0835118987b932cbf09`; initial worktree clean.
- Lean/Mathlib `v4.34.1`.
- Inspected `GNThreeHenselDepth.lean`, `GNThreePairedDepth.lean`, and the
  imported cubic lift/derivative APIs. The cubic digit construction solves a
  linear equation modulo q; its quadratic Taylor expansion and derivative
  `2*g+3*u` are the degree-specific pieces.
- Audited Mathlib polynomial Taylor expansion, Henselian rings, p-adic Hensel,
  roots of unity/cyclotomic roots, ZMod field and residue APIs, and divisibility.
  `hensels_lemma` is a completion/norm formulation; `HenselianLocalRing` works
  in a local ring with a lifting assumption. Neither directly supplies this
  finite integer `Fin q` next-digit endpoint.
- Mathlib already provides
  `Polynomial.exists_mul_sq_add_linear_part_eq_eval_add`. It supports a
  degree-independent finite digit theorem without reimplementing Taylor theory.
- Existing `GTail_one_eq_GTailCyclotomicShell` connects GN with its homogeneous
  cyclotomic shell; `GN_zero_eval` supplies the zero-gap boundary value.

The implemented depth is integer divisibility: `q^k` divides the shell and
`q^(k+1)` does not. No numerical valuation equality, infinite coherent p-adic
branch, or paired CRT generalization is claimed.

## Common polynomial Hensel layer

File: `DkMath/Lib/NumberTheory/PolynomialHenselDigit.lean`.
All names have prefix `DkMath.Lib.NumberTheory`:

- `polynomial_powLift_iff`: for `P : ℤ[X]`, `q>0`, `k≥1`, and
  `q^k ∣ P(x)`,

  ```text
  q^(k+1) divides P(x+q^k*t)
    iff q divides P(x)/q^k + t*P'(x).
  ```

- `existsUnique_polynomial_powLift_digit`: if q is prime and
  `q ∤ P'(x)`, exactly one `t : Fin q` satisfies the next-depth divisibility.
- `polynomial_shift_preserves_dvd`: evaluation preserves a supplied root under
  a modulus-sized shift, for any integer polynomial and integer modulus.
- `exists_polynomial_exact_depth_digit`: under the same simple-root hypotheses,
  some other digit preserves depth k and fails depth k+1.

The linearization uses the existing Taylor remainder `c*(q^k*t)^2`.
After factoring `q^k`, its remaining contribution is divisible by q because
`k≥1`. Integer exact division is justified by the supplied divisibility.
The unique digit solves `c+t*d=0` in the field `ZMod q`; cancellation of the
nonzero derivative proves uniqueness. The exact-depth endpoint chooses a
different digit, possible because a prime has at least two residues.

This is the extracted common structure, independent of degree or GN. It is
promoted through `DkMath/Lib.lean`.

## Prime-shell production API

File: `DkMath/NumberTheory/PrimeShellHensel.lean`.
All names below have prefix `DkMath.NumberTheory`.

`primeShellPolynomial p u` is the existing tail `GTail p 1 X (C u)` in `ℤ[X]`.
It does not introduce a competing shell definition. Its two evaluation bridges
are `primeShellPolynomial_eval` and `primeShellPolynomial_map_eval`.

`primeShellPolynomial_derivative_identity` proves the polynomial identity

```text
P + X*P' = p*(X+C u)^(p-1).
```

It follows by differentiating the existing Cosmic Formula polynomial identity.

`primeShell_root_iff` is slightly more general than the prime application: for
any field K, natural p with `(p : K) ≠ 0`, and `u ≠ 0`,

```text
GTail p 1 g u = 0
  iff ((g+u)/u)^p = 1 and (g+u)/u ≠ 1.
```

`primeShell_dvd_iff_rootOfUnity` supplies the direct integer/mod-q form. Its
hypotheses are p prime, q prime (`[Fact q.Prime]`), `q ≠ p`, and `q ∤ u`.
It relates `q ∣ GTail p 1 g u` to the same nontrivial p-th root of unity in
`ZMod q`. Division occurs only by the explicitly nonzero field base; the
integer shell and integer lifting introduce no base division.

`primeShell_derivative_not_dvd` proves that this root has derivative not divisible
by q. At a root, the differentiated identity gives

```text
g*P'(g) = p*(g+u)^(p-1) modulo q.
```

The right side is nonzero: p is nonzero modulo the distinct prime q, and the
root-of-unity relation forces `g+u ≠ 0` when the base is a unit. A zero
derivative would contradict that identity. Also the zero-gap boundary
`GN p 0 u = p*u^(p-1)` shows that such a nonramified root has nonzero gap.

The lifting/depth endpoints are:

- `existsUnique_primeShell_powLift_digit`: p and q prime, `q ≠ p`, `k≥1`,
  integer base/gap `u,g`, `q ∤ u`, and `q^k ∣ GN p g u` imply a unique digit
  giving divisibility by `q^(k+1)` after shifting the gap by `q^k*t`.
- `exists_primeShell_pow_root`: a supplied root modulo q extends to roots at
  every finite positive depth by iterating those unique digits.
- `exists_primeShell_exact_depth`: for every `k≥1`, a supplied root modulo q
  yields an integer gap with exact divisibility depth k. It lifts to a deeper
  root and then chooses a digit other than the unique next lift.

These are conditional root-lifting APIs; they do not supply a root for every
pair of distinct primes. Uniqueness is stated as the unique next digit at each
depth, not as an additional global RingEquiv or separately constructed infinite
tower. The witnesses are integer gaps, allowing negative inputs as well.

The public `DkMath.lean` facade imports the prime-shell module.

## Ramified and base boundaries

`primeShell_ramified_root_iff` states for prime p and `g,u : ZMod p`:

```text
GTail p 1 g u = 0 iff g = 0.
```

It uses Frobenius and the zero-gap value; it does not assert simple-root
lifting there. The regression at p=q=3 has derivative divisible by 3 and no
next digit lifting the gap-zero root to modulus 9. This is a concrete obstruction
to omitting the distinct-prime condition. The API does not claim every ramified
prime degree has a multiple root: degree two is a linear shell.

Similarly, a zero base can give singular roots even away from p; the explicit
`q ∤ u` hypothesis is retained throughout the nonramified shell endpoints.

## Existing cubic compatibility

At p=3 the shell polynomial is `g^2+3*g*u+3*u^2`, with derivative `2*g+3*u`.
The calibration theorem `DkMathTest.PrimeShellHensel.cubic_derivative` checks
that derivative exactly. Generic and existing Nat cubic next-digit APIs are
both exercised at q=7, gap/base 1.

The existing cubic modules retain their implementations and public signatures.
The new common layer permits later proof reuse; this checkpoint verifies the
specialization without changing the established Nat casting and primitive
wrappers. Existing primitive cubic roots derive their base-unit condition from
primitivity; the generic integer theorem states that condition directly.
The paired cubic CRT/scaling orientation constructions remain degree-specific
downstream APIs, rather than being silently promoted to arbitrary primes.

## Regressions and audit

Files:

- `DkMathTest/NumberTheory/PrimeShellHenselCalibration.lean`.
- `DkMathTest/NumberTheory/PrimeShellHenselAxiomAudit.lean`.

Regressions cover prime degree 2 at q=3, degree 3 at q=7, degree 5 at q=11
and depth two (the seed value is `GN 5 2 1 = 121`), arbitrary finite and exact
depth for that degree-five seed, the root-of-unity iff, the explicit cubic
derivative, the ramified obstruction, and failure of the base-unit condition.
Finite `fin_cases` occurs only in the fixed ramified regression, not in a
generic theorem proof.

All 14 public theorem endpoints are printed in the audit file. Their dependency
lists contain only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`
or project-added axioms.

## Validation

Commands ran from `lean/dk_math`:

| Command | Result |
| --- | --- |
| `lake env lean DkMath/Lib/NumberTheory/PolynomialHenselDigit.lean` | Pass, exit 0 |
| `lake env lean DkMath/NumberTheory/PrimeShellHensel.lean` | Pass, exit 0 |
| `lake env lean DkMathTest/NumberTheory/PrimeShellHenselCalibration.lean` | Pass, exit 0 |
| `lake env lean DkMathTest/NumberTheory/PrimeShellHenselAxiomAudit.lean` | Pass, exit 0 |
| Final combined build: `DkMath.Lib`, prime-shell module, `GNThreeHenselDepth`, `GNThreePairedDepth`, both new tests | Pass, 8971 jobs, exit 0 |
| `lake build` | Pass, 10340 jobs, exit 0 |

`git diff --check` and individual new-file checks with
`git diff --no-index --check /dev/null <file>` produced no whitespace diagnostics.
The new production/test source scan found no `sorry`, `admit`, `unsafe`, or
axiom declaration candidates. Build logs are `/tmp/drc-005-focused.log` and
`/tmp/drc-005-full-build.log`.

No obstruction remains within the stated finite-depth integer API. Infinite
p-adic branch construction and generic paired CRT/orientation transport remain
outside this checkpoint's implemented theorem boundary.

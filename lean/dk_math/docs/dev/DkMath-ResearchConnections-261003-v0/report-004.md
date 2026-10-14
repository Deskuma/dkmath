# DRC-004 — Integral prime cyclic glue

## Outcome A

Compatible integer and integral cyclotomic components can be reconstructed,
and determine a unique class in the existing integral AKS cyclic quotient.
Compatibility is explicitly equality in `ZMod p`. Genuine p-th powers in both
components reconstruct a genuine p-th power in the cyclic quotient.
No mathematical novelty claim is made.

## Audit and design

- Branch: `research/DkMath-ResearchConnections-261003-v0`.
- Initial HEAD: `8e681d8438144a6bad421bd77c7285d2d85d84c5`; initial worktree clean.
- Lean/Mathlib `v4.34.1`.
- Audited the existing `AKSBridge.lean` cyclic ideal and quotient; Mathlib
  `AdjoinRoot`, ideal quotient maps, Chinese remainder APIs, cyclotomic
  evaluation, and residue/divisibility APIs.
- `AKSCyclicQuotient ℤ p` already is `ℤ[X]/(X^p-1)`.
- Mathlib `AdjoinRoot (Polynomial.cyclotomic p ℤ)` already is
  `ℤ[X]/(Φ_p)`, the integral cyclotomic presentation used here.
- Existing Mathlib Chinese remainder equivalences require coprime ideals.
  Here the two components meet at the prime residue, so those equivalences
  do not directly give the required integral gluing statement. No directly
  applicable reconstruction endpoint was found in the targeted audit.

The chosen API uses these existing carriers. Existence is expressed via common
polynomial representatives, with uniqueness expressed in the AKS quotient.
This smaller formulation checks the arithmetic reconstruction content without
introducing a separate fiber-product carrier or claiming a formal RingEquiv.
No identification with a separately chosen number field's ring of integers is
needed or asserted.

## Production API

File: `DkMath/NumberTheory/PrimeCyclicGlue.lean`.
All names below have prefix `DkMath.NumberTheory` and assume `[Fact p.Prime]`.
The module is imported by the public `DkMath.lean` facade. It stays in
NumberTheory because it reuses the existing AKS implementation there.

- `primeCyclotomicResidue`: a ring homomorphism from `AdjoinRoot (Φ_p)` to
  `ZMod p`. It evaluates coefficients modulo p and sends the adjoined root to 1.
- `primeCyclotomicResidue_mk`: on a representative `f`, this map is
  `(f.eval 1 : ℤ)` reduced modulo p.
- `exists_polynomial_prime_glue_iff`: for `a : ℤ` and `q : ℤ[X]`,

  ```text
  (exists f, f(1)=a and Φ_p divides f-q)
    iff p divides a-q(1).
  ```

- `exists_prime_cyclic_glue_iff`: for an actual cyclotomic quotient element `b`,

  ```text
  (exists f, f(1)=a and [f] mod Φ_p=b)
    iff (a mod p)=primeCyclotomicResidue p b.
  ```

- `cyclic_dvd_sub_iff_components`:

  ```text
  (X^p-1 divides f-g)
    iff f(1)=g(1) and Φ_p divides f-g.
  ```

- `aks_prime_cyclic_glue_eq_iff`: the quotient version of the preceding iff,
  using `aksQuotientMap ℤ p` and `AdjoinRoot.mk (Φ_p)` directly. Thus different
  representatives with the same two components give the same cyclic class.
- `aks_prime_cyclic_is_pow_of_components`: if `f(1)=a^p` and its cyclotomic
  class is `b^p`, then

  ```lean
  ∃ q : AKSCyclicQuotient ℤ p, aksQuotientMap ℤ p f = q ^ p
  ```

No unit multiplier is present in the hypotheses or conclusion of this power
endpoint. It provides no unit-times-power conversion.

## Proof architecture

Mathlib gives `Φ_p(1)=p` and `Φ_p * (X-1)=X^p-1`.

For existence, a compatibility witness `a-q(1)=p*k` gives the explicit
polynomial `f=q+Φ_p*C k`. Its evaluation is `a`, and its cyclotomic component
is the class of `q`. The converse evaluates the divisibility witness at 1.
Surjectivity of `AdjoinRoot.mk` upgrades this to arbitrary cyclotomic quotient
elements. `ZMod.intCast_zmod_eq_zero_iff_dvd` expresses the condition as actual
residue equality. `AdjoinRoot.lift` constructs the residue homomorphism because
evaluation of `Φ_p` at 1 vanishes in `ZMod p`.

For uniqueness, write `f-g=Φ_p*t`. Equal augmentations force `p*t(1)=0`.
The integer prime is nonzero, so `t(1)=0`, and Mathlib's `dvd_iff_isRoot` gives
`X-1` divides `t`. The cyclotomic factorization then gives `X^p-1` divides
`f-g`. The reverse direction uses that factorization directly.
`Ideal.Quotient.mk_eq_mk_iff_sub_mem` and `Ideal.mem_span_singleton` translate
this into the existing AKS quotient equality.

For p-th-power gluing, the common residue of `f` shows that the p-th powers
of the supplied roots `a` and `b` have equal residues. `ZMod.pow_card` says
the p-th-power map is the identity in `ZMod p`, so the roots themselves are
compatible. Reconstruct their common representative `q`; the uniqueness iff
identifies the class of `f` with the class of `q^p`. This uses element equality,
not norm equality.

## Connection to previous checkpoints

The existing AKS cyclic quotient is reused rather than duplicated. DRC-003's
full length-p cyclic determinant has the complete power-difference carrier,
including its trivial-character factor. This checkpoint describes how the
integral trivial and cyclotomic components of that cyclic setting must be
glued modulo p. It does not identify the DRC-003 matrix with a quotient
multiplication operator or add a determinant factorization theorem; that
basis-level bridge remains separate. Prime cyclotomic field norms remain
distinct from integral element reconstruction, and no FLT conclusion follows
from the API here alone.

## Regressions

File: `DkMathTest/NumberTheory/PrimeCyclicGlueCalibration.lean`.

- `prime_two_reconstruction`: augmentation 3 and cyclotomic representative
  `X` agree modulo 2 and reconstruct.
- `prime_three_reconstruction`: augmentation 4 and the quotient class of
  `X` agree modulo 3 and reconstruct.
- `incompatible_pair`: augmentation 2 and `X` disagree modulo 3; no common
  representative exists.
- A corrected representative and its addition by `X^3-1` have the same AKS
  class, checked through the component equality endpoint.
- `genuine_cube`: for arbitrary polynomials `q,t`, the class of
  `q^3+(X^3-1)*t` reconstructs as a genuine cube from its two cube components.
- `composite_boundary`: at length 4, `Φ_4(1)=2`. A representative with zero
  cyclotomic component and augmentation 2 exists although 4 does not divide 2.
  Thus substituting a composite length into the prime residue criterion would
  be incorrect.

## Validation and axiom audit

File: `DkMathTest/NumberTheory/PrimeCyclicGlueAxiomAudit.lean`.
All seven public definitions/theorems listed above print dependencies
`[propext, Classical.choice, Quot.sound]`. There is no `sorryAx` or project-added
axiom in those dependency lists.

Commands ran from `lean/dk_math`:

| Command | Result |
| --- | --- |
| `lake env lean DkMath/NumberTheory/PrimeCyclicGlue.lean` | Pass, exit 0 |
| `lake build DkMath.NumberTheory.PrimeCyclicGlue` | Pass, exit 0 |
| `lake env lean DkMathTest/NumberTheory/PrimeCyclicGlueCalibration.lean` | Pass, exit 0 |
| `lake env lean DkMathTest/NumberTheory/PrimeCyclicGlueAxiomAudit.lean` | Pass, exit 0 |
| Combined build of both new test modules | Pass, 8935 jobs, exit 0 |
| `lake build` | Pass, 10338 jobs, exit 0 |

`git diff --check` and checks of every new file with
`git diff --no-index --check /dev/null <file>` produced no whitespace diagnostics.
Source scanning found no forbidden proof constructs; the sole `admit` word hit
was English prose in the incompatibility regression's docstring.
Build logs are `/tmp/drc-004-production.log`, `/tmp/drc-004-focused.log`, and
`/tmp/drc-004-full-build.log`.

There is no remaining obstruction to the reconstruction API above. A full
fiber-product RingEquiv and an explicit ring-of-integers identification are
outside this selected smaller theorem boundary.

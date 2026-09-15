# Current shell arithmetic inventory

Read-only source audit of production; no production edits or build claims.
No `AGENTS.md` found in the workspace or searched parent development trees.

All paths below are relative to `lean/dk_math/`.

## Exact witness and norm data

- `DkMath/ABC/GNExcessCubicRealizedIncidence.lean:24–26`:
  `GNExcessCubicFullRepeatedModulus a := GNNonExceptionalRepeatedPart 3 a 1`.
- `GNExcessCubicRealizedIncidence.lean:28–39,69–83`: shell membership is exactly
  `1 ≤ a`, `a ≤ X`, `X+1 < M(a)`, `D ≤ M(a)`, `M(a) < 2*D`.
- `DkMath/ABC/GNExcessCubicComplement.lean:49–52`: the canonical nonexceptional
  repeated modulus equals `repeatedPrimePowerPart (GN 3 a 1)`.
- `DkMath/ABC/GNExcessLargeBoundaryPacket.lean:29–33,46–52`:
  `repeatedPrimePowerPart N` retains the entire exponent `v_q(N)` when it is
  at least two, and exponent zero otherwise. It does not round exponents down
  to an even number.
- `GNExcessCubicComplement.lean:149–151`: `S(a)` is the quotient of the cubic
  GN value by that full repeated part.
- `GNExcessCubicComplement.lean:166–188`:
  `GNNonExceptionalRepeatedPart_mul_GNExcessCubicComplement_eq_quadratic`,
  `squarefree_GNExcessCubicComplement`, and
  `coprime_GNNonExceptionalRepeatedPart_GNExcessCubicComplement` hold for every
  natural `a`, without shell assumptions.
- `GNExcessCubicRealizedIncidence.lean:218–230`:
  `GNExcessCubicRealizedLargeModulusShellWitness_complement_packet` combines
  all shell bounds with `M*S=a^2+3*a+3`, `Squarefree S`, `Nat.Coprime M S`,
  and `S ≤ X`.
- `DkMath/ABC/GNExcessCubicEisensteinCoordinates.lean:28–33,37–52`:
  `cubicQuadratic_eq_eisensteinNorm` and
  `GNExcessCubicRealizedLargeModulusShellWitness_product_eq_eisensteinNorm`
  identify that product with `norm (eisensteinCoord ((a:ℤ)+2) 1)`.

## Correct square allocation

`DkMath/ABC/SquareTailBasic.lean:86–87,105–106,130–131` defines

```text
r = oddPart M  = product q^(v_q(M) % 2)
d = evenPart M = product q^(v_q(M) / 2)
M = r*d^2, for M ≠ 0.
```

`DkMath/ABC/GNExcessCubicSquarefulPell.lean:98–125` proves the full packet
`M=r*d^2`, `Squarefree r`, `r ∣ d`, `Squarefree S`, `Coprime M S`, and
`Coprime r S` for a represented shell pair. Lines 128–138 prove
`Squarefree (r*S)`.

Thus the intended nontrivial provider should use

```text
norm gamma = d,
norm beta = T := r*S,
norm alpha = T*d^2.
```

There is no reason for `M` to be a square. For exponent `v_q(N)=3`, `M`
retains `q^3`, `r` retains `q`, and `d` retains `q`. This alone refutes the
allocation `norm(gamma)^2=M`; it does not refute the corrected provider.

The Pell identity is already
`GNExcessCubicRealizedLargeModulusShellIncidencePair_pell_identity`
(`GNExcessCubicSquarefulPell.lean:143–168`):
`(2*a+3)^2+3=4*T*d^2`.

## Existing prime channels

- `GNExcessCubicComplement.lean:30–43`: the cubic quadratic is never divisible
  by `9`.
- `DkMath/ABC/GNExcessCubicThreeSector.lean:21–56`:
  `three_dvd_cubicQuadratic_iff` and `cubicQuadratic_three_exact_depth_one`.
  Thus `3` occurs with norm exponent one exactly when `3 ∣ a`.
- `GNExcessCubicThreeSector.lean:69–82,84–119`: `3` divides none of `M`, `r`,
  `d`, or the squareful quotient. Lines 121–153 place `3` in `S` exactly when
  `3 ∣ a`, and exclude `9 ∣ S`.
- `DkMath/ABC/GNExcessCubicRealizedModuli.lean:251–277`:
  `GNExcessCubicRealizedLargeModulusSpace_prime_sq_dvd` and
  `GNExcessCubicRealizedLargeModulusSpace_prime_mod_three_eq_one` prove every
  prime in `M` occurs at least twice and is `1 mod 3`.
- `DkMath/ABC/GNExcessCubicPrimitivePell.lean:59–88` gives the same `1 mod 3`
  restriction for prime divisors of `r`, `d`, and the squareful quotient.
- `DkMath/NumberTheory/GNThreePrimeArithmetic.lean:166–172`:
  `three_dvd_prime_sub_one_of_prime_dvd_GN_three_of_coprime_of_ne_three`
  applies to **every** non-three prime divisor of the primitive quadratic,
  including primes in `S`. Instantiate `u=a`, `x=1`, `Nat.Coprime a 1`.
  It returns `3 ∣ q-1`; converting this to `q % 3=1` is elementary.
  Consequently no inert rational prime occurs anywhere in the norm.
- `GNThreePrimeArithmetic.lean:255–261`:
  `prime_not_dvd_cubic_boundary_derivative` excludes `q ∣ 2*a+3` for every
  non-three prime divisor of the norm.
- `GNExcessCubicPrimitivePell.lean:103–150` packages
  `Coprime (2*a+3) M`, and coprimality with `r`, `d`, and the squareful quotient.
- `DkMath/NumberTheory/GNThreeHenselDepth.lean:120–129`:
  `existsUnique_GN_three_powLift_digit` gives a unique next finite root digit
  under `q^k ∣ GN`, `k≥1`, and nonvanishing derivative. It does not by itself
  identify an Eisenstein prime or prove an element valuation equality.

At each split prime, the missing element theorem must transport the rational
valuation into the unique oriented prime dividing the actual coordinate-one
element. The rational exponent arithmetic itself is already present.

## Exact receiver equations

For `beta=c+dω`, `gamma=m+nω`, put

```text
P = m^2-n^2,
Q = 2*m*n-n^2.
```

Then the required equations are

```text
c*P-d*Q = a+2,
c*Q+d*(P-Q) = 1.
```

This is `DkMath/Lib/NumberTheory/EisensteinCoordinates.lean:56–62`
(`eisensteinCoord_mul_sq`), specialized to the cubic point. Its coordinate
extraction theorems are at lines 99–120. The second equation immediately
gives `IsCoprime Q (P-Q)` (lines 124–131). The ABC wrappers in
`DkMath/ABC/GNExcessCubicEisensteinFactorConsequences.lean:27–66` all assume
the factor equality. The first two do not use shell membership at all.

## Adversarial same-data pair cannot exist in this family

`DkMath/ABC/GNExcessCubicIncidenceObstruction.lean:44–50` already proves

```lean
theorem cubicQuadratic_injective :
  Function.Injective (fun a : ℕ => a^2 + 3*a + 3)
```

`DkMath/ABC/GNExcessCubicComplementIncidence.lean:44–62` already proves
`GNExcessCubicIncidencePair_injective`. Therefore equal exact norms force
equal natural witnesses; equal `(M,S)` also forces equal witnesses. The
requested counterexample with distinct natural witnesses and identical exact
norm/repeated/complement data is impossible. Generic conjugate norm
counterexamples cannot establish information loss for this restricted family.

## Candidate strictly narrower bridge (not claimed proved)

With the verified Euclidean-domain infrastructure imported for
`R=TraceOneInt (-1)`, define

```text
alpha = eisensteinCoord ((a:ℤ)+2) 1
g = gcd alpha (d:R).
```

A useful reusable theorem shape is

```lean
theorem cubic_coord_gcd_square_factor
    {a d : ℕ}
    (hd2 : d^2 ∣ a^2 + 3*a + 3)
    (h3 : ¬ 3 ∣ d) :
    norm (gcd (eisensteinCoord ((a:ℤ)+2) 1) (d:R)) = (d:ℤ) ∧
    (gcd (eisensteinCoord ((a:ℤ)+2) 1) (d:R))^2 ∣
      eisensteinCoord ((a:ℤ)+2) 1
```

The shell packet supplies these hypotheses with `d=evenPart M`. Defining
`gamma=g` and taking the divisibility quotient supplies `beta`; norm
multiplicativity and `d>0` force `norm beta=T`. A unit arising from gcd
normalization is absorbed into unrestricted `beta`.

This gcd uses the actual witness coordinate `a`, hence selects split
orientation internally. The bridge needs an actual proof (via the
primitive-coordinate/conjugate coprimality calculation and prime powers,
or the ideal `(d,alpha)` and its norm/index). Neither a norm-only
counterexample nor absence of an existing wrapper proves the bridge false.

## Kernel-checked scalar allocation bridge

`scratch/ShellAllocation.lean` now proves:

1. `Scratch.ABCEisensteinLanding.nat_squarefree_square_decomposition_unique`:
   if `T` and `B` are squarefree, `d,G ≠ 0`, and `T*d^2=B*G^2`, then
   `B=T` and `G=d`.
2. `Scratch.ABCEisensteinLanding.shell_squarefree_norm_allocation`:
   shell membership plus `Squarefree B`, `G ≠ 0`, and
   `a^2+3*a+3=B*G^2` implies
   `B=oddPart M*S` and `G=evenPart M`.

The first proof compares prime valuations. Squarefree exponents lie in
`{0,1}`, so `v_q(T)+2*v_q(d)=v_q(B)+2*v_q(G)` determines both terms.
The second uses the existing shell squarefree/Pell packet.

Exact Mathlib sources (relative to `.lake/packages/mathlib/Mathlib/`):

- `Data/Nat/Squarefree.lean:50`: `Squarefree.natFactorization_le_one`.
- `Data/Nat/Factorization/Defs.lean:155`: `Nat.factorization_mul`.
- `Data/Nat/Factorization/Defs.lean:184`: `Nat.factorization_pow`.
- `Data/Nat/Factorization/Defs.lean:105`: `Nat.eq_of_factorization_eq`.

Verification from `lean/dk_math/`:

```sh
lake env lean docs/dev/ABC-Eisenstein-landing-provider-260915/scratch/ShellAllocation.lean
```

Exit code `0`; both printed axiom lists are exactly
`[propext, Classical.choice, Quot.sound]`. This checks the scalar uniqueness
and allocation, not the still separately investigated element provider.

Memory registry `MEMORY.md:471–479` was used only to locate the Lib canonical
coordinate owner and known build-order convention; the coordinate owner was
checked directly in the current source above.

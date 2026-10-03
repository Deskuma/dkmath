# FLT5 current-source audit — checkpoint 001

Date: 2026-10-04. Scope: bounded source inspection of the completed exponent-five
route and its reverse projection. No production code changed. Axiom/build
verification is coordinated by the parent audit and must be recorded separately;
source inspection alone is not a fresh kernel check.

## Verified endpoint and dependency route

The current source really contains the unconditional endpoint

```lean
DkMath.FLT.Five.flt5Target : FLT5Target
-- FLT5Target = ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
--   ¬ Fermat5Equation x y z
```

Owner: `DkMath/FLT/Five/Main.lean:55,79`. Its ordinary-argument wrapper is
`fermatFive_no_positive_solution` at line 88. Scope is positive naturals with
exponent exactly five. The actual term is
`flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion`, with the
proved `goldenUnitClassesModFifth` supplied by the receiver, rather than an
unsupplied provider or an imported theorem of general FLT.

The source dependency chain is:

```text
positive Fermat5Equation
 -> exists_counterexamplePack_of_positive_fermat5 (gcd normalization)
 -> CounterexamplePack.branchB_orientation (possibly swap x/y)
 -> signedBranchA_normalForm_of_branchB (difference or sum orientation)
 -> signedFiveAdicPacket_of_normalForm
 -> signedFiveAdicPowerSplit_of_normalForm
 -> signedSquareGoldenExceptionalPacket_of_powerSplit
 -> signedGoldenRamifierStrippedPacket_of_exceptional
 -> beta_relPrime_conj + beta_mul_conj_eq_fifth
 -> goldenCoprimeFactorOfFifthPower
 -> goldenUnitClassesModFifth (five phi classes)
 -> signedGolden_nonzero_unitSector_false (classes 1..4)
 -> zeroSector_snd_factor_eq + zeroSector_tenthPower_split (class 0)
 -> GoldenZeroSectorCandidate (exact inversion data)
 -> goldenZeroSectorDescentPacket_of_candidate
 -> GoldenZeroSectorDescentPacket.strictDescent
 -> goldenZeroSectorDescentPacket_false (strong induction on |s|)
 -> goldenZeroSectorArithmeticExclusion
 -> flt5Target
```

The final factor-exclusion layer calls
`goldenZeroSectorCandidate_false packet.inversion.source`. Therefore its
three factor branches retain the exact inversion source; they do not infer
element equality from a norm or invoke the final endpoint circularly.

## Seven requested axes

| Axis | Actual current exponent-five source/result |
| --- | --- |
| Integer/GN | `add_pow_five_sub_eq_mul_GN5` in `Five/GN5.lean` gives `(g+y)^5-y^5=g*GN5 g y`; `pow_five_sub_pow_five_eq_gap_mul_GN5` is the endpoint-gap form. `SignedFiveAdicSource` records the difference source `(w-v, GN5 (w-v) v)` or the sum source `(u+v, SumGN5 u v)`. |
| Algebraic carrier | `GoldenInt` is the explicit integral pair ring with `phi^2=phi+1`, conjugation `(r,s) ↦ (r+s,-s)`, and norm `r^2+r*s-s^2`. The completed FLT5 route uses this real quadratic coordinate order, not a degree-four cyclotomic element. |
| Ramified correction | `goldenTau=⟨2,1⟩`, `goldenSqrtFive=⟨-1,2⟩`, `goldenTau_eq_phi_mul_sqrtFive`, `goldenSqrtFive_sq`, `goldenNorm_tau=5`. `exists_goldenTau_factor_of_five_dvd` gives actual coordinates for `alpha=tau*beta`. `SignedGoldenRamifierStrippedPacket` retains `tau_not_dvd_beta`, so the chosen element has one visible tau factor. |
| Normalized power | The production proof goes directly to an element fifth power up to a unit. `beta_mul_conj_eq_fifth` is an element identity, `beta_relPrime_conj` is a common-divisor/unit certificate, and `goldenCoprimeFactorOfFifthPower` uses GoldenInt's norm-Euclidean GCD/UFD structure and `exists_associated_pow_of_mul_eq_pow`. There is no explicit ideal-factorization stage in this completed chain; an ideal fifth-power equality is a consequence, not a separate implemented argument. |
| Unit/phase | `goldenUnitClassesModFifth` proves every GoldenUnit is `phi^i*delta^5`, `i : Fin 5`, with signs absorbed by odd fifth powers. This is a p-specific classification proved by coordinate descent; the five sectors are algebraic classes, not angular sectors. |
| Integral/additive landing | `goldenPow_five_fst`, `goldenPow_five_snd`, and `golden_unit_*_mul_fifth_snd` compute actual coordinates. `zeroSector_snd_factor_eq` applies `.snd` to `beta=gamma^5`, yielding `s*H(r,s)=-5^6*a^10`; the original square-source provenance remains explicit. No norm-only argument produces these identities. |
| Descent/contradiction | `GoldenZeroSectorDescentPacket.strictDescent` reconstructs positive `t,D`, coprime coordinates, norm prime to five, and exact fifth-power shapes. `goldenZeroSectorDescentMeasure=p.base.snd.natAbs` strictly decreases by `fifthRoot_measure_lt`; strong induction excludes the packet. The successor is a Golden descent packet, not asserted to be a smaller original Fermat triple. |

## Exact ramified and coordinate data

`signedFiveAdicPacket_gcd_eq_five` proves gcd(carrier,residual)=5 in both
orientations. `SignedFiveAdicPowerSplit` then has

```text
carrier = 5^4 * a^5
residual = 5 * b^5
distinguished = 5 * a * b
a,b > 0, gcd(a,b)=1, 5 ∤ b
```

`SignedSquareGoldenExceptionalPacket` retains the source coordinates:

```text
difference: M=w^2+v^2, N=w*v, delta=w^2-v^2
sum:        M=u^2+v^2, N=-(u*v), delta=u^2-v^2
GoldenNorm M N=5*b^5
M-2*N=5^8*a^10
M^2-4*N^2=delta^2
```

In the stripped packet, the integral diagonal equation `2*M+N=5*k` gives
`beta=⟨M-k,2*k-M⟩` and the actual equality `alpha=tau*beta`. Its data are

```text
N(beta)=b^5
beta.snd=-5^7*a^10
5 ∤ N(beta)
tau ∤ beta
```

`GN5_eq_goldenNorm_squareLink` is a particular polynomial identity in
endpoint-square coordinates. It does not identify `alpha` with a full
cyclotomic factor from matching norms.

## Honest reverse projection onto the requested sequence

```text
ramified correction:
  alpha=tau*beta, tau∤beta
 -> normalized ideal fifth power:
  collapsed by the stronger direct element theorem
  beta=epsilon*gamma^5 from coprime conjugate factors in a Euclidean domain
 -> unit class:
  epsilon=phi^i*delta^5; four nonzero classes excluded mod five
 -> additive/coordinate landing:
  actual snd equation s*H(r,s)=-5^6*a^10,
  primitive split |s|=5^6*c^10, |H|=d^10
 -> descent:
  re-entry T(r,s)=(r^2+r*s+s^2,s^2),
  T(base)=gamma^5, next packet with |gamma.snd|<|base.snd|
```

The exact theorem collapsing the ideal-to-element gap is
`goldenCoprimeFactorOfFifthPower` in `GoldenCoprimeFactor.lean:36`, backed by
`goldenEuclideanDomain` in `GoldenEuclidean.lean:228`. It does **not** collapse
the unit class: `GoldenUnitClassesModFifth` and the sector exclusions remain
essential. The element theorem suffices to infer an ideal fifth power, but
describing the completed proof as a class-group principalization argument
would change its actual proof architecture.

The formal strength of `GoldenUnitClassesModFifth` is completeness of the
five representatives, not a proved quotient cardinality or uniqueness of
the representative. Its exact contract is

```lean
∀ epsilon : GoldenInt, GoldenUnit epsilon →
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

The production contradiction needs only this completeness and the
coordinate exclusion for each `i ≠ 0`; no distinctness assertion is used.

The exact recursive invariant is `GoldenZeroSectorDescentPacket`:

```text
base=(r,s), t,D∈Nat positive
gcd(|r|,|s|)=1
s=±5*t^5
H(r,s)=D^5
5∤N(base)
```

`goldenZeroSectorLift_norm` proves `N(T(base))=H(r,s)`, and
`exists_lift_eq_fifthPower` proves the stronger `T(base)=gamma^5` plus
`N(gamma)=D`. Actual coordinate equality drives the descent; norm equality
is insufficient. `strictDescent` preserves the displayed invariant and
`fifthRoot_measure_lt` supplies the strict natural decrease.

## Generic p=5 TraceOne endpoint is separate

`DkMath/FLT/Five/TraceOneBridge.lean:26` contains the genuine
coordinate-preserving ring equivalence
`goldenTraceOneRingEquiv : GoldenInt ≃+* TraceOneInt 1`. Thus GoldenInt versus
TraceOneInt 1 is a presentation distinction once this map is used, rather
than a mathematical obstruction. Norm compatibility alone is not the reason.

`PrimeTraceOneFiveSectorClosure.lean` transports the proved five sectors and
the Euclidean structure through this equivalence. It proves
`classGroupPTorsionFreeAt_traceOneOne_five` and
`exists_goldenSector_mul_fifth_of_primeTraceOneStrippedIdealPacket_five`.
The latter still **requires** supplied `PrimeAdicFactorPacket`,
`PrimeTraceOneCoordinatePacket`, and `PrimeTraceOneStrippedIdealPacket`; it
returns a sector-times-fifth-power formula. It neither removes the sectors
nor constructs a strict descent nor invokes specialized `flt5Target`.

This generic endpoint therefore cannot be substituted for the completed
FLT5 contradiction theorem. Conversely the existence of the completed
GoldenInt proof does not populate every generic TraceOne packet bridge.

## Non-cosmetic split and candidate common state

The completed exponent-five route supports a shared *descriptive* sequence
"ramified correction → power extraction → unit class → coordinate landing
→ strict packet descent". Its source does not by itself establish one
theorem simultaneously instantiated by the current p=3,5,7 carriers.

At exponent five, the earliest important arithmetic specialization is the
endpoint-square identity `GN5_eq_goldenNorm_squareLink` together with the
retained square-discriminant source. This reduces the quartic GN factor to
a binary norm in a real quadratic order. The current p=7 phase-corrected
degree-six carrier cannot be identified with this binary carrier or with a
quadratic TraceOne element by equal norms. After extraction, the explicit
quartic re-entry identity `goldenZeroSectorLift_norm` and its strict
inequality are further p-specific closure mechanisms.

Essential state visible within p=5 is: signed source orientation, explicit
carrier/order and coordinate map, ramified load, conjugate coprimality,
unit class modulo fifth powers, exact coordinate/source relations, and the
recursive packet measure. `p mod 4` selects real-versus-imaginary quadratic
arithmetic in the generic layer, but it cannot alone encode the higher
degree current p=7 carrier. The five phi classes give a source-grounded
discrete "stripe" variable; calling their interaction a moire theorem
would require an additional proved invariant that is absent here.

## Next verification action

Run a coordinated small axiom probe for `flt5Target`,
`goldenCoprimeFactorOfFifthPower`, `goldenUnitClassesModFifth`,
`GoldenZeroSectorDescentPacket.strictDescent`, and
`goldenZeroSectorDescentPacket_false`; preserve its command/output in the
audit log. No full build is justified by this documentation-only pre-audit.

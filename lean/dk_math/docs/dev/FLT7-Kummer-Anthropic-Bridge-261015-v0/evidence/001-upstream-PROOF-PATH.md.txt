# The route of the proof

The argument is that of Frey, Serre, Ribet, Wiles and Taylor-Wiles, largely as in Darmon, Diamond and Taylor,
run as a proof by contradiction. A theorem `X.y` is stated in `Theorems/Thm_X_y.lean` and proved in
`P2M/Sol/S_X_y.lean`, whose `import Theorems.Thm_…` lines are exactly the theorems it cites. Where this prose and the
Lean differ, the Lean is right. Named classical theorems are proved in the strength the argument needs; the last
section says exactly what that is.

**1. Reduction to a prime p ≥ 5.** `fermat_last_theorem` follows in one line from `FLT.fermatLastTheorem : FermatLastTheorem`
(Mathlib's formulation), whose proof applies Mathlib's `FermatLastTheorem.of_odd_primes` (using exponent 4)
and `fermatLastTheoremThree` and hands a prime p ≥ 5 to `FreyPackage.fermatLastTheoremFor_of_five_le`, proved from
exactly `FreyPackage.of_counterexample` and `FreyPackage.no_frey_package`.

**2. Frey package.** A Frey package (`Definitions/Def_FLTPrelim_FreyPackage.lean`, adapted from the Imperial College
London FLT project) is a solution a^p + b^p = c^p in nonzero integers, p ≥ 5 prime, normalised to gcd(a,b) = 1,
a ≡ 3 (mod 4), 2 | b, with the Frey curve E_P : y² + xy = x³ + ((b^p − 1 − a^p)/4)x² − (a^p b^p/16)x, an integral
model of y² = x(x − a^p)(x + b^p). `FreyPackage.of_counterexample` builds one from any counterexample in nonzero integers with prime exponent
p ≥ 5 (citing only Mathlib); `FreyPackage.no_frey_package (P : FreyPackage) : False` is assembled from exactly the four theorems of steps
3 to 6: irreducible and modular gives, after level lowering, a nonzero weight-2 cusp form on Γ₀(2), and there is
none.

**3. Irreducibility.** `FreyPackage.Mazur_Frey` proves `GaloisRepIsIrreducible ℚ P.freyCurve P.p`
(`Definitions/Def_FLTPrelim_GaloisRep.lean`: E_P[p] is nontrivial with no Galois-stable F_p-submodule besides 0 and
itself). The case a ≡ 3 (mod 8) has its own argument at the prime 2 (`FreyPackage.Mazur_Frey_of_a_mod_eight`).
Otherwise reducibility would give a Galois-stable line with trivial action on the quotient
(`FreyPackage.frey_reducible_hasCofixedLine`, Serre's observation, using that E_P has no rational point of order p),
excluded in three ranges:
- p ≥ 17: `FreyPackage.frey_no_cofixed_large`, Mazur's Eisenstein-ideal argument carried out for this situation
  (X₀(N), its Jacobian and Néron model, the cuspidal subgroup, the Eisenstein quotient; `ModularCurve` and
  `AlgebraicGeometry` namespaces; the global input is `WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`). This is
  by far the largest part of the step.
- p = 11 (`FreyPackage.frey_no_cofixed_eleven`) and p ∈ {5, 7, 13} (`FreyPackage.frey_no_cofixed_small`) hold
  vacuously because those exponents are settled outright: `fermatLastTheoremFive` by a self-contained descent in
  Z[(1+√5)/2]; `fermatLastTheoremSeven`, `…Eleven`, `…Thirteen` by Kummer's theorem for regular primes `flt_regular`
  (a port of the flt-regular project: cases I and II, Kummer's lemma via Hilbert's theorems 90-94) plus proofs
  that the rings of integers of the 7th, 11th and 13th cyclotomic fields are principal
  (`IsCyclotomicExtension.Rat.seven_pid`, `….eleven_pid`, `….thirteen_pid`).

**4. Modularity.** `FreyPackage.frey_isModular` follows from `WeierstrassCurve.modularity_of_semistableModel`: every
integral Weierstrass model with Δ ≠ 0 and no prime dividing both Δ and c₄ (`IsSemistableModel`) is modular
(`IsModular`: a_ℓ matches a normalised weight-2 eigenform on some Γ₀(N) at good primes; both in
`Definitions/Def_FLTPrelim_Modularity.lean`; cusp forms, Γ₀(N) and q-expansions are Mathlib's). The proof is Wiles's:
- one of ρ̄_{W,3}, ρ̄_{W,5} is irreducible (`WeierstrassCurve.modThreeOrFiveIrreducible`: if both were reducible W would
  have a rational 15-isogeny, and `WeierstrassCurve.fifteenIsogenyClassification` pins c₄³/Δ of such a curve to one of
  four values, none of which a semistable model can have);
- Langlands-Tunnell in the weight-2, level-conditioned form Wiles uses,
  `WeierstrassCurve.isResiduallyModular_three_and_noInertiaFixedTorsion_and_not_cube_dvd_of_isSemistableModel`: a
  weight-one form for the odd octahedral representation lifting ρ̄_{W,3}
  (`LanglandsTunnell.exists_isWeightOneChiNegThreeRealized_eq_trace_lift`, for surjective ρ̄₃ with cyclotomic determinant,
  by Tunnell's argument: monomial automorphy over the subfields cut out by subgroups of GL₂(F₃), cyclic base change,
  a converse theorem with Rankin-Selberg integrals), then multiplication by the Eisenstein series E₁(1, χ₋₃) and a
  Deligne-Serre lifting lemma to reach a congruent weight-2 eigenform;
- two modularity lifting theorems, R = T by Taylor-Wiles patching in Diamond's formulation
  (`GaloisRep.DeformationRingData`, `CuspForm.HeckeGaloisRepDatum`, `Algebra.PatchingDatum`,
  `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`):
  `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd`
  (p = 3; a condition on inertia-fixed 3-torsion when 9 divides the residual level) and
  `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd` (p ∈ {3, 5}; p² not
  dividing the residual level);
- the 3-5 switch `WeierstrassCurve.threeFiveSwitchCurve` (a second semistable model W′ with ρ̄_{W′,3} irreducible and
  a_ℓ(W′) ≡ a_ℓ(W) (mod 5) at common good primes ℓ ≠ 5, built beneath from a curve with W′[5] ≅ W[5] taken from an
  explicit family in the `RubinSilverberg` namespace) and `WeierstrassCurve.isResiduallyModularOfLevel_of_switch`.
If ρ̄_{W,3} is irreducible, Langlands-Tunnell and lifting at 3; otherwise the switch gives W′, the first case makes
W′ modular, W is residually modular mod 5, and lifting at 5 finishes.

**5. Level lowering.** `FreyPackage.level_lowering_to_two`: E_P modular and ρ̄_{E_P,p} irreducible give a nonzero
`f : CuspForm (CongruenceSubgroup.Gamma0 2) 2`. First `FreyPackage.modularRepOfConductorLevel`: the representation arises
from a squarefree level supported on the primes dividing abc, "arises from" (`ModularRepOfLevel`,
`Definitions/Def_FLTPrelim_ModularRep.lean`) being a congruence of traces modulo a prime above p, not an isomorphism
of representations (this proof re-derives modularity itself, so the `IsModular` hypothesis above is formally
unused). Then primes are removed one at a time (`FreyPackage.level_lowering_to_two_of_conductorLevel`): an odd
q ≠ p, at which E_P[p] is unramified, by `FreyPackage.level_lowering_odd_prime_of_conductorLevel`, Ribet's theorem
in the form needed (Čerednik-Drinfeld uniformisation, `CerednikDrinfeld` namespace); p itself by
`FreyPackage.level_lowering_at_p_of_conductorLevel`, the Mazur-Ribet step, using that E_P[p] is finite at p
(`FreyCurve.isPeuRamifieeAt_odd_of_integralForm`). Levels 1 and 2 are closed by `ModularForm.S2_Gamma0_one_eq_zero`
and step 6.

**6. S₂(Γ₀(2)) = 0.** `ModularForm.S2_Gamma0_2_eq_zero`: every `f : CuspForm (CongruenceSubgroup.Gamma0 2) 2` is 0,
proved from Mathlib alone.

## Exact strength of the named steps

- **Mazur.** Proved: irreducibility of E_P[p] for Frey curves (p ≥ 17 by the Eisenstein quotient; p ≤ 13 by
  Kummer or descent, not modular curves). Not proved: Mazur's theorems on rational isogenies or torsion of
  general curves.
- **Langlands-Tunnell.** Proved: the octahedral case with explicit lift, for surjective ρ̄₃ with cyclotomic
  determinant, delivered as a weight-one form and then as weight-2 residual modularity with level conditions.
  Not proved: automorphy of general odd two-dimensional representations with soluble image.
- **Modularity lifting.** Proved: the two level-conditioned statements above for semistable W at p = 3 and
  p ∈ {3, 5}. Not proved: versions without the level conditions, for non-semistable curves or other p.
- **Wiles.** Proved: every semistable integral Weierstrass model with Δ ≠ 0 is modular in the a_ℓ-matching
  sense. The hypothesis is on a chosen integral equation; nothing is said about non-semistable curves, modular
  parametrisations or L-functions.
- **Ribet.** Proved: level lowering for the Frey representation at squarefree conductor-supported levels, as a
  congruence of traces. Not proved: Ribet's theorem for a general modular mod-p representation.
- **"Irreducible"** is F_p-irreducibility of E[p]; absolute irreducibility, where lifting needs it, is derived in
  the tree (`ResidualGaloisRep.isAbsolutelyIrreducible_of_isIrreducible_of_isOdd`).

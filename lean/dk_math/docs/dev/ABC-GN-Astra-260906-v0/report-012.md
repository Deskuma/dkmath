# LUNA-012 — complement-slice / incidence-pair coordinates

## Scope

This checkpoint implements the exact complement-coordinate and incidence-pair
geometry requested by `instruction-012.md`. It remains in fact-freezing mode:
there is no shell-count estimate, fiber-cardinality bound, Pell/conic count,
incidence sparsity theorem, provider assumption, or use of `abc_main_axiom`.

## Files

Production:

- `DkMath/ABC/GNExcessCubicComplementIncidence.lean`
- `DkMath/ABC.lean` (public import immediately after the LUNA-011 module)

Campaign records:

- `README.md`, `ROADMAP.md`, `validation-012.txt`, and this report.

## Canonical pair and injectivity

`GNExcessCubicIncidencePair a` is exactly

```text
(GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a).
```

No new modulus or complement is introduced. The projection lemmas expose the
two coordinates, and
`GNExcessCubicIncidencePair_mul_eq_quadratic` proves

```text
pair(a).1 * pair(a).2 = a^2 + 3*a + 3.
```

`GNExcessCubicIncidencePair_injective` multiplies equal pairs and applies the
existing `cubicQuadratic_injective`. Thus the pair is injective even though
the individual modulus and complement maps are not asserted to be injective.

## Complement slices

`GNExcessCubicRealizedLargeModulusShellComplementSpace X D` is the image of
the LUNA-011 shell witness space under the canonical complement. Its
membership theorem is the exact represented-value existential. Every member
has the support facts

```text
0 < S,  S ≤ X,  Squarefree S,
```

and the space is contained in `Finset.Icc 1 X`. Positivity is obtained from
the packet equation and the positivity of the large repeated modulus; the
upper and squarefree facts are direct consumers of the LUNA-011 packet.

`GNExcessCubicRealizedLargeModulusShellComplementFiber X D S` filters shell
witnesses by `GNExcessCubicComplement a = S`. Represented complements have a
nonempty fiber. Distinct represented complement fibers are pairwise disjoint,
and the exact partition is

```text
biUnion complementSpace (complementFiber X D)
  = shellWitnessSpace X D.
```

Consequently,

```text
shellWitnessCount X D
  = ∑ S ∈ complementSpace X D, (complementFiber X D S).card.
```

No uniform bound on these fiber cards is claimed; the existing Pell family is
the reason to keep this boundary explicit.

## Incidence-pair shell

`GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D` is the image of
the shell witness space under the pair map. Its membership theorem records
exactly which witness realizes `(M,S)`. Pair injectivity gives the exact card
preservation theorem

```text
(pairSpace X D).card = shellWitnessCount X D.
```

The two projections are exact:

```text
(pairSpace X D).image Prod.fst = modulusShell X D,
(pairSpace X D).image Prod.snd = complementSpace X D.
```

The resulting card inequalities for the two projection images are only the
elementary image-cardinality inequalities; they are not presented as
sparsity progress.

For every represented pair,
`GNExcessCubicRealizedLargeModulusShellIncidencePair_packet` supplies a
witness and the stable packet

```text
1 ≤ a ≤ X,
D ≤ M < 2D,
X+1 < M,
0 < S ≤ X,
Squarefree S,
Nat.Coprime M S,
M*S = a^2 + 3*a + 3.
```

`GNExcessCubicRealizedLargeModulusShellIncidencePair_existsUnique_witness`
proves uniqueness of this witness from pair injectivity. This is pair
uniqueness only; no modulus-fiber or complement-fiber uniqueness is inferred.

For a fixed complement fiber,
`GNExcessCubicRealizedLargeModulusShellComplementFiber_equation` exposes

```text
M(a)*S = a^2 + 3*a + 3,
D ≤ M(a) < 2D.
```

It deliberately does not solve or count this equation.

## Exact finite ledger

The theorem
`GNExcessCubicRealizedLargeModulusShell_three_way_card_ledger` records the
three exact identities together:

```text
shellWitnessCount
  = ∑ M ∈ modulusShell, (modulusFiber M).card
shellWitnessCount
  = ∑ S ∈ complementSpace, (complementFiber S).card
pairSpace.card
  = shellWitnessCount.
```

## Verification and trust boundary

The focused module build and the public `DkMath.ABC` aggregator build both
pass. The changed production module contains no `sorry`, `admit`, new
`axiom`, `abc_main_axiom`, or `native_decide`. The principal pair, partition,
cardinality, projection, and unique-witness declarations audit to the standard
Lean trust boundary `propext`, `Classical.choice`, and `Quot.sound` (or a
subset).

## Remaining frontier

The remaining problem is an arithmetic finite-lattice incidence question for
represented pairs satisfying the shell bounds, squarefree/coprime support,
and the canonical product equation. LUNA-012 freezes those coordinates and
their exact finite ledger; it proves no nontrivial bound for a shell count,
either fiber, pair-space size, Pell family, or ABC quality coupling.

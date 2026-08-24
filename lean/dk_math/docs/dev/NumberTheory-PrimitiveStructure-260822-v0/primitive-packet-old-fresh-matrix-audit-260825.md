# PRIM-L023: Full-Cover Old/Fresh Packet Branch Matrix Audit

Date: 2026-08-25

Branch: `wip/number-theory/primitive-structure-260822-v2`

Environment: Lean / Mathlib v4.32.2

This checkpoint is a read-only mathematical/API reconnaissance. No Lean
source file, import, dependency revision, `lean-toolchain`, Lake
configuration, PRIM-C001/C002, PRIM-L022, or Legendre facade/frontier file was
changed.

## Executive outcome

**Outcome B — STRUCTURAL REFINEMENT.**

The existing per-seat C002/L022 dichotomy is sufficient to expand every fully
covered canonical packet into the four conceptual cells

```text
O/O, O/F, F/O, F/F.
```

Here `O` is old-generated and `F` is the unique fresh-prime split with a
nontrivial small cofactor. The cells are disjoint because a fresh direction
excludes old generation, although no packet-level predicate or four-cell
inductive type currently exists.

The F/F cell has a useful exact factor rectangle:

```text
L = ℓ₁ * k₁,
R = ℓ₂ * k₂,
ℓ₂ * k₂ - ℓ₁ * k₁ = n.
```

It has `2 ≤ k₁, k₂ ≤ n`, both `kᵢ` in the canonical coprime base world,
`Coprime ℓᵢ kᵢ`, all four cross-side coprimalities, and `ℓ₁ ≠ ℓ₂`.
These are genuine packet-level coordinates, but they are obtained by
combining existing exact theorems and do not currently produce a new
cardinality obstruction, descent, or incompatibility against full cover.

The small-cofactor return is only a bounded coordinate return. There is no
smaller Legendre state, reconstruction theorem, or well-founded decreasing
measure. The correct recommendation is to stop this route for now and not
start PRIM-L024 automatically.

## 1. Exact current theorem inventory

| Layer | Existing declarations | Source and role |
|---|---|---|
| Generic old/fresh split | `primeScaleGeneratedBy_or_uniqueFresh_small_split_of_le_squareBody`, `squareBody_large_prime_small_cofactor_split`, `not_primeScaleGeneratedBy_of_freshPrimeDirection` | `Primitive/SquareBody.lean`, `StructuralArithmetic/PrimitiveDirection.lean`; exact finite alternatives and separation |
| Square-offset transport | `squarePoint_le_squareBody_of_squareOffset`, `squarePoint_pos_of_squareOffset`, `squareOffset_oldGenerated_or_uniqueFresh_small_split` | `Legendre/SmallCofactor.lean`; applies C002 to either packet point |
| Covered fresh refinement | `two_le_smallCofactor_of_covered_fresh_split`, `smallCofactor_mem_coprimeBase_of_fresh_split`, `oldGenerated_or_uniqueFresh_nontrivialSmall_of_fullyCovered` | `Legendre/SmallCofactor.lean`; gives `2 ≤ k ≤ n` and canonical-base membership |
| Packet seats | `mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets`, `mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets` | `Legendre/CoprimePacket.lean`; validates `r` and `n+r` |
| Complete-point separation | `coprime_squarePacketPoints_of_mem_base`, `not_prime_dvd_both_squarePacketPoints` | `Legendre/PacketCoprimality.lean`; separates all prime divisors of `L` and `R` |
| Existing factor rectangle | `squareAnchorPacketCrossOffsets_coprime_factorization`, `packetCross_factor_rectangle_coprime`, `exists_coprime_factor_rectangle_of_fullyCovered` | `Legendre/PacketCoprimality.lean`; selected-old quotient rectangle |
| Residues and determinant | `squarePacket_left_modEq_base`, `squarePacket_right_modEq_base`, `packetCross_factor_products_modEq`, `packetCross_factor_determinant_eq_anchor`, `packetCross_factor_determinant_sub_eq_anchor` | `Legendre/PacketUnitResidue.lean`; `Nat.ModEq` and one-anchor difference |
| Quotient collisions | `squareAnchorIncidenceQuotient_injective_of_four_le`, `card_squareAnchorCoprimeGlobalQuotients_of_four_le` | `Legendre/Quotient.lean`; injectivity of incidence-to-quotient, not seat-to-cofactor |

`FreshPrimeDirection` records one prime divisor outside a finite world, while
`SupportDisjointFrom` excludes every old prime divisor. They are not the same
notion.

## 2. Q1 — packet-level branch predicates

The classification is **B: equivalent theorems exist, but the packet-level
branch matrix is not packaged**.

There is no current packet old/fresh predicate, enum, or four-cell theorem.
The smallest existing chain is to apply
`oldGenerated_or_uniqueFresh_nontrivialSmall_of_fullyCovered` to `r` and to
`n+r`. The required membership facts are supplied by
`mem_squareAnchorCoprimeBaseOffsets_mem_coprimeOffsets` and
`mem_squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets`.

The theorem's O/F alternatives are exclusive: the F witness contains
`FreshPrimeDirection`, and
`not_primeScaleGeneratedBy_of_freshPrimeDirection` rules out the O branch.
This does not use `SupportDisjointFrom` and does not assert a fresh direction
on an O seat.

## 3. Q2 — exactness of the four cells

For `L := n^2+r` and `R := n^2+(n+r)`, the two sidewise disjunctions give

```text
(O/O) ∨ (O/F) ∨ (F/O) ∨ (F/F).
```

Under full cover, the F side is strengthened by
`two_le_smallCofactor_of_covered_fresh_split`; the cofactor belongs to
`squareAnchorCoprimeBaseOffsets n` by
`smallCofactor_mem_coprimeBase_of_fresh_split`. No new arithmetic is needed,
and no cell is assumed inhabited. The four cells are pairwise disjoint by
the sidewise O/F exclusivity above.

No new packet predicate should be added merely to make this table convenient.

## 4. Branch matrix

For an F side write, locally,

```text
F(L): L = ℓ₁*k₁,
      Prime ℓ₁, n < ℓ₁, 2 ≤ k₁ ≤ n,
      k₁ ∈ squareAnchorCoprimeBaseOffsets n,
      k₁ old-generated, and ℓ₁ uniquely fresh for L.
```

Define `F(R)` analogously. This is report-local notation; no Lean predicate
or inductive type is introduced.

| Cell | Exact available content | Status |
|---|---|---|
| O/O | Both points are generated by `primeScalesUpTo n`; `Coprime L R` follows from L020. | Exact old-support separation; no present contradiction |
| O/F | `L` is old-generated and `R = ℓ₂*k₂` has the nontrivial canonical cofactor package. | Exact mixed factor separation; no support-cardinality bound |
| F/O | Symmetric to O/F. | Same status |
| F/F | Both products, the determinant, canonical cofactors, same-side fresh/cofactor coprimality, cross-side coprimality, and distinct fresh primes. | Strongest finite structural cell only |

The table does not claim that any cell is populated for a particular `n`.

## 5. Q3 — exact F/F factor rectangle

The two L022 fresh witnesses give

```text
L = ℓ₁*k₁,
R = ℓ₂*k₂,
ℓ₂*k₂ - ℓ₁*k₁ = n,
2 ≤ k₁,k₂,
k₁,k₂ ≤ n,
k₁,k₂ ∈ squareAnchorCoprimeBaseOffsets n.
```

The determinant is the rewrite
`(n^2+n+r) - (n^2+r) = n`; it is the same identity as
`packetCross_factor_determinant_sub_eq_anchor`.

`coprime_squarePacketPoints_of_mem_base` gives `Coprime L R`. Since each
factor divides its complete point, `Nat.Coprime.of_dvd` transfers this to

```text
Coprime k₁ k₂,
Coprime ℓ₁ k₂,
Coprime k₁ ℓ₂,
Coprime ℓ₁ ℓ₂.
```

`Coprime ℓ₁ k₁` and `Coprime ℓ₂ k₂` are already C002/L022 fields; they do
not come from L020. The cofactor theorem gives `Coprime n k₁` and
`Coprime n k₂`, and `Coprime n ℓᵢ` follows by factor-divisor transfer from
the coprime complete point (or directly from prime `ℓᵢ` and `n < ℓᵢ`).
Thus every coprimality item listed in the instruction is supported, although
the combined F/F tuple is not a public theorem.

This must not be generalized to arbitrary same-side old quotient factors:
L020 intentionally leaves `Coprime p a` unresolved because selected-prime
depth may be greater than one.

The existing `Nat.ModEq` route is sufficient. Rewriting
`squarePacket_left_modEq_base` and `squarePacket_right_modEq_base` with the
F/F products gives

```text
ℓ₁*k₁ ≡ r [MOD n],
ℓ₂*k₂ ≡ r [MOD n].
```

`packetCross_factor_products_modEq` gives their transitive congruence, while
the exact determinant theorem gives the integer difference. No `ZMod`
infrastructure is needed, and residue equality is not integer equality by
itself.

## 6. Q4 — distinct fresh primes

The conclusion `ℓ₁ ≠ ℓ₂` is immediate in F/F. If `ℓ₁ = ℓ₂`, the fresh
prime divides both `L` and `R`, contradicting `Coprime L R`. The existing
`not_prime_dvd_both_squarePacketPoints` and
`Nat.Prime.not_coprime_iff_dvd` give this route directly.

No ordering follows. Although `R > L`, the comparison is between
`ℓ₁*k₁` and `ℓ₂*k₂`, and the cofactors can differ. Neither `ℓ₁ < ℓ₂` nor
`ℓ₂ < ℓ₁` is justified.

## 7. Q5 — small-cofactor return map

For a fixed fresh seat, the small cofactor is uniquely determined once the
fresh branch exists. If two fresh splits use `(ℓ₁,k₁)` and `(ℓ₂,k₂)`, the
uniqueness field in C001/C002 gives `ℓ₁ = ℓ₂`; the two product equations then
give `k₁ = k₂` by cancellation. Thus the fresh prime and cofactor are both
unique, but the construction is not a total function because the O branch
remains possible.

For two arbitrary fresh seats with a common cofactor `k`, subtraction of the
two product equations gives only

```text
k ∣ (r₂-r₁)
```

when the subtraction is oriented naturally. This does not rule out equal
cofactors for arbitrary distinct seats.

Inside one F/F packet the point difference is `n`. Hence common `k` would
give `k ∣ n`; together with `Coprime n k` and `2 ≤ k`, this forces the
contradiction `k = 1`. Therefore `k₁ ≠ k₂` within F/F. This is already a
consequence of complete-point coprimality and factor divisibility, not a
global cofactor-map injectivity theorem.

The existing L014 theorem
`squareAnchorIncidenceQuotient_injective_of_four_le` concerns
`(q,r) ↦ squareOffsetSupportQuotient n q r`, not `r ↦ k`; it cannot be
relabelled as cofactor injectivity. No global surjectivity, permutation, or
fixed-point-free map was found.

## 8. Q6 — F/F descent or self-return

The return statement is only

```text
k₁,k₂ ∈ squareAnchorCoprimeBaseOffsets n,
2 ≤ k₁,k₂ ≤ n.
```

It does not define a smaller Legendre instance.

| Descent requirement | Current status |
|---|---|
| State type | None. `k` is a natural/canonical base offset, not a packet state with cover data. |
| Reconstruction theorem | None. No theorem reconstructs an F/F packet at anchor `k`, or creates `SquareOffsetsFullyCovered k`. |
| Preserved hypotheses | `Coprime n kᵢ` and base membership remain facts about the original anchor only. |
| Strict measure | `kᵢ ≤ n` is a bound, not a strict decrease of a recursively reconstructed state. |

Thus F/F is a bounded coordinate return, not descent or a self-return cycle.
No recursive Legendre state should be invented here.

## 9. Q7 — O/O and mixed branches

### O/O

If both points are old-generated, every prime divisor of both points lies in
`primeScalesUpTo n`. Complete-point coprimality separates their old supports.
The current source does not convert that fact into a strict support-card
bound, totient deficit, or impossibility. The packet ledger theorem
`totient_le_packetCrossPairCount_of_fullyCovered` counts cross incidences but
does not distinguish O/O.

### O/F and F/O

If, for example, `L` is O and `R = ℓ₂*k₂` is F, then `Coprime L R` and
factor divisibility give

```text
Coprime L ℓ₂,
Coprime L k₂.
```

The old support of the O-side is therefore disjoint from the old support
carried by the F-side cofactor, in the exact divisibility sense. The F/O
case is symmetric. No existing theorem turns this into a finite support
partition with a strict cardinality deficit; it remains support separation,
not a density or probability assertion.

## 10. Q8 — interaction with L019/L020/L021

For selected old primes `p` on the left and `q` on the right, the existing
factor rectangle gives

```text
L = p*a,
R = q*b,
p*a + n = q*b,
Coprime p q,
Coprime p b,
Coprime a q,
Coprime a b,
p*a ≡ r [MOD n],
q*b ≡ r [MOD n].
```

These are `squareAnchorPacketCrossOffsets_coprime_factorization`,
`packetCross_factor_rectangle_coprime`, and
`squareAnchorPacketCrossOffsets_unitResidue_factorization`.

In F/F, L022 refactors the selected quotient factors as

```text
a = ℓ₁ * (k₁ / p),
b = ℓ₂ * (k₂ / q).
```

This is exactly
`squareOffsetSupportQuotient_eq_fresh_mul_smallResidual` together with
selected-support divisibility. Substitution yields

```text
p * ℓ₁ * (k₁/p) + n = q * ℓ₂ * (k₂/q),
```

which is the same determinant identity after cancellation. The residue
statements are likewise the same product congruences. No stronger theorem is
exposed: the refactorization adds provenance, not a new inequality,
injectivity, or contradiction.

The O/F and F/O substitutions give the same exact mixed rectangle and do not
constrain the internal old factorization of the O-side beyond generation by
the finite world.

## 11. Q9 — cardinality and matching leverage

No immediate cardinality imbalance was found. The natural source and target
sets are both based on

```text
(squareAnchorCoprimeBaseOffsets n).card = Nat.totient n.
```

The cofactor return lies in the same ambient base set, but no existing theorem
makes the global return map injective or surjective. The F/F fact `k₁ ≠ k₂`
is only a two-element within-packet separation.

The existing maps have different domains or targets:

- `squareAnchorIncidenceQuotient_injective_of_four_le` is an incidence-to-
  quotient map;
- `squareAnchorPacketCrossPairCount_eq_sum_support_card_mul` is a support
  cross-pair count;
- `totient_le_packetCrossPairCount_of_fullyCovered` is a lower bound, not a
  strict source/target mismatch.

No fixed-point-free permutation, involution, forced cycle, or Hall-type
deficiency is exposed. Matching infrastructure has no immediate consumer.

## 12. Q10 — final leverage classification

The route is classified as

```text
Outcome B — STRUCTURAL REFINEMENT.
```

It is not Outcome A: no new full-cover exclusion, strict cardinality bound,
global cofactor injectivity, well-founded descent, or contradiction was found.

It is not merely Outcome C: the packet combination exposes a bounded
canonical cofactor pair, same-side fresh/cofactor coprimality, four cross-side
coprimalities, and distinct fresh primes, none of which is currently packaged
as one packet theorem. These remain exact finite coordinates rather than a
new obstruction.

## 13. Attractive but invalid inferences

The following were explicitly rejected:

- fresh existence on every covered seat;
- identifying `FreshPrimeDirection` with `SupportDisjointFrom`;
- treating an old-generated point as prime;
- inferring `ℓ₁ < ℓ₂` from `R > L` in F/F;
- inferring that `k₁,k₂ ≤ n` defines a smaller Legendre packet;
- inferring that complete-point coprimality makes same-side old factors
  coprime;
- promoting residue equality to integer equality without product equations;
- treating a finite cofactor return as descent;
- treating equal finite cardinalities as a permutation without bijectivity;
- turning support separation into a density or probability claim;
- importing PrimitiveBeam or Zsigmondy origin into the finite-world split;
- using local parity or odd global `Ω` as a primality criterion.

## 14. Recommendation for PRIM-L024

**Recommendation: stop this packet branch-matrix route for now; do not start
PRIM-L024 automatically.**

There is no immediate theorem consumer that justifies a packet branch
predicate, an inductive cell type, a cofactor map, matching machinery, or a
recursive descent state.

If a later review identifies a concrete consumer, the smallest possible API
would be one theorem returning the existing nested O/F disjunction for both
sides, followed by an F/F factor package containing the product, determinant,
canonical-cofactor, and cross-coprimality fields. It should reuse
`SmallCofactor`, `PacketCoprimality`, and `PacketUnitResidue`, without a new
branch enum. At present even this packaging is a structural convenience, not
an implementation step justified by a new obstruction.

## 15. v4.32.2 API sensitivity

The audit encountered only the pinned v4.32.2 APIs:

- C001/C002 freshness is represented by proposition fields, including
  `∀ q, FreshPrimeDirection ... q → q = ℓ`;
- `Nat.Coprime.of_dvd` is the factor-divisor transfer used by existing packet
  rectangle proofs;
- packet residues already use `Nat.ModEq`, so no `ZMod` import is needed;
- `squareAnchorCoprimeBaseOffsets_shift_mem_coprimeOffsets` is the bridge for
  the right packet side;
- L020 packages cross-side coprimality while leaving same-side selected-prime
  depth open;
- no v4.33.0 upgrade or compatibility rewrite was attempted.

## 16. Verification and stop condition

No Lean source modification or temporary scratch file was made. The only
requested repository artifact is this report. Final verification is
`git diff --check` plus whitespace and forbidden-placeholder audits on this
file; a Lean build is not required for this documentation-only checkpoint.

PRIM-L024 is not started.

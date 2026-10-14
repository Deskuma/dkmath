# Report 003 — selective transport and conservation certificates

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Outcome **B — reusable algebraic transport instrument**. Step 003 is complete.
Stop before Step 004.

## Files changed

Paths are relative to `lean/dk_math`:

- `DkMath/Lib/Cosmic/GTailTransport.lean`: two movement-sum definitions,
  one private partition helper, and twelve public theorem endpoints.
- `DkMathTest/CosmicFormula/GTailTransport.lean`: semiring and natural modular
  regressions, counterexamples to unconditional invariance, and all axiom checks.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-003.md`: pre-code
  inventory of prerequisite source/reports/reviews and Mathlib contracts.
- This report and the adjacent `ROADMAP.md`.

Initial working tree was clean. Existing selection/factor/GTail sources and
all FLT owners are unchanged. License headers, import ordering, module-file
prints, comments and code formatting follow the established repository style.
The module is a direct import; no façade export is added.

## Definitions and exact public theorem types

Namespace: `DkMath.CosmicFormula`. The semiring parameters on the movement
sums are implicit:

```lean
def sumMovedIn {R : Type*} [CommSemiring R]
    (d : ℕ) (S T : Finset ℕ) (x u : R) : R :=
  ∑ k ∈ activeSelectedIndices d T \ activeSelectedIndices d S, selectedTerm d k x u

def sumMovedOut {R : Type*} [CommSemiring R]
    (d : ℕ) (S T : Finset ℕ) (x u : R) : R :=
  sumMovedIn d T S x u
```

Only active terms move. No second selected Body, Gap, binomial term or GTail
is defined. Arbitrary input sets may overlap, agree, be empty/full, or include
indices outside `0..d`. The following signatures expand the file's implicit
semiring variable binders; the modular endpoint uses only naturals.

```lean
theorem selectedBody_transport
    {R : Type*} [CommSemiring R] (d : ℕ) (S T : Finset ℕ) (x u : R) :
    selectedBody d T x u + sumMovedOut d S T x u =
      selectedBody d S x u + sumMovedIn d S T x u

theorem selectedGap_transport
    {R : Type*} [CommSemiring R] (d : ℕ) (S T : Finset ℕ) (x u : R) :
    selectedGap d T x u + sumMovedIn d S T x u =
      selectedGap d S x u + sumMovedOut d S T x u

theorem selected_balance_transport
    {R : Type*} [CommSemiring R] (d : ℕ) (S T : Finset ℕ) (x u : R) :
    selectedGap d S x u + selectedBody d S x u =
      selectedGap d T x u + selectedBody d T x u

theorem selectedBody_insert
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hnot : k ∉ S) :
    selectedBody d (insert k S) x u = selectedBody d S x u + selectedTerm d k x u

theorem selectedGap_insert
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hnot : k ∉ S) :
    selectedGap d S x u = selectedGap d (insert k S) x u + selectedTerm d k x u

theorem selectedBody_erase
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hmem : k ∈ S) :
    selectedBody d S x u = selectedBody d (S.erase k) x u + selectedTerm d k x u

theorem selectedGap_erase
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R)
    (hk : k ≤ d) (hmem : k ∈ S) :
    selectedGap d (S.erase k) x u = selectedGap d S x u + selectedTerm d k x u

theorem selected_insert_of_mem
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R) (hmem : k ∈ S) :
    selectedBody d (insert k S) x u = selectedBody d S x u ∧
      selectedGap d (insert k S) x u = selectedGap d S x u

theorem selected_insert_of_lt
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R) (hdk : d < k) :
    selectedBody d (insert k S) x u = selectedBody d S x u ∧
      selectedGap d (insert k S) x u = selectedGap d S x u

theorem selected_erase_of_lt
    {R : Type*} [CommSemiring R] (d k : ℕ) (S : Finset ℕ) (x u : R) (hdk : d < k) :
    selectedBody d (S.erase k) x u = selectedBody d S x u ∧
      selectedGap d (S.erase k) x u = selectedGap d S x u

theorem selectedBody_Ico_split_at
    {R : Type*} [CommSemiring R] (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d) :
    selectedBody d (Finset.Ico r (d + 1)) x u =
      x ^ r * (∑ k ∈ Finset.range (s - r),
        (Nat.choose d (r + k) : R) * x ^ k * u ^ (d - (r + k))) +
        selectedBody d (Finset.Ico s (d + 1)) x u

theorem selected_modEq_of_dvd_moved (d : ℕ) (S T : Finset ℕ) (x u m : ℕ)
    (hterms : ∀ k ∈ (activeSelectedIndices d T \ activeSelectedIndices d S) ∪
        (activeSelectedIndices d S \ activeSelectedIndices d T), m ∣ selectedTerm d k x u) :
    Nat.ModEq m (selectedBody d S x u) (selectedBody d T x u) ∧
      Nat.ModEq m (selectedGap d S x u) (selectedGap d T x u)
```

## Proof route and dependencies

The private helper `sum_selection_transport` partitions each finite set into
its difference and intersection. `Finset.disjoint_sdiff_inter`, `sum_union`,
and `sdiff_union_inter` give the two exact sums; `inter_comm` and associativity/
commutativity finish the additive accounting. It does not cancel an addend.

`selectedBody_transport` directly instantiates that helper on the existing
active sets. `selectedGap_transport` applies it to their complements within
`range (d+1)`. Bounded complement differences reverse the incoming/outgoing
sets. Membership extensionality proves those identities; no infinite complement
or unbounded input-set subtraction is used.

Single insertion uses the in-range active-set/filter identity and
`Finset.sum_insert`. Erasure adapts insertion with `Finset.insert_erase`.
Repeated insertion uses `insert_eq_of_mem`; out-of-range no-ops use filter
extensionality and the exclusion of the index from `range (d+1)`.

`selected_balance_transport` is an immediate adapter of the Step 001 balance
kernel. No second reconstruction proof is introduced. The interval adapter
uses `selectedBody_Ico`, `GTail_split_at`, `mul_add`, `pow_add` and
`r+(s-r)=s`. Increasing r removes Body layers, indexed by the power of x.
The normalized-layer sum in its statement is multiplied by `x^r` so its
absolute exponents remain `x^(r+k)`.

The generic modular endpoint first uses `Finset.dvd_sum` to prove divisibility
of both moved sums. It takes `% m` of the two semiring movement equalities and
uses `Nat.add_mod`, `Nat.mod_eq_zero_of_dvd` and `Nat.mod_mod` to remove their
zero residues. No positive-modulus assumption is necessary. At m=0 the guard
requires every moved term to be zero, and the resulting observations agree
as actual natural values. No universal gcd/content/valuation invariance is used.

Production imports are exactly the neutral `GTailFactor`, `GTailPascal`,
and `Mathlib.Data.Nat.ModEq`. Selection is imported through Factor. No FLT
owner or future theorem is a dependency.

## Regression evidence

The focused test checks:

- Degree-three insert of endpoint 0 and erase of interior index 1 over any
  CommSemiring; both Body and Gap equations use the correct transfer direction.
- Degree-five S={1,3}, T={2,3}: independently computed moved-in set `{2}` and
  moved-out set `{1}` produce incoming `10*x^2*u^3` and outgoing `5*x*u^4`.
  Both arbitrary movement identities are instantiated with these nonzero terms.
- Equal selections, empty/full balance and movement sums, repeated insertion,
  insertion/erasure of index 100 outside degree three, degree-zero insertion
  of index 0, and degree-zero no-op insertion of index 1.
- Zero x and zero u cases, where the transferred interior term vanishes.
- The interval adapter at d=3, r=1, s=2, removing `x*(3*u^2)` from Body.
- At degree seven, introducing the `u^7` endpoint changes coefficient gcd
  from 7 to 1 while both transfer identities and Big balance remain exact.
- Generic prime p, empty-to-interior selection: all moved coefficients are
  divisible by p, giving both modular congruences for arbitrary natural x,u.
- Degree-five movement with both entering and departing terms divisible by 5,
  and an explicit m=0 regression with vanishing movement terms.
- A failed guard and nonpreservation counterexample: d=7, x=u=1, interior S
  and T=insert 0 S. The moved term is 1, not divisible by 7. Body values are
  126 and 127 (residues 0 and 1); Gap values are 2 and 1 (residues 2 and 1).
  The negated congruences and failed divisor are checked by Lean `decide`.

The counterexamples do not refute any stated theorem: its explicit guard
fails. They expose coefficient-content change and modular nonpreservation
under an unguarded endpoint transfer. No degree-seven factorization is used.

## Validation commands, outputs and exit status

Working directory: `lean/dk_math`. Final successful runs:

```text
lake build DkMath.Lib.Cosmic.GTailTransport
ℹ [1067/1067] Built DkMath.Lib.Cosmic.GTailTransport (2.2s)
info: DkMath/Lib/Cosmic/GTailTransport.lean:11:0: file: DkMath.Lib.Cosmic.GTailTransport
Build completed successfully (1067 jobs).
exit 0

lake build DkMathTest.CosmicFormula.GTailTransport
ℹ [1068/1068] Built DkMathTest.CosmicFormula.GTailTransport (3.1s)
info: DkMathTest/CosmicFormula/GTailTransport.lean:10:0: file: DkMathTest.CosmicFormula.GTailTransport
Build completed successfully (1068 jobs).
exit 0

lake build DkMath.Lib.Cosmic.GTailFactor DkMathTest.CosmicFormula.GTailFactor
Build completed successfully (1063 jobs).
exit 0
```

All three final runs have no warnings/errors. The factor replay reports its
sixteen existing axiom checks again. These are focused incremental runs, not
a clean or full-workspace build. Initial elaboration issues were corrected by
membership case splits, propositional simplification after normalizing bounds,
explicit unfolding of the outgoing sum, and parentheses around test erase
applications. Temporary diagnostics and unused simp arguments were removed.
No contract was weakened or strengthened to bypass these issues.

The test contains `#print axioms` for every one of the twelve public endpoints.
The exact results are:

```text
'DkMath.CosmicFormula.selectedBody_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedGap_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selected_balance_transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedGap_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedGap_erase' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selected_insert_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selected_insert_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selected_erase_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selectedBody_Ico_split_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'DkMath.CosmicFormula.selected_modEq_of_dvd_moved' depends on axioms: [propext, Classical.choice, Quot.sound]

```

Only standard Lean foundations occur; no `sorryAx` or nonstandard extra axiom.

From repository root:

```text
rg -n '\b(sorry|admit|axiom|unsafe)\b|^import DkMath\.FLT\.' \
  lean/dk_math/DkMath/Lib/Cosmic/GTailTransport.lean \
  lean/dk_math/DkMathTest/CosmicFormula/GTailTransport.lean
(no matches; exit 1)

git diff --check
(no output; exit 0)
```

Both new Lean files were read back for review; a separate whitespace check
covers all four new files, since ordinary git diff checks do not include
untracked files. No unexpected source changes are present.

## Invariants, variable observations and research boundary

**Proved invariants:** exact Big balance for every selection; natural modular
observations under divisibility of every moved term. The generic modular
contract is complete, not a single-term fallback.

**Selection-dependent observations:** Body/Gap values, coefficient content,
active support and factor shape are not claimed to be universally preserved.
Endpoint insertion demonstrably changes coefficient gcd. No evaluated gcd,
valuation, divisibility, FLT-counterexample packet, or support invariant is
silently inferred from the additive balance.

**Research conjectures:** deriving an FLT7 obstruction, descent or closure
from transported conditions remains outside these finite identities. There is
no new arithmetic obstruction claimed. Outcome B records the reusable tool
and its guarded invariant; the negative examples demonstrate the intended
boundary rather than a failure of the implemented specification.

No specification repair was necessary. Steps 004–007, norm-square identities,
GTailSeven, FLT7 bridge, and façade promotion remain deferred. Work stops here.

# Source inventory 003 — before coding

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Initial working tree: clean. Paths are relative to `lean/dk_math`.
No AGENTS.md was found by the repository scan including hidden directories.

## Read prerequisites

Read `GTailSelection.lean`, `GTailFactor.lean`, canonical `GTail.lean` and
`GTailPascal.lean` under `DkMath/Lib/Cosmic`, the corresponding focused tests
under `DkMathTest/CosmicFormula`, reports 001/002, and reviews 001/002.
The reviews approve those bounded checkpoints and explicitly distinguish
invariant balance from selection-dependent coefficient gcd and factor shape.

Namespace: `DkMath.CosmicFormula`. Existing reusable contracts:

```lean
selectedTerm {R : Type*} [CommSemiring R] (d k : ℕ) (x u : R) : R
selectedBody {R : Type*} [CommSemiring R] (d : ℕ) (S : Finset ℕ) (x u : R) : R
selectedGap {R : Type*} [CommSemiring R] (d : ℕ) (S : Finset ℕ) (x u : R) : R
selectedGap_add_selectedBody {R : Type*} [CommSemiring R]
  (d : ℕ) (S : Finset ℕ) (x u : R) :
  (x+u)^d = selectedGap d S x u + selectedBody d S x u
selectedBody_Ico {R : Type*} [CommSemiring R]
  (d r : ℕ) (x u : R) (hr : r ≤ d) :
  selectedBody d (Finset.Ico r (d+1)) x u = x^r * GTail d r x u
activeSelectedIndices (d : ℕ) (S : Finset ℕ) : Finset ℕ
mem_activeSelectedIndices (d : ℕ) (S : Finset ℕ) (k : ℕ) :
  k ∈ activeSelectedIndices d S ↔ k ≤ d ∧ k ∈ S
coeffGCD (d : ℕ) (S : Finset ℕ) : ℕ
coeffGCD_prime_interior (p : ℕ) (hp : Nat.Prime p) :
  coeffGCD p (Finset.Ico 1 p) = p
coeffGCD_eq_one_of_zero_mem (d : ℕ) (S : Finset ℕ) (hzero : 0 ∈ S) :
  coeffGCD d S = 1
GTail_split_at {R : Type _} [CommSemiring R]
  (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d) :
  GTail d r x u =
    (∑ k ∈ Finset.range (s-r),
      (Nat.choose d (r+k) : R)*x^k*u^(d-(r+k))) + x^(s-r)*GTail d s x u
```

Body uses the active filter; Gap its opposite filter within `range (d+1)`.
`selectedBody_complement` / `selectedGap_complement` already swap these.
`GTail` removes prefixes indexed by powers of x. No new balance definition,
GTail family, factor/gcd claim, or numerical subtraction is needed.

## Mathlib finite-set and sum audit

`Algebra/BigOperators/Group/Finset/Basic.lean` generates additive declarations
from the multiplicative versions via `to_additive`. For an additive commutative
monoid, `f : ι → M` and finite sets A,B (DecidableEq ι):

- `Finset.sum_union (h : Disjoint A B)`:
  `∑ k ∈ A ∪ B, f k = (∑ k ∈ A, f k) + ∑ k ∈ B, f k`.
- `Finset.sum_sdiff (h : A ⊆ B)`:
  `(∑ k ∈ B \ A, f k) + ∑ k ∈ A, f k = ∑ k ∈ B, f k`.
  The union/intersection partition is preferable here and needs no subtraction.
- `Finset.sum_filter_add_sum_filter_not (s : Finset ι) (p : ι → Prop)
  [DecidablePred p] [∀ k, Decidable (¬ p k)] (f : ι → M)`:
  `(∑ k ∈ s.filter p, f k) + ∑ k ∈ s.filter (fun k => ¬ p k), f k = ∑ k ∈ s, f k`.
- `Finset.sum_insert (ha : a ∉ s)`:
  `∑ k ∈ insert a s, f k = f a + ∑ k ∈ s, f k`.

Set partitions inspected in `Data/Finset/Basic.lean` and `SDiff.lean`:
`Finset.disjoint_sdiff_inter (A B) : Disjoint (A \ B) (A ∩ B)`;
`Finset.sdiff_union_inter (A B) : A \ B ∪ A ∩ B = A`.
Membership extensionality proves active insertion/erasure and the bounded
complement difference identities. `insert_erase` and `insert_eq_of_mem`
provide the symmetric erase and repeated-insert cases.

## Natural modular audit

`Data/Nat/ModEq.lean` defines `Nat.ModEq m a b` as equality of residues.
`Nat.modEq_zero_iff_dvd : Nat.ModEq m a 0 ↔ m ∣ a`.
`Nat.ModEq.add_right_cancel` takes congruent added terms and a congruence of
sums; it requires no positive-modulus hypothesis. Alternatively congruence of
movement equalities under `fun n => n % m`, `Nat.add_mod`, and
`Nat.mod_eq_zero_of_dvd` directly remove divisible movement sums.
`Finset.dvd_sum` supplies divisibility of the sums from each moved term.

## Planned additions

Direct imports: `GTailFactor` (which imports selection), `GTailPascal`, and
Mathlib's natural modular API. Define only `sumMovedIn` and `sumMovedOut`,
using the two differences of existing active sets. A private common-part
partition helper will establish the movement identities without cancellation.

Public contracts: single insert/erase, repeated insert and out-of-range
insert/erase no-ops, arbitrary Body/Gap movement, Big balance adapter,
interval-to-GTail split adapter, and the generic natural modular conjunction
under divisibility of every index in the union of the moved active sets.
Regression will demonstrate changed coefficient gcd and failed congruence
when the moved endpoint is not divisible by the modulus. Step 004 onward
and façade promotion remain outside this instruction.

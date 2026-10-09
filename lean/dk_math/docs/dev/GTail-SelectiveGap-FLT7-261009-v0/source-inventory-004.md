# Source inventory 004 — before implementation

Date: 2026-10-09. Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Initial working tree: clean. Paths below are relative to `lean/dk_math`.
Repository scan, including hidden directories, found no AGENTS.md.

## Read and reused APIs

Read sources and focused tests for `GTailSelection`, `GTailFactor`,
`GTailTransport`, canonical `GTail` / `GTailPascal`, and review 003's approved
boundary. The previous turns' reviewed contracts remain unchanged.
Namespace below is `DkMath.CosmicFormula`. Semiring APIs have implicit
`{R : Type*} [CommSemiring R]` unless shown otherwise.

```lean
GTail (d r : ℕ) (x u : R) : R
-- ∑ k ∈ range (d+1-r), (choose d (r+k) : R)*x^k*u^(d-(r+k))
GTail_rec (d r : ℕ) (x u : R) (hr : r < d) :
  GTail d r x u = (Nat.choose d r : R)*u^(d-r) + x*GTail d (r+1) x u
GTail_self_eq_one (d : ℕ) (x u : R) : GTail d d x u = 1
GTail_split_at (d r s : ℕ) (x u : R) (hrs : r ≤ s) (hsd : s ≤ d) :
  GTail d r x u =
    (∑ k ∈ Finset.range (s-r),
      (Nat.choose d (r+k) : R)*x^k*u^(d-(r+k))) + x^(s-r)*GTail d s x u
selectedGap_add_selectedBody (d : ℕ) (S : Finset ℕ) (x u : R) :
  (x+u)^d = selectedGap d S x u + selectedBody d S x u
selectedBody_Ico (d r : ℕ) (x u : R) (hr : r ≤ d) :
  selectedBody d (Finset.Ico r (d+1)) x u = x^r*GTail d r x u
selectedBody_eq_monomial_mul_residual
  (d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R)
  (_hij : i ≤ j) (hjd : j ≤ d)
  (hbounds : ∀ k ∈ activeSelectedIndices d S, i ≤ k ∧ k ≤ j) :
  selectedBody d S x u = x^i*u^(d-j)*selectedResidual d S i j x u
selectedBody_insert (d k : ℕ) (S : Finset ℕ) (x u : R)
  (hk : k ≤ d) (hnot : k ∉ S) :
  selectedBody d (insert k S) x u = selectedBody d S x u + selectedTerm d k x u
selectedGap_insert (d k : ℕ) (S : Finset ℕ) (x u : R)
  (hk : k ≤ d) (hnot : k ∉ S) :
  selectedGap d S x u = selectedGap d (insert k S) x u + selectedTerm d k x u
selected_balance_transport (d : ℕ) (S T : Finset ℕ) (x u : R) :
  selectedGap d S x u + selectedBody d S x u =
    selectedGap d T x u + selectedBody d T x u
```

Factor's existing `activeSelectedIndices (d : ℕ) (S : Finset ℕ) : Finset ℕ`
is the range-filter intersection; `selectedResidual` has the same semiring
carrier and explicit `(d : ℕ) (S : Finset ℕ) (i j : ℕ) (x u : R)` arguments.
Existing natural content/divisor contracts:

```lean
coeffGCD (d : ℕ) (S : Finset ℕ) : ℕ
coeffGCD_prime_interior (p : ℕ) (hp : Nat.Prime p) :
  coeffGCD p (Finset.Ico 1 p) = p
coeffGCD_eq_one_of_zero_mem (d : ℕ) (S : Finset ℕ) (hzero : 0 ∈ S) :
  coeffGCD d S = 1
prime_mul_coords_dvd_selectedBody_interior (p x u : ℕ) (hp : Nat.Prime p) :
  p*x*u ∣ selectedBody p (Finset.Ico 1 p) x u
```

## Degree-seven and norm overlap audit

Searches of Lean sources for `GTail 7 5`, `GTail 7 6`, and the square of
`x^2+x*u+u^2` found no matching existing production calibration endpoint.
Step 001 tests already list the six interior degree-seven terms. Step 003
tests already specialize insertion and content change at degree seven; the new
observation will additionally expose the calibrated Body factor through those
transport lemmas. No duplicate selection, factor, or transport kernel is needed.

Inspected `DkMath/FLT/Seven/CubicSecondCoordinateSplit.lean`:
`seventhPowerSndCore_factor (u v : ℤ)` factors a TraceOne seventh-power second
coordinate into two *cubic* polynomials. It is not the binomial interior identity.
It and related FLT owners are not imported or edited.

Actual norm APIs inspected (not dependencies of the new module):

- `DkMath.NumberTheory.TraceOneQuadratic.norm {s : ℤ}
  (x : TraceOneInt s) : ℤ := x.fst^2+x.fst*x.snd-s*x.snd^2`.
- `DkMath.NumberTheory.TraceOneQuadratic.traceOneNorm_neg_one (a b : ℤ)`:
  `norm (⟨a,b⟩ : TraceOneInt (-1)) = a^2+a*b+b^2`.
- `DkMath.Lib.NumberTheory.EisensteinCoordinates.lean`:
  `eisensteinCoord (m n : ℤ) : TraceOneInt (-1) := ⟨m,-n⟩`;
  `norm_eisensteinCoord (m n : ℤ)` gives `norm (eisensteinCoord m n) = m^2-m*n+n^2`.

The signs and carriers are explicit. A general CommSemiring polynomial is not
identified with either norm map; no new arithmetic carrier/map is built here.
The optional quadratic identity will be a semiring polynomial calibration only.

## Planned new interfaces

Direct import `GTailTransport`; narrow tactic imports for finite numerical
coefficient evaluation and the small residual polynomial identity. Keep the
quadratic expression explicit, with no new norm or duplicate helper definition.

Add named r=6/r=5 GTail evaluations and selected Body adapters; interior Gap,
monomial-residual, coefficient gcd and natural divisor adapters; residual square,
Body factor, semiring Big reconstruction, and a separately typed CommRing
subtraction reading. A public endpoint-insertion observation will combine the
new factor with existing Body/Gap transport, plus the content-change adapter.

Use ring normalization only on the evaluated finite residual and small algebraic
rearrangements. Tests will independently expand the degree-seven identity and
compare exact sides at (1,1), (2,3), and (3,2), as well as zero coordinates.
Step 005 onward, genuine norm maps, FLT7 hypotheses and façade promotion remain
deferred.

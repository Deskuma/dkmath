# CFZP-0068A / CFZP-040 correction

## close the Abel sum -> raw prime cell -> CFZP-039 period-cell chain

Working branch:

`wip/RH-CFBRC-cosmic-formula-zeta-projection-260815-v0`

CFZP-040 review result: Green-B, one finite API closure gap.

The current module already closes:

```text
cfzp040PrimeCarrierSumIoc_eq_abel
cfzp040RawPrimeCarrierCellSupport
cfzp040RawPrimeCarrierCellMass
cfzp040RawPrimeCarrierCellMass_eq_cfzp039CellMass
cfzp040PrimeCarrierSumIoc_eq_smooth_add_discrepancy
```

However the direct equality between `cfzp040PrimeCarrierSumIoc` at the exponential cell endpoints and `cfzp040RawPrimeCarrierCellMass` is missing.  Without it, the theorem-level chain

```text
finite Abel expression
  -> cfzp040PrimeCarrierSumIoc
  -> cfzp040RawPrimeCarrierCellMass
  -> cfzp039PrimeAxisLeadingCarrierCellMass
```

is not yet closed.

This correction stays inside CFZP-040. Do not start CFZP-041 yet.

---

## 1. Required exact raw-cell equality

Add a theorem of the following shape (name may vary slightly):

```lean
theorem cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_rawCellMass
    (ε : ℝ) (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ) :
    cfzp040PrimeCarrierSumIoc ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp040RawPrimeCarrierCellMass ε W c n := by
  ...
```

No prime-distribution or analytic hypothesis should be needed.

The proof is purely finite:

1. unfold `cfzp040PrimeCarrierSumIoc`, `cfzp040RawPrimeCarrierCellMass`, and `cfzp040RawPrimeCarrierCellSupport`;
2. both sides use the same `Finset.Ioc` natural endpoint block;
3. convert the prime filter into `cfzp040PrimeIndicator` (`if Nat.Prime k then 1 else 0`);
4. for prime terms use the exact specialization
   `cfzp040PrimeAxisCarrierTestFunction_natPrime` or unfold the definitions;
5. nonprime terms vanish.

Prefer `Finset.sum_filter`, `Finset.sum_congr`, and a `by_cases hp : Nat.Prime p`; do not introduce a new support predicate.

---

## 2. Required composed CFZP-039 cell equality

Compose the theorem above with the already-closed

```text
cfzp040RawPrimeCarrierCellMass_eq_cfzp039CellMass
```

to expose the actual bridge used by the next stage:

```lean
theorem cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_cfzp039CellMass
    {ε : ℝ} (hε : 0 < ε)
    (W : PascalCenteredXiResidueTransportWindow)
    (c : ℝ) (n : ℕ)
    (hcell : max (3 * ε) 1 ≤ cfzp039CarrierCellLeft W c n) :
    cfzp040PrimeCarrierSumIoc ε W
        (cfzp040CarrierCellExpLeft W c n)
        (cfzp040CarrierCellExpRight W c n) =
      cfzp039PrimeAxisLeadingCarrierCellMass ε W c n
        (cfzp040CarrierCellNaturalLeft W c n)
        (cfzp040CarrierCellNaturalRight W c n) := by
  ...
```

This is the main correction target.

---

## 3. Preferred direct Abel specialization

If short and stable, also expose a theorem taking the existing differentiability/integrability hypotheses and returning the Abel formula directly for the CFZP-039 period-cell mass.

Use:

```text
cfzp040CarrierCellExpLeft_pos
cfzp040CarrierCellExpLeft_lt_right
cfzp040PrimeCarrierSumIoc_eq_abel
cfzp040PrimeCarrierSumIoc_cellEndpoints_eq_cfzp039CellMass
```

The result should identify

```text
cfzp039PrimeAxisLeadingCarrierCellMass ...
```

with the finite Abel endpoint-minus-integral expression on `[ExpLeft, ExpRight]` / `Ioc ExpLeft ExpRight`.

This direct theorem is strongly preferred because CFZP-041 should consume the 039 cell mass without manually replaying two adapter rewrites.

---

## 4. Roadmap

Amend the CFZP-040 roadmap entry with one line such as:

```text
Abel prime sum -> raw prime cell -> CFZP-039 carrier cell: CLOSED
```

Do not change the existing OPEN/GAP status for PNT, discrepancy decay, density-integral reduction, exceptional/higher-power residual elimination, or global RH.

---

## 5. Firewall

Do not add:

- PNT / Mertens / Dirichlet / Bertrand;
- infinite prime sums;
- summability or limit exchange;
- automatic `σ < 1`;
- exceptional or higher-power residual elimination;
- CFZP-018 provider;
- RH.

This is only a finite theorem-API closure correction.

# FLT7-015R implementation report

## Outcome

Outcome A. Prime-address uniqueness and exact valuation isolation are complete
on the corrected, specialized `AwayCubicRoutingPacket` surface.

The generic counterexample from FLT7-015 remains valid and is preserved in
`report-flt7-015.md`. No generic uniqueness theorem for
`CoprimeTripleRouting` was introduced.

## Specialized repair

The endpoint accessors expose pairwise coprimality of `y`, `z`, and `y+z` from
`r.cubic.endpointTriple`. The root-column accessors expose pairwise
coprimality of `7*vPart`, `leftPart`, and `rightPart`; the two facts involving
`7*vPart` reuse nondivisibility of the cubic parts by seven and the existing
root-triple coprimality.

The natural selectors `endpointRoutingFactorNat` and
`rootRoutingFactorNat`, together with their cell-divisibility theorems, retain
the routing grid's outer provenance.

## Address theorem surface

The specialized uniqueness chain is:

- `AwayCubicRoutingPacket.row_eq_of_prime_dvd_cells`;
- `AwayCubicRoutingPacket.column_eq_of_prime_dvd_cells`;
- `AwayCubicRoutingPacket.prime_address_unique`.

If a prime divides two cells, the cells divide their respective outer row and
column factors. Distinct rows or columns would therefore make the prime divide
two members of a pairwise-coprime outer triple, forcing the prime to equal one.

`AwayRoutingPrimeAddress` packages the prime, its row and column, divisibility,
and specialized uniqueness. A nontrivial cell produces such an address through
`nonempty_awayRoutingPrimeAddress_of_cell_ne_one`.
The accessors `not_dvd_other_column` and `not_dvd_other_row` explicitly exclude
the prime from the other cells in its addressed row and column.

## Exact valuation isolation

For every specialized address:

```text
v_q(cell) = v_q(endpoint row factor),
v_q(cell) = v_q(root column factor).
```

These are the theorems
`AwayRoutingPrimeAddress.cell_depth_eq_endpoint_depth` and
`AwayRoutingPrimeAddress.cell_depth_eq_root_depth`. The proofs expand the
appropriate row or column product and use internal cell coprimality to show
the other two factors have valuation zero. Positivity of the endpoint triple
proves all nine routing cells are nonzero.

`AwayRoutingPrimeDepthPacket` records the exact positive exponent together
with both depth equalities. `AwayRoutingPrimeAddress.toDepthPacket` constructs
it without selecting another prime or address.

## Generic counterexample regression

The focused test permanently constructs the FLT7-015 diagonal grid
`c11=2,c22=2,others=1` as a valid
`CoprimeTripleRouting 2 2 1 2 2 1`, and checks that `2` divides both diagonal
cells. This prevents accidental reintroduction of the false generic theorem.

## Scope

FLT7-014 and the FLT7-015 counterexample report are unchanged. This repair does
not construct `ZMod (q^e)` solutions, global signed reconstruction, recursive
descent, or an FLT7 contradiction.

## Verification

The specialized module, focused regression tests, facade, and full
`DkMath.FLT` target passed. Axiom audits for the public address and valuation
surface report only Lean/Mathlib foundations (`propext`, `Classical.choice`,
and `Quot.sound`). No `sorry`, `admit`, custom axiom, or `native_decide` was
introduced.

## Recommended next boundary

Resume the finite prime-power audit only through
`AwayRoutingPrimeDepthPacket`. Reduce the actual endpoint, root, and
first-coordinate integers modulo `q^exponent`, prove unit and homogeneous
Bezout facts there, and classify the resulting full-depth solution families.
Do not generalize the address theorem back to arbitrary routing grids.

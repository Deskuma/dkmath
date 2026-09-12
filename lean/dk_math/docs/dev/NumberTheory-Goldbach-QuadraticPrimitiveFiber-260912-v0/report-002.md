# QP-002 — separated supports and exact removal

Predecessor: QP-001 commit `fb098d0b3`.

`center_divisor_absent` is stronger than the prime candidate: any `r>1` with
`r∣n` is absent from both raw endpoint supports if `u≤n` and `Coprime n u`.
Primality is unnecessary. `two_absent` needs only bounded subtraction and
opposite coordinate parity. Thus all center prime divisors and two may be
removed from the cutoff on the primitive-parity fiber.

`leftSupport` / `rightSupport` retain the **proper** endpoint exceptions.
`support_union` is exactly the production `goldbachObstructionSupport`.
`support_disjoint_of_coprime` requires only coprime endpoints, not prime
endpoints, admissibility, or positive offset. Within the bounded primitive
regime `shared_support_eq_two` proves any shared prime is two, and
`support_disjoint_iff_not_shared_two` gives the exact condition, weaker than
opposite parity because endpoint two is not a proper obstruction.
`primitive_support_disjoint` is the requested fiber specialization.

`reducedWorld` removes two and center divisors.
`survives_reduced_iff` proves pointwise equality of the reduced-world and
original proper survival conditions on every retained seat. Removing those
directions does not furnish additional survivors on that seat.

## Counterexamples and numerical evidence

The standard-library Python script reproduces production range `0≤u<n-1` and
inclusive cutoff `r*r≤2*n`, recording raw/proper supports, intersections,
endpoint exceptions, exact set counts and rational densities. The snapshot
`numeric/qp-002-snapshot.json` records centers 0..500 and selected seat details.
Minima are lexicographic within that exhaustive range.

- Primitive without parity: reflected gcd failure first at `(3,1)`; proper
  intersection failure first at `(5,1)` with endpoints 4,6 and shared two.
- Opposite parity without primitive: shared odd proper factor first at `(9,0)`
  (diagonal 9,9); the positive version has example `(12,3)` (9,15).
- Raw support differs from proper support even on the normalized fiber, first
  at `(5,2)` (3,7). Removing center factors/two does not remove this exception.
- Higher support multiplicity persists: primitive first `(13,7)` (6,20),
  primitive-parity first `(31,4)` (27,35), support `{3,5,7}`. These are scan
  findings here; QP-003 adds a kernel regression for the latter.
- Outside bounded subtraction the earliest scanned boundary failure is `(0,1)`.
  QP-001's `(1,2)` is a valid illustrative counterexample, not the minimum.

All correctly qualified coordinate, gcd, positive-pair, center-factor, two,
support-separation and reduced-support checks had no failures in this range.
Exact numerical survivor accounting includes a separate prime-center diagonal.
No universal density conclusion follows from the finite scan.

Executed from `lean/dk_math`:

```bash
lake build DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra
python3 docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/goldbach_quadratic_primitive.py --max-center 500 --json docs/dev/NumberTheory-Goldbach-QuadraticPrimitiveFiber-260912-v0/numeric/qp-002-snapshot.json
```

Both final commands exited 0; focused build 8692 jobs, scratch 7.2 seconds.
The first build exposed opaque reduction in three finite `decide` examples;
`decide +kernel` closed these without changing the propositions. Universal
lemmas had compiled on the first attempt. Production files remain unchanged.

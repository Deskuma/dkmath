# QP-001 — quadratic boundary and exact hypotheses

Predecessor: QP-000 commit `7014733c2`. Scratch namespace throughout:
`DkMathTest.GoldbachQuadraticPrimitiveAstra`.

Kernel-checked `coordinate_coprime` is a direct Mathlib wrapper requiring `u≤n`;
`right_coordinate_coprime` needs no bound. `quadratic_tail` evaluates canonical
GTail and `quadratic_boundary` uses `gcd_GN_eq_gcd_of_one_le` to obtain
`gcd(n-u,n+u)=gcd(n-u,2)`. No prime hypothesis is needed.

The strongest parity conclusion under these assumptions is an equivalence:
`endpoints_coprime_iff` says coprime endpoints iff `n%2 ≠ u%2`.
`parity_iff_odd_left` identifies this with oddness of the left endpoint.
Thus the boundary is a specialization and the parity step is an exact
normalization, not an extra Goldbach existence theorem.

`positive_pair_primitive` proves that **positivity of u and primality of both
endpoints suffice**, without a separately supplied admissibility assumption.
Primality of `n-u` implies the required bound; the endpoints are distinct
primes. Their common coordinate gcd divides their gcd, which is one.
`positive_pair_parity` follows from the same coprime endpoints.

`diagonal_pair` and `pair_of_center_prime` isolate the omitted diagonal.
A naive primitive-only replacement is false already at center 2: its only
prime pair has offset zero and `Coprime 2 0` is false. Any exact criterion must
retain the center-prime disjunct. The ordinary statement does not require a
positive offset at prime centers.

Scratch definitions `primitiveOffsets`, `primitivePositiveOffsets`,
`primitiveParityOffsets` have exact `mem_...` theorems. The last includes
positivity explicitly. For admissible n≥2, primitive membership itself rules
out zero; keeping the positive filter makes the intended search explicit.

Regression examples use kernel `decide`:

- `(n,u)=(3,1)`: primitive, but reflected gcd is 2 (smallest positive admissible
  primitive failure when parity is omitted).
- `(1,2)`: primitive/opposite parity, but unbounded natural subtraction breaks
  the claimed boundary equality.
- Centers 0,1,2 have empty primitive-parity fiber; center 2 still has a pair.
- `(1,0)` satisfies the bounded primitive gcd conclusion; `(0,0)` is not primitive.

Validation executed from `lean/dk_math`:
`lake build DkMathTest.NumberTheory.GoldbachQuadraticPrimitiveAstra` — exit 0,
8692 jobs, scratch built in 4.9 seconds. No scratch warnings.
API reconnaissance also used a temporary `#check` file; one guessed name
`Nat.dvd_sub'` did not exist, and the actual proof uses `Nat.dvd_sub`.
Numerical enumeration is introduced in QP-002; no finite scan is claimed here.

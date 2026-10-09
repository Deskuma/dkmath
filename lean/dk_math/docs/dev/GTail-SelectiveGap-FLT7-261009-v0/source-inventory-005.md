# Source inventory 005

Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`. Initial worktree clean.
`review-004.md`: APPROVED / Outcome B; report-004 and earlier approvals present.
No existing GTailBridge owner was found.

## Exact contracts and route

- `DkMath.CosmicFormula.add_pow_eq_mul_GTail_one_add_gap {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : (x+u)^d = x * GTail d 1 x u + u^d`.
- `DkMath.CosmicFormula.add_pow_seven_eq_gap_add_interior {R : Type*} [CommSemiring R] (x u : R) : (x+u)^7 = (u^7+x^7) + 7*x*u*(x+u)*(x^2+x*u+u^2)^2`.
  Its proof uses selectedGap_add_selectedBody, selected Gap and Body; Body uses the general active-index factor and finite residual evaluation from Steps 001–004.
- `DkMath.FLT.Seven.Fermat7Equation (x y z : ℕ) : Prop := x^7+y^7=z^7`.
- `CounterexamplePack (x y z : ℕ) : Prop` has hx,hy,hz positivity, hxy : Nat.Coprime x y, hEq : Fermat7Equation x y z.
- Basic's `right_lt_of_fermat7Equation {x y z : ℕ} (hx : 0<x) (hEq : Fermat7Equation x y z) : y<z` and `gap_pos_of_fermat7Equation ... : 0<z-y` concern z-y, not the proposed a+b-c focus. They are not needed.
- Existing PrimitiveCoordinateCoprime / QuadraticCoprimeFactor owners were searched; their carrier/coprime APIs are unnecessary and will not be imported. No Boundary.lean or Gap.lean owner exists under those literal names.

## Imports and anticycle audit

Only direct imports: `DkMath.Lib.Cosmic.GTailSeven` and `DkMath.FLT.Seven.Basic`.
The local DkMath import closure is exactly Basic, GTail, GTailSelection, GTailFactor, GTailPascal, GTailTransport, GTailSeven. None imports another FLT owner. Basic imports broad Mathlib; this existing dependency is retained, without editing Basic.
A recursive source import audit and search for Fermat/contradiction endpoints is recorded in report-005. Mathlib reachability is distinct from proof use: the new proof explicitly uses the two algebraic balances, associativity/commutativity, the equation field and natural addition cancellation only.
No DkMath.FLT.Seven facade, FLT.Three or FLT.Five import is intended. No closure theorem or contradiction eliminator is used. The ring defect is optional and derived from the same shell. Height/focus targets are deferred to Step 006.

Recursive audit includes `public import` and `private import`: 8833 reachable module names; the seven local DkMath modules above are the entire local closure. Basic's Mathlib import reaches Mathlib.NumberTheory.FLT.Basic/Four/Three/Polynomial/MasonStothers. These include exponent-three/four results and polynomial Fermat results, not a natural exponent-seven endpoint. Explicit search of installed Mathlib sources for `FermatLastTheoremFor 7|fermatLastTheoremSeven|fermatLastTheorem_seven` returned no matches (exit 1). This lexical audit is not a proof that no alternative spelling exists; the explicit proof route is the noncircularity evidence.

Nearest existing FLT tests use flat `DkMathTest/FLT/Seven*.lean` names. This step follows the explicitly required new nested path `DkMathTest/FLT/Seven/GTailBridge.lean`, covered by the existing DkMathTest.+ Lake glob.

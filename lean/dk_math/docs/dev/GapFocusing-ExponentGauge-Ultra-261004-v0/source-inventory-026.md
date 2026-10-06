# Source inventory 026

The checkout is clean on research/GapFocusing-ExponentGauge-Ultra-261004-v0. Read report-025.md and instruction-026.md before production edits.

## Existing DkMath APIs

- Legendre.GnomonPascalCell exports the strict square shell, shell prime birth mass, its positivity criterion, the exact cell log split, and the conditional old-budget frontier. Preserve these definitions and the n>=3 cell ledger boundary.
- PascalPrebirthBirth exports prime_prebirth_birth_packet, prime_power_resynchronization_packet, pascalPrimePowerLogGauge_eq and prime-only birth mass identities. Reuse these for a shell higher-event packet.
- PascalPrebirthBoundary classifies common support and common gcd. BinomialPrimePower supplies prime-power prebirth and whole-row divisibility, not genuine birth at every positive exponent.
- PrimitiveSet.VonMangoldtShadow is a witness-based finite log cost on PrimePowerLabel and channels. It deliberately distinguishes that finite shadow from the classical arithmetic function.
- RH.CFBRC.PascalPrimePowerCanonicalFold constructs a canonical prime-power witness and shadow cost. RH.CFBRC.PascalVonMangoldtLSeriesBridge proves its cost equal to ArithmeticFunction.vonMangoldt and connects finite Dirichlet sums and L-series. Those high-level RH imports are unnecessary for foundational shell arithmetic. No RH production dependency will be introduced.

## Installed Mathlib

- ArithmeticFunction.vonMangoldt_apply returns log(minFac q) at IsPrimePow q and zero otherwise. vonMangoldt_apply_pow requires a nonzero exponent. vonMangoldt_apply_prime gives log p. vonMangoldt_eq_zero_iff identifies the non-prime-power case. Nonnegativity and positivity are already available.
- isPrimePow_nat_iff exposes a prime base and positive exponent. isPrimePow_nat_iff_bounded_log_minFac supplies an existing finite exponent representation. IsPrimePow.minFac_pow_factorization_eq gives the canonical power equality. Nat.Prime.pow_minFac fixes the base of a positive prime power.
- Chebyshev.psi and theta take real arguments. psi_eq_sum_Icc and theta_eq_sum_Icc use the natural floor; at natural endpoints the floor reduces exactly. theta_eq_sum_primesLE_log uses the finite prime carrier Nat.primesLE.
- Chebyshev.sum_PrimePow_eq_sum_sum and psi_eq_sum_theta supply global exponent decompositions, using real root cutoffs. A shell-local natural exponent carrier avoids introducing real roots.
- Chebyshev.theta_le_log4_mul_x is a global linear upper bound. psi_sub_theta_le_mul_sqrt gives an existential global square-root constant. psi_le_const_mul_self gives a global linear psi bound. These cannot be subtracted as unrelated upper bounds to obtain a sharp short-shell increment estimate.
- pow_add_mul_le_add_pow provides the finite derivative lower bound for consecutive powers in an ordered semiring. This is the candidate fixed-exponent gap bridge, to be accepted only after Lean verification.
- Nat.le_log_of_pow_le is the existing base-two exponent cutoff API. No new logarithm theory is needed.

## Planned dependency surface

SquareShellPrimePower will own natural square-shell arithmetic and event carriers. SquareShellVonMangoldt will own the exact arithmetic-function split and Chebyshev shell identities. SquareShellPrimePowerGauge will own canonical log weights, injections, correction bounds and conditional consumers. All stay under the Legendre namespace and use Mathlib directly. Existing Basic is left unchanged to keep the generic square-shell extension local.

Fixed-exponent uniqueness and the stronger event-count bound are experimental acceptance targets until the proofs compile. The remaining shell von Mangoldt lower bound must remain an explicit hypothesis.

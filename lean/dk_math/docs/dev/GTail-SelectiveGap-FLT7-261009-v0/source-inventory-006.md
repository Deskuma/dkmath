# Source inventory 006 — arithmetic receiver and frontier

Date 2026-10-09; branch feature/GTail-SelectiveGap-FLT7-261009-v0; initial worktree clean. Review 005 APPROVED Outcome B, with no repair. Reports 001–005 and selection/factor/transport contracts inspected. No existing requested owner/arithmetic module found.

## Exact interfaces inspected

- `gtail_seven_shell {R : Type*} [CommSemiring R] (a b c g : R) (hsum : a+b=c+g) : g*GTail 7 1 g c+c^7=(a^7+b^7)+7*a*b*(a+b)*(a^2+a*b+b^2)^2`.
- `gtail_seven_eq_of_fermat7Equation {a b c g : ℕ} (hEq : Fermat7Equation a b c) (hsum : a+b=c+g) : g*GTail 7 1 g c=7*a*b*(a+b)*(a^2+a*b+b^2)^2`.
- `Fermat7Equation (a b c : ℕ) := a^7+b^7=c^7`; `CounterexamplePack` has hx,hy,hz : positive coordinates, hxy : Nat.Coprime a b, hEq.
- `right_lt_of_fermat7Equation {x y z : ℕ} (hx : 0<x) (hEq : Fermat7Equation x y z) : y<z` (Basic). Symmetry supplies the other coordinate bound.
- `add_pow_seven_eq_gap_add_interior {R : Type*} [CommSemiring R] (x u : R) : (x+u)^7=(u^7+x^7)+7*x*u*(x+u)*(x^2+x*u+u^2)^2` (GTailSeven). It uses selected balance, active factor, finite residual; its transport families do not assert gcd preservation.
- `prime_dvd_GN_iff_dvd_gap {p g u : ℕ} (hp : Nat.Prime p) : p ∣ GTail p 1 g u ↔ p ∣ g` (GTailCongruence); no endpoint coprimality needed.
- `GN_modEq_head_mod_sq_of_odd_prime_dvd_x {p : ℕ} (x u : ℕ) (hp : Nat.Prime p) (hp3 : 3≤p) (hpx : p∣x) : GTail p 1 x u ≡ p*u^(p-1) [MOD p^2]`.
- `gcd_GN_eq_gcd_of_one_le {d g u : ℕ} (hd : 1≤d) (hcop : Nat.Coprime g u) : Nat.gcd g (GTail d 1 g u)=Nat.gcd g d` (GTailBoundary).
- `not_prime_sq_dvd_GN_of_dvd_gap {p g u : ℕ} (hp : Nat.Prime p) (hp3 : 3≤p) (hcop : Nat.Coprime g u) (hpg : p∣g) : ¬p^2∣GTail p 1 g u` and `padicValNat_GN_prime_eq_one_of_dvd_gap` with the same inputs and valuation=1 (GTailPadic). The proposed no-second-layer lemma replaces full coprimality by explicit ¬7∣c and does not import this p-adic owner.
- `coprime_y_z_of_counterexamplePack {x y z : ℕ} (hPack : CounterexamplePack x y z) : Nat.Coprime y z` and `coprime_gap_y_of_counterexamplePack ... : Nat.Coprime (z-y) y` (CounterexampleRouting). The gap is z-y, not x+y-z; these cannot be transferred blindly.
- `fermat7Equation_modSeven_linear {x y z : ℕ} (hEq : Fermat7Equation x y z) : (x : ModSeven)+(y : ModSeven)=(z : ModSeven)` (ModSevenSectors). Thus proposed 7∣focused gap is known, new route only.
- `AwayDescentClosureProvider (x y z : ℕ) (p : AwayValuationTransferPacket x y z) : Type` fields nextX,nextY,nextZ,nextPack,nextRoute,carrier_match : nextRoute.carrier=Int.natAbs p.normal.root.snd (DescentClosureAudit). No provider will be introduced.
- `traceOneNorm_neg_one (a b : ℤ) : norm (⟨a,b⟩ : TraceOneInt (-1))=a^2+a*b+b^2`; `norm_eisensteinCoord (m n : ℤ) : norm (eisensteinCoord m n)=m^2-m*n+n^2` where eisensteinCoord m n=⟨m,-n⟩. Existing Eisenstein square coefficient coprimality is a Bezout/coordinate statement, not the proposed Nat factor coprimality.

## Candidate overlap map

| Candidate | Classification before implementation | Existing comparison |
| --- | --- | --- |
| max(a,b)<c | already available coordinate-wise | Basic.right_lt, symmetry |
| c<a+b; focused positive smaller gap | new packaging/route to known height fact | selected interior positivity and strict-power comparison |
| 7∣g | new route to known fact | ModSevenSectors linear residue |
| Coprime a Q, b Q, (a+b) Q, (a*b*(a+b)) Q | neutral general-purpose packaging; exact endpoints not found | Nat coprime/add/mul APIs; Eisenstein coordinate lemmas differ |
| 7∣tail and ¬49∣tail from 7∣g, ¬7∣c | new weaker-premise receiver for known residual fact | GTailCongruence + GTailPadic exact layer |
| Coprime g c / g Q from coprime a b and coordinate relation | failed hypothesis | concrete counterexamples to be kernel checked |
| separate square allocation from product | unproved without split data | no factor witness should be supplied |
| smaller next counterexample | unproved reconstruction | AwayDescentClosureProvider and unit/root normalization |

Searches covered exact Q spellings and quadratic/coprime names in repository Lean sources, plus EisensteinCoordinates and TraceOneQuadratic. SevenRealCubicSimplestCubicCertificate has an integer sourcePlaneNormSevenQuadratic definition, not these Nat coprime endpoints; no new Q definition is needed.

## Intended import closures before file creation

Neutral add-on imports GTailCongruence, Nat.GCD.Basic, NormNum and Ring. Owner imports GTailBridge and this add-on. Neither imports CounterexampleRouting, ModSevenSectors, DescentClosureAudit, GTailPadic or norm carriers.
Existing recursive source closure (public/private imports included): 8836 module names. Exact local DkMath closure before the two new modules:

```text
DkMath.FLT.Seven.Basic
DkMath.FLT.Seven.GTailBridge
DkMath.Lib.Cosmic.GTail
DkMath.Lib.Cosmic.GTailCongruence
DkMath.Lib.Cosmic.GTailFactor
DkMath.Lib.Cosmic.GTailNat
DkMath.Lib.Cosmic.GTailPascal
DkMath.Lib.Cosmic.GTailSelection
DkMath.Lib.Cosmic.GTailSeven
DkMath.Lib.Cosmic.GTailTransport
```

The two new modules add only themselves to that closure, with direction neutral arithmetic -> FLT owner -> tests. Basic's existing broad Mathlib import reaches FLT.Basic/Three/Four/Polynomial/MasonStothers; no DkMath FLT closure or heavy owner is reachable. Prior explicit Mathlib exponent-seven lexical search found no endpoint; this is a spelling-limited audit, not proof of absence under all names. Noncircularity rests on explicit proof routes and satisfiable neutral regressions.

## Verified final source import closures

```text
DkMath.Lib.Cosmic.GTailSevenArithmetic: 1518 module names
DkMath.Lib.Cosmic.GTail
DkMath.Lib.Cosmic.GTailCongruence
DkMath.Lib.Cosmic.GTailNat
DkMath.Lib.Cosmic.GTailSevenArithmetic

DkMath.FLT.Seven.GTailConstraintAudit: 8838 module names
DkMath.FLT.Seven.Basic
DkMath.FLT.Seven.GTailBridge
DkMath.FLT.Seven.GTailConstraintAudit
DkMath.Lib.Cosmic.GTail
DkMath.Lib.Cosmic.GTailCongruence
DkMath.Lib.Cosmic.GTailFactor
DkMath.Lib.Cosmic.GTailNat
DkMath.Lib.Cosmic.GTailPascal
DkMath.Lib.Cosmic.GTailSelection
DkMath.Lib.Cosmic.GTailSeven
DkMath.Lib.Cosmic.GTailSevenArithmetic
DkMath.Lib.Cosmic.GTailTransport
```

Supplemental inspection: `GapFocusing/UnitGauge.lean` provides SameUnitPowerClass, fixedRamifier_unitPowerClass_independent, and ramifier_rescaling_same_class_iff. Root-choice invariance fixes a nonzero ramifier; rescaling it preserves the class only when the weighted unit has the required power witness. `SevenBaseTerminalRamifiedUnitClassAudit.lean` already classifies the mod-49 seventh-power unit image as {1,18,19,30,31,48}; no new classifier is implemented or imported.

# Constraint ledger 006

Date 2026-10-09. Overall **Outcome B**: checked arithmetic receivers and explicit missing premises. Some weakened proposals are refuted (local C findings); no FLT7 contradiction or new independent obstruction.
Notation here only: Q=a^2+a*b+b^2, T=GTail 7 1 g c, all coordinates in ℕ unless stated. No new Q/carrier definition was introduced.

| Candidate / exact premises | Status | Proof/evidence | Classification / smallest blocker |
| --- | --- | --- | --- |
| `0<a`, `0<b`, Fermat7Equation a b c -> `max a b<c ∧ c<a+b` | proved | Basic right_lt and its symmetric instance; positive selected interior; strict seventh-power comparison | known height fact, new selected-factor proof route for upper bound |
| same premises, `c+g=a+b` -> `g<a ∧ g<b` | proved | height plus natural linear arithmetic | conditional consequence, not descent |
| same premises -> `∃ g, 0<g ∧ g<a ∧ g<b ∧ c+g=a+b` | proved | canonical g=a+b-c; subtract only after c≤a+b | focused certificate; no positivity of c premise needed separately |
| Fermat7Equation a b c, `a+b=c+g` -> `7∣g` | proved | GTailBridge product; prime divisor split; prime_dvd_GN_iff_dvd_gap | new route to known ModSevenSectors linear residue, not an independent obstruction |
| Nat.Coprime a b -> Nat.Coprime a Q and Nat.Coprime b Q | proved, neutral | add-multiple cancellation against squared opposite coordinate | new reusable packaging of standard gcd arithmetic; satisfiable inputs |
| Nat.Coprime a b -> Nat.Coprime (a+b) Q | proved, neutral | Q+ab=(a+b)^2; common divisor would divide ab | same classification; no norm carrier assumed |
| Nat.Coprime a b -> Nat.Coprime (a*b*(a+b)) Q | proved, neutral | multiply the three coprime factors | localizes primes of Q, not g or T |
| Nat.Prime q, Nat.Coprime a b, q∣Q -> ¬q∣a*b*(a+b) | checked example schema | gcd_eq_one of preceding endpoint | straightforward consequence; not extra public wrapper |
| `7∣g`, `¬7∣c` -> `7∣T ∧ ¬49∣T` | proved, neutral | prime address + existing mod-49 head congruence, cancel 7 | known residual mechanism with weaker premise than full Nat.Coprime g c; (g,c)=(14,2) separates the hypotheses |
| `7∣g` alone -> `¬49∣T` | refuted | g=c=7; 49∣T checked | endpoint unit premise missing |
| Nat.Coprime a b, c+g=a+b -> Nat.Coprime g c | refuted even with height and 7∣g | (a,b,c,g)=(11,17,21,7), gcd(g,c)=7 | these weakened inputs omit Fermat equation; does not refute a theorem under full FLT hypotheses |
| Nat.Coprime a b, c+g=a+b, Nat.Coprime g c -> Nat.Coprime g Q | refuted even with height and 7∣g | (8,11,12,7), Q=273, gcd(g,Q)=7 | same scope caution; coprime gap/endpoint does not force coprime gap/quadratic |
| CounterexamplePack a b c, c+g=a+b -> Nat.Coprime g c | unproved here | existing coprime_gap_y theorem concerns c-b, not a+b-c | cannot apply boundary gcd until a proof or explicit premise supplies this coprimality |
| q²∣g*T -> q²∣g, or instead always q²∣T | allocation not supplied | ordinary 3*3 counterexample to forced left allocation; actual GTail example g=c=3 has 9∣g*T but ¬9∣g | neither a general product claim nor an example omitting the coordinate/Fermat assumptions settles the stronger FLT-conditioned allocation problem |
| positive primitive equation + q∣Q, q≠7 -> valuation split | deferred | target v_q(g)+v_q(T)=2*v_q(Q) once all factors nonzero | requires checked valuation identities; splitting the sum further needs actual boundary/unit data |
| positive equation, coordinate relation, ¬7∣c -> exact v_7(g) identity | deferred | proposed identity in report from exact-one tail and product valuation | finite divisibility endpoint proved; valuation equality not promoted |
| positive primitive equation + all a,b,c units mod7 -> even v_7(g), 49∣g | proposed, deferred | follows from preceding proposed valuation route and coordinate unit tests | no new obstruction classification without proof and overlap audit |
| a smaller positive g -> a next primitive Fermat triple | unproved reconstruction | no nextX/nextY/nextZ or nextPack constructed | needs a new equation, positivity, coprimality, carrier identification and strict measure proof |
| Q as TraceOneInt(-1) norm -> cyclotomic seventh-power unit class closes | unsupported | typed norm sign conventions inspected only | missing map, fixed ramifier normalization, root/unit extraction and class witness |

## Descent frontier

`AwayDescentClosureProvider` requires nextX,nextY,nextZ, a proof of CounterexamplePack on them, a new AwayValuationTransferPacket, and carrier_match with the existing root's signed second coordinate absolute value. Our g is a different coordinate; smaller size does not supply these fields or the required equation. No structure field or axiom pretending to supply a universal next packet is added.

A constructive descent would need: (1) prime-power allocations in fixed carriers with nonzero side conditions, (2) compatible roots and units after a specified ramifier extraction, (3) an explicit signed/natural coordinate reconstruction conserving the Fermat equation, (4) primitive/positive next-packet proofs, and (5) a strict bound for the measure actually used by that packet. UnitGauge.fixedRamifier_unitPowerClass_independent fixes the ramifier; ramifier_rescaling_same_class_iff requires the weighted rescaling unit to be a power. A norm-shaped scalar identity supplies neither that unit witness nor a conversion to the FLT7 carrier.

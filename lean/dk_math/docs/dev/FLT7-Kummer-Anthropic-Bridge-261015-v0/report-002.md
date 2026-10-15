# Gate 002 — concrete Kummer unit lemma

**Accepted / Outcome A** ([review](review-002.md)). FLT7 remains OPEN.

Implementation:
`DkMath/FLT/Seven/PrimeTraceOneDirectCyclotomicKummerUnit.lean`.
Namespace:
`DkMath.FLT.Seven.SevenCyclotomicDegreeSixInt`.

## Proven theorem contracts

```lean
theorem unit_eq_starUnit_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    u = starUnit u

theorem exists_normUnit_seventhPower_of_congruent_mod_seven
    (u : Ringˣ)
    (h : DegreeSixUnitCongruentToRationalModSeven (u : Ring)) :
    ∃ v : SevenRealCubicIntˣ, quadraticNormUnit u = v ^ 7

theorem degreeSixKummerUnitLemmaAtSeven :
    DegreeSixKummerUnitLemmaAtSeven
```

G1: scalar congruence persists under conjugation. The norm-one
phase `u / starUnit u` is congruent to 1 modulo seven and is 1
by the existing theorem.

G2: from `u = m + 7*k`, the relative quadratic norm satisfies
`quadraticNormUnit u = m^2 + 7*c` in the real-cubic integer ring.
Both nonconstant mod-seven coordinates vanish, so
`projectiveLog = 0` and existing real-unit classification supplies
the seventh root.

G3: `u^2 = (ofRealUnit v)^7`; the explicit unit root
`w=(ofRealUnit v)^4 * u⁻¹` satisfies `w^7=u`.

The original `DegreeSixKummerUnitLemmaAtSeven : Prop` is unchanged;
G3 inhabits it for **every unit meeting its congruence condition**,
without a chosen packet. The small implementation additionally makes
two existing helpers public in
`PrimeTraceOneDirectCyclotomicRelativeNormPhase.lean`.
An opt-in arbitrary-congruent-unit regression source exists.

**Axiom result for all G1/G2/G3:** `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx`.
Final repository CI acceptance remains separate from this local
proof review. Default-Facade reachability is a Gate-003 task.

**Remaining frontier:** actual successor in cyclotomic integers,
strictly decreasing ramifier exponent, or an independent GN-derived
contradiction. This Gate does not prove FLT7.

Comparison source: [Anthropic pinned Kummer lemma](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_flt_regular.lean#L3247-L3288).
No upstream proof-body port was made.

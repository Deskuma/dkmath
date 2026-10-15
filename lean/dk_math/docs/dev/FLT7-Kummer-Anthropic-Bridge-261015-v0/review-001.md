# review-001 — DkMath × Anthropic Kummer audit

Date: 2026-10-15 JST  
Branch: `research/FLT7-Kummer-Anthropic-Bridge-261015-v0`  
Reviewed artifacts: [report-001.md](report-001.md), [bridge-matrix-001.md](bridge-matrix-001.md), and relevant live proof bodies.  
Gate 001 decision: **ACCEPTED / Outcome B (research mapping, not new Lean proof)**  
FLT7 independent closure: **OPEN**.

## Reviewed findings

1. **P0 PID / carrier: confirmed existing.** The degree-seven cyclotomic
   integers have a PID proof and an explicit integral-ring equivalence to
   `SevenCyclotomicDegreeSixInt.Ring`. Re-proving this layer would duplicate
   established work.
2. **P0/P1 chosen packet: confirmed existing.** Under the explicit
   `PrimitiveCounterexampleRamifiedProvenance` and chosen quotient packet,
   DkMath proves integral scalar congruence, unit seventh-power absorption,
   `Q = gamma^7` and `L = ramifiedUniformizer * gamma^7`.
   The ramifier is **not** removed in the last equality.
3. **P3 actual obstruction: confirmed missing.** Anthropic Case II constructs
   new `x',y',z'` in cyclotomic integers, retaining a unit factor, with the
   ramifier exponent strictly decreased. The old DkMath `q`-peel asks for
   a natural-number root with other coordinates fixed. A general adapter is
   neither found nor warranted. Norm is not additive.
4. **Trust audit: sufficient for the requested source inventory.** Codex
   reports 49 declaration probes and recursive axiom dependency auditing separated
   existing `sorryAx` routes from clean chosen-factor results.
   These are reported local checks, not a CI verdict.
   `#print axioms` on a `Prop` definition does not prove it.
5. **Conservative theorem status:** `DegreeSixKummerUnitLemmaAtSeven : Prop`
   remains an uninhabited specification in the surveyed source; the chosen
   packet theorem is stronger only for its restricted constructed unit.
   Gate 002 may close the general concrete congruence-conditioned specification
   without solving FLT7.

## Errata and review conditions

- **Source identity:** For permanently reproducible documentation, identify
  Anthropic declarations by the exact pinned GitHub commit
  `6e837e75355538c7f80bab5b956861e86c4eacc2`, source path and line.
  The Gate 001 matrix/report contain old aliases for temporary comparison
  copies, which are not Git-tracked canonical sources. In Gate 002, correct
  the *narrative source pointers* to the canonical source without falsifying
  historical command results. Do not assume a local comparison copy exists.
- **Namespace correction is substantive:** `KummersLemma` and
  `FltIdeals` at the cited sites are Lean `section` labels, not namespace
  segments. Compare using the resolved `P2MW.S_flt_regular.FltRegular.*`
  names shown by Gate 001, not imagined nested names.
- **Axiom language:** Report direct `sorryAx` dependency per exported
  theorem, not simply the presence of an unrelated `sorry` in imports.
  The legacy peel existence core has a `sorry`; the chosen-factor power
  theorem's audited declaration does not depend on it.
- **No premature promotion:** Do not create public `DkMath.Lib.*` APIs,
  modify the generic old Kummer peel, or import a finished external
  `fermatLastTheoremSeven` as an endpoint during Gate 002.

## Authorized next gate

**Gate 002: concrete degree-six Kummer unit bridge (G1–G3)**, per
[instruction-002.md](instruction-002.md). Initial implementation order:

1. From scalar congruence `u ≡ m (mod 7)`, prove `u = starUnit u`
   using the *existing* norm-one phase theorem.
2. Derive the seventh-power property of `quadraticNormUnit u` by a
   verifiable link to the *existing* real-cubic projective-log criterion.
3. Combine these into a proof inhabiting
   `DegreeSixKummerUnitLemmaAtSeven`, with a named theorem, without
   assuming unconditional seventh-power surjectivity for all units.

**Gate 002 is permitted to return Outcome B/C.** If the required congruence
to projective-log implication cannot be proved, report its exact missing
lemma and tests; do not elevate a guessed assertion to an axiom, build a
convenient stronger receiver, or replace it with a purely packet-specific
restatement.

### Explicitly deferred

Case II extended-state construction, strict `m+1 -> m` descent, first/second
case merger, old natural q-peel reconstruction, and any terminal FLT7 theorem.
Separate mathematical planning after Gate 002 review.

**Review verdict:** ACCEPT Gate 001 Outcome B and authorize ONLY Gate 002.

**Artifact retention update (2026-10-15):** historical raw build logs, evidence dumps, and temporary audit probes are not retained in Git. Review decisions rest on the source-linked matrix and the actual Lean declarations; CI is the final integration check.

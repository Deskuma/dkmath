# Instruction 038 — total focused prime routing across Gap and Tail, with a typed native receiver boundary

Date: 2026-10-11
Target branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`
Working directory: `lean/dk_math`
Prerequisites: `review-037.md`, `report-037.md`, `frontier-037.md`.
**Scope: Step 038 only.** Formally route a hypothetical **positive primitive focused Fermat7 input at every eligible prime q|Q** into the already proved **Gap** or **Tail** alternatives; show why the canonical seventh-root construction feeding Step037's common receiver belongs **only to the Tail case**; and package the existing generic C kernel, scalar-depth and bounded mixed support without introducing a new Fermat contradiction. This is a branch coverage/interface audit following Step037's genuine generic-prime construction, NOT another ideal-power/grid tower.

## 0. Exact preexisting mathematics and its limits

Notation, with real code owners and types:

```text
Q(a,b) := a^2+a*b+b^2 : ℕ
T(c,g) := DkMath.CosmicFormula.GTail 7 1 g c : ℕ
E := TraceOneInt (-1)
R := SevenCyclotomicDegreeSixInt.Ring
C := GTailCommonReceiver.Carrier = QuadraticAlgebra R (-1) 1
ιE := GTailCommonReceiver.fromEisenstein : E→+*C
ιR := GTailCommonReceiver.fromCyclotomic : R→+*C
```

**Step010 already kernel checked**, for q prime, q≠7, a,b positive, Nat.Coprime a b, `hEq:Fermat7Equation a b c`, `hfocus:a+b=c+g`, and q|Q:

```text
prime_focused_support_exclusive ... :
  (q ∣ g ∧ ¬q ∣ T) ∨ (q ∣ T ∧ ¬q ∣ g)

prime_square_focused_allocation ... :
  (q^2 ∣ g ∧ ¬q ∣ T) ∨ (q^2 ∣ T ∧ ¬q ∣ g)

not_prime_dvd_endpoint_of_quadratic ... : ¬q ∣ c
not_prime_dvd_coordinate_product_of_quadratic ... : ¬q ∣ a*b*(a+b)
```

**Step031** already supplies, on the **Tail branch hT:q|T**, `focused_norm_depth_guards` deriving q∤a,b,a+b,c,g, q≠3, and `focused_norm_scalar_depth_readouts` deriving `v_q(T)=2v_q(Q)`, q²|T, parity, q³|T↔q⁴|T and q⁴|T↔q²|Q.

**Step037** already supplies:
- \`evPair t r ... : C→+*ZMod q\`, its maximal \`pairedKernel\`, typed E/R contractions and exact **joint ideal sum**;
- \`nativeKernel a b c g hQ hb hc hg hT\`, requiring **q∤b,c,g AND q|T**, and actual E-norm coordinate α and selected cyclotomic factor F0 images in it;
- \`native_square_support\` under extra q≠3, q²|T gives source squares and one-way mixed M³/M⁴ support;
- \`focused_receiver\` under the **full Fermat equation, positivity, primitive, focus, q≠7 and q|Q,T**, reuses all the above and Step031's scalar valuation parity.

**Step032** already proves under additive focus:
`Fermat7Equation a b c ↔ g*T=7*a*b*(a+b)*Q²` (also INT norm version).
No local kernel, joint ideal sum, residue equality, gap/Tail split or power inequality is known to imply the exact global scalar balance.

**CRITICAL BRANCH TRAP:** Step037's \`nativeKernel\` is **not** defined on a general q|Q input until hT and q∤g have been produced. A q|g prime has the **trivial** natural Tail ratio `(c+g)/c=1` modulo q when q∤c; it does *not* yield the nonidentity seventh-root certificate demanded by Step037's Tail receiver. It is incorrect to "cover" this branch by a fabricated nontrivial root. The separate abstract supplied-root \`evPair\` may still exist at some q with **other roots**; the forbidden step is falsely identifying such an arbitrary root with the natural **canonical** Gap-side ratio.

## Gate 0 — detailed source/signature/inventory and no new hidden assumptions

Read exactly:
- `DkMath.FLT.Seven.GTailPrimeAllocationAudit` Step010 \`prime_square_focused_allocation\`, \`prime_focused_support_exclusive\`, \`not_prime_dvd_endpoint_of_quadratic\`, \`not_prime_dvd_coordinate_product_of_quadratic\`, and actual units;
- `DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge` Step031 \`focused_norm_depth_guards\`, \`focused_norm_scalar_depth_readouts\`, E square and R K²/K³/K⁴ endpoints;
- `DkMath.FLT.Seven.GTailFocusedGenericPrimeReceiver` Step037 generic \`evPair\`, \`nativeKernel\`, \`native_residue_zeros\`, \`native_square_support\`, \`focused_receiver\`, \`pairedKernel_eq_sup\`;
- `DkMath.Lib.NumberTheory.GTailSevenPairedResidue`: exact definition \`gtailSevenTailRatio q c g\`, its q∤c/q∤g/q|Tail guards and supporting ZMod arithmetic;
- `DkMath.FLT.Seven.GTailGlobalBalanceFirewall` exact balance iff and Step032 q43 non-Fermat controls;
- `DescentClosureAudit.AwayDescentClosureProvider` and `SevenRamifiedSignedRootDepth.RamifiedSignedRootDepthPacket` signatures (read-only audit; **no direct new import or value construction**);
- Mathlib actual \`ZMod.natCast_zmod_eq_zero_iff_dvd\` or the available verified equivalent, \`div_eq_iff\`, \`eq_div_iff\`, \`ZMod.isUnit_iff\`, \`Nat.Prime.dvd_of_dvd_pow\` and q-divisibility transit; confirm signatures by \`#check\`, do not guess.

Produce `source-inventory-038.md` with a two-branch table:
(A) primes q|Q under *hEq* and q≠7;
(B) the **Gap** constructor q²|g, q∤T, r=1;
(C) the **Tail** constructor q²|T, q∤g and Step037 kernel/typed contractions/mixed support;
(D) exact global balance/source signed packet still missing.
State all source-typed lemma owners, Fermat/positivity assumptions, denominator guards and the exact q7/q3 exceptions. Note that abstract supplied-root \`evPair\` is not equivalent to a native Tail root.

Suggested small new owner:
`DkMath/FLT/Seven/GTailFocusedPrimeRoute.lean`
importing Step037 owner directly and existing Step010 only if its declarations truly are not already in the transitive closure. Tests:
`DkMathTest/FLT/Seven/GTailFocusedPrimeRoute.lean`.
Do not modify Step010/031/032/037, existing rings, nativeKernel definition, old signed packets, generic polynomial Hensel owners or facades.

## Gate 1 — canonical ratio at a Gap prime is exactly ONE (mandatory)

For arbitrary prime q, natural c,g, with

```text
hc : ¬ q ∣ c
hg : q ∣ g
```

prove the source-actual statement

```text
gtailSevenTailRatio q c g = (1 : ZMod q).
```

Do not require hEq, hfocus, c/g positivity, q|T, q|Q or q≠7 in this basic residue lemma. The true proof is that (g:ZMod q)=0 from q|g and (c:ZMod q)≠0 from q∤c, hence (c+g)/c=1 in a field. Verify q.Prime and casts; use the existing \`gtailSevenTailRatio\` definition and \`div_eq_iff\` with correct side hypotheses, not a false cancellation \`c/c=1\` when c=0 mod q.

**Explicit negative guard**: the canonical Gap root **cannot** satisfy
`gtailSevenTailRatio q c g ≠1`, so the Step037 \`nativeKernel\` Tail certificate is unavailable **from these same native data**.

Do not assert that *no* seventh root exists in ZMod q at a Gap prime. The abstract supplied-root receiver can be constructed for some q≡1 mod21 using a different root r; it would simply **not** be the canonically selected ratio (c+g)/c. This distinction is essential and should be regression-tested with a satisfying artificial root example if inexpensive.

Compile Gate1 in isolation before the conditional routing.

## Gate 2 — total two-branch focused primitive q|Q routing (mandatory)

Under the **exact Step010** positive primitive hypothetical Fermat inputs

```text
variable {q a b c g : ℕ} [Fact (Nat.Prime q)]
ha : 0<a
hb : 0<b
hcop : Nat.Coprime a b
hEq : Fermat7Equation a b c
hfocus : a+b=c+g
hq7 : q≠7
hQ : q ∣ a²+a*b+b²
```

do **not** assume `hT:q|GTail` at theorem entry.

First, derive q∤a,b,a+b and **q∤c** using the checked Step010 theorems without hT. Then invoke the **already proved** \`prime_square_focused_allocation\` (not a new p-adic valuation proof) to obtain

```text
(q² ∣ g ∧ ¬q ∣ T) ∨ (q² ∣ T ∧ ¬q ∣ g).
```

Strengthen the **Gap alternative** with the Gate1 actual ratio identity:
```text
q² ∣ g ∧ ¬q ∣ T ∧ gtailSevenTailRatio q c g = 1.
```

Keep the **Tail alternative** as q²|T, q∤g (plus a proof hT:q|T for the next gate). A basic, compact public disjunction theorem is the first mandatory endpoint. If useful, define a lightweight (non-exotic) inductive \`FocusedQuadraticPrimeRoute\` with distinct constructors gap and tail **whose fields are exactly these checkable consequences**, but not a structure whose constructor assumes a nonexistent common kernel on the Gap side.

**Logical boundary:** a complete case split under hEq does not prove hEq is impossible, and its gap branch must remain a live alternative. Do not use a known nonexistence of hypothetical Fermat solutions to close either branch, as that would be circular or tautological.

## Gate 3 — attach the EXISTING Step037 common receiver only to the Tail branch

Under the same full hypothetical data and **in the Tail case q²|T**, derive `hT:q|T` from q²|T. Use Step010/031 to obtain q∤b,c,g and q≠3. Invoke the already proved Step037 \`focused_receiver\` or its smaller direct \`nativeKernel\` endpoints to obtain:

```text
J : Ideal C := nativeKernel a b c g hQ hbUnit hcUnit hgUnit hT
J.IsMaximal
comap ιE J = P_{-a/b} : Ideal E
comap ιR J = K_{(c+g)/c} : Ideal R
J = Ideal.map ιE P_{-a/b} ⊔ Ideal.map ιR K_{(c+g)/c}
ιE (gtailSevenNormCoord a b) ∈ J
ιR (gtailCyclotomicFactor c g 0) ∈ J
v_q(T)=2*v_q(Q)
Even(v_q(T))
q²|T, q³|T↔q⁴|T, q⁴|T↔q²|Q
ιE(α²), ιR F0 ∈ J²
ιEα * ιR F0∈J³
ιE(α²)*ιR F0∈J⁴.
```

The exact theorem signature may package the Tail consequences via \`let hu := ...\` as in existing Step037, or use a small \`TailReceiverPacket\` whose fields are **actual** Lean checked proof statements. Preserve the source ideal types and the **single canonical** nonidentity seventh root (c+g)/c. Do not write an untyped M or compare P and K as equal ideals. If a very large nested conjunction becomes hard to elaborate, prove the scalar route separately and reuse Step037 directly in a small Tail adapter rather than duplicating Step037's thirty-line tuple.

**Optional desirable**: combine Gate2's disjunction with Gate3's Tail adapter to expose one publicly usable **sum/route** result that a future FLT7 theorem could consume without redoing its proof split. The Gap case should expose the exact ratio=1 guard failure; the Tail case should expose a **real** C kernel with typed source contractions. Avoid hiding the split in a \`Nonempty\` that discards crucial source data.

Do NOT turn the conditional even-Tail valuation into an unconditional q-local theorem, derive a primitive next Fermat tuple or claim local power support produces the Step032 exact global balance.

## Gate 4 — separate real carrier-equality firewall (valuable optional theorem)

Step034/q43 proved **one example** where both source images lie in a common kernel but are unequal. Consider a general, source-typed theorem for any q-prime with supplied R seventh root r and any natural a,b with q∤b:

```text
∀ u : R,
  fromEisenstein (gtailSevenNormCoord a b) ≠ fromCyclotomic u.
```

The proof is elementary in C: applying \`QuadraticAlgebra.im\` to a hypothetical equality gives `(b:R)=0` by the actual \`gtailSevenNormCoord_eq\`, while the coefficient evaluation \`evalCyclotomicFromSeventhRoot r ... :R→+*ZMod q\` gives `(b:ZMod q)=0`, contradicting `¬q∣b`. This theorem needs **neither hEq nor q|Q nor q|T**, only a supplied suitable R evaluation and the q-unit b. If a stronger direct six-coordinate proof with b≠0 avoids root assumptions, verify the integer cast injectivity API before generalizing; do not assume R is a domain without evidence.

Specialize it to the **Tail branch J** and to the q43 numeric non-Fermat control. The result demonstrates source elements remain distinct despite equal zero residue. It is **not** an FLT7 obstruction: nothing in Fermat7Equation asserts equality of α with the single selected F0 inside C. Do not reverse this to claim the hypothetical hEq is false.

If this optional gate is expensive, retain the mandatory ratio split and Tail receiver; report the exact missing cast/coordinate API.

## Gate 5 — honest numeric and symbolic regressions

Include checkable tests for:

**Generic (symbolic q):**
- exact Gap ratio=1 from q|g,q∤c and therefore failure of the nonidentity Tail guard;
- the full hypothetical positive primitive q|Q **either** Gap q² support/Tail absence **or** Tail q² support/Gap absence, **without q|T as initial premise**;
- a universal Tail-branch theorem signature that instantiates the **actual existing nativeKernel**, original E/R typed contractions, parity and bounded common-power readouts. This must use symbolic hEq; no invented positive Fermat tuple.
- q∤b,a,c from source Step010 and not assumptions silently added in one branch.

**Concrete non-Fermat controls:**
- q43, (a,b,c,g)=(1166,1857,1858,1165) with true Tail local Q/T support, **not** hEq: Step037 constructs M43 and true bounded mixed support; it may not call the new Fermat-conditioned total route.
- q43, (a,b,c,g)=(5,8,9,4) **does satisfy additive focus** and selects M43 but violates q² Tail support and doubled scalar budget; keep the corrected Step032 history.
- q13, (a,b,c,g)=(14,29,30,13), with additive focus and q|g but q∤c and q∤Tail. Check **canonical** ratio=1 (since g≡0 mod13); no native nontrivial seventh root and no Step037 nativeKernel from this tuple. The tuple is **not** an hEq instance, so test only the raw Gap ratio and support facts.
- q127 t20/r2 verifies supplied-root generic evPair, but does not imply any *natural* Q/T input or hEq; this remains a separate receiver-control example.
- q=7 (ramified) and q=3 (E repeated) require their own guards; never smuggle root existence into the Gap branch.

Explicitly test that Step032 still proves `Fermat7Equation ↔ exact scalar balance` under focus, and that the true non-Fermat q43 local examples fail the global balance. This protects against treating full branch coverage as a new proof of FLT7.

## Gate 6 — reconstruction contract and stop criterion

`report-038.md` / optional `frontier-038.md` must distinguish these exact operations and *missing* contracts:

| Stage | Proven through Step038 if Gate2+3 pass | Still missing |
| --- | --- | --- |
| q prime dividing Q under hypothetical hEq | Actual q² Gap OR q² Tail alternatives, precise nontrivial ratio guard | A contradiction or further restriction on at least one live branch |
| Gap branch | q²|g, q∤T, canonical Tail ratio=1 | Any appropriate source-linked Gap-side algebraic recipient / new descent, if needed |
| Tail branch | Native common C maximal kernel, E/R typed contraction, sourced norm/square and mixed M³/M⁴ lower bounds, even vq(T) | New global arithmetic restriction, exact M-adic valuation, source-to-signed carrier transfer |
| Exact global balance | Equivalent to hEq under additive focus (Step032) | Derivation from **weaker** data without assuming hEq |
| Old signed packet | no newly constructed fields | Balanced axis, signed identities, p=7 units, normalizedEquation |
| AwayDescentClosureProvider | no newly constructed fields | nextX/Y/Z, primitive CounterexamplePack, AwayValuationTransferPacket, carrier_match |

\`AwayDescentClosureProvider x y z p\` specifically needs
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd`.
A q-local C ideal equality or one-way mixed-power membership does not supply this **natural carrier** equality.

**Scientific classification:** completing a route theorem and a Tail receiver by Step010/037 composition is Outcome B (formal API completeness), not a new unconditional FLT7 obstruction. The optional generic source-image inequality is a source-type separation firewall, not a Fermat contradiction. Any proposed truly new obstruction must have an explicit theorem whose conclusion is *not* already a direct consequence of Step010/031 or tautologically equivalent to an assumed hEq.

## Deliverables and build discipline

Required:
- `DkMath/FLT/Seven/GTailFocusedPrimeRoute.lean`;
- `DkMathTest/FLT/Seven/GTailFocusedPrimeRoute.lean`;
- `source-inventory-038.md`, `report-038.md`;
- truthful post-037 `ROADMAP.md` append, preserving historical Step032 correction and prior reports/reviews/owner files byte-stable;
- optional `frontier-038.md` if clear two-branch/new-provider contract table warrants a separate artifact.

Build sequential with process-local `LEAN_NUM_THREADS=2`:
1. source-actual canonical Gap ratio=1 and nonidentity guard failure;
2. Step010 primitive q|Q square-support disjunction, **without initial hT**;
3. Tail-only conditional generic receiver readout and preservation of E/R ideal types;
4. optional generic E-vs-R image inequality; q43/q13/q127 controls;
5. final focused source/test, Step037/036 direct regressions, all public \`#print axioms\`, import DAG, neutral Lib→FLT, forbidden-token/whitespace and final warning audits.

Log actual command/exit/warning for each step, all public theorem signatures, intermediate Lean failures/repairs, all standard/nonstandard axiom names and checked proof-owner references. No all-suite clean build, global proof-resource-limit override, new E/R/C definitions, old signed-owner modification, new generic grid, K⁵/all-k, facade change, PR/rebase/merge.

**Outcome B expected:** honest total q|Q branch routing that **exposes the Gap branch instead of pretending Step037 receives it**, and supplies a genuinely typed generic local C receiver only when canonical Tail q-support holds. The branch split and scalar budget already exist, so this is a correct interface/guard theorem, not independent Fermat descent.
**Outcome C/partial:** an actual inconsistency in expected q-unit/ratio transport or inaccessible old source theorem. Preserve compiled intermediate lemmas and report precisely the blocked type or missing premise without manufacturing an hT assumption.
**Outcome A:** only if a genuinely new, noncircular restriction on hypothetical positive primitive Fermat7 solutions is discovered and checked, beyond the existing Gap/Tail exclusion and scalar parity.

**STOP after Step038.** Do not automatically build a Gap-side common receiver, another 2×6 grid, exact mixed valuations, all-prime spectrum, cross-source ideal power equalities, new signed root packet, class/unit principalization, primitive recursive provider or unconditional FLT7 closure. After this complete two-branch route, the next **research** decision must evaluate a genuinely new global obstruction or explicit primitive-descent reconstruction theorem, not merely another local depth increment.

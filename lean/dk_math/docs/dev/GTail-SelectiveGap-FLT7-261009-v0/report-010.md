# Report 010 — q-local square allocation in the exact GTail bridge

Instruction date: 2026-10-09. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
**Step 010 COMPLETE — Outcome B.** The local endpoint unit, exclusive prime support, doubled q-valuation budget and unsplit square allocation are proved under the exact stated primitive/positive equation hypotheses. No FLT7 closure or independent new obstruction is claimed.

Notation only: Q=a²+ab+b², T=GTail 7 1 g c, all naturals. No new carrier or norm definition.

## Exact changed files

Relative to `lean/dk_math`:

- `DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean`: three neutral public endpoints, importing only GTailNat and Lib.NumberTheory.PadicValNat.
- `DkMath/FLT/Seven/GTailPrimeAllocationAudit.lean`: five conditional public endpoints and one private nonzero helper; imports GTailConstraintAudit and the new neutral module.
- `DkMathTest/CosmicFormula/GTailSevenPrimeAllocation.lean`: eight examples plus a private abstract calibration budget; prints all three neutral public axioms.
- `DkMathTest/FLT/Seven/GTailPrimeAllocationAudit.lean`: five conditional theorem-applying examples, five public axiom prints.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-010.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-010.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`

The four new Lean modules preserve existing MIT headers, import-before-file-print and namespace/documentation style. No facade promotion, root-driver change, historical ledger rewrite, previous mathematics change or Legendre/Lake configuration edit. Lake's submodule glob discovers both new tests; only focused builds were run.

## Full public signatures

Neutral namespace `DkMath.CosmicFormula`, [source](../../../DkMath/Lib/Cosmic/GTailSevenPrimeAllocation.lean):

```lean
theorem not_prime_dvd_gtail_seven_of_gap {q g c : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hgap : q ∣ g) (hc : ¬ q ∣ c) :
    ¬ q ∣ GTail 7 1 g c

theorem padicValNat_prime_square_product {q g T A B C Q : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hg : g ≠ 0) (hT : T ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hprod : g * T = 7 * A * B * C * Q ^ 2)
    (huA : ¬ q ∣ A) (huB : ¬ q ∣ B) (huC : ¬ q ∣ C) :
    padicValNat q g + padicValNat q T = 2 * padicValNat q Q

theorem prime_square_allocation_of_budget {q g T Q : ℕ}
    (hq : Nat.Prime q) (hg : g ≠ 0) (hT : T ≠ 0) (hQ : Q ≠ 0) (hqQ : q ∣ Q)
    (hbudget : padicValNat q g + padicValNat q T = 2 * padicValNat q Q)
    (hexclude : q ∣ g → ¬ q ∣ T) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ T) ∨ (q ^ 2 ∣ T ∧ ¬ q ∣ g)
```

Conditional namespace `DkMath.FLT.Seven`, [source](../../../DkMath/FLT/Seven/GTailPrimeAllocationAudit.lean):

```lean
theorem not_prime_dvd_coordinate_product_of_quadratic {q a b : ℕ}
    (hq : Nat.Prime q) (hcop : Nat.Coprime a b)
    (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) : ¬ q ∣ a * b * (a + b)

theorem not_prime_dvd_endpoint_of_quadratic {q a b c : ℕ}
    (hq : Nat.Prime q) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    ¬ q ∣ c

theorem prime_focused_support_exclusive {q a b c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ∣ g ∧ ¬ q ∣ GTail 7 1 g c) ∨ (q ∣ GTail 7 1 g c ∧ ¬ q ∣ g)

theorem padicValNat_focused_quadratic_budget {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    padicValNat q g + padicValNat q (GTail 7 1 g c) =
      2 * padicValNat q (a ^ 2 + a * b + b ^ 2)

theorem prime_square_focused_allocation {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hqQ : q ∣ a ^ 2 + a * b + b ^ 2) :
    (q ^ 2 ∣ g ∧ ¬ q ∣ GTail 7 1 g c) ∨
      (q ^ 2 ∣ GTail 7 1 g c ∧ ¬ q ∣ g)
```

## Exact proof route and premise audit

**Ordinary units:** Coprime a b implies Coprime (a*b*(a+b)) Q. A prime q dividing Q and that product would divide its gcd=1, impossible. Each of a,b,a+b is consequently a local q-unit.

**Endpoint unit, derived rather than assumed:** the balanced seventh-power identity plus the exact Fermat equation gives `(a+b)^7=c^7+7*a*b*(a+b)*Q²`. If q∣c, both summands are divisible by q, since q∣Q. Then primality implies q∣a+b, contradicting the preceding unit. This uses addition, never a truncated natural difference. This endpoint only needs hq,hcop,hEq,hqQ: positivity, q≠7 and the focus relation are unnecessary for that local conclusion.

**Actual GTail exclusion:** when q∣g, the head-unit theorem applies at degree 7/index 1. The head is choose 7 1*c⁶=7*c⁶; prime q≠7 gives q∤7 and the derived endpoint unit gives q∤c⁶. Thus q∤T. The exact product and q∣Q also give q∣g*T. Primality splits this support, and the head exclusion makes it exclusive. The support theorem does not need positive a,b.

**Nonzero discipline for budget:** positive focused height yields c<a+b, so hsum forces g>0. The exact RHS is positive when a,b>0; if T=0, the exact product would be zero, contradicting RHS positivity. Therefore g,T,a,b,a+b,Q and Q² are nonzero. The abstract budget expands products with `[Fact q.Prime]`, nonzero factors, and power valuation. Ordinary factors and coefficient seven contribute zero. It yields `v_q(g)+v_q(T)=2*v_q(Q)` without assuming a residual valuation of one.

**Square upgrade:** q∣Q and Q≠0 give vq(Q)≥1. If q∣g, head exclusion gives vq(T)=0; hence vq(g)≥2 and q²∣g. If q∤g, vq(g)=0, so vq(T)≥2 and q²∣T. Divisibility conversion explicitly requires the selected nonzero factor. This is the exact requested disjunction, not an arbitrary choice of its side.

No Coprime g c or Coprime g Q is derived or assumed; no primitive CounterexamplePack or typed cyclotomic quotient is created. The new budget/allocation proof uses only the primitive pair, positive coordinates, exact equation/focus relation, prime q≠7 and q∣Q.

## Satisfiable and missing-premise calibrations

All finite checks use ordinary kernel-checked `decide`.

- **Actual left prime address:** q=13,g=13,c=2. Lean checks T=13143019 and 13∤T, both through the head theorem and independently by concrete arithmetic.
- **Actual right prime address:** q=43,g=3,c=1. Lean checks T=5461=43*127, 43∤g and 43∣T. This is a neutral one-layer address, not an instance of the exact Fermat allocation theorem or evidence of q²∣T in these arbitrary coordinates.
- **Endpoint-unit premise matters:** q=13,g=c=13 gives 13∣T, so dropping q∤c invalidates head exclusion.
- **Degree-prime distinction matters:** q=7,g=7,c=2 gives 7∣g and 7∣T despite the endpoint unit. q≠7 is essential for this exclusion; the separate seven-adic canon handles this branch.
- **Satisfiable exclusive abstract product:** q=43,g=43²,T=7,A=B=C=1,Q=43. The exact equation holds, the neutral theorem proves its doubled budget, and the explicit exclusion 43∤7 allows the square-allocation theorem. These factors are not a claimed GTail/Fermat packet.
- **Mixed allocation counterexample to budget-only upgrading:** q=43,g=43,T=7*43,A=B=C=1,Q=43. The same exact abstract product and doubled budget hold. Both g and T are divisible by 43, while neither is divisible by 43². Thus neither disjunct of an unsplit-square claim is possible without exclusion. This satisfies the ordinary-factor unit conditions; what it lacks is the actual GTail head-unit exclusion.

The owner tests apply all five exact conditional interfaces with their hypotheses. No positive exact Fermat solution is supplied. The concrete counterexamples refute only the explicitly weakened neutral contracts, not the proved full conditional result.

## Sequential validation

Cwd `lean/dk_math`, process-local `LEAN_NUM_THREADS=2`, incremental and sequential. Local command/exit/duration records and raw logs are in `.lake/build/gtail-step010/`. No clean/root/facade/all-suite build.

| Command | Exit | Seconds | Local raw log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.Cosmic.GTailSevenPrimeAllocation` | 0 | 3.32 | `01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailPrimeAllocationAudit` | 1 | 13.72 | `02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailPrimeAllocationAudit` | 0 | 14.13 | `03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSevenPrimeAllocation` | 0 | 3.33 | `04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeAllocationAudit` | 0 | 14.00 | `05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSevenPrimeAllocation` | 0 | 3.48 | `06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.SevenUnitAllocation` | 0 | 1.44 | `07-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailSevenUnitAudit` | 0 | 8.03 | `08-build.log` |

The first owner build failed at a rewrite: the existing seven-power identity orders its endpoint terms as b⁷+a⁷, while Fermat7Equation uses a⁷+b⁷. Added the targeted `add_comm (b^7) (a^7)` rewrite before substituting the equation. The corrected owner and both new tests pass. The later neutral test build includes additional concrete value/missing-premise checks; it passes. Both Step 009 regression targets pass. No false full-premise inference or unresolved blocker remains; the local rewrite repair is not Outcome C.

## Axioms, dependency and hygiene evidence

All **8/8 new public endpoint** axiom prints in the successful final direct tests are exactly `[propext, Classical.choice, Quot.sound]`. No sorryAx/additional axiom; final new test logs have no warnings/errors. Private helpers are excluded from public counts and are in the audited source dependency of their consumers.

Comment-stripped import-header closure audit: neutral owner 1078 names / 4 local modules; conditional owner 8795 / 15; neutral test 1079 / 5; conditional test 8796 / 16. DFS union passes across 17 local modules. Neutral has zero FLT modules. No Seven facade, descent/closure, prime-address/Norm/unit owner is reachable through the local new-owner graph. Full lists are in local `imports.json`; name counts include external terminals and omit implicit compiler/native dependencies, not build jobs or hole-free whole-workspace evidence.

Whole-word sorry/admit/axiom/unsafe, False.elim/exfalso and unconditional FLT impossibility patterns: no matches in all four new Lean sources. `git diff --check`, new-file whitespace/final-newline review and protected-source byte comparisons pass. Existing facades, root driver, Steps 008–009 owners, constraint-ledger-006, LegendreMergedCRT and Lake configuration are unchanged.

## Source overlap and classification

[source-inventory-010.md](source-inventory-010.md) records the actual prerequisites and bounded comparison by path/name:

- `CounterexampleRouting.gcd_gap_GN_seven_dvd_seven` already excludes simultaneous support away from seven under **full** Coprime g y. Its packet adapter uses difference gap z-y. This new sum-focus route derives only the q-local endpoint unit at primes of Q, without unjustified global coprimality or coordinate transfer.
- `SevenBaseTerminalPrimeSupport.mem_awaySevenBaseTerminalPrimeSupport_iff` and `AwaySevenBaseTerminalRoutingPacket.primeSupport_ne_seven` concern a typed terminal cubic-root load. q∣Q is not membership in that load support.
- `SevenRamifiedFusionCyclotomicPrimeAddress.prime_dvd_quotientRoot_modSeven_eq_one` requires a RamifiedSignedRootDepthPacket and divisibility of its integer quotientRoot. No such typed packet is supplied by the scalar allocation, and its prime-order conclusion is not transferred.
- `PrimeTraceOneDirectRealCubicSquarePrimeSupport.directOrbitSquareRefinement_squareRoots_norm_product` uses ring roots, fixed refinement and a cube/norm carrier. Scalar Q² allocation supplies no matching map or residual unit class.

The new coordinate-specific necessary condition is correctly checked, but a separate novelty/independent obstruction proof is absent. **Outcome B**, not A or FLT7 closure.

## Lean結果からの気づき・example・実装提案

1. **確認済み:** q∤cを隠れた仮定にせず、原始二次式と正確な加法恒等式から導けました。この局所端点単元の証明自体には、正性・focus関係・q≠7が不要です。各定理は実際に消費する仮定だけを持ちます。
2. **確認済み:** 排他性はq∣Qに局所化されています。原始入力から全体のCoprime g cを主張する必要がありません。付値予算は両左因子の和として残し、平方の配分は排他性を別に証明してから適用しました。
3. **確認済み:** q=43の抽象積は、排他的配分も一段ずつの混合配分も同じ右辺を持てます。したがって、積の整除性や付値予算だけでは側を選べません。新しい中立平方定理はこの違いを明示的なhexclude引数で表しています。
4. **確認済み:** 実際のGTailの二つのprime addressは中立に満たされますが、それだけでQ²配分の候補全体を表すわけではありません。具体的尾T=5461の43整除は一段です。正確なFermat関係を省いた数値例を、条件付き平方定理の成立例として扱っていません。
5. **実装提案（未実施）:** 必要になれば、同じ排他性と予算から選ばれた側の付値が正確に `2*vq(Q)` であるAPIを追加できます。今回の要求はq²整除の排他的選択までなので、追加定理や選択関数は作っていません。
6. **次の比較課題（未実施）:** scalar Q-support と既存のtyped terminal/cyclotomic prime supportとの接続には、carrierと座標を一致させる具体的写像が必要です。今回の結果から位数21や単元類・次候補を推論していません。

## Frontier and stop

The historical [constraint-ledger-006.md](constraint-ledger-006.md) stays intact. Its deferred q-budget is now proved under the exact primitive positive equation/focus hypotheses. The stronger square allocation is also proved **with the derived local endpoint unit and GTail head exclusion**, not by the previously rejected plain product-divisibility route. No globally fixed left/right side is asserted.

Order-21, typed cyclotomic Norm/unit carrier transfer, global root/unit reconstruction and constructive next primitive Fermat packet remain open. Stop after Step 010; no outside proof-corpus search, full test suite, unrelated performance edit, facade promotion, PR or merge.

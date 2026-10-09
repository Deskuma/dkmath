# Report 011 — independent finite-field orders on the tail branch

Date: 2026-10-10 (JST). Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
**Step 011 COMPLETE — Outcome B.** Neutral nontrivial order-seven and order-three mechanisms yield the tail-side order intersection. Exact FLT7 data supply the local units/branch guard; no contradiction, descent or number-field carrier transfer.

Notation: Q=a²+ab+b², T=GTail 7 1 g c, naturals. The conclusion is restricted to q∣T, not universal over the prime divisors of Q.

## Exact changed files

Relative to `lean/dk_math`:

- `DkMath/Lib/NumberTheory/GTailSevenPrimeOrder.lean`: four public neutral theorems and one private finite-field unit-order helper. Imports only GTailNat, Mathlib.FieldTheory.Finite.Basic, FieldSimp and Ring.
- `DkMath/FLT/Seven/GTailPrimeOrderAudit.lean`: two public conditional theorems, importing only GTailPrimeAllocationAudit and the new neutral module.
- `DkMathTest/NumberTheory/GTailSevenPrimeOrder.lean`: nine nonvacuous/boundary examples and all four neutral axiom prints.
- `DkMathTest/FLT/Seven/GTailPrimeOrderAudit.lean`: two conditional theorem-applying interfaces, an independent Step 010 head-unit application on the gap calibration, an explicit negative Fermat check and both conditional axiom prints.
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/source-inventory-011.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/report-011.md`
- `docs/dev/GTail-SelectiveGap-FLT7-261009-v0/ROADMAP.md`

Existing production/test mathematics, facades/root driver, historical ledger, LegendreMergedCRT and Lake configuration are unchanged. New modules preserve MIT header, import-before-file-print, documentation and namespace style. Direct tests are discovered by the existing test-submodule glob. No full-suite build or facade promotion.

## Full public signatures

Neutral namespace `DkMath.Lib.NumberTheory`, [source](../../../DkMath/Lib/NumberTheory/GTailSevenPrimeOrder.lean):

```lean
theorem seven_dvd_prime_sub_one_of_gtail {q c g : ℕ}
    (hq : Nat.Prime q) (_hq7 : q ≠ 7) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ GTail 7 1 g c) : 7 ∣ q - 1

theorem prime_ne_three_of_gtail {q c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g)
    (hT : q ∣ GTail 7 1 g c) : q ≠ 3

theorem three_dvd_prime_sub_one_of_quadratic {q a b : ℕ}
    (hq : Nat.Prime q) (hq3 : q ≠ 3) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (ha : ¬ q ∣ a) (hb : ¬ q ∣ b) : 3 ∣ q - 1

theorem twentyOne_dvd_prime_sub_one_of_quadratic_gtail {q a b c g : ℕ}
    (hq : Nat.Prime q) (hq7 : q ≠ 7)
    (hQ : q ∣ a ^ 2 + a * b + b ^ 2) (hT : q ∣ GTail 7 1 g c)
    (ha : ¬ q ∣ a) (hb : ¬ q ∣ b) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) :
    21 ∣ q - 1
```

Conditional namespace `DkMath.FLT.Seven`, [source](../../../DkMath/FLT/Seven/GTailPrimeOrderAudit.lean):

```lean
theorem twentyOne_dvd_prime_sub_one_of_focused_tail {q a b c g : ℕ}
    (hcop : Nat.Coprime a b) (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hT : q ∣ DkMath.CosmicFormula.GTail 7 1 g c) : 21 ∣ q - 1

theorem prime_square_dvd_gap_of_not_twentyOne {q a b c g : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hEq : Fermat7Equation a b c) (hsum : a + b = c + g)
    (hq : Nat.Prime q) (hq7 : q ≠ 7) (hQ : q ∣ a ^ 2 + a * b + b ^ 2)
    (hnot : ¬ 21 ∣ q - 1) : q ^ 2 ∣ g ∧ ¬ q ∣ DkMath.CosmicFormula.GTail 7 1 g c
```

## Neutral mechanism: two independently nontrivial orders

**Order seven.** Instantiate Fact q.Prime before field division. q∤c gives a nonzero denominator; q∤g gives a nonzero gap residue. Cast the natural identity `(g+c)^7=g*T+c^7` to ZMod q, using the **cast of the natural GTail value**. q∣T gives `(g+c)^7=c^7`. Thus r=(c+g)/c has r^7=1. This forces r≠0 (otherwise 0=1); if r=1, cancellation gives g=0, forbidden. Package r as Units.mk0 r hr0, transfer the power/nonidentity equations by Units.ext and coercion, and use `orderOf_eq_prime` to prove that unit's order is exactly seven. `ZMod.orderOf_units_dvd_card_sub_one` yields 7∣q-1.

The q≠7 parameter is retained to match the scoped branch, with `_hq7` explicitly recording that the root argument itself does not use it. A nontrivial seventh root already forces the divisibility for any prime field satisfying the remaining premises. No Q, coordinate-sum relation or Fermat equation is used by this neutral theorem.

**Order three.** q∤a,b gives nonzero coordinate residues and s=a/b is a unit. q∣Q becomes s²+s+1=0 after denominator clearing. The ring identity s³-1=(s-1)(s²+s+1) gives s³=1. If s=1, the quadratic becomes 3=0; prime q≠3 forbids this. Its unit therefore has order exactly three, and the same finite-group API yields 3∣q-1.

**Intersection.** Order seven excludes q=3 since 7∤2. Apply the third-order theorem with this derived exception, then use the checked Coprime 3 7 and `mul_dvd_of_dvd_of_dvd` to get 21∣q-1. The two root constructions use different ratios and independent nonidentity proofs. A root equation alone is never treated as an exact order statement.

The prime-field, units and finite cardinality APIs are named and sourced in source-inventory-011. The existing finite-unit order theorem encodes Lagrange/Fermat for the cardinality q-1; no new order/cardinality axiom is introduced.

## Exact owner receiver and optional routing

The owner derives q∤a,b from the primitive quadratic coprimality, q∤c from the exact power identity, and q∤g from Step 010's exclusive support together with q∣T. It then applies the neutral intersection. No hidden q∤g hypothesis is added.

The tail receiver needs no coordinate positivity: the local-unit/exclusive-support inputs already suffice. Its stronger signature omits 0<a and 0<b; in particular it applies under the requested positive equation hypotheses. It still exposes the explicit focus relation consumed by the Step 010 support theorem.

The optional routing endpoint does need positive a,b for Step 010 square allocation. If 21∤q-1, the tail receiver rules out q∣T. Reject the tail-square disjunct of the exact allocation, leaving q²∣g and q∤T. This is a branch-sensitive necessary routing statement, not a global restriction on every Q-prime and not a constructed next packet.

## Complete nonvacuous calibrations

All finite arithmetic is checked by ordinary kernel `decide`; no exact Fermat sample is invented.

- **Tail branch:** q=43,(a,b,c,g)=(5,8,9,4). Lean checks a+b=c+g, Coprime a b, Q=129=43*3, q∣Q, q∣T, q∤a*b*c*g, 21∣42 and 42∣42, and the seventh-power equation modulo 43. The neutral intersection is separately applied to these values. The natural exact power inequality is checked in the neutral test; ¬Fermat7Equation 5 8 9 is checked in the owner test after unfolding only that definition. This is modular compatibility, not a positive Fermat solution.
- **Gap branch contrast:** q=13,(a,b,c,g)=(14,29,30,13). Lean checks the coordinate relation, Coprime a b, q∣Q, q∣g, q∤c, q∤T and 21∤12. The owner test independently applies Step 010's head-unit theorem for q∤T. This neutral sample asserts no exact equation and refutes the unguarded order-21 inference over all Q-primes. It does not instantiate the exact square-routing theorem.
- **Standalone seventh order:** q=43,c=1,g=3 has q∣actual GTail and unit endpoint/gap; the neutral order-seven and q≠3 endpoints are applied directly.
- **Standalone third order:** q=7,a=1,b=2 has Q=7 and unit coordinates; the neutral order-three endpoint applies, yielding 3∣6. Excluding seven from the tail branch does not exclude it from the independent third-order theorem.
- **Characteristic three:** q=3,a=b=1 has q∣Q and unit coordinates, but 3∤2. The ratio is explicitly checked equal to one. This verifies the necessity of the q≠3 exception.
- **Zero gap residue at characteristic seven:** g=7,c=2 gives 7∣T and 7∣g, but 7∤6. It cannot supply the required nontrivial seventh root because q∤g fails. No overstrong order theorem is claimed at this boundary.

These counterexamples concern only omitted branch/unit/prime-exception hypotheses; they do not refute the proved neutral or conditional statements. Overall Outcome B remains appropriate.

## Sequential focused builds

Cwd `lean/dk_math`; process-local `LEAN_NUM_THREADS=2`; incremental sequential builds. Full command/exit/duration rows and raw logs are local `.lake/build/gtail-step011/`. No clean/root/facade/full-test build. The command table is appended below from actual run records.

| Command | Exit | Seconds | Local raw log |
| --- | --- | --- | --- |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenPrimeOrder` | 1 | 4.52 | `01-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.Lib.NumberTheory.GTailSevenPrimeOrder` | 0 | 4.63 | `02-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailPrimeOrderAudit` | 0 | 13.83 | `03-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.NumberTheory.GTailSevenPrimeOrder` | 0 | 4.58 | `04-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMath.FLT.Seven.GTailPrimeOrderAudit` | 0 | 14.34 | `05-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeOrderAudit` | 0 | 13.61 | `06-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.CosmicFormula.GTailSevenPrimeAllocation` | 0 | 1.58 | `07-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeAllocationAudit` | 0 | 8.35 | `08-build.log` |
| `LEAN_NUM_THREADS=2 lake build DkMathTest.FLT.Seven.GTailPrimeOrderAudit` | 0 | 13.47 | `09-build.log` |

The initial neutral build found two local elaboration issues: an expected ZMod type reinterpreted GTail as a ring-valued row rather than a natural row cast, and denominator clearing produced a factored quadratic form. Fixed these with the explicit cast `((GTail ... : ℕ) : ZMod q)`, explicit denominator nonzero input and `convert ... <;> ring`. No theorem hypothesis was weakened or limit raised.

The first owner build passed with an unused focus-relation warning. Revised its proof to consume Step 010's actual exclusive-support theorem, as intended, and recover q∤g from the tail support. The final owner/test builds are warning-free. The additional head-unit application in the final owner test was also rebuilt. Both Step 010 direct regression modules pass.

## Axioms, source dependencies and hygiene

All **6/6 new public endpoint** axiom outputs in the final direct tests are exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx/additional axiom. Private helper dependencies are covered by the public endpoint prints. Final new test logs contain no warning/error.

Comment-free import-header closures: neutral owner 1888 source names / 3 local modules, conditional owner 8797 / 17, neutral test 1889 / 4, conditional test 8798 / 18. DFS passes over the union's 19 local modules. Neutral has zero FLT modules; no typed root-depth/Norm/unit carrier owner, closure endpoint or Seven facade is reachable through the new local graph. The complete name sets are in local imports.json. Counts include external terminal names and omit implicit compiler/native dependencies; they are not jobs or proof-hole guarantees over external declarations.

Whole-word sorry/admit/axiom/unsafe, False.elim/exfalso and unconditional FLT impossibility scans are empty for all four new Lean sources. `git diff --check`, new-file trailing-whitespace/final-newline review and protected-file byte checks pass. Historical ledger, prior owners/tests, facades, root driver, LegendreMergedCRT and Lake configuration are unchanged.

## Existing overlap and classification

The neutral GTailCyclotomic shell/homogeneous polynomial APIs identify the scalar row but do not supply the nontrivial finite-field orders; they were inspected and not imported. The scalar additive identity suffices.

Existing `SevenRamifiedFusionCyclotomicPrimeAddress.prime_dvd_quotientRoot_modSeven_eq_one` supplies a seventh-order restriction for a typed RamifiedSignedRootDepthPacket and an integer quotientRoot divisor. It does not automatically identify that divisor with the scalar Q/T support here. `Lib.NumberTheory.ClassGroupTorsionBridge.classGroupPTorsionFreeAt_of_coprime_card` uses generic order/cardinality constraints on a different group; it is not imported as a shortcut. No typed carrier, Norm or unit-class conversion is proved.

This bounded comparison and the independent neutral calibrations support **Outcome B**: checked mechanisms and a correctly guarded scalar necessary condition. No separately validated independent new FLT7 obstruction is claimed.

## Lean結果からの気づき・example・実装提案

1. **確認済み:** q∣Qだけでは位数21は出ません。gap側q=13の校正が反例であり、尾側の非自明な7乗根を確保するq∤gが不可欠です。正確なFLT側では、この条件をStep 010の排他性から取得できました。
2. **確認済み:** q=3で二次式の根は1と重なるため、3乗根の等式だけから位数3を結論できません。尾側の位数7を先に得ると、その境界をq≠3として自動的に除外できます。
3. **確認済み:** 7と3の比はそれぞれ(c+g)/cとa/bです。二つの別の非自明性を証明してから位数を交差させることで、全Q-primeに根を仮定する誤りを避けています。
4. **確認済み:** 尾側のorder receiverには正性が不要ですが、平方のgap routingにはStep 010の非零性が必要で、正性を残しました。付値配分と有限体の位数が消費する前提は異なります。
5. **実装提案（未実施）:** 将来の必要があれば、今回の内部ratio/unitと正確なorderOf証明を構造化した小さい証明書APIにできます。ただし、その証明書を既存の型付きcyclotomic prime addressへ移すには、実際のcarrier/座標対応が別途必要です。今回その変換は実装していません。
6. **比較課題（未実施）:** gap側と尾側の素因子を分類した結果を次候補の構成へつなぐには、根・単元・符号・原始性・正の座標と方程式の保存を同時に保証する必要があります。合同校正はその構成やexact仮定の整合性を与えません。

## Frontier and stop

The historical constraint-ledger-006 remains intact. Its order-21 candidate is now proved **on the tail branch with the explicit/derived local unit premises**, with a neutral gap-side contrast. No global order constraint on g-side primes is inferred. Root/unit carrier transport, global signed/natural reconstruction, constructive next Fermat packet and descent remain open. Stop after Step 011; no broad proof search, all-test build, facade promotion, PR or merge.

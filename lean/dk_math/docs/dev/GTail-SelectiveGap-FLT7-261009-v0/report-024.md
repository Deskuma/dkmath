# Step 024 — guarded native Tail depth-one cutoff

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `bbad4a0924db50073d8a18660cbac9c418e77d93`.
**Step024 COMPLETE / Outcome B**。scalar contraction、finite excess membership、guarded cutoff が成功。
optional scalar reverse direction も含めた iff を証明。

## Mathematical preflight and actual proof gates

Target は prime q、q∤c、q∤g、q|T、q²∤T (T=GTail7 1 g c) の下で、
各 actual integral factor F_i が assigned kernel K_(sixInverseSlot i) に所属し、
その二乗には所属しないという **conditional depth-one cutoff**。
非仮定の q²∤T を証明した結果ではなく、一般 ideal-adic valuation の導入でもない。

Phase0/1: 紙上の elementary route を actual owner の最小 scalar sandbox で検証。
`Ideal.mem_span_singleton_mul` により n∈(q)*K を n=q*y, y∈K に正当に書き直す。
actual coordinates_natCast_mul と coordinate0 の整数値から q|n を得る。
自然数 m を n=q*m の witness として取り、六つの signed coordinates 上で非零整数 q を消去する。
actual additive equivalence の injectivity により y=(m:R)。
actual RingHom の map_natCast と ZMod.natCast_eq_zero_iff により q|m、従って q²|n。
逆向きは q²|n の witness k から y=(q*k:R)∈K を構成。

結果 `natCast_mem_scalar_mul_sixRootKernel_iff` は **全 natural scalar n** に対する iff。
(q)*K と(q²) の ideal equality は使用・主張しない。
scalar multiplication injectivity 自体は prime を必要とせず、q≠0 だけで成立。
Domain/PID/UFD を新 import/仮定せず actual signed coordinate torsionfree proof を使った。
scalar-only focused build は02-build.logで exit0。この gate が通るまで finite-product receiver を追加しなかった。

Phase2: 任意 CommRing、任意 finite indexed ideal family J と x_j∈J_j について、
x_i∈J_i² なら ∏x_j∈(∏J_j)*J_i を証明。
`Finset.prod_erase_mul` で element と ideal の両有限積から selected factor を切り分け、
`Ideal.prod_mem_prod`, `Ideal.mul_mem_mul`, pow_two / associativity を使う。
個々の x_j が J_j の generator であるという仮定はない。
`Fin6≃Fin6` を inverse-slot involution の両 inverse proofs から明示的に構成し、
`Equiv.prod_comp` で同一の kernel family に reindex。
Step022 の genuine six-kernel splitting により ∏J=(q)。
finite product / reindex gate は05-build.logで exit0。

Phase3: Step023 actual element product=GTail と全六 factors の assigned kernel membership を
finite excess lemma に渡し、F_i∈assigned K² ⇒ scalar T∈(q)*assigned K を証明。
Phase1 scalar iff により q²|T を得るため、hT2:q²∤T が selected square を除外。
既存 first-power membership と組にして `gtailCyclotomicFactor_depth_one` を公開。
full source gate は06-build.logで exit0。

## All new public signatures

Namespace `DkMath.FLT.Seven`。7 theorems、new definitions0。以下は実装から抽出。

```lean
theorem cyclotomic_natCast_mul_injective (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (fun z : SevenCyclotomicDegreeSixInt.Ring => (q : _) * z)
```

```lean
theorem natCast_mem_scalar_mul_sixRootKernel_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (j : Fin 6) (n : ℕ) :
    (n : SevenCyclotomicDegreeSixInt.Ring) ∈
      cyclotomicScalarIdeal q * sixRootKernel r hr0 hr7 hr1 j ↔ q ^ 2 ∣ n
```

```lean
theorem prod_mem_prod_mul_of_mem_square {A ι : Type*} [CommRing A] [Fintype ι]
    (J : ι → Ideal A) (x : ι → A) (hx : ∀ j, x j ∈ J j) (i : ι)
    (hi : x i ∈ J i ^ 2) : (∏ j, x j) ∈ (∏ j, J j) * J i
```

```lean
theorem prod_inverseSlot_sixRootKernel_eq_scalarIdeal {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) :
    (∏ i : Fin 6, sixRootKernel r hr0 hr7 hr1 (sixInverseSlot i)) =
      cyclotomicScalarIdeal q
```

```lean
theorem GTail_mem_scalar_mul_kernel_of_factor_mem_square {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6)
    (hi : gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2) :
    ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring) ∈
      cyclotomicScalarIdeal q * sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i)
```

```lean
theorem gtailCyclotomicFactor_not_mem_square {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT2 : ¬ q ^ 2 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2
```

```lean
theorem gtailCyclotomicFactor_depth_one {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT2 : ¬ q ^ 2 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ∧
    gtailCyclotomicFactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2
```

## Numerical, satisfiable and negative controls — 30 examples

- arbitrary signed actual x,y に対する nonzero natural scalar multiplication injectivity、q43 instance。
- 任意 j,n の q43 scalar contraction iff を generic theorem から受信。
  全六 slots で scalar1849=43²∈(43)*K_j、scalar43∉(43)*K_j、scalar0∈(43)*K_j。
- arbitrary finite family の excess membership lemma と inverse-slot product=(43) の受信。
- q43,c9,g4: T=14491387=43*337009、337009%43=18。
  43|T と43²∤T を別々に `decide`。
  全 i の F_i∈assigned K ∧ F_i∉assigned K² は **generic theorem の適用**。
  全五 wrong slots の first-power exclusion、permutation [0,3,4,1,2,5] も受信。
- element ∏F=T と scalar T∈(43)、さらに全 j について T∉(43)*K_j を検証。
  これらは individual span{F_i}=K_j を意味しない。
- **Found and Lean-checked false-guard sample:** q43,c9,g1165。
  q∤c,g、q|T、q²|T が同時に成立し、canonical ratio は同じ11。
  `GTail7 1 1165 9 = 2638461449052811747 = 1849*1426966711223803`。
  Python の有限探索は g=4+43k (0≤k<43) の candidate 探索だけ。
  final test の4 examples が actual GTail value、両端unit/divisibilities、guard否定、ratio11を独立に検証。
  この例に hT2 は存在せず、新 cutoff は適用できない。
  F_i の二乗への実 membership や deeper local multiplicity はこの例では未検証。
- g=0、c=0 でも Step023 unconditional source product は成立。
  scalar43 divides0 なので q-local receiver の nondivisibility guard は失敗する。
- q13 Gap support は Tail support を持たず、ratio1。q7 は非identity scalar seventh root がない。
  old ramified source と今回 bare-root splitting を混同しない。
- `¬ Fermat7Equation 5 8 9` を明示して q43 calibration を exact Fermat solution としない。

## Source/API audit and comparison with old depth owner

[Source inventory](source-inventory-024.md) に actual carrier、proof route、checked names を記録。
principal membership は `Ideal.mem_span_singleton_mul` を使用。
finite-family membership は `Ideal.prod_mem_prod` と `Ideal.mul_mem_mul`、
finite reindex は explicit Equiv と `Equiv.prod_comp`。
scalar proof は `coordinates_natCast_mul`、`coordinates.injective`、整数 `mul_right_inj'`、
Nat cast/divisibility conversions、`mem_sixRootKernel_iff`、`map_natCast`、`ZMod.natCast_eq_zero_iff`。
integer contraction owner も source確認したが、今回は same actual RingHom の natural scalar restriction を直接使用。
これは typed contraction の小さい証明であり packet kernel の仮定ではない。

旧 `SevenRamifiedFusionOrientedCarrierValuationOwnership.carrier_mem_orientedKernelPower_iff`
（namespace/packet context を保持）は
`p.signedDepth.cyclotomicDegreeSixCarrier ∈ s.orientedKernel^k ↔ k≤s.quotientExponent`。
s は `p.QuotientPrimeSupport`、quotientExponent は
`padicValNat s.1 (Int.natAbs p.signedDepth.quotientRoot)`。
旧 source と July30 U1.2 report
`DkMath/FLT/Seven/docs/FLT7-FUSION-004B-U1-2-ORIENTED-CARRIER-VALUATION-OWNERSHIP-REPORT.md`
を読んだ。既存 theorem は exact all-power cutoff、conjugate orientation、real-core valuation と
faithfully-flat contraction、ramified-axis coprimality を含む。
今回の成果を repository初の local depth/valuation theorem と呼ばない。

今回の contract は natural F_i、bare ratio root、六 slots、scalar hT2 だけ。
旧 signed carrier=F_i、s.orientedKernel=assigned bare K、signed quotientRoot valuation=natural GTail valuation
の typed identifications がないため旧 exact iff は直接適用できない。
旧 owner の再実装/追加 import、新 packet reconstruction は不要。
optional FLT reader は追加しなかった。今回 hT2 は caller premise であり Fermat equation から導いていない。

## Exact sequential build evidence

cwd=`/home/deskuma/develop/lean/dkmath/lean/dk_math`。
process-local `LEAN_NUM_THREADS=2` の incremental focused builds。
command/log/exit/time の原記録は ignored `.lake/build/gtail-step024/runs.json`、各 build log は同directory。

P=`DkMath.FLT.Seven.GTailCyclotomicTailDepthOne`
T=`DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne`
R23=`DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct`
R22=`DkMathTest.FLT.Seven.GTailCyclotomicSixRootInterpolation`

各 command は `LEAN_NUM_THREADS=2 lake build <target>`。

| Log | Target | Exit | Seconds | Gate/result |
|---|---|---:|---:|---|
| 01-build.log | P | 1 | 13.98 | scalar reverse cast normalization repaired |
| 02-build.log | P | 0 | 14.81 | scalar cancellation / full contraction iff passed |
| 03-build.log | P | 1 | 14.29 | reindex rewrite elaboration failed |
| 04-build.log | P | 1 | 14.52 | guessed Equiv.ofInvolutive name rejected |
| 05-build.log | P | 0 | 14.95 | finite excess / explicit Equiv reindex passed |
| 06-build.log | P | 0 | 14.81 | full guarded depth-one source passed |
| 07-build.log | T | 1 | 15.5 | dependent root rewrite in numeric test rejected |
| 08-build.log | T | 0 | 16.74 | 30 examples / all7 axiom outputs passed |
| 09-build.log | R23 | 0 | 8.49 | Step023 regression passed |
| 10-build.log | R22 | 0 | 8.15 | Step022 regression passed |

Failed attempts は保持した。01: reverse scalar witness の nested Nat casts が残り、
`rw` の固定回数では cast(q*q) を展開し切れなかった。`push_cast; ring` に修正し02成功。
03/04: 推測した `Equiv.ofInvolutive` は actual imported environment に存在しない。
rewrite の未確定項を明示して名前エラーを確認後、inverse maps と両 inverse proofs を持つ
explicit `Equiv` に置き換え05成功。存在しない API を最終 code/inventory の verified names に含めない。
07: root r に依存する kernel proof arguments のため `rw [ratio11] at hm` は motive error。
明示した actual q43 iff へ `simpa only [ratio11] using hm` で transport して08成功。
数学的 guard/結論を弱めず、proof-limit option を追加しない。final06/08 logs の warning は0。

## All public axiom outputs

Final08 test の全7 outputs。標準論理公理だけで sorryAx/新公理なし。

```text
cyclotomic_natCast_mul_injective: [propext, Classical.choice, Quot.sound]
natCast_mem_scalar_mul_sixRootKernel_iff: [propext, Classical.choice, Quot.sound]
prod_mem_prod_mul_of_mem_square: [propext, Classical.choice, Quot.sound]
prod_inverseSlot_sixRootKernel_eq_scalarIdeal: [propext, Classical.choice, Quot.sound]
GTail_mem_scalar_mul_kernel_of_factor_mem_square: [propext, Classical.choice, Quot.sound]
gtailCyclotomicFactor_not_mem_square: [propext, Classical.choice, Quot.sound]
gtailCyclotomicFactor_depth_one: [propext, Classical.choice, Quot.sound]
```

## Dependency, preservation and style checks

production の direct import は Step023 owner 一つ、test は今回 owner 一つ。
comment/string 除去後 local/Mathlib source import graph を追跡。
neutral GTailSevenRealTraceResidue:1907 modules/local20、FLT dependencies0。
production:8932/local152、test:8933/local153。local union153 vertices の DFS cycle0。
external source のない依存名は leaf。repository/package全体の graph claim はしない。
new production は Step023 closure から今回 owner 一つの追加。
full FLT.Seven facade、Domain、old global oriented factorization、old oriented valuation、Kummer、QR bridge の
owners は new owner/test closure に含まれない。既存 heavy carrier closure と narrow direct imports を区別する。

MIT2026/Authors header、imports後 file print、namespace/2space code style を維持。
新二 Lean files の comment/string 除去後 whole-word sorry/admit/axiom/unsafe/native_decide、False.elim、set_option は0。
`git diff --check` と新四 files の no-index whitespace check、ROADMAP append-only 検査を実施。
tracked edit は ROADMAP の post023 append のみ。旧 rings / signed owners / root drivers / facades / ledger は変更しない。
axiom audit は今回の7 public declarations の依存結果であり、全 repository の axiom-free 性を主張しない。

## Lean-derived observations and bounded proposals

1. **Confirmed:** actual six-dimensional integral coordinates により非零 natural scalar の cancellation を
   Domain hierarchy の追加 import なしで証明できた。q≠0 は scalar lemma に明示され、prime q では自動充足。
2. **Confirmed:** scalar iff は n=0 も含み、full ideal equality より弱いが main cutoff に必要十分。
   ideal (q)*K が(q²) と等しいという推論は不要であり、採用しない。
3. **Confirmed:** excess-factor lemma 自体は arbitrary finite CommRing family に成立。
   kernel maximality、primality、principality を要求しない。splitting と arithmetic contraction は別々に適用する。
4. **Confirmed:** valid Tail input でも q²|T はあり得る。c9,g1165 の実数値例が hT2 を独立した
   arithmetic assumption として維持する必要性を示す。深い factor multiplicity は未解決。
5. **Proposal only / unproved here:** signed scalar contraction の ℤ version や、higher excess copies の
   finite membership lemma は自然な reusable API 候補。ただし新しく一般 exact valuation を導入するには
   scalar contraction / factor ownership の追加証明が要る。今回それらは実装しない。

**Outcome B**: native natural GTail の satisfiable squarefree-at-q guard による actual selected prime-square exclusion。
unit/class-group、individual factor principalization、signed packet construction、primitive counterexample reconstruction、
FLT7 descent / unconditional closure は結論しない。**STOP after Step024**。

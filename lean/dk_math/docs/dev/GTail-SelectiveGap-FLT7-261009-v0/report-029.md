# Step029 — actual selected cyclotomic cube membership

2026-10-10. **COMPLETE / Outcome B**.
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
Base HEAD `2f205a77ff859ace37ee3fa67b70e149a2f602c3`。
review028/report028/inventory028を確認。reviewはstatic inspection、独立rebuildではない。

## Verified endpoint and exact scope

Actual R=SevenCyclotomicDegreeSixInt.Ring、canonical Tail prime/unit/support contractのもとで、全i:Fin6:

```text
F_i(c,g) ∈ K_(sixInverseSlot i)^3 ↔ q³ ∣ GTail 7 1 g c.
```

Supplied nonzero nonidentity seventh rootを持つ各K_jについて、全natural scalar n:

```text
(n:R)∈K_j² ↔ q²∣n,
(n:R)∈K_j³ ↔ q³∣n.
```

Step028のscalar q³ supportを actual ideal K³ receiver に接続。
これはbounded selected-factor theorem、valuation functionやprincipalizationではない。
K⁴ exclusion、all-k selected valuation、FLT7 obstruction/descentは証明していない。

## Complement and ideal-intersection algebra

Single definition `sixRootKernelComplement` J_j=erased other-five-kernel product。
`Finset.prod_erase_mul` と actual six-kernel productで K_j*J_j=cyclotomicScalarIdeal q。
`IsCoprime.prod_right` の premiseは erased membership h≠j と Step021 の各pair sup=top。
J_jが異なるというだけでcomaximalityを仮定していない。
`Ideal.pow_sup_eq_top`で K_j^n⊔J_j=top（n=0も含む）を取得。
これはideal algebraのpower-sup factで、selected factorのall-k valuationではない。

Private generic CommRing helper（I⊔J=top、n≠0）のproof:
I^n∩J=I^n*J は現行 `Ideal.mul_eq_inf_of_isCoprime` のsymm。
I*J≤Jから I^n∩(I*J)≤I^n∩J。
逆は I^n*J≤I^n と I^n≤I の `Ideal.mul_mono` による I^n*J≤I*J。
これにより **I^n∩(I*J)=I^n*J**。
Power2/3でspecializeしcommutative ideal multiplicationをregroup:

```text
K²∩(q)=K²*J=(q)*K,
K³∩(q)=K³*J=(q)*K².
```

Deprecated inf_eq_mul_of_isCoprime は使用せず、実際のcurrent APIを使用。
No global K^n=(q^n) or (q)*K=(q²) claim。

## Scalar contraction in the actual torsionfree carrier

Private scalar-support helperは kernel membershipを actual RingHom evaluationでzeroにし、
map_natCast / ZMod.natCast_eq_zero_iffでq∣nを取得。natural witness n=q*m によりembedded n∈(q)。

Square forward: Ideal.pow_le_selfでK²≤K、scalar supportを得てintersection identityから n∈(q)*K。
既存 Step024 `natCast_mem_scalar_mul_sixRootKernel_iff` により q²∣n。
Square reverse: Step025既存 scalar square theorem。

Cube forward: K³≤Kでn=q*m。intersection identityで n∈(q)*K²。
`Ideal.mem_span_singleton_mul` は y∈K²と(q:R)*y=(n:R)を与える。
Nat.cast_mulによりright side=(q:R)*(m:R)。
**既存 cyclotomic_natCast_mul_injective**（six signed integral coordinates、prime q≠0）で y=cast(m)。
Scalar square contractionから q²∣m、natural witnessesを合わせq³∣n。
このcancellationはactual Rのcoordinate proofに限定し、IsDomain/DVR hypothesisを追加していない。
Cube reverse: q∈K、Ideal.pow_mem_powでq³∈K³、ideal multiplication closureで全q³ multiples。

## Selected factor saturation

Actual U_i∉K と U_i*F_i=cast(T) を Step025から使用。
Forward F_i∈K³ → U_i*F_i∈K³は Ideal.mul_mem_left。
Reverseは K.IsMaximal instance と実際の `Ideal.IsMaximal.mul_mem_pow K h`、
そのdisjunctionを U_i∉Kでresolve_left。
U_iがglobal ring Rでunitであるとは主張しない。
Product equalityをrewriteし、new scalar cube contractionでmandatory iff。

## Calibration and observations

25 new examples:

| gap g | Scalar support | Actual selected factors (all six) |
|---:|---|---|
| 4 | 43∣T, 43²∤T | F_i∈K、F_i∉K²、F_i∉K³ |
| 1165 | 43²∣T, 43³∤T | F_i∈K²、F_i∉K³ |
| 32598 | 43³∣T, 43⁴∤T | F_i∈K³、K⁴ exclusion UNPROVED |

Cube membership/exclusionsは **generic selected cube iff** のspecializations。
Positive cubic supportは Step028 native linear criterion → existing polynomial finite-digit API。
q43 scalar arithmeticのdecideだけを ideal membership proofの代わりにはしていない。
三gapのratio11を全て確認。Inverse permutation[0,3,4,1,2,5]も検証。
三gap全てのwrong-slot exclusionsはexisting unique-slot theoremから取得。

All slotsのscalar43³∈K³、scalar43²∉K³、scalar43²∈K²、zero∈K³をnew scalar iff/ideal APIで確認。
Complement product、power-sup、square/cube intersection identitiesもall-slot tests。
New g32598全六cofactor readout28をgeneric formulaで検証。
Step028 generic Fin43 uniquenessとpositive supportによりsecond digit17を再確認。
Scalar43⁴ nondivisibilityは別のdecide regression、ideal K⁴についての結論ではない。
Step028 regressionはderivative28/ratio11/first digit27等のchainも維持。
q7nonidentity-root absence、q13missing Tail support、unit zero failure、unconditional g0 source product、
a5/b8/c9 Fermat equation falseを確認。

Lean結果からの気づき: scalar contractionはroot slotによらず同じq³ conditionになるが、
actual factor receiverはinverse permutationで選択される。scalar theoremとfactor theoremの量化・対象を分ける必要がある。
また、cofactor非zero readout28はcube membershipとも両立する。
第一・第二段階の有限体simple-root dataはhigher source membershipを禁止しないというStep026の説明が、
今回actual K³ receiverでも具体化された。

実装提案（未実施）: 将来signed scalar contractionが必要になった場合、整数nの符号とnatural witnessのtransportを
独立に設計できる。今回public APIsはnatural scalarのみ。
Private generic intersection lemmaはneutral ideal algebraに移せる可能性があるが、
今回source scopeとimportを増やす必要はないためowner内に留めた。
このgeneric algebra helperが任意positive nに成立しても、higher selected-factor contraction/valuationは別proof contract。
今回K⁴ cutoffを推論しない。

## Old ownership overlap boundary

Old SevenRamifiedFusionOrientedCarrierValuationOwnership.orientedKernelPower_dvd_span_carrierは
PrimeSupport family p、signedDepth carrier、oriented/conjugate packet dataに依存。
新APIはbare natural c,g、canonical root、actual F_i/U_iであり、そのpacketを構成していない。
Comparisonのみで旧ownerはimport/editしない。
Classical comaximal ideal splitting + integral scalar contractionとしてOutcome B。
新Dedekind/DVR theoremやFLT7 descentとして扱わない。

## Public signatures (9: one definition, eight theorems)

Namespace DkMath.FLT.Seven。実装から抽出。

```lean
noncomputable def sixRootKernelComplement {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) : Ideal Ring
```

```lean
theorem sixRootKernel_mul_complement {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) :
    sixRootKernel r hr0 hr7 hr1 j * sixRootKernelComplement r hr0 hr7 hr1 j =
      cyclotomicScalarIdeal q
```

```lean
theorem sixRootKernel_sup_complement {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) :
    sixRootKernel r hr0 hr7 hr1 j ⊔ sixRootKernelComplement r hr0 hr7 hr1 j = ⊤
```

```lean
theorem sixRootKernel_pow_sup_complement {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) (n : ℕ) :
    sixRootKernel r hr0 hr7 hr1 j ^ n ⊔ sixRootKernelComplement r hr0 hr7 hr1 j = ⊤
```

```lean
theorem sixRootKernel_square_inf_scalar {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) :
    sixRootKernel r hr0 hr7 hr1 j ^ 2 ⊓ cyclotomicScalarIdeal q =
      cyclotomicScalarIdeal q * sixRootKernel r hr0 hr7 hr1 j
```

```lean
theorem sixRootKernel_cube_inf_scalar {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) :
    sixRootKernel r hr0 hr7 hr1 j ^ 3 ⊓ cyclotomicScalarIdeal q =
      cyclotomicScalarIdeal q * sixRootKernel r hr0 hr7 hr1 j ^ 2
```

```lean
theorem natCast_mem_sixRootKernel_square_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) (n : ℕ) :
    (n : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 2 ↔ q ^ 2 ∣ n
```

```lean
theorem natCast_mem_sixRootKernel_cube_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) (n : ℕ) :
    (n : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 3 ↔ q ^ 3 ∣ n
```

```lean
theorem gtailCyclotomicFactor_mem_cube_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 3 ↔
      q ^ 3 ∣ GTail 7 1 g c
```

## Sequential focused build evidence

全commandsはlean/dk_math、process-local LEAN_NUM_THREADS=2。
Ignored local logs `.lake/build/gtail-step029/`、exact commands/exits/timeはruns.json。

| Log | Target after `LEAN_NUM_THREADS=2 lake build` | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDepthThree` | 0 | 16.46 |
| 02-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDepthThree` | 0 | 15.62 |
| 03-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDepthThree` | 0 | 16.6 |
| 04-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthThree` | 0 | 18.78 |
| 05-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit` | 0 | 8.25 |
| 06-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailTaylorLift` | 0 | 8.23 |

Phase1 algebra gate01成功（unused mul_one warning1）。Unused simp argumentを除去。
Phase2 scalar contraction gate02成功、Phase3 mandatory selected iff/source03成功。
New tests04、Step028 regression05、Step027 regression06成功。Final source/test warning0。
Lean errorによるfailed buildは今回なし。Signature guessing/global resource workaroundsは使用していない。

## Axioms/imports/preservation audits

9 public #print axioms全件standard propext/Classical.choice/Quot.soundのみ。
New axiom / sorryAxなし。新source/testのcomment/string除外scan:
sorry/admit/axiom/unsafe/native_decide/set_option/False.elim=0。
MIT2026header、import後file-print、既存2-space styleを維持。

Neutral GTailSevenRealTraceResidue closure1907/local20、new owner8938/local158、new test8939/local159。
Local union159 vertices cycle0、neutral→FLT0。
Step028 source closureとの差はnew owner1のみ、added Mathlib0、removed0。
Full FLT.Seven facade、degree-six Domain、global oriented factorization、oriented valuation ownership、
Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridgeはnew source/test closureにない。
imports.json / import-impact.json / audit.jsonに検査結果。

git diff --check、新4files whitespace check成功。ROADMAP historical prefixを保持したpost028 append。
既存Lean owner、generic neutral API、facades、ring/ideal definitions、signed packets、reviews/ledgerは変更なし。
No all-k selected valuations, K⁴ cutoff, p-adic completion, integral ring transfer, packets,
class/unit-power extraction, primitive Fermat tuple or unconditional FLT7 closure。Step029で停止。

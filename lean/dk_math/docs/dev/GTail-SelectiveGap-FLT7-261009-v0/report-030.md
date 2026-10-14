# Step030 — fourth-power firewall and bounded exact third depth

2026-10-10. **COMPLETE / Outcome B**。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
Base HEAD `b6debb8dfc381a7493c4230dc6548865baf341a4`。
review029/report029/inventory029を確認。reviewはstatic inspection、独立rebuildではない。

## Verified endpoint

Actual R=SevenCyclotomicDegreeSixInt.Ring、supplied nonzero nonidentity seventh root、prime q、各slot j:

```text
K_j⁴ ∩ cyclotomicScalarIdeal q = cyclotomicScalarIdeal q * K_j³,
(n:R)∈K_j⁴ ↔ q⁴∣n                      (n:ℕ).
```

Canonical natural Tail q-unit/support contract（q∤c,g、q∣T）で全i:Fin6:

```text
F_i(c,g)∈K_(sixInverseSlot i)⁴ ↔ q⁴∣GTail 7 1 g c.
q³∣T ∧ ¬q⁴∣T → F_i∈K_assigned³ ∧ F_i∉K_assigned⁴.
```

q43,c9,g32598で全六因子の **K³所属・K⁴非所属** が確認された。
Exact depth threeはこのbounded membership cutoffの意味。一般valuation functionやprincipalizationは導入していない。

## Proof gates and exact dependencies

Step029のprivate `pow_inf_mul_of_comaximal` と `scalar_support_of_kernel_mem` は公開識別子として参照しない。
新owner内で同じshort private proofを独立recheck。Compiler-generated private nameは使用せず、旧owner変更なし。
Private generic intersection proofはI⊔J=top、n≠0のCommRing ideal algebraだけ。
Public intersectionはn=4のみ。

K*J=(q) はStep029 public sixRootKernel_mul_complement。
K⁴∩J=K⁴*Jは Ideal.pow_sup_eq_top / isCoprime_iff_sup_eq / mul_eq_inf_of_isCoprime。
K*J≤J と K⁴≤K、Ideal.mul_mono / mul_le_left による両包含で K⁴∩(K*J)=K⁴*J。
Powersを展开・ac_rflでregroupし K⁴*J=(K*J)*K³=(q)*K³。
No IsDomain/Dedekind/DVR/Principal hypotheses。Whole-ideal K⁴=(q⁴) や (q)*K³=(q⁴)は主張しない。

Scalar forward:
K⁴≤K、actual RingHom evaluation / map_natCast / ZMod.natCast_eq_zero_iffでq∣n。
Natural witness n=q*mでembedded n∈(q)。Intersection identityから n∈(q)*K³。
Ideal.mem_span_singleton_mulでactual y∈K³、(q:R)*y=(n:R)。
Step024 cyclotomic_natCast_mul_injective（six signed integral coordinates、q≠0）でy=cast(m)。
Step029 public natCast_mem_sixRootKernel_cube_iffでq³∣m、natural witnessesを合わせq⁴∣n。
Cancellationはactual RのみでありZMod qやarbitrary CommRingではない。

Reverse: q∈Kをactual evaluationで証明、Ideal.pow_mem_powでq⁴∈K⁴、ideal multiplication closureでq⁴倍数。
Selected factor iff: Step025 actual U_i∉K、U_i*F_i=cast(T)、Step021 maximality。
ForwardはIdeal.mul_mem_left、reverseはIdeal.IsMaximal.mul_mem_pow（n=4）のdisjunctionをU_i nonmemberでresolve。
U_iがglobal R unitであるとは仮定しない。
最後にscalar iffを適用。Depth-three pairは既存cube iffとnew fourth iffのみから構成。

## Calibration and Lean-derived observations

38 examples（prior bounded casesを保持してfourth-power casesを追加）。

| gap g | Scalar support | All six actual selected factors |
|---:|---|---|
| 4 | 43∣T, 43²∤T | K所属、K²/K³/K⁴非所属 |
| 1165 | 43²∣T, 43³∤T | K²所属、K³/K⁴非所属 |
| 32598 | 43³∣T, 43⁴∤T | K³所属、K⁴非所属 |

Positive scalar cube supportはStep028 native linear lift criterion（existing finite polynomial API経由）。
New selected fourth iff / bounded cutoffから全六のnew ideal nonmembershipを証明。
数値scalar decideをactual ideal theoremの代用にはしていない。

All slotsで scalar43⁴∈K⁴、scalar43³∉K⁴、zero∈K⁴、fourth intersection identityをgeneric theoremで確認。
三gapのratio11、inverse permutation[0,3,4,1,2,5]、全wrong-slot first-power exclusionsを維持。
三gapのderivative28と全六cofactor readout28をgeneric formulaで確認。
既存second digit17 uniqueness、scalar43⁴ failure、q7例外、q13Tail-support failure、zero-unit failure、
unconditional g0 source element product、false Fermat tupleを保持。
Step028 regressionはfirst digit27→second17の二段階scalar chainを再確認。
第三Hensel correctionは計算していない。

気づき: Step029で保留したK⁴非所属は、今回のscalar-specific contractionとcofactor saturationを通すことで初めて
source-typedな結論になった。Numerical43⁴非整除だけではその結論を得られない。
今回もfinite-field derivative/cofactor28は変わらず、bounded exact source ideal depthの違いと両立する。

## Distinct frontier reassessment proposal (not implemented)

Step030で停止し、次はK⁵への延長ではなく別checkpointとして接続のfrontierを再評価することを提案する。

1. Eisenstein Q² / focused GTail product側とdegree-six cyclotomic prime-root address側の
   **実際のsource signatures・carrier・整数readout・q-unit/support・符号/正規化条件**を並べる。
2. 共通の整数または有限体readoutを選ぶ場合、既存のnorm/evaluation等のどの写像を使うかを明示し、
   同じoriginal GTail arithmetic quantityを読んでいることをsource-typed equality/congruenceとして証明する。
3. 一方のsquare/focused supportから他方のroot/kernel conditionへ何が移るかを個別に検証する。
   必要な追加premiseや失われる情報を明示し、Eisenstein→cyclotomic integral ring homやsigned-depth packetを仮定しない。
4. 得られたbridgeが既存scalar supportの再表現か、新しい必要条件を与えるかを比較する。
   実際のFermat counterexampleに適用するには別途source-typed入力契約が必要。

この提案のcarrier transfer/class/unit extraction/packet constructionは今回実装していない。
旧oriented valuation ownerはPrimeSupport family pとsignedDepth carrierを持つ別契約で、比較のみ。
Bare c,gからそのpacketは作っていない。Classical split-prime arithmeticとしてOutcome B。

## Public signatures (4 theorems)

Namespace DkMath.FLT.Seven、実装から抽出。

```lean
theorem sixRootKernel_fourth_inf_scalar {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) :
    sixRootKernel r hr0 hr7 hr1 j ^ 4 ⊓ cyclotomicScalarIdeal q =
      cyclotomicScalarIdeal q * sixRootKernel r hr0 hr7 hr1 j ^ 3
```

```lean
theorem natCast_mem_sixRootKernel_fourth_iff {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1) (j : Fin 6) (n : ℕ) :
    (n : Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 4 ↔ q ^ 4 ∣ n
```

```lean
theorem gtailCyclotomicFactor_mem_fourth_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 4 ↔
      q ^ 4 ∣ GTail 7 1 g c
```

```lean
theorem gtailCyclotomicFactor_depth_three {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT3 : q ^ 3 ∣ GTail 7 1 g c) (hT4 : ¬ q ^ 4 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 3 ∧
    gtailCyclotomicFactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 4
```

## Focused sequential build evidence

All commands: lean/dk_math、process-local LEAN_NUM_THREADS=2。
Ignored local logs `.lake/build/gtail-step030/`、exact commands/exits/timingはruns.json。

| Log | Target after `LEAN_NUM_THREADS=2 lake build` | Exit | Seconds |
|---|---|---:|---:|
| 01-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDepthFour` | 0 | 15.26 |
| 02-build.log | `DkMath.FLT.Seven.GTailCyclotomicTailDepthFour` | 0 | 14.58 |
| 03-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour` | 0 | 16.82 |
| 04-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthFour` | 0 | 16.83 |
| 05-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailDepthThree` | 0 | 8.19 |
| 06-build.log | `DkMathTest.FLT.Seven.GTailCyclotomicTailSecondDigit` | 0 | 8.33 |

01はintersection/scalar fourth/selected fourth iffを一緒に確認したsource build、02はbounded cutoffを追加したfinal source。
03は33 examples、04は三gapのreadout/derivative checksを補った38 examplesのfinal test。
05 Step029、06 Step028 direct regressions。全exit0、final source/test warning0。
Failed proof gateなし。Intermediate repairはcopied theorem docstringのcubic→fourth-power校正のみで、
proof/resource-limit workaroundは不要だった。

## Public axioms and import/style audits

All4 public #print axioms:
- `sixRootKernel_fourth_inf_scalar`: `[propext, Classical.choice, Quot.sound]`
- `natCast_mem_sixRootKernel_fourth_iff`: `[propext, Classical.choice, Quot.sound]`
- `gtailCyclotomicFactor_mem_fourth_iff`: `[propext, Classical.choice, Quot.sound]`
- `gtailCyclotomicFactor_depth_three`: `[propext, Classical.choice, Quot.sound]`

New axiom / sorryAxなし。新source/testのcomment/string除外token scanで
sorry/admit/axiom/unsafe/native_decide/set_option/False.elim=0。
MIT2026header、import後file-print、既存2-space style維持。

Neutral GTailSevenRealTraceResidue closure1907/local20、new source8939/local159、new test8940/local160。
Local union160vertices cycle0、neutral→FLT0。
Step029比new local owner1のみ、added Mathlib0、removed0。
Full FLT.Seven facade、degree-six Domain、global oriented factorization、oriented valuation ownership、
Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridgeは新source/test closureにない。
imports.json / import-impact.json / audit.jsonに記録。

git diff --check、新4files whitespace check成功、ROADMAP historical prefixを保持。
既存source owners/facades/ring definitions/signed-depth files/reviews/ledgerは変更なし。
No all-suite build、global options、K⁵/all-k hierarchy、p-adic completion、integral carrier transfer、
class/unit extraction、primitive Fermat descent or unconditional FLT7 closure。Step030で停止。

# Step 025 — exact selected second-power membership

Date: 2026-10-10. Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`.
Base HEAD `8dbcac8169005b23f1f370d73e289e71b85ce26a`.
**Step025 COMPLETE / Outcome B**。generic maximal square saturation、cofactor gate、reverse implication と exact iff が成功。

## Checked mathematical endpoint

Prime q、natural c,g、hc:q∤c、hg:q∤g、hT:q|GTail を前提として、
r=gtailSevenTailRatio q c g、J_i=sixRootKernel r ... (sixInverseSlot i) に対して

```text
F_i(c,g) ∈ J_i² ↔ q² ∣ GTail 7 1 g c
```

を actual existing degree-six integral ring で証明した。
Step024 の forward implication を再利用し、今回 missing reverse を独立に証明。
旧 guard theorem と historical Step024 の記録は変更しない。
q²|T は普遍的な結論ではなく、この bounded second-level membership と同値な arithmetic input。
J³ membership や higher multiplicity は今回未解決。

## Proof gates and exact method

**Gate1**: `mem_maximal_square_of_mul_mem` は arbitrary CommRing A、actually maximal J、U∉J の下で
U*x∈J² ⇒ x∈J² を証明する。
Mathlib actual `Ideal.IsMaximal.mul_mem_pow` を n=2 で受信し、membership disjunction の左側を hU で除く。
その source proof を検査した：`Ideal.IsMaximal.exists_inv_pow J hU 2` が
∃a,∃b∈J²,a*U+b=1 の actual witness を作り、その式を x 倍して ideal add/mul closure で結論を得る。
exists_inv_pow 自体は maximality の `Ideal.IsMaximal.exists_inv` から Bézout pair を取り、
powered remainder と幾何 recurrence で証明されている。

この witness は principal(U) と J² の comaximality の具体的証拠であり、
新 span-sup theorem を重複実装する必要はなかった。
zero divisors、nonprincipal maximal ideal、unit U を排除せず、IsDomain/PID は仮定しない。
merely J.IsPrime で同じ saturation を主張しない。
単独 Gate1 build は02-build.logで exit0。成功するまで selected factors は追加しなかった。

**Gate2**: actual five-factor cofactor を Finset.univ.erase i で定義。
Step023 unique-slot iff と involution injectivity により、erase family の **全五 factors** が selected J_i の外。
actual J_i.IsPrime と `Ideal.IsPrime.prod_mem_iff` で cofactor 全体も外。
`Finset.prod_erase_mul` と Step023 actual source product により U_i*F_i=(T:R)。
cofactor/multiplication gate は03-build.logで exit0。

**Gate3**: scalar q∈J_i は actual RingHom の map_natCast / ZMod divisibility iff で証明。
`Ideal.pow_mem_pow` で scalar q²∈J_i²、その ideal の multiplication closure で
q²|T の witness k に対する scalarT∈J_i²。
cofactor product equality で U_i*F_i に戻し、Gate1 maximal saturation を適用して reverse theorem。
Step024 excess-product membership と scalar contraction iff を forward direction として exact iff を組む。
full Gate3 source は04-build.logで exit0。
(q)*J_i=(q²) や span{F_i}=J_i を使わず、新 signed packet も作らない。

## All new public signatures

Namespace `DkMath.FLT.Seven`。1 definition、6 theorems、計7宣言。actual source から抽出。

```lean
theorem mem_maximal_square_of_mul_mem {A : Type*} [CommRing A] (J : Ideal A)
    (hJ : J.IsMaximal) (U x : A) (hU : U ∉ J) (hProd : U * x ∈ J ^ 2) :
    x ∈ J ^ 2
```

```lean
def gtailCyclotomicCofactor (c g : ℕ) (i : Fin 6) : SevenCyclotomicDegreeSixInt.Ring
```

```lean
theorem gtailCyclotomicCofactor_mul_factor (c g : ℕ) (i : Fin 6) :
    gtailCyclotomicCofactor c g i * gtailCyclotomicFactor c g i =
      ((GTail 7 1 g c : ℕ) : SevenCyclotomicDegreeSixInt.Ring)
```

```lean
theorem gtailCyclotomicCofactor_not_mem_selected {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    gtailCyclotomicCofactor c g i ∉
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i)
```

```lean
theorem natCast_mem_sixRootKernel_square_of_sq_dvd {q : ℕ} [Fact (Nat.Prime q)]
    (r : ZMod q) (hr0 : r ≠ 0) (hr7 : r ^ 7 = 1) (hr1 : r ≠ 1)
    (j : Fin 6) (n : ℕ) (hn : q ^ 2 ∣ n) :
    (n : SevenCyclotomicDegreeSixInt.Ring) ∈ sixRootKernel r hr0 hr7 hr1 j ^ 2
```

```lean
theorem gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (hT2 : q ^ 2 ∣ GTail 7 1 g c) (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2
```

```lean
theorem gtailCyclotomicFactor_mem_square_iff {q : ℕ} [Fact (Nat.Prime q)]
    (c g : ℕ) (hc : ¬ q ∣ c) (hg : ¬ q ∣ g) (hT : q ∣ GTail 7 1 g c)
    (i : Fin 6) :
    gtailCyclotomicFactor c g i ∈
      sixRootKernel (gtailSevenTailRatio q c g)
        (gtailSevenTailRatio_ne_zero hc hT) (gtailSevenTailRatio_pow_seven hc hT)
        (gtailSevenTailRatio_ne_one hc hg) (sixInverseSlot i) ^ 2 ↔
      q ^ 2 ∣ GTail 7 1 g c
```

## Strong calibration — 27 examples

Generic saturation は arbitrary CommRing/maximal J の test receiver と U=1 の unit case を検証。
no IsDomain/nonprincipal exclusion は actual signature と Mathlib witness proof で確認した。
zero-divisor ring の具体的 maximal ideal を新定義する numeric example は今回は実施していない。

| q,c,g | Natural T | q² support | All six selected factor squares |
|---|---:|---|---|
| 43,9,4 | 14491387 | absent | all excluded by new generic iff |
| 43,9,1165 | 2638461449052811747 | present | all included by new generic reverse theorem |

両例の canonical ratio11 を別 theorem で確認。
positive case は q∤9、q∤1165、q|T、q²|T を checked `decide` で得てから、
**全 i:Fin6 の actual ideal-square membership を generic reverse theorem の適用で証明**。
finite field の decide を ideal-power membership の代用にはしない。
negative case は新 iff から全六二乗非所属を得るとともに、旧 Step024 first-order certificate も受信した。

g1165 でも全五 wrong first-order kernel slots に factor は属さない。
permutation [0,3,4,1,2,5] は unchanged。
scalar1849∈K_j² も全六 slots で generic scalar theorem から受信した。
actual cofactor*factor=T は arbitrary c,g,i の source equality として受信し、g1165 element product も受信。
両ケースの全六 cofactors が selected kernels の外にあることを general theorem で確認。

**Additional checked observation:** selected root における cofactor RingHom value は両ケースとも全六 i で28。
actual RingHom を map_prod と actual factor evaluation theorem で有限 field expression に変換し、
二つの forall-Fin6 examples を `decide` で検証。cofactor nonmembership の一般証明はこの数値28に依存しない。

Boundaries: g0 の unconditional product、c0,g1 の product1 は Step023 theorem で成立。
q43 divides0 なのでこれらを canonical nondivisibility contract の証明には使わない。
q13 Gap ratio1 と q∤Tail、q7 no nonidentity seventh scalar root を確認。
q7 の old ramified ζ↦1 address を今回六-root branch と同一視しない。
`¬ Fermat7Equation 5 8 9` を別 example で確認。

## Exact APIs, source overlap and preservation of mathematical types

[Source inventory](source-inventory-025.md) に API gates を記載。
`Ideal.IsMaximal.exists_inv`, `Ideal.IsMaximal.exists_inv_pow`, `Ideal.IsMaximal.mul_mem_pow`
の actual source を読み、maximality が powered ideal saturation を保証することを確認。
`IsCoprime.pow_right` も source確認したが、今回 existing maximal saturation がより直接的。
`Ideal.IsPrime.prod_mem_iff`, `Finset.mem_erase`,
`sixInverseSlot_involutive.injective`, `Finset.prod_erase_mul`, `Ideal.pow_mem_pow`,
`Ideal.mul_mem_right`, `map_natCast`, `ZMod.natCast_eq_zero_iff`, Nat cast APIs を使う。

旧 `SevenRamifiedFusionOrientedCarrierValuationOwnership.carrier_mem_orientedKernelPower_iff`
と July30 U1.2 report
`DkMath/FLT/Seven/docs/FLT7-FUSION-004B-U1-2-ORIENTED-CARRIER-VALUATION-OWNERSHIP-REPORT.md`
を comparison-only で再確認。
旧 theorem は p.signedDepth carrier、s:p.QuotientPrimeSupport、all-k exact padicValNat cutoff。
今回 natural F_i / bare canonical ratio root / selected kernel / natural GTail と旧 carrier/kernel/quotientRoot
の typed identifications はない。旧 result を新 reverse theorem の proof として利用しない。
repository初の valuation result とは呼ばず、natural branch の bounded second-level iff と分類する。

Scalar ideal、kernel power、individual principal factor ideal、element product は異なる対象。
今回 scalarT∈J² は membership であり ideal equality ではない。
F_i∈J_i² から factor が J_i を生成するとは結論しない。

## Exact sequential build evidence and repair

cwd=`/home/deskuma/develop/lean/dkmath/lean/dk_math`。
process-local LEAN_NUM_THREADS=2 の incremental focused builds。
raw commands/exits/times は ignored `.lake/build/gtail-step025/runs.json`、build logs は同directory。

P=`DkMath.FLT.Seven.GTailCyclotomicTailDepthTwo`
T=`DkMathTest.FLT.Seven.GTailCyclotomicTailDepthTwo`
R24=`DkMathTest.FLT.Seven.GTailCyclotomicTailDepthOne`
R23=`DkMathTest.FLT.Seven.GTailCyclotomicTailFactorProduct`

各 command は `LEAN_NUM_THREADS=2 lake build <target>`。

| Log | Target | Exit | Seconds | Gate/result |
|---|---|---:|---:|---|
| 01-build.log | P | 1 | 15.07 | maximal API qualification repaired |
| 02-build.log | P | 0 | 15.68 | generic saturation-only gate passed |
| 03-build.log | P | 0 | 15.67 | cofactor gate passed |
| 04-build.log | P | 0 | 15.35 | reverse / exact iff source passed |
| 05-build.log | T | 0 | 17.77 | 27 examples / all7 public axioms passed |
| 06-build.log | R24 | 0 | 8.42 | Step024 regression passed |
| 07-build.log | R23 | 0 | 8.28 | Step023 regression passed |

01 の失敗: `J.IsMaximal.mul_mem_pow` は Prop expression への field notation となり無効。
actual namespace-qualified `Ideal.IsMaximal.mul_mem_pow J hProd` の結果は disjunction なので
`.resolve_left hU` を適用する形に修正。
同時に proposition instance の `letI` style warning を `let : J.IsMaximal := hJ` で解消。
名前不存在や数学的 counterexample による失敗ではなく、checked API の適用形の修正。
02以降の stage proofs と05 test は成功。final04/05 logs は warning0。
new axiom/placeholder/limit option で gate を代替しない。

## All public axiom outputs

Final05 test の全7 declarations。標準公理だけで sorryAx/新公理なし。

```text
mem_maximal_square_of_mul_mem: [propext, Classical.choice, Quot.sound]
gtailCyclotomicCofactor: [propext, Classical.choice, Quot.sound]
gtailCyclotomicCofactor_mul_factor: [propext, Classical.choice, Quot.sound]
gtailCyclotomicCofactor_not_mem_selected: [propext, Classical.choice, Quot.sound]
natCast_mem_sixRootKernel_square_of_sq_dvd: [propext, Classical.choice, Quot.sound]
gtailCyclotomicFactor_mem_square_of_sq_dvd_GTail: [propext, Classical.choice, Quot.sound]
gtailCyclotomicFactor_mem_square_iff: [propext, Classical.choice, Quot.sound]
```

## Import, neutral dependency, token and style audit

新 owner は Step024 owner のみ direct import、新 test は今回 owner 一つ。
comment/string 除去後 local/Mathlib source closure を追跡。
neutral GTailSevenRealTraceResidue:1907 modules/local20、FLT dependencies0。
production:8933/local153、test:8934/local154、local union154 vertices の DFS cycle0。
external source のない依存名は leaf。全 repository/package cycle-free claim ではない。
Step024 production closure から今回 owner 一つの追加。
full FLT.Seven facade、Domain、old global oriented factorization、old oriented valuation、Kummer、QR bridge は
新 owner/test closure に含まれない。existing heavy carrier closure は残る。

新二 Lean files は既存 MIT2026/Authors header、import後 file print、namespace、2space style を維持。
comment/string 除去後 whole-word sorry/admit/axiom/unsafe/native_decide、False.elim、set_option は0。
`git diff --check` と新四 files の no-index whitespace check、ROADMAP append-only 検査を実施。
tracked edit は post024 ROADMAP append のみ。旧 rings、signed owners、drivers、facades、historical ledger は変更なし。
この7 public declaration axiom audit は全 repository の axiom-free 性の主張ではない。

## Lean-derived observations and bounded proposals

1. **Confirmed:** existing Mathlib maximal-power saturation は一般の CommRing で利用できる。
   Step025 で必要な cancellation は U の ring-unit 性でなく、J² に対する unit-mod-ideal 性。
   domain cancellation と prime-only cancellation のどちらも必要としない。
2. **Confirmed:** Step024 の g1165 sample は今回「guard fails / multiplicity unknown」から
   **全六 selected square memberships が成立**へ進んだ。古い記録はその checkpoint 時点の事実として残す。
   J³ membership/nonmembership は引き続き未解決。
3. **Confirmed:** residue root と endpoint residues が同じ両 numeric cases の cofactor residues はすべて28。
   この非零数値は generic maximal saturation の input を可視化する calibration である。
4. **Proposal only / unproved here:** homogeneous cyclotomic shell の derivative を用いた cofactor evaluation formula は
   全六同じ residue28となる理由の独立 API 候補。今回 derivative formula 自体は証明していない。
5. **Proposal only / unproved here:** general Mathlib saturation が既存でも、all-k natural factor iff に必要な
   scalar contraction / finite excess-copy induction は別の作業。今回 n=2 を越える新 theorem は作らない。

**Outcome B**: canonical natural Tail branch の exact second-level prime-power membership iff。
principalization、ideal class/unit extraction、integral Eisenstein map、signed packet identification、
primitive smaller Fermat tuple、FLT7 descent / unconditional closure は結論しない。
**STOP after Step025**。

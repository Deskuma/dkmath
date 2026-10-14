# Step031 — typed norm-scalar / cyclotomic-depth inventory

2026-10-10。Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
Base HEAD `ff652d916ccdb2986286d92cc92b8a70ecd937ec`。
review030/report030/inventory030 と実ソースの署名・import を確認。
review030 は既存の静的レビュー記録であり、今回の再ビルド結果とは区別する。

## 二つの integral carrier と共通の scalar carrier

| Source ring | Exact element | Selected ideal | Scalar map | Extra hypotheses | Lost data | Owner |
|---|---|---|---|---|---|---|
| E = TraceOneInt (-1) | α = gtailSevenNormCoord a b = eisensteinCoord a (-b) | まだ指定しない | norm α = (Q:ℤ), norm (α²) = (Q²:ℤ) | norm identity 自体は全 a,b | norm は座標・向き・理想アドレスを保持しない | Lib.NumberTheory.GTailSevenNormReadout (012) |
| E | α² | P_t*P_t, t = gtailSevenResidueRoot q a b | E→ZMod q の t-slot evaluation | Fact prime q, q≠3, q∣Q, q∤b | normだけから conjugate/scalar ideal 所属を復元できない | Lib.NumberTheory.GTailSevenIdealSquareAddress (017) |
| R = SevenCyclotomicDegreeSixInt.Ring | F_i = gtailCyclotomicFactor c g i | K_(sixInverseSlot i), r = gtailSevenTailRatio q c g | R→ZMod q の六 root-slot evaluation | Fact prime q, q∤c,g, q∣T | scalar T は factor index と slot を保持しない | GTailCyclotomicTailDepthTwo/Three/Four (025/029/030) |
| ℕ / ℤ | Q=a²+ab+b², T=GTail 7 1 g c | integral ideal なし | gT=7ab(a+b)Q²; v(g)+v(T)=2v(Q) | 正 a,b, primitive, hEq, hsum, prime q≠7, q∣Q | norm-value divisibility は integral element の divisibility ではない | GTailBridge, GTailPrimeAllocationAudit (010), GTailNormReadoutAudit (012) |
| old signed packet の carrier | p.signedDepth.cyclotomicDegreeSixCarrier | s.orientedKernelPower | routed-cell load / quotientExponent | s : PrimeSupport family p | bare natural c,g から packet の再構成・同一性は供給されない | SevenRamifiedFusionOrientedCarrierValuationOwnership, 比較のみ |

E→ZMod q と R→ZMod q は異なる source ring 上の評価である。同じ finite field を codomain
に持つだけでは E→R RingHom は定まらない。逆像の lift、integral relation preservation、
α² と F_i の対応が必要だが、既存 API はこれらを供給しない。
P_t は Ideal E、K_j は Ideal R。今回の接続は共通 q と ℕ/ℤ の Q,T,norm-value に限る。
旧 orientedKernelPower_dvd_span_carrier は signed packet を要求する。今回の偶数付値から
その quotientExponent の偶奇は導けない。旧 owner の import/edit はない。

## 既存 API の契約と再利用

- norm_gtailSevenNormCoord / norm_gtailSevenNormCoord_sq は unconditional scalar identities。
  dvd_quadratic_iff_dvd_gtailSevenNormCoord は q∣Q ↔ (q:ℤ)∣norm α。
- gtailSevenNormCoord_split_square_address は q≠3, q∣Q, q∤b の下で
  α²∈P_t*P_t、α²∉P_(1-t)、α²∉eisensteinScalarIdeal q。
  root polynomial は gtailSevenResidueRoot_polynomial と conjugate_polynomial が供給する。
- focused_gtail_eq_norm_square は hEq, hsum から **integer scalar** gT=7ab(a+b)norm(α²)。
- not_prime_dvd_coordinate_product_of_quadratic は hq,hcop,hQ から q∤ab(a+b)。
  その各 factor の unit を新 owner 内で取り出す。
- not_prime_dvd_endpoint_of_quadratic は hq,hcop,hEq,hQ から q∤c。
- prime_focused_support_exclusive は hq,hq7,hcop,hEq,hsum,hQ から
  (q∣g ∧ q∤T) ∨ (q∣T ∧ q∤g)。追加 hT で Tail branch を選ぶ。
- padicValNat_focused_quadratic_budget は ha,hb,hcop,hEq,hsum,hq,hq7,hQ から
  v_q(g)+v_q(T)=2v_q(Q)。**今回の偶数性はこの既存予算の直接適用。**
- prime_square_focused_allocation は同じ仮定から square support の排他的割当。
  hT で q²∣T を再利用し、新しい square allocation 証明を作らない。
- q≠3 は neutral prime_ne_three_of_gtail hq hq7 hc hg hT を使用。
  Step011 の stronger 21∣q−1 は今回不要。GTailSevenPairedResidue の共有 ZMod q は
  integral map を与えないので import 追加不要。
- source の private focused_gap_tail_ne_zero は public API ではない。
  新 private helper は gT の正の右辺を直接用い g≠0,T≠0,Q≠0 を証明する。
- Step025/029/030 の actual factor membership iff はそれぞれ q²/q³/q⁴∣T。
  既存 cofactor saturation / ideal contraction 証明の再実装はない。
- Vp_ge_one_iff hp hn : 1≤padicValNat p n ↔ p∣n。
  padicValNat_le_iff_dvd hp hn k : k≤padicValNat p n ↔ p^k∣n。
  hp:Nat.Prime p と hn:n≠0 が必須。Fact prime の要求は padicValNat_self/prime_pow にもある。
  eq_zero_of_not_dvd hgu 自体は非整除の仮定だけで使える。
  padicValNat q 0 = 0 のため T,Q の非零仮定を削除できない。
  abstract helper で g≠0 は hgu から既に従うため独立の冗長引数にはしていない。

## 最小 direct imports と実測した到達性

新 FLT owner は Step030, Step010 allocation, Step012 FLT norm readout,
Step017 ideal square address の4 direct imports。
Step030 比の追加 module は次の7 local ownersのみ（Mathlib追加0、削除0）。

```text
DkMath.FLT.Seven.GTailBridge
DkMath.FLT.Seven.GTailConstraintAudit
DkMath.FLT.Seven.GTailFocusedNormCyclotomicDepthBridge
DkMath.FLT.Seven.GTailNormReadoutAudit
DkMath.FLT.Seven.GTailPrimeAllocationAudit
DkMath.Lib.Cosmic.GTailSevenArithmetic
DkMath.Lib.Cosmic.GTailSevenPrimeAllocation
```

Source closure 8946/local166、test closure8947/local167、local union167、cycle0。
前段 neutral root GTailSevenRealTraceResidue は1907/local20、FLT到達0。
さらに新 source 到達範囲内の neutral Lib owners 全部について逆依存を監査（report参照）。
FLT.Seven façade、degree-six domain、global oriented factorization、oriented valuation ownership、
Kummer.CyclotomicPrincipalization、CyclotomicQRTraceOneBridge は新source/test closureにない。
ただし Step030 から引き継ぐ carrier dependency のため DescentClosureAudit 等の旧 modules は
到達範囲にある。DescentClosureAudit は closureProvider を要求する条件付き API であり、
unconditional FLT closure ではない。今回の proof はそれらを使わず、上記 budget と typed
receiver のみを接続する。import closure の広さと新 theorem の proof dependency は区別する。

STOP031。K⁵/all-k、integral transport、signed packet、principalization、unit/class extraction、
次の primitive tuple、unconditional FLT7 impossibility は今回の契約外。

# Step038 source inventory

2026-10-11。Base HEAD: `9422f149699ea15fb603551e900f62c6cef140a3`。
Branch: `feature/GTail-SelectiveGap-FLT7-261009-v0`。
review-037 / report-037 / frontier-037 と現行 Lean owners を確認した。
新 owner の direct import は GTailFocusedGenericPrimeReceiver（Step037）一つ。
Step010 は既存 transitive closure に含まれるため direct import を追加しない。

## 実際の型と二分岐

Q=a²+ab+b²:ℕ、T=GTail 7 1 g c:ℕ。
E=TraceOneInt (-1)、R=SevenCyclotomicDegreeSixInt.Ring、
C=GTailCommonReceiver.Carrier=QuadraticAlgebra R (-1)1。
ιE=fromEisenstein:E→+*C、ιR=fromCyclotomic:R→+*C は変更しない。
P_t:eisensteinResidueIdeal t ht は Ideal E、K_r:seventhRootKernel r ... は Ideal R。

| Stage | Actual hypotheses | Checked consequence / owner | Missing contract |
|---|---|---|---|
| A: every eligible q∣Q | q prime, a,b>0, Nat.Coprime a b, hEq, a+b=c+g, q≠7, q∣Q; entry hT なし | Step010 prime_square_focused_allocation の q² Gap OR q² Tail; coordinate/end units | contradiction / new global restriction |
| B: Gap | derived q²∣g, q∤T, q∤c | new gap_ratio_eq_one: (c+g)/c=1; nonidentity guard failure | native nonidentity Tail root, appropriate Gap-side recipient |
| C: Tail | derived q²∣T, q∤g; q∣T obtained by divisibility transit | Step031 guards、Step037 actual nativeKernel:Ideal C、E/R contractions、joint sum、memberships、doubled valuation / parity、bounded M²/M³/M⁴ | exact M depth / signed reconstruction |
| D: global / signed | Step032 exact balance iff under focus; old signed/provider field signatures | no new construction | weaker-data global balance, signed identities, primitive nextPack/nextRoute/carrier_match |

Gap ratio lemma は q prime、q∤c、q∣g のみを要する。
hEq / hfocus / positivity / q∣Q / q∣T / q≠7 は不要。
新 focused_coordinate_units は hcop,hEq,hQ だけから q∤a,b,a+b,c を導く。
新 focused_prime_route は A の全仮定を受け、最初から hT を要求しない。
Tail constructor は hT と q∤g を備えるが Gap constructor に kernel はない。
abstract supplied-root evPair と natural ratio が一致するとは限らない。

## Source-typed proof owners / exact guards

- GTailPrimeAllocationAudit（Step010）:
  not_prime_dvd_coordinate_product_of_quadratic は q prime,hcop,hQ から q∤a*b*(a+b)。
  not_prime_dvd_endpoint_of_quadratic はさらに hEq を要して q∤c。
  prime_focused_support_exclusive は hEq,hfocus,q≠7,hcop,hQ を要し、positivity は不要。
  prime_square_focused_allocation はそれに a,b>0 を加え、q² support の二分岐を供給する。
- GTailFocusedNormCyclotomicDepthBridge（Step031）:
  focused_norm_depth_guards は hcop,hEq,hfocus,q≠7,hQ,hT から
  q∤a,b,a+b,c,g と q≠3。focused_norm_scalar_depth_readouts はさらに a,b>0 を要し、
  vq(T)=2vq(Q)、q²∣T、q⁴∣T↔q²∣Q、q³∣T↔q⁴∣T。
  focused_eisenstein_norm_square_endpoint の平方は Ideal E、
  focused_cyclotomic_depth_endpoint の K²/K³/K⁴ は Ideal R に留まる。
  新 owner はこれらの higher depth proof を再実装しない。
- Lib.NumberTheory.GTailSevenPairedResidue:
  gtailSevenTailRatio q c g は ((c:ZMod q)+(g:ZMod q))/(c:ZMod q)。
  ne_zero / pow_seven は q∤c,hT、ne_one は q∤c,q∤g を要する。
- GTailFocusedGenericPrimeReceiver（Step037）:
  evPair は t²−t+1=0 と r≠0,r⁷=1,r≠1 を受ける actual unital map。
  pairedKernel_eq_sup は別型の source ideal を map した二つの Ideal C の sup。
  nativeKernel / native_residue_zeros は hQ,q∤b,c,g,hT を要し hEq は不要。
  native_square_support はさらに q≠3,q²∣T、focused_receiver は A+hT から全 guards を導く。
- E square owner: Lib.NumberTheory.GTailSevenIdealSquareAddress の
  gtailSevenNormCoord_split_square_address。R bounded source owners:
  GTailCyclotomicTailDepthTwo / Three / Four の factor_mem_square / cube / fourth_iff。
  既存 map_pow transport と一方向包含を今回も保持する。
- GTailGlobalBalanceFirewall（Step032）:
  fermat7Equation_iff_focused_scalar_balance は hfocus の下で
  hEq ↔ g*T=7*a*b*(a+b)*Q²。local kernel からこの等式を逆導出しない。
- norm-image firewall は GTailCommonReceiver の実際の C.im、
  Lib.NumberTheory.gtailSevenNormCoord_eq、actual R root evaluation を使う。
  q∤b と supplied R evaluation のみで任意 u:R と区別し、hEq / hQ / hT は要しない。

q7 は total square route の明示例外。Gap ratio lemma は q7 でも成立する。
q3 は total route から除かず、Tail branch の Step031 guard が q≠3 を導く。
q3 の quadratic repeated root と trivial Gap ratio は別の有限例で確認する。

## Verified Mathlib APIs

`.lake/build/gtail-step038/api-probe-fixed.log` の実際の #check:
`ZMod.natCast_eq_zero_iff (a b : ℕ) : ↑a=0 ↔ b∣a`。
`div_eq_iff (hb:b≠0) : a/b=c ↔ a=c*b`、
`eq_div_iff (hb:b≠0) : c=a/b ↔ c*b=a`。
`Nat.Prime.dvd_of_dvd_pow`、`dvd_pow_self` と divisibility transit を確認した。
`ZMod.isUnit_iff` は現行 constant として存在しなかった（初回 probe の実際の error）。
代わりに `ZMod.isUnit_iff_coprime`、`ZMod.isUnit_natCast_iff_not_dvd_pow`、
field の `isUnit_iff_ne_zero` を #check した。証明では denominator≠0 を直接使う。

## Read-only reconstruction audit

DescentClosureAudit.AwayDescentClosureProvider は nextX/Y/Z:ℕ、
nextPack:CounterexamplePack nextX nextY nextZ、
nextRoute:AwayValuationTransferPacket nextX nextY nextZ、
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd` を要する。
SevenRamifiedSignedRootDepth.RamifiedSignedRootDepthPacket は balanced axis、
signed roots と旧 normPacket roots の一致、IsCoprime、gapRoot/quotientRoot、
signedGap=7⁴*gapRoot、signedQuotient=7*quotientRoot、両 root の7-unit、normalizedEquation。
新 Ideal C の join / membership はいずれの field も構成しない。
これらは既存 transitive imports として残るが新 direct import / proof-body reference は追加しない。
旧 rings、Step010/031/032/037、facades、過去 reports/reviews は変更しない。

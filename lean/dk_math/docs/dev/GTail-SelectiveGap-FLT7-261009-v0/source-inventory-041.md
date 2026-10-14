# Step041 source inventory — actual capacity countermodels

2026-10-11。Base HEAD `3e5db727b77799fd163834bb9b3c799097d7b187`。
Branch `feature/GTail-SelectiveGap-FLT7-261009-v0`。
review/report/source-inventory/frontier-040 と現行 source owners を確認した。

## Source contracts

| Owner | Actual API / contract |
|---|---|
| Step040 GTailFocusedDefectGlobalCapacity | squarePrimeSupportModulus、dvd_iff、finite_defect_zero_certificate、quadratic_prime_support、quadratic_modulus_le_square、full_quadratic_defect_zero_certificate。最後は Q≠0、全 prime-square support、strict natAbs bound の両方を要求 |
| Step039 GTailFocusedDefectSquareFirewall | focusedFermatDefect : ℕ→ℕ→ℕ→ℤ、zero_iff、endpoint_unit_of_defect、defect_square_prime_route。selected route は hEq-free、q²∣Δ を要求 |
| Step032 GTailGlobalBalanceFirewall | fermat7Equation_iff_focused_scalar_balance。focus の下で exact scalar balance iff Fermat |
| Step037 GTailFocusedGenericPrimeReceiver | namespace GTailGenericPrimeReceiver。nativeEval / nativeKernel は q∣Q,T と q∤b,c,g から actual roots を取る |
| Step035 GTailEisensteinCyclotomicPrimeGrid | namespace GTailPrimeGrid。eisenstein43Root=[37,7]、seven43Root=11 の sixSlotRoot、evGrid、M=ker evGrid、typed E/R contractions |
| Step034 GTailEisensteinCyclotomicCommonReceiver | namespace GTailCommonReceiver。Carrier=QuadraticAlgebra R (-1) 1、R=SevenCyclotomicDegreeSixInt.Ring、E=TraceOneInt (-1)、fromEisenstein / fromCyclotomic と generator evaluation |
| Mathlib | Nat.primeFactors_mul、Nat.Prime.primeFactors、Nat.mem_primeFactors_of_ne_zero は新 test の実際の #check に記録。factor product と norm_num prime certificates で支持集合を構成 |

production direct import は Step040 一つ、test direct import は新 production 一つ。
新 ABC.Rad、Mathlib、facade、signed provider の direct import はない。

## Witness obligations

A=(13,35,46,2)、Q=43²=1849、support={43}、M=1849<Q²=3418801。
Δ=-371415611824、全支持 true、size false。
T=75625342528、43²∣T、43∤b,c,g、native roots=(7,16)。
actual nativeKernel : Ideal Carrier が M (1:Fin2) (4:Fin6) に一致する。
proof は nativeEval / evGrid の全座標 evaluation equality を ext/rfl で示し ker に移す。

B=(1497,2797,2802,1492)、Q=37*385171=14251327。
37、385171 は norm_num の kernel certificate、support={37,385171}。
M=203100321260929=Q²、Δ=-179820312066002。
strict size true、両 prime の first-power / square divisibility false。

両方で positivity / coprimality / focus / strict inequalities / ¬Fermat / ¬exact balance を検証。
production exports はこれらの geometry と true premise / negated missing premise / ¬Fermat を
含む二つの existential。全 positive data に対する universal independence claim ではない。

## Read-only reconstruction boundary

AwayDescentClosureProvider の nextX/Y/Z、nextPack : CounterexamplePack、
nextRoute : AwayValuationTransferPacket と
`carrier_match : nextRoute.carrier = Int.natAbs p.normal.root.snd` は未構成。
RamifiedSignedRootDepthPacket の balanced、signed roots identities / coprimality、
gapRoot / quotientRoot、signedGap_eq / signedQuotient_eq、7-unit guards、normalizedEquation も未構成。
単独の support、size、native kernel はこれらの field や FLT7 contradiction を与えない。

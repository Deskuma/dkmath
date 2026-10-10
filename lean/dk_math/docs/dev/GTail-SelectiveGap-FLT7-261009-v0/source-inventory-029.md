# Step029 — third-power feasibility inventory

2026-10-10. Branch feature/GTail-SelectiveGap-FLT7-261009-v0。
Base HEAD 2f205a77ff859ace37ee3fa67b70e149a2f602c3。
review028/report028/inventory028 を確認。reviewはstatic、独立 rebuildではない。

Actual carrierは SevenCyclotomicDegreeSixInt.Ring（six signed integer coordinates）。
Step021 sixRootKernel_sup_eq_top / maximal prime、Step022 prod_sixRootKernel_eq_scalarIdealを使用。
Step024 cyclotomic_natCast_mul_injective と scalar-only (q)*K contractionを使用。
Step025 actual U_i*F_i=T、U_i nonmember、square iffは保持。
Step028 scalar cube calibrationは ideal cube membershipをまだ提供していない。

## Proof gates

Complement J_j は erased-slot finite productを一度だけ定義。
Finset.prod_erase_mulでK*J=(q)、IsCoprime.prod_rightと erased membershipでK⊔J=top。
Ideal.pow_sup_eq_topで powersとJのcomaximality。
Private generic CommRing lemmaは I^n∩(I*J)=I^n*J（n≠0）、
Ideal.mul_eq_inf_of_isCoprime と mul_le/mul_mono/pow_le_selfの lattice証明。
Public endpointsは square/cube inf scalar identitiesのみ。
Deprecated inf_eq_mul_of_isCoprimeを使わず現行mul_eq_inf theoremのsymm。

Scalar square contractionはK²≤Kからq|n、embedded n∈(q)、intersection identity→(q)*K、Step024 iff。
Scalar cube contractionは同様に intersection→(q)*K²、Ideal.mem_span_singleton_mulでy∈K²。
n=q*mとして actual coordinate injectivityにより y=cast m、square contractionを適用。
Reverseは q∈K、Ideal.pow_mem_pow、ideal scalar multiplication closure。
No DVR/IsDomain hypothesis。qのcancellationは actual torsionfree carrierに限定。
Selected factor cube iffは actual cofactor productと Ideal.IsMaximal.mul_mem_pow（exponent3）でsaturation。

## Old ownership contract comparison

SevenRamifiedFusionOrientedCarrierValuationOwnership.orientedKernelPower_dvd_span_carrierは
PrimeSupport family p、signedDepth.cyclotomicDegreeSixCarrier、oriented/conjugate power dataに依存。
今回の bare natural c,g、canonical root、actual F_i、U_iにはその signed packet contractがない。
旧ownerはcomparisonのみ、import/editなし。No packet identification/transfer。

Direct importはStep028のみ。新しいmathlib umbrella/domain/oldvaluation ownerは追加しない。
K³ iffはboundedselected theorem、K⁴ cutoff/exact valuation/general all-k selected APIは未実装。

## Measured final cost

New source8938/local158、new test8939/local159、local union159 cycle0。
Step028比new owner1のみ、added Mathlib0。Neutral closure1907/local20、neutral→FLT0。

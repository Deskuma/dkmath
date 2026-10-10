# Step030 — fourth-power firewall inventory

2026-10-10. Branch feature/GTail-SelectiveGap-FLT7-261009-v0。
Base HEAD b6debb8dfc381a7493c4230dc6548865baf341a4。
review029/report029/inventory029を確認。reviewはstatic inspection、独立rebuildではない。

Actual R=SevenCyclotomicDegreeSixInt.Ring、six signed integer coordinates。
K=sixRootKernel、J=Step029 sixRootKernelComplement、K*J=cyclotomicScalarIdeal q、K⊔J=top。
Step029 private pow_inf_mul_of_comaximal / scalar_support_of_kernel_memは公開APIではない。
新owner内のprivate helpersとして同じgeneric lattice proofとscalar RingHom proofを再検証。
Compiler-generated private identifiersを参照せず、以前のownerは変更しない。

Public gates:
- K⁴∩(q)=(q)*K³: K⁴∩J=K⁴*J、mul_le_right / pow_le_self / mul_monoによる両包含、power regroup。
- Natural scalar n∈K⁴ iff q⁴|n: q|nとn=q*m、mem_span_singleton_mulでy∈K³、
  Step024 actual cyclotomic_natCast_mul_injectiveでy=cast m、Step029 public cube iff。
- Actual selected F_i∈K⁴ iff q⁴|GTail: Step025 U_i product/nonmemberとmaximal power saturation n=4。
- Cube iffと新fourth iffでbounded exact depth-three pair。

Current Mathlib signaturesをsource確認:
Ideal.mul_eq_inf_of_isCoprime、pow_sup_eq_top、pow_le_self、mul_mono、mem_span_singleton_mul、
IsMaximal.mul_mem_pow、pow_mem_pow。Deprecated inf_eq_mul aliasは使わない。
No IsDomain/Dedekind/DVR/Principal premise。Natural scalar cancellationはactual Rに限定。
Whole-ideal K⁴=(q⁴)、(q)*K³=(q⁴)とは主張しない。

Step021/022 actual six slots/comaximal scalar productをStep029 public interfaces経由で保持。
Step028 finite Hensel second digit scalar sourceとgeneric PolynomialHenselDigitは既存API。
第三補正の計算やgeneric finite-depth proof再実装は行わない。
Old oriented valuation ownerはPrimeSupport family p / signedDepth carrierを入力とする。
Bare natural Tail c,gとそのsigned packetの同一視/transferは今回ない。比較のみ、import/editなし。
Direct importはStep029一つだけ。No facade/refactor/all-k selected valuation or K⁵ endpoint。

## Final measured closure

New source8939/local159、新test8940/local160、union160cycle0。Neutral1907/local20、neutral→FLT0。
Step029比new owner1、added Mathlib0。All4public axioms standardのみ。

# Step037 source inventory

Base HEAD: `e338940c46b6eda8f9fbe1cbd02cb412ec59d582`。
Step036 review/report/frontier と Step034–036 の実際の型を参照。
E=TraceOneInt (-1)、R=SevenCyclotomicDegreeSixInt.Ring、C=GTailCommonReceiver.Carrier。
既存 E/R→C の単射・integer scalar agreement は不変。直接 E↔R hom は Step033 で否定。

新 evPair : C →+* ZMod q は {q:ℕ} [Fact (Nat.Prime q)] の下で
supplied t,r:ZMod q、ht:t²−t+1=0、hr0:r≠0、hr7:r⁷=1、hr1:r≠1 を必要とする。
pairedKernel : Ideal C の contraction は P_t:Ideal E と K_r:Ideal R にそれぞれ戻る。
全射性は GTailCyclotomicPrimeAddress の既存 R evaluation を利用。
Mathlib ker_isMaximal_of_surjective / RingHom.comp / Ideal.ext / comap は既存実 API。

CommonReceiver（NoDirectHom import）の eval43 は同じ座標評価の q43 特殊例。
PrimeGrid（CommonReceiver import）は t37/7 と sixSlotRoot11 の grid。
PrimeJoin（PrimeGrid import）は row coordinate decomposition と bounded powers n:Fin 3。
これらの owner と元の定義を変更せず、generic receiver は PrimeJoin 一つだけを直接 import。

Lib/NumberTheory/GTailSevenEisensteinResidue の gtailSevenResidueRoot q a b は −a/b。
gtailSevenResidueRoot_polynomial は q∣Q と q∤b から二次関係を得る。
GTailSevenResidueIdeal（EisensteinResidue + Mathlib Ideal.Maps import）の
actual residue RingHom / ideal と gtailSevenNormCoord_mem_residueIdeal を再利用。
Tail root gtailSevenTailRatio q c g は (c+g)/c。GTailSevenPairedResidue の guards は
q∤c,q∤g,q∣Tail から nonzero / seventh / nonidentity を得る。
CyclotomicLocalEval / PrimeAddress / SixRootOrbit / TailFactorProduct は actual R の評価・kernel・
unique inverse-slot membership を提供する。slot0 を selected factor F0 に使う。

focused_norm_depth_guards は hcop,hEq,hfocus,hq7,hQ,hT から
q∤a,b,a+b,c,g と q≠3 を得る。focused_norm_scalar_depth_readouts はさらに a,b>0 を要し、
v_q(T)=2v_q(Q)、q²∣T、q⁴∣T↔q²∣Q、q³∣T↔q⁴∣T を提供する。
これらは既存 Step031 の条件付き API であり新しい obstruction ではない。
GlobalBalanceFirewall の scalar/norm iff の hEq を local support で置換しない。

Mathlib map_le_iff_le_comap、mem_map_of_mem、map_pow、mul_mem_mul、
ZMod.natCast_zmod_val と QA coordinate laws は既存 closure 内。
map f (I^n)=(map f I)^n は正しく、M^n への包含との違いを維持する。
型は E/R の source ideal → Ideal C の extension → common kernel の順に保つ。

read-only signed reconstruction audit は新 import / proof dependency にしない。
AwayDescentClosureProvider の nextPack,nextRoute,carrier_match と
RamifiedSignedRootDepthPacket は local ideal/membership の出力とは別の契約。
一般の grid / spectrum / source exact valuations / signed packet / FLT closure は未構成。

## Exact guards, powers and packet fields

Lib/NumberTheory/GTailSevenPairedResidue.lean:24,28,40,49 が Tail ratio と三つの guards の
直接 owner。RealTraceResidue はこれを import する既存 trace layer。
source α の所属は q∣Q と q∤b のみ、source F0 の所属は c/g units と q∣Tail のみ。
新 nativeEval / nativeKernel は両 root guards を構成するため五つすべての local input を受ける。
Fermat equation と additive focus はここでは使用しない。

native_square_support は別途 q≠3 と q²∣Tail を明示入力にする。
E の平方所属は Step017 split-square theorem、R の平方所属は Step025 mem_square_iff。
map_pow の等式で extended source square に入り、map_le_iff_le_comap と
pow_le_pow_left' で common square に包含。mul_mem_mul と pow_add で mixed powers3/4。
任意 q の all-k API や exact M-adic valuation は追加しない。

focused_receiver の input は a,b>0、coprime、hEq、hfocus、q≠7、q∣Q/T。
unit guards と q≠3 を Step031 から導き、padicValNat(T)=2*padicValNat(Q)、Even、
q²∣T、q⁴∣T↔q²∣Q、q³∣T↔q⁴∣T を同じ既存 API から得る。
入力 hEq から出る条件付き adapter であり、local kernel から hEq を逆導出していない。

read-only SevenRamifiedSignedRootDepth.RamifiedSignedRootDepthPacket は
balanced axis packet、signed roots と既存 normPacket roots への一致、IsCoprime、
gapRoot/quotientRoot、signedGap=7⁴*gapRoot、signedQuotient=7*quotientRoot、
両 root の7-unit、normalizedEquation を要求する。
AwayDescentClosureProvider は nextX/Y/Z、nextPack、nextRoute、carrier_match を要求する。
new pairedKernel : Ideal C はこれらの field のいずれにも値を供給しない。
これらの宣言は read-only audit。新 proof body で参照せず、direct import も追加しない。

## Optional generic join

pairedKernel_eq_sup は任意の supplied root pair に対する一つの joint ideal equation。
private coordinate_split(n:ℕ,x:C) を Step036 と同じ QA.ext / natCast 方法で検証し、
y=x.re+(t.val:R)x.im、d=τ−(t.val:E) の所属から reverse inclusion を得た。
既存 q43 grid は再構築しない。natural nativeKernel の join はこの theorem の specialization。
map_pow は generic join proof では使わず、平方支持の transport にだけ使う。

q127 は t20,r2 の supplied-root calibration。381=3*127、2⁷=128=1 modulo127。
これは native Fermat tuple の構成ではない。q43 の二つの tuple は source ratio で root37/11 を選ぶ。
(5,8,9,4) も additive-focused であり、first-power local input は成立するが doubled budget は不成立。
q7/q3/q13 の nonidentity seventh-root contract の不成立は finite Lean controls で検証する。

DescentClosureAudit と SevenRamifiedSignedRootDepth は既存 Step036 closure にすでに含まれる。
今回の direct import は指定通り Step036 一つであり、closure 差分は新 owner 一つのみ。
read-only audit を新たな import や proof body の packet 参照にしたものではない。
これらのモジュールが全 transitive closure から消えたとは主張しない。

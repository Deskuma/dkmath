# Step034 — actual third quadratic receiver inventory

2026-10-11。Base HEAD `cb44d90a3efe0b35354cf42fbf312c457eeb629f`。
review033/report033/source-inventory033/frontier033 と現行 ソースの署名を確認。
review033はstatic reviewであり、今回のfocused Lean結果とは区別。

| Source / target | Exact definition / API | Relation / obligations | Proven or required status |
|---|---|---|---|
| E=TraceOneInt(-1) | τ=tau(-1), traceOne_tau_sq | τ²=τ−1, actual signed coordinate multiplication | existing CommRing |
| R=SevenCyclotomicDegreeSixInt.Ring | QuadraticAlgebra SevenRealCubicInt (-1) (alpha−1), zeta, ofReal | ζ²=(alpha−1)ζ−1 and zeta_geom_sum | existing signed degree-six carrier |
| C=GTailCommonReceiver.Carrier | QuadraticAlgebra R (-1) 1 | ω²=−1+ω, constant/im coefficients live in R | actual receiving algebra；field/domain/compositum statusは別 |
| R→+*C | fromCyclotomic=algebraMap R C | bundled unital ring laws | canonical QuadraticAlgebra coefficient injection |
| E→+*C | fromEisenstein x=⟨cast x.fst,cast x.snd⟩ | zero/one/add/mul、E parameter−1とC parameters−1,1を実際の座標で比較 | signed 座標を用いた RingHom、τ↦ω |
| ℤ→R | cast, actual coordinate z.re.fst | nested scalar coordinate equals original integer | private injectivity lemmaで検証；ring名から推定しない |
| E/R injections | coordinate chart / algebraMap_injective | coefficientsのinjectivityとpair equality | 個別Lean proof、二つのmapsを構築しただけではassertしない |
| E→ZMod43 | eisensteinResidueRingHom37、kernel=P37 | 37²−37+1=0 | existingactualhom/ideal |
| R→ZMod43 | evalCyclotomicFromSeventhRoot11、kernel=seventhRootKernel11 | prime43,11≠0,11⁷=1,11≠1 | existingactualhom/ideal |
| C→ZMod43 | eval43 x=evR x.re+37·evR x.im | coordinate mul＋quadratic 根の関係 | newunitalhom；evR injectivityやintegral root liftを仮定しない |
| M43=ker eval43 | new Ideal C | two 可換三角形 / Ideal.comap | separatelytypedP37/K0 contractions、cross-ringideal equalityではない |

## Mathlib/source convention と overlap

QuadraticAlgebra/Defs.lean: re_mul z w=z.re*w.re+a*z.im*w.im、
im_mul z w=z.re*w.im+z.im*w.re+b*z.im*w.im。
Basic.lean omega_pow_two_eq_add は ω²=a•1+b•ω。このためC=(-1,1)はEのdiscriminant−3。
旧TraceOneInt(-2) companionのdiscriminant−7を代入しない。
algebraMap_eq r=⟨r,0⟩、algebraMap_injective を実ソースで確認。
re_intCastとSevenRealCubicInt.fst_intCastで実際の Rへの整数castをprojectして検証。

TraceOneResidueType.residueMap s q はTraceOneInt s→QuadraticAlgebra(ZModq)(cast s)1の
既存coordinate residue model。今回のtargetは実際の R over integralreceiverなのでその有限体
specializationを代用できない。traceOneRatHomはrationaltarget、CyclotomicQRProvenanceLiftの
integralEmbedding/gaussEmbeddingはconditional field/integers targetでありこのC契約ではない。
共通R receiving mapの重複ownerは検索範囲に見つからず、新しいnarrowownerで検証した。
これらのheavy新importや共通 neutral API の変更はしない。

QuadraticAlgebra.lift はsupplied rootをR-algebraへのAlgHomにする既存API。
今回のevCにはevR係数mapがあるため、local R-algebra instanceを追加する方法も可能。
単純なdirect座標を用いた RingHomを選び、根の関係による乗法の保存を明示した。
RingHom.comp/ker、Ideal.comap/mem_comap、Ideal.extを実APIで確認。

Step033 no-direct-mapは維持。Step032のbalance iffとq43countermodelはregression対象。
共通の受け入れ先やkernel contractionは正確な大域的収支、norm-to-elementlifting、equalextendedideals、
idealpowertransferを供給しない。数学的境界はreport/frontier034。

## Import / ownership boundary

New productionはStep033一つだけをdirectimport。QuadraticAlgebra必要APIは実際の R既存closure内に
あり追加の Mathlib importは不要。testもnewowner一つ。E/R/neutralLib/oldpacket/facadesの変更なし。
新commonreceiverのproofchainはcoordinate/ring/residue/kernelのcontractに限定。
到達可能module数・cycle・neutral→FLT監査の実測値はreport034。
STOP034：rank12basis、domain/field、uniquecompositum、tensoruniversalproperty、idealdepthlifting、
signedrootpacket、新しい primitive packet、FLTdescentを追加しない。

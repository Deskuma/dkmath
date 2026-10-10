# Step036 source inventory

Base HEAD: `6c4659126d9ba8fb3ebe42f1490019ffea6b68a9`。
Step035 review/report/inventory/frontier と実際の PrimeGrid owner を参照。
E=TraceOneInt (-1)、R=SevenCyclotomicDegreeSixInt.Ring、C=GTailCommonReceiver.Carrier。
Step034 の fromEisenstein : E →+* C、fromCyclotomic : R →+* C は不変。

PrimeGrid は CommonReceiver のみを import。M e j : Ideal C、
P_e=eisensteinResidueIdeal t_e (...) : Ideal E、K_j=sixRootKernel 11 (...) j : Ideal R。
map_eisenstein_le / map_cyclotomic_le は別々の拡大の包含。
両 contraction、両可換三角形、M_injective、M00=M43、両 strictness を再利用する。

CommonReceiver は NoDirectHom を import。C は QuadraticAlgebra R (-1) 1。
algebraMap_eq と re_mul/im_mul、ext で座標分解を検証する。
ResidueIdeal は EisensteinResidue と Mathlib.RingTheory.Ideal.Maps を import。
実際の eisensteinResidueRingHom_tau、map_natCast、ZMod.natCast_zmod_val により
τ−t_e.val の source kernel 所属を得る。SixRootOrbit は PrimeAddress を import、
mem_sixRootKernel_iff は実際の R evaluation の零条件。

提案する恒等式は x=iR(x.re+t_e.val*x.im)+iE(τ−t_e.val)*iR(x.im)。
x∈M の場合だけ係数の remainder が K_j に属し、右辺の二項から ideal sum を得る。
Mathlib Maps.lean:70 mem_map_of_mem、76 map_le_iff_le_comap、671 Ideal.map_pow を確認。
map f (I^n)=(map f I)^n は正しい。これと包含の単調性は M^n への一方向の所属を与える。
Operations.lean の mul_mem_mul / pow_mem_pow を使用する。正確な深さや逆向きは得ない。

TailDepthTwo（TailDepthOne import）の F0∈K0² と
Lib/NumberTheory/GTailSevenIdealSquareAddress（RamifiedThreeIdeal import）の α²∈P37² は
異なる source 環の既存契約。数値組は Step032 の non-Fermat witness のまま。
新 owner は Step035 のみを直接 import。旧 owner と neutral Lib の変更なし。
全 spectrum、global Fermat balance、signed carrier reconstruction、provider/descent は未構成。

## Verified precise substitute and bounded contract

Mathlib Ideal ディレクトリの検索では Ideal.pow_mono という宣言は見つからなかった。
実際の代替は Algebra/Order/Monoid/Unbundled/Pow.lean:159 の
pow_le_pow_left' (h : I ≤ J) n : I^n ≤ J^n。理想の包含に対する既存順序構造を使う。
冪 transport の API は n:Fin 3 とし、n.val∈{0,1,2} に明示的に限定した。
A/B の冪への所属と M の冪への所属を別定理にして、等式と一方向の包含を分離する。

分解 proof は先に fromEisenstein(rowDifference e)=ω−(t_e.val:C) を
map_sub / map_natCast / fromEisenstein_tau で証明する。
自然数代表の cast と ZMod.cast を混同しないよう、座標計算には simp only と
re_natCast / im_natCast を使う。この整数 lift は E 内の有限体根の存在を仮定しない。

join の reverse inclusion は mem_map_of_mem、ideal.mul_mem_right、add_mem と
型を明示した le_sup_left/right を使用。一般 lattice の ≤ は型が決まるまで
membership の関数として使えないため、Ideal C の包含として明示して適用する。

旧 Step032 の global balance iff は入力 Fermat equation を同値に言い換える契約であり、
今回の join からその equation を得ることはない。旧 signed carrier に必要な
next primitive pack、route、carrier_match と unit/orientation の再構成は未供給。

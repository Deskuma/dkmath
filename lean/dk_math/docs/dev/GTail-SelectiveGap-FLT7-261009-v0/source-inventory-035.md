# Step035 source inventory

Base HEAD: `d0773dad48577653ec0604c363b1447a1d4d4463`。
Step034 review / inventory / frontier の実際の型を確認した。

E = TraceOneInt (-1)、R = SevenCyclotomicDegreeSixInt.Ring、
C = GTailCommonReceiver.Carrier = QuadraticAlgebra R (-1) 1。
既存の fromEisenstein : E →+* C と fromCyclotomic : R →+* C は変更しない。
Step033 の no-direct-hom と両立する第三の受け入れ先である。

Step034 eval43 と M43 は t=37, s=11 の既存特殊例。
E の根は 37,7（t²−t+1=0）、R は sixSlotRoot 11 j。
sixSlotRoot_pow_seven / ne_zero / ne_one / injective と sixRootKernel_ne を再利用する。
E contraction は Ideal E、R contraction は Ideal R であり相互の等式ではない。
GTailSevenResidueIdeal の eisensteinResidueRingHom_tau と実際の kernel を使う。
GTailCyclotomicPrimeAddress の surjective evaluation と maximal kernel を使う。

QuadraticAlgebra.re_mul / im_mul は係数の積と (-1,1) の二次関係を与える。
RingHom.comp と ker、Ideal.comap と ext によって二つの制限を照合する。
Mathlib RingTheory/Ideal/Maps.lean:76 の map_le_iff_le_comap は
map f I ≤ K ↔ I ≤ comap f K。拡大の包含に使えるが等式や深さは供給しない。
GTailCyclotomicTailFactorProduct の unique_slot と TailDepthTwo の平方支持、
GTailSevenIdealSquareAddress と Step032 の数値例は独立した source の情報である。

直接 import は Step034 の一つ。旧 owner、facade、neutral Lib は変更しない。
十二点は有限の集合であり、全 spectrum、rank、domain、FLT descent の証明ではない。
拡大の厳密性には別の評価で検出する member/nonmember が必要。
任意の ideal-power depth の比較には追加の source-linked transport が必要である。

## Exact owners and overlap

- DkMath/FLT/Seven/GTailEisensteinCyclotomicCommonReceiver.lean:
  Carrier、fromEisenstein、fromCyclotomic、eval43、M43 と両 contraction。
  direct import は GTailEisensteinCyclotomicNoDirectHom。
- GTailEisensteinCyclotomicNoDirectHom は GTailGlobalBalanceFirewall を import。
  not_nonempty_eisenstein_to_seven_cyclotomic と逆方向の theorem は維持。
- GTailCyclotomicSixRootOrbit は GTailCyclotomicPrimeAddress を import。
  sixRootKernel r hr0 hr7 hr1 j : Ideal R と sixRootKernel_ne を再利用。
- GTailCyclotomicPrimeAddress は GTailCyclotomicLocalEval を import。
  evalCyclotomicFromSeventhRoot_surjective は実際の R → ZMod q の全射性。
- DkMath/Lib/NumberTheory/GTailSevenResidueIdeal.lean は
  GTailSevenEisensteinResidue と Mathlib.RingTheory.Ideal.Maps を import。
  eisensteinResidueRingHom t ht : E →+* ZMod q、
  eisensteinResidueIdeal t ht := RingHom.ker (...) : Ideal E。
- GTailCyclotomicTailFactorProduct は SixRootInterpolation と Lib.Cosmic.GTailCyclotomic を import。
  gtailCyclotomicFactor_unique_slot は実際の factor の所属を j=sixInverseSlot i と同値にする。
- GTailCyclotomicTailDepthTwo は TailDepthOne を import。
  既存の F0 ∈ K0² は Step034 regression で維持し、C の冪への同一視には使わない。
- Lib/NumberTheory/GTailSevenIdealSquareAddress は GTailSevenRamifiedThreeIdeal を import。
  gtailSevenNormCoord_split_square_address は E の選択平方支持・共役除外を提供する。
  Step032 の (1166,1857,1858,1165) は non-Fermat witness のままである。

Mathlib Maps.lean:650,671 には Ideal.map_mul と Ideal.map_pow が実在する。
従って map f (I^n)=(map f I)^n 自体は正しい。未証明なのはこれを M(e,j)^n と
置換したり、異なる source の深さを同一視したりすること。
今回の strict inclusion はその置換が n=1 ですでに誤りであることを示す。

新 API の重複は Step034 の特殊例だけで、evGrid_zero_zero / M_zero_zero で正確に接続。
一般素数への constructor や rank/domain/spectrum certificate は追加していない。

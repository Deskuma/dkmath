/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularPrime37
import DkMath.Lib.NumberTheory.GaloisPhaseObstructionTransport

#print "file: DkMath.FLT.Kummer.IrregularGalois37"

/-!
# IRR-006: 障害付き State と37次ガロア作用

既存の `ObstructedState` は座標・原始性・非分岐性を保持する。
ここではそのデータを取り直さず、記録済みの位相イデアル根に輸送定理を適用する。
同じ State 内の位相を置換するには座標 x,y の固定性が必要であり、整数座標なら
それが自動的に従う。降下後の一般の円分整数座標が整数であるとは仮定しない。

37次の実例は仮想 State を入力とする条件付き保存則である。非自明な類の具体例、
Herbrand–Ribet の接続、FLT37 の閉包を構成するものではない。
-/

namespace DkMath.FLT.Kummer
open DkMath.Lib.NumberTheory
open scoped NumberField nonZeroDivisors

namespace IrregularDescent.ObstructedState
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {p : ℕ} [Fact p.Prime] {P : RamifiedPhasePacket R p} {m : ℕ}

/-- 元の座標を固定する自己同型は、記録済みの根と類を同じ位相置換で運ぶ。
根の選択依存性はイデアル冪の単射性で除かれ、正則性には依存しない。 -/
theorem galois_transport (O : IrregularDescent.ObstructedState P m)
    (e : R ≃+* R) (a : (ZMod p)ˣ) (hzeta : e P.zeta = P.zeta ^ a.val.val)
    (c : Rˣ) (hc : e P.lambda = c * P.lambda)
    (hx : e O.source.x = O.source.x) (hy : e O.source.y = O.source.y) (i : Fin p) :
    mapNonzeroIdeal e (O.phases.power i).root =
      (O.phases.power (RamifiedPhasePacket.phaseMul a i)).root ∧
    ClassGroup.mulEquiv e (O.phases.obstruction i) =
      O.phases.obstruction (RamifiedPhasePacket.phaseMul a i) :=
  ⟨P.phase_root_galois O.phases _ _ _ O.factor_eq (O.source.center_spec (by omega))
      e a hzeta c hc hx hy i,
   P.phase_obstruction_galois O.phases _ _ _ O.factor_eq (O.source.center_spec (by omega))
      e a hzeta c hc hx hy i⟩

end IrregularDescent.ObstructedState

namespace IrregularPrime37
attribute [local instance] prime37 cyclotomic37

/-- 実際の37次円分体の全ガロア自己同型を整数環上に実現する。 -/
noncomputable abbrev sigma37 (a : (ZMod 37)ˣ) : 𝓞 Cyclotomic37 ≃+* 𝓞 Cyclotomic37 :=
  CyclotomicPhaseGalois.sigma a

/-- 整数座標を持つ仮想37次 State の観測障害は σₐ(ωᵢ)=ωₐᵢ を満たす。
`observe` の既存のイデアル根をそのまま使い、State のいかなる不変量も変更しない。 -/
theorem observe_galois {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (a : (ZMod 37)ˣ) (i : Fin 37) :
    mapNonzeroIdeal (sigma37 a) ((observe E).phases.power i).root =
      ((observe E).phases.power (RamifiedPhasePacket.phaseMul a i)).root ∧
    ClassGroup.mulEquiv (sigma37 a) ((observe E).phases.obstruction i) =
      (observe E).phases.obstruction (RamifiedPhasePacket.phaseMul a i) := by
  obtain ⟨c, hc⟩ := CyclotomicPhaseGalois.exists_ramifier_unit
    (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) (by decide) a
  apply (observe E).galois_transport (sigma37 a) a
    (CyclotomicPhaseGalois.sigma_zeta
      (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) a) c hc
  · change sigma37 a E.x = E.x
    rw [hx]
    exact CyclotomicPhaseGalois.sigma_int a A
  · change sigma37 a E.y = E.y
    rw [hy]
    exact CyclotomicPhaseGalois.sigma_int a B

end IrregularPrime37
end DkMath.FLT.Kummer

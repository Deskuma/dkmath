/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularGalois37
import DkMath.Lib.NumberTheory.CyclotomicClassNorm

#print "file: DkMath.FLT.Kummer.IrregularNorm37"

/-!
# IRR-008: 37次 State の位相0の障害除去

既存の State の整数座標を前提に、ω₀N(ω₁)=1 と全共役イデアルのノルムを合成する。
イデアル根が主となるのは位相0であり、他の36位相は同じガロア軌道に残る。
非自明な37-torsion が残る場合、それはガロア固定成分ではないことも分かる。
特定の非自明指標への所属や Herbrand–Ribet、FLT37 の排除は別の算術である。
-/

namespace DkMath.FLT.Kummer.IrregularPrime37
open DkMath.Lib.NumberTheory
open scoped NumberField
attribute [local instance] prime37 cyclotomic37

/-- 正則性を使わず、整数座標の37次 State の位相0の障害を除去する。 -/
theorem observe_zero_obstruction_eq_one {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37)) :
    (observe E).phases.obstruction 0 = 1 := by
  have h := observe_orbit_norm E A B hx hy
  simpa only [CyclotomicPhaseGalois.orbitNorm_eq_one, mul_one] using h

/-- 位相0の実際の記録済みイデアル根が主イデアルになる。根を選び直さない。 -/
theorem observe_zero_root_principal {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37)) :
    (((observe E).phases.power 0).root : Ideal (𝓞 Cyclotomic37)).IsPrincipal :=
  (((observe E).phases.power 0).trivial_iff_principal).mp
    (observe_zero_obstruction_eq_one E A B hx hy)

/-- 位相0の因子を単元×37乗として復元する。同じ根の生成元と単元を両方保持し、
単元そのものが37乗であるという未供給の条件を混ぜない。 -/
theorem observe_zero_unit_generator {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37)) :
    ∃ (u : (𝓞 Cyclotomic37)ˣ) (b : 𝓞 Cyclotomic37),
      Ideal.span {b} = (((observe E).phases.power 0).root : Ideal (𝓞 Cyclotomic37)) ∧
        (observe E).phases.factor 0 = u * b ^ 37 :=
  ((observe E).phases.power 0).exists_unit_generator
    (observe_zero_obstruction_eq_one E A B hx hy)

/-- 非零位相の障害の自明性は全て同値。全て自明であるという存在しない結論は足さない。 -/
theorem observe_nonzero_trivial_iff {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (i : Fin 37) (hi : i ≠ 0) :
    (observe E).phases.obstruction i = 1 ↔ (observe E).phases.obstruction 1 = 1 := by
  obtain ⟨a, ha, _⟩ := RamifiedPhasePacket.exists_phaseMul_one i hi
  have he := (observe_galois E A B hx hy a 1).2
  rw [ha] at he
  rw [← he]
  constructor
  · intro h
    apply (ClassGroup.mulEquiv (sigma37 a)).injective
    simpa only [map_one] using h
  · intro h
    rw [h, map_one]

/-- 非自明な位相1障害があれば、それを動かす真のガロア自己同型が存在する。
自明指標成分の消滅は、非自明指標の選定とは別の構造的結論である。 -/
theorem observe_nontrivial_moves {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (hne : (observe E).phases.obstruction 1 ≠ 1) :
    ∃ a : (ZMod 37)ˣ, ClassGroup.mulEquiv (sigma37 a) ((observe E).phases.obstruction 1) ≠
      (observe E).phases.obstruction 1 := by
  by_contra h
  push Not at h
  exact hne (CyclotomicPhaseGalois.fixed_p_torsion_eq_one _ ((observe E).phases.torsion 1) h)

end DkMath.FLT.Kummer.IrregularPrime37

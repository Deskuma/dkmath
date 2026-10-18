/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularGalois37

#print "file: DkMathTest.FLT.Kummer.GaloisPhaseOrbitNorm"

/-!
# IRR-007 回帰例

37の巨大な展開はせず、有限位相の軌道と真の類群作用を検査する。
最後の例は抽象的な全積則の限界を示すもので、37次類群の非自明な類ではない。
-/

namespace GaloisPhaseOrbitNormTest
open DkMath.Lib.NumberTheory RamifiedPhasePacket
open DkMath.FLT.Kummer
open scoped NumberField

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

-- 36個の非零位相が、単元群と一対一に対応する。
example : Fintype.card {i : Fin 37 // i ≠ 0} = 36 := by decide
example : (ZMod 37)ˣ ≃ {i : Fin 37 // i ≠ 0} := nonzeroPhaseEquiv
example : ∃! a : (ZMod 37)ˣ, phaseMul a 1 = (36 : Fin 37) :=
  exists_phaseMul_one 36 (by decide)
example : phaseMul (-1 : (ZMod 37)ˣ) (1 : Fin 37) = 36 := by decide

-- 一般定理の p=37 特殊化。全位相が一度ずつ登場する。
example {G : Type*} [CommMonoid G] (f : Fin 37 → G) :
    ∏ i, f i = f 0 * ∏ a : (ZMod 37)ˣ, f (phaseMul a 1) :=
  prod_eq_zero_mul_orbit f

local instance : IsCyclotomicExtension {37} ℚ IrregularPrime37.Cyclotomic37 :=
  IrregularPrime37.cyclotomic37

-- 位相0と非零軌道の関係。State の整数座標の前提を落とさない。
example {m : ℕ} (E : RegularDescent.State IrregularPrime37.phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 IrregularPrime37.Cyclotomic37))
    (hy : E.y = (B : 𝓞 IrregularPrime37.Cyclotomic37)) :
    (IrregularPrime37.observe E).phases.obstruction 0 *
      CyclotomicPhaseGalois.orbitNorm (p := 37)
        ((IrregularPrime37.observe E).phases.obstruction 1) = 1 :=
  IrregularPrime37.observe_orbit_norm E A B hx hy

-- 真の円分体の類群上で、ノルムは固定され、37-torsion を保つ。
example (a : (ZMod 37)ˣ) (w : ClassGroup (𝓞 IrregularPrime37.Cyclotomic37)) :
    ClassGroup.mulEquiv (IrregularPrime37.sigma37 a)
      (CyclotomicPhaseGalois.orbitNorm (p := 37) w) =
        CyclotomicPhaseGalois.orbitNorm (p := 37) w :=
  CyclotomicPhaseGalois.orbitNorm_fixed a w
example (w : ClassGroup (𝓞 IrregularPrime37.Cyclotomic37)) (hw : w ^ 37 = 1) :
    CyclotomicPhaseGalois.orbitNorm (p := 37) w ^ 37 = 1 :=
  CyclotomicPhaseGalois.orbitNorm_torsion w hw

-- 全積が1でも各項は1とは限らない。実際の類群の torsion 供給とは区別する。
example : ∃ f : Fin 37 → Multiplicative (ZMod 37),
    (∀ (a : (ZMod 37)ˣ) i, f i = f (phaseMul a i)) ∧
      (∏ i, f i) = 1 ∧ f 1 ≠ 1 := by
  refine ⟨fun _ => Multiplicative.ofAdd 1, fun _ _ => rfl, ?_, ?_⟩
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    decide
  · decide

end GaloisPhaseOrbitNormTest

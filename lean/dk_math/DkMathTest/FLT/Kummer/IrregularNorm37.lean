/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularNorm37

#print "file: DkMathTest.FLT.Kummer.IrregularNorm37"

/-!
# IRR-008 回帰例

任意の本当のイデアル・類を入力に取る。非自明類を仮造せず、整数座標を持つ
仮想 State の位相0除去、非零軌道の自明性の同値、固定37-primary類の消滅を検査する。
-/
namespace IrregularNorm37Test
open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open scoped NumberField
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : IsCyclotomicExtension {37} ℚ IrregularPrime37.Cyclotomic37 :=
  IrregularPrime37.cyclotomic37

example (I : Ideal (𝓞 IrregularPrime37.Cyclotomic37)) (hI : I ≠ ⊥) :
    (∏ a : (IrregularPrime37.Cyclotomic37 ≃ₐ[ℚ] IrregularPrime37.Cyclotomic37),
      I.map (GaloisIdealNorm.integerAut a)) = Ideal.span {(I.absNorm : 𝓞 IrregularPrime37.Cyclotomic37)} := by
  let := IsCyclotomicExtension.isGalois {37} ℚ IrregularPrime37.Cyclotomic37
  exact GaloisIdealNorm.prod_map_eq_span_absNorm I hI

example (w : ClassGroup (𝓞 IrregularPrime37.Cyclotomic37)) :
    CyclotomicPhaseGalois.orbitNorm (p := 37) w = 1 :=
  CyclotomicPhaseGalois.orbitNorm_eq_one w

example (w : ClassGroup (𝓞 IrregularPrime37.Cyclotomic37)) (r : ℕ) (ht : w ^ (37 ^ r) = 1)
    (hf : ∀ a : (ZMod 37)ˣ, ClassGroup.mulEquiv (IrregularPrime37.sigma37 a) w = w) : w = 1 :=
  CyclotomicPhaseGalois.fixed_p_primary_eq_one w r ht hf

example : CyclotomicPhaseGalois.characterComponent
    (K := IrregularPrime37.Cyclotomic37) (1 : (ZMod 37)ˣ →* (ZMod 37)ˣ) = ⊥ :=
  CyclotomicPhaseGalois.trivial_characterComponent

section State
variable {m : ℕ} (E : RegularDescent.State IrregularPrime37.phase37 (m + 1))
  (A B : ℤ) (hx : E.x = (A : 𝓞 IrregularPrime37.Cyclotomic37))
  (hy : E.y = (B : 𝓞 IrregularPrime37.Cyclotomic37))

example : (IrregularPrime37.observe E).phases.obstruction 0 = 1 :=
  IrregularPrime37.observe_zero_obstruction_eq_one E A B hx hy
example : (((IrregularPrime37.observe E).phases.power 0).root :
    Ideal (𝓞 IrregularPrime37.Cyclotomic37)).IsPrincipal :=
  IrregularPrime37.observe_zero_root_principal E A B hx hy
example : (IrregularPrime37.observe E).phases.obstruction 36 = 1 ↔
    (IrregularPrime37.observe E).phases.obstruction 1 = 1 :=
  IrregularPrime37.observe_nonzero_trivial_iff E A B hx hy 36 (by decide)
example (hne : (IrregularPrime37.observe E).phases.obstruction 1 ≠ 1) :
    ∃ a : (ZMod 37)ˣ, ClassGroup.mulEquiv (IrregularPrime37.sigma37 a)
      ((IrregularPrime37.observe E).phases.obstruction 1) ≠
        (IrregularPrime37.observe E).phases.obstruction 1 :=
  IrregularPrime37.observe_nontrivial_moves E hne
end State
end IrregularNorm37Test

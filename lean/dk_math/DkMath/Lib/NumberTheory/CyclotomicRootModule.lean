/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib.Algebra.Module.ZMod
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.AbsoluteGaloisGroup

#print "file: DkMath.Lib.NumberTheory.CyclotomicRootModule"

/-!
# p乗根の群を加法的なFₚ空間として読む

根の積を加法、冪をスカラー倍と読むと、μₚはZMod p加群になる。
この翻訳は離散対数や原始根の選択を要しない。標数0の体の代数閉包には
p個のp乗根が存在し、MathlibのmodularCyclotomicCharacterを絶対ガロア群へ制限できる。
その指標の定義式は、ガロア作用がμₚ上で指標によるスカラー倍となることそのものである。
楕円曲線のWeil対を構成する前に独立に固定できる、円分側の数学である。
-/
namespace DkMath.Lib.NumberTheory.CyclotomicRootModule
variable (L : Type*) [Field L] (n : ℕ)

/-- n乗根の乗法群を、積を加法とする型に読み替える。 -/
abbrev RootSpace := Additive (rootsOfUnity n L)

/-- n乗で1になることを、n倍で零になる加法群のZMod加群へ翻訳する。 -/
noncomputable instance rootModule : Module (ZMod n) (RootSpace L n) :=
  AddCommGroup.zmodModule (by
    intro z
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    apply Subtype.ext
    exact (mem_rootsOfUnity n z.toMul.val).mp z.toMul.property)

/-- 根の空間のスカラー倍は、ZModの代表元を用いた通常の冪である。 -/
theorem smul_toMul [NeZero n] (a : ZMod n) (z : RootSpace L n) :
    (a • z).toMul = z.toMul ^ a.val := by
  rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, toMul_nsmul]
  simp only [ZMod.natCast_zmod_val]

variable {K : Type*} [Field K] [CharZero K] (p : ℕ) [Fact p.Prime]

/-- 代数閉包の根の個数はpであり、楕円曲線の位数公式を必要としない。 -/
theorem prime_root_card : Nat.card (rootsOfUnity p (AlgebraicClosure K)) = p :=
  HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) p

/-- p乗根への作用で定まる実際のmod p円分指標。原始根の選択に依存しない。 -/
noncomputable def cyclotomicCharacter : Field.absoluteGaloisGroup K →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure K) (prime_root_card (K := K) p)).comp
    { toFun := fun σ => σ.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- 円分指標は全てのp乗根へのガロア作用を同時に記述する。 -/
theorem cyclotomicCharacter_spec (σ : Field.absoluteGaloisGroup K)
    (z : rootsOfUnity p (AlgebraicClosure K)) :
    σ.toAlgHom (z.val : AlgebraicClosure K) =
      (z.val : AlgebraicClosure K) ^ (cyclotomicCharacter p σ : ZMod p).val :=
  modularCyclotomicCharacter.spec (AlgebraicClosure K) (prime_root_card (K := K) p)
    σ.toRingEquiv z.property

end DkMath.Lib.NumberTheory.CyclotomicRootModule

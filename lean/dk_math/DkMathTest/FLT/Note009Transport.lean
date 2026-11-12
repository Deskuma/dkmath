/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularCharacterTransport37
import DkMath.FLT.FreyCounterexample

#print "file: DkMathTest.FLT.Note009Transport"

/-!
# NOTE-009 回帰: 位相と指標、正規化と元の整数

B₃₂から得るのは対象指標の同定まで。非零類は作らない。
37次Sourceは任意の整数反例を入力とする条件付き構成として検査する。
原始化と偶奇操作は実在する指数1の整数解で検査し、指数5以上の実例と混同しない。
-/
namespace Note009TransportTest
open DkMath.Lib.NumberTheory Cyclotomic37CharacterDecomposition
open DkMath.FLT.Kummer.IrregularPrime37
open scoped NumberField
attribute [local instance] prime37 cyclotomic37

example : character (generator ^ 32) = powMonoidHom 32 := character_generator_pow 32
example : character bernoulli32Label = powMonoidHom 5 := bernoulli32_character
example : (1 - (32 : ZMod 36)) = 5 := bernoulli32_residual_exponent
example : bernoulli32Label ≠ 1 := bernoulli32Label_ne_one
example : ((character bernoulli32Label (Units.mk0 2 (by decide)) : (ZMod 37)ˣ) : ZMod 37) = 32 := by
  rw [bernoulli32_character]
  rfl
example : ((character bernoulli32Label (-1) : (ZMod 37)ˣ) : ZMod 37) = -1 := by
  rw [bernoulli32_character]
  change (-1 : ZMod 37) ^ 5 = -1
  norm_num
example (x : Space Cyclotomic37) (a : (ZMod 37)ˣ) :
    characterSupport (action a x) = characterSupport x := characterSupport_action a x
example (x : Space Cyclotomic37) (a : (ZMod 37)ˣ) :
    projector bernoulli32Label (action a x) = (a : ZMod 37) ^ 5 • projector bernoulli32Label x := by
  rw [projector_action, bernoulli32_character]
  rfl

example {m : ℕ} (E : DkMath.FLT.Kummer.RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (i : Fin 37) (hi : i ≠ 0) :
    characterSupport (observeVector E i) = characterSupport (observeVector E 1) :=
  observe_nonzero_characterSupport_eq E A B hx hy i hi
example {m : ℕ} (E : DkMath.FLT.Kummer.RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37)) :
    projector bernoulli32Label (observeVector E 0) = 0 := observe_zero_projector E A B hx hy _
example {m : ℕ} (E : DkMath.FLT.Kummer.RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = (A : 𝓞 Cyclotomic37)) (hy : E.y = (B : 𝓞 Cyclotomic37))
    (i : Fin 37) (hi : i ≠ 0) :
    projector bernoulli32Label (observeVector E i) ≠ 0 ↔
      projector bernoulli32Label (observeVector E 1) ≠ 0 :=
  observe_nonzero_projector_iff E A B hx hy _ i hi

open DkMath.FLT.Frey
example : ¬ IsCoprime (6 : ℤ) 32 := by norm_num [Int.isCoprime_iff_gcd_eq_one]
example : Nonempty (PrimitiveReduction 1 6 32 38) :=
  exists_primitiveReduction (by decide) (by decide) (by decide) (by decide) (by norm_num)
example : Nonempty (PrimitiveReduction 1 (-6) (-32) (-38)) :=
  exists_primitiveReduction (by decide) (by decide) (by decide) (by decide) (by norm_num)
-- 右辺が偶数の場合も、実際の整数解3+13=16で確認する。
example : ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ IsCoprime x y ∧
    x ^ 1 + y ^ 1 = z ^ 1 ∧ Odd x ∧ Even y ∧ ParityTrace 3 13 16 x y z :=
  orient_parity (by decide) (by decide) (by decide) (by decide) (by decide)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)
-- 偶数が最初の座標にある場合の交換。
example : ∃ x y z : ℤ, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ IsCoprime x y ∧
    x ^ 1 + y ^ 1 = z ^ 1 ∧ Odd x ∧ Even y ∧ ParityTrace 16 3 19 x y z :=
  orient_parity (by decide) (by decide) (by decide) (by decide) (by decide)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)
example : 4 ∣ -(1 : ℤ) + 1 :=
  (odd_mod_four_orientation (by decide : Odd (1 : ℤ))).resolve_left (by decide)
example : 4 ∣ (-1 : ℤ) + 1 :=
  (odd_mod_four_orientation (by decide : Odd (-1 : ℤ))).resolve_right (by decide)

noncomputable example (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ 37 + b ^ 37 = c ^ 37) : Source 37 :=
  Source.ofCounterexample 37 (by decide) (by decide) a b c ha hb hc he
example (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ 37 + b ^ 37 = c ^ 37) :
    let S := Source.ofCounterexample 37 (by decide) (by decide) a b c ha hb hc he
    4 ∣ S.a + 1 ∧ Even S.b ∧
      ∃ R : PrimitiveReduction 37 a b c, OrientationTrace R.A R.B R.C S.a S.b S.c :=
  Source.ofCounterexample_spec 37 (by decide) (by decide) a b c ha hb hc he
end Note009TransportTest

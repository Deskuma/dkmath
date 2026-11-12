/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.IrregularGalois37

#print "file: DkMathTest.FLT.Kummer.GaloisPhaseObstruction"

/-!
# IRR-006 回帰: 本当の円分体作用、単元補正、既存 State への接続

37次の負号作用で λ が固定されないことを確認する。これにより、正規化後の
元の等式から単元補正を省く誤った実装を検出する。添字0・非零添字・逆作用を含む。
-/

namespace GaloisPhaseObstructionTest
open DkMath.Lib.NumberTheory DkMath.FLT.Kummer
open RamifiedPhasePacket
open scoped NumberField nonZeroDivisors

local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : IsCyclotomicExtension {37} ℚ IrregularPrime37.Cyclotomic37 :=
  CyclotomicField.isCyclotomicExtension 37 ℚ

open IrregularPrime37

-- 2·20 ≡ 3 (mod 37): 還元せず自然数40の位相を使う実装を検出する。
example : phaseMul (ZMod.unitOfCoprime 2 (by decide) : (ZMod 37)ˣ) (20 : Fin 37) = 3 := by
  decide

example : phaseMul (-1 : (ZMod 37)ˣ) (1 : Fin 37) = 36 := by decide
example : phaseMul (-1 : (ZMod 37)ˣ) (0 : Fin 37) = 0 := by decide

example (a : (ZMod 37)ˣ) (i : Fin 37) : phaseMul a⁻¹ (phaseMul a i) = i :=
  (phasePerm a).left_inv i

example (a b : (ZMod 37)ˣ) (w : ClassGroup (𝓞 Cyclotomic37)) :
    ClassGroup.mulEquiv (sigma37 (a * b)) w =
      ClassGroup.mulEquiv (sigma37 a) (ClassGroup.mulEquiv (sigma37 b) w) := by
  have hs : sigma37 (a * b) = (sigma37 b).trans (sigma37 a) :=
    CyclotomicPhaseGalois.sigma_mul a b
  rw [hs, classGroup_map_trans]

-- σ₋₁ は ζ を ζ³⁶ へ運ぶ。体上の作用が整数環上にも一致する。
example : sigma37 (-1) phase37.zeta = phase37.zeta ^ 36 :=
  CyclotomicPhaseGalois.sigma_zeta
    (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) (-1)

-- λ は固定されない。正規化後には実際に補正が必要。
example : sigma37 (-1) phase37.lambda ≠ phase37.lambda := by
  intro h
  have he : phase37.zeta ^ 36 = phase37.zeta := by
    have hz : sigma37 (-1) phase37.zeta = phase37.zeta ^ 36 :=
      CyclotomicPhaseGalois.sigma_zeta
        (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) (-1)
    rw [phase37.lambda_eq, map_sub, map_one, hz] at h
    linear_combination -h
  have hi := phase37.primitive.pow_inj (by decide : 36 < 37) (by decide : 1 < 37)
    (by simpa only [pow_one] using he)
  omega

-- 2のガロア作用の補正単元は1+ζ。符号を逆に選ぶ間違いも検出する。
example : IsUnit (1 + phase37.zeta) := by
  let a : (ZMod 37)ˣ := ZMod.unitOfCoprime 2 (by decide)
  obtain ⟨c, hc⟩ := CyclotomicPhaseGalois.exists_ramifier_unit
    (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) (by decide) a
  have he : sigma37 a phase37.zeta = phase37.zeta ^ 2 :=
    CyclotomicPhaseGalois.sigma_zeta
      (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) a
  change sigma37 a phase37.lambda = (c : 𝓞 Cyclotomic37) * phase37.lambda at hc
  have hunit : (c : 𝓞 Cyclotomic37) = 1 + phase37.zeta := by
    apply mul_right_cancel₀ phase37.lambda_prime.ne_zero
    rw [← hc, phase37.lambda_eq, map_sub, map_one, he]
    ring
  rw [← hunit]
  exact c.isUnit

-- 実際の観測 packet の選択済み根に対する、整数座標付き State の輸送。
example {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (A B : ℤ) (hx : E.x = A) (hy : E.y = B) (a : (ZMod 37)ˣ) (i : Fin 37) :
    ClassGroup.mulEquiv (sigma37 a) ((observe E).phases.obstruction i) =
      (observe E).phases.obstruction (phaseMul a i) :=
  (observe_galois E A B hx hy a i).2

-- 非自明な障害は自己同型で消えない。積が1でも個別消滅を結論しない。
example (a : (ZMod 37)ˣ) (w : ClassGroup (𝓞 Cyclotomic37)) (hw : w ≠ 1) :
    ClassGroup.mulEquiv (sigma37 a) w ≠ 1 := by
  intro h
  exact hw ((ClassGroup.mulEquiv (sigma37 a)).injective (h.trans (map_one _).symm))

end GaloisPhaseObstructionTest

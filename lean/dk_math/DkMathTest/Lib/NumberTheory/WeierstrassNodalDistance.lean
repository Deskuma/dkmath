/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.WeierstrassNodalDistance
import DkMathTest.Lib.NumberTheory.WeierstrassNodalOrbit

#print "file: DkMathTest.Lib.NumberTheory.WeierstrassNodalDistance"

/-! 既存の節点曲線と実際の37点軌道で、候補中心からの分離を確認する。 -/
namespace WeierstrassNodalDistanceTest
open WeierstrassCurve WeierstrassCurve.Affine
open DkMath.Lib.NumberTheory WeierstrassNodalDistance WeierstrassNodalOrbit
open EllipticNodalTorsion.NodalTorsion WeierstrassNodalVeluTest WeierstrassNodalOrbitTest
noncomputable section
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {k : Type*} [Field k] {m n : ℕ} [Fact m.Prime] [Fact n.Prime]

/-- 異なる素数位数の実点と実核の軌道は、候補中心から離れる。 -/
theorem actual_orbit_avoids_candidate {u v : k} (hu : IsPrimitiveRoot u m) (hv : IsPrimitiveRoot v n)
    (hnd : ¬ m ∣ n) (hn : (n : k) ≠ 0) :
    (∑ j ∈ Finset.range n, (rootPoint hu + j • rootPoint hv).xc) -
      (∑ j ∈ Finset.range n, (j • rootPoint hv).xc) ≠
        (n : k) * 0 - ∑ j ∈ Finset.range n, (j • rootPoint hv).xc := by
  have F : Frame (splitCurve k) 0 0 0 := by constructor <;> norm_num [splitCurve]
  have hsep : (0 : k) ≠ -(splitCurve k).a₁ - 0 := by norm_num [splitCurve]
  have hQ : IsPrimitiveRoot (tc (splitCurve k) 0 0 0 (rootPoint hv)) n := by
    change IsPrimitiveRoot (tc (splitCurve k) 0 0 0 (parameterPoint _ _ _)) n
    rw [parameter_tc]
    exact hv
  have hP : n • rootPoint hu ≠ 0 := by
    intro he
    have ht := (nsmul_eq_zero_iff F hsep (rootPoint hu)).mp he
    change tc (splitCurve k) 0 0 0 (parameterPoint _ _ _) ^ n = 1 at ht
    rw [parameter_tc] at ht
    exact hnd (hu.dvd_of_pow_eq_one n ht)
  exact normalized_x_ne_candidate F hsep hn _ _ hQ hP

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 標数2の実37点核と位数5の実点で、候補中心からの分離が成立する。 -/
theorem characteristic_two_37_avoids_candidate :
    ∃ (u v : AlgebraicClosure (ZMod 2)) (hu : IsPrimitiveRoot u 5) (hv : IsPrimitiveRoot v 37),
      (∑ j ∈ Finset.range 37, (rootPoint hu + j • rootPoint hv).xc) -
        (∑ j ∈ Finset.range 37, (j • rootPoint hv).xc) ≠
          (37 : AlgebraicClosure (ZMod 2)) * 0 - ∑ j ∈ Finset.range 37, (j • rootPoint hv).xc := by
  have : NeZero (5 : ZMod 2) := ⟨by decide⟩
  have : NeZero (37 : ZMod 2) := ⟨by decide⟩
  obtain ⟨u, hu⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 5
  obtain ⟨v, hv⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ZMod 2)) 37
  have hn : (37 : AlgebraicClosure (ZMod 2)) ≠ 0 := by
    have he : (37 : AlgebraicClosure (ZMod 2)) = 1 := by
      simpa only [map_ofNat, map_one] using congrArg (algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)))
        (by decide : (37 : ZMod 2) = 1)
    rw [he]; exact one_ne_zero
  exact ⟨u, v, hu, hv, actual_orbit_avoids_candidate hu hv (by decide) hn⟩

/-- 既存の実3点核の源を47で還元した曲線。 -/
def sampleSource47 : WeierstrassCurve (ZMod 47) := ⟨1, 0, 7, 0, 0⟩

/-- 同じ実3点核による既存標的の47での剰余曲線。 -/
def sampleTarget47 : WeierstrassCurve (ZMod 47) := ⟨1, 0, 7, -35, -350⟩

/-- この具体例では源の節点は(26,7)、標的の節点は(31,28)。
核のx座標は全て0なので、候補中心3·26−0=31が実際の標的節点に一致する。 -/
theorem concrete_target_candidate :
    sampleSource47.toAffine.Equation 26 7 ∧ ¬ sampleSource47.toAffine.Nonsingular 26 7 ∧
    sampleTarget47.toAffine.Equation 31 28 ∧ ¬ sampleTarget47.toAffine.Nonsingular 31 28 ∧
      (3 : ZMod 47) * 26 - (0 + 0 + 0) = 31 := by
  norm_num [sampleSource47, sampleTarget47, equation_iff', nonsingular_iff']; decide

end
end WeierstrassNodalDistanceTest

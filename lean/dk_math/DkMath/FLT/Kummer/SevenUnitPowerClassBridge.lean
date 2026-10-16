/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Algebra.UnitPowerClass
import DkMath.FLT.Kummer.SevenKummerUnit
import DkMath.FLT.Seven.CurrentCarrierNormalizedPower

/-!
# 単元の同一性から、七乗剰余類の比較へ

GN と現在の carrier の根や単元を同一視せず、正確な因子表示を比較する。
現在の分岐因子は `1-zeta`、GN は `zeta^i-1` なので、補正単元 `-S_i` を保持する。
現在の source と GN source の等式は明示的な入力であり、この章では構成しない。
-/

open scoped BigOperators NumberField
open DkMath.FLT.Seven DkMath.Lib.NumberTheory DkMath.Lib.Algebra

namespace DkMath.FLT.Kummer.SevenPrimaryNorm

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

/-- GN の元そのものを、向きを固定した環同型で六次モデルへ運ぶ。 -/
def GNPhaseFactor (x u : ℤ) (i : ℕ) : SevenCyclotomicDegreeSixInt.Ring :=
  integralEquiv ((x : 𝓞 (CyclotomicField 7 ℚ)) +
    (1 - septicRoot_spec.toInteger ^ i) * (u : 𝓞 (CyclotomicField 7 ℚ)))

/-- 分岐因子を `zeta^i-1` から `1-zeta` へ揃える補正単元は `-S_i`。 -/
def GNRamifierTwist {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) :
    SevenCyclotomicDegreeSixInt.Ringˣ :=
  -(Units.map integralEquiv.toMonoidHom (ramifiedGeomUnit septicRoot_spec hi))

/-- 補正単元と現在の分岐因子の積が、GN の分岐因子に厳密に一致する。 -/
theorem GNRamifierTwist_spec {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) :
    (GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ring) *
      SevenCyclotomicDegreeSixInt.ramifiedUniformizer = SevenCyclotomicDegreeSixInt.zeta ^ i - 1 := by
  change -(integralEquiv (ramifiedGeomUnit septicRoot_spec hi : _)) *
    (1 - SevenCyclotomicDegreeSixInt.zeta) = _
  rw [ramifiedGeomUnit_val, map_sum]
  simp_rw [map_pow, integralEquiv_septicRoot]
  linear_combination -(mul_neg_geom_sum SevenCyclotomicDegreeSixInt.zeta i)

/-- 同じ GN パケットの分解を、現在の分岐因子に揃えて書き直す。 -/
theorem GNPhaseFactor_decomposition {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket septicRoot_spec x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction septicRoot_spec (by decide : Odd 7) (Q.generator i) = 1) :
    GNPhaseFactor x u i = SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
      (((GNRamifierTwist hi * Units.map integralEquiv.toMonoidHom (Q.primaryUnit hi) :
          SevenCyclotomicDegreeSixInt.Ringˣ) : SevenCyclotomicDegreeSixInt.Ring) *
        integralEquiv (Q.generator i) ^ 7) := by
  have heq := congrArg integralEquiv (Q.primaryUnit_spec (by decide : Odd 7) hi hγ).2.2
  change GNPhaseFactor x u i = _ at heq
  rw [map_mul, map_sub, map_pow, map_one, integralEquiv_septicRoot,
    map_mul, map_pow] at heq
  rw [heq, ← GNRamifierTwist_spec hi]
  change ((GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ring) *
      SevenCyclotomicDegreeSixInt.ramifiedUniformizer) *
      (integralEquiv (Q.primaryUnit hi : _) * integralEquiv (Q.generator i) ^ 7) =
    SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
      (((GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ring) *
        integralEquiv (Q.primaryUnit hi : _)) * integralEquiv (Q.generator i) ^ 7)
  ring

/-- 同じ非零 GN source の任意の剥離分解の単元は、補正単元 -S_i と同じ七乗剰余類。
一次単元 δ_i は七乗だが、-S_i 自身を七乗と仮定したことにはしない。 -/
theorem unit_class_of_GN_source {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket septicRoot_spec x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction septicRoot_spec (by decide : Odd 7) (Q.generator i) = 1)
    (ε : SevenCyclotomicDegreeSixInt.Ringˣ) (β : SevenCyclotomicDegreeSixInt.Ring)
    (hA : GNPhaseFactor x u i ≠ 0)
    (hleft : GNPhaseFactor x u i = SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
      ((ε : SevenCyclotomicDegreeSixInt.Ring) * β ^ 7)) :
    (ε : SevenCyclotomicDegreeSixInt.Ringˣ ⧸ unitPowerSubgroup SevenCyclotomicDegreeSixInt.Ring 7) =
      (GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ringˣ ⧸
        unitPowerSubgroup SevenCyclotomicDegreeSixInt.Ring 7) := by
  let δ := Units.map integralEquiv.toMonoidHom (Q.primaryUnit hi)
  have he := quotient_eq_of_fixed_extraction ε (GNRamifierTwist hi * δ)
    (by decide : 7 ≠ 0) hA SevenCyclotomicDegreeSixInt.ramifiedUniformizer_ne_zero
    hleft (GNPhaseFactor_decomposition Q hi hγ)
  obtain ⟨κ, hk⟩ := GN_primary_unit_seventh Q hi hγ
  have hδ : δ = (Units.map integralEquiv.toMonoidHom κ) ^ 7 := by
    dsimp only [δ]
    rw [hk, map_pow]
  rw [hδ, QuotientGroup.mk_mul] at he
  have hp : (((Units.map integralEquiv.toMonoidHom κ) ^ 7 : SevenCyclotomicDegreeSixInt.Ringˣ) :
      SevenCyclotomicDegreeSixInt.Ringˣ ⧸ unitPowerSubgroup SevenCyclotomicDegreeSixInt.Ring 7) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨Units.map integralEquiv.toMonoidHom κ, rfl⟩
  simpa only [hp, mul_one] using he

/-- 一般位相でも、既知の補正単元を除いた単元は七乗。
補正自身を七乗と仮定せず、比較で得た同じ七乗剰余類を実際の根へ戻す。 -/
theorem unit_seventh_after_twist_of_GN_source {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket septicRoot_spec x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction septicRoot_spec (by decide : Odd 7) (Q.generator i) = 1)
    (ε : SevenCyclotomicDegreeSixInt.Ringˣ) (β : SevenCyclotomicDegreeSixInt.Ring)
    (hA : GNPhaseFactor x u i ≠ 0)
    (hleft : GNPhaseFactor x u i = SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
      ((ε : SevenCyclotomicDegreeSixInt.Ring) * β ^ 7)) :
    ∃ k : SevenCyclotomicDegreeSixInt.Ringˣ, ε * (GNRamifierTwist hi)⁻¹ = k ^ 7 := by
  obtain ⟨k, hk⟩ := sameUnitPowerClass_iff_quotient_eq.mpr
    (unit_class_of_GN_source Q hi hγ ε β hA hleft)
  refine ⟨k, ?_⟩
  rw [hk, mul_comm (GNRamifierTwist hi) (k ^ 7), mul_assoc, mul_inv_cancel, mul_one]

/-- 第1位相では補正単元は -1。七乗剰余類として自明であり、符号を安全に吸収できる。 -/
theorem GNRamifierTwist_one (hi : 1 ∈ (Finset.range 7).erase 0) : GNRamifierTwist hi = -1 := by
  apply Units.ext
  change -(integralEquiv (ramifiedGeomUnit septicRoot_spec hi : _)) = -1
  rw [ramifiedGeomUnit_val]
  simp

/-- 第2位相の補正単元のノルムは `1+alpha`。固定した単元の等式として記録する。 -/
theorem GNRamifierTwist_two_norm (hi : 2 ∈ (Finset.range 7).erase 0) :
    Units.map relativeNorm (GNRamifierTwist hi) = SevenRealCubicInt.alphaAddOneUnit := by
  have ht : (GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ring) =
      -1 - SevenCyclotomicDegreeSixInt.zeta := by
    change -(integralEquiv (ramifiedGeomUnit septicRoot_spec hi : _)) = _
    rw [ramifiedGeomUnit_val]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
      zero_add, map_add, map_one, integralEquiv_septicRoot]
    ring
  apply Units.ext
  change relativeNorm (GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ring) =
    (SevenRealCubicInt.alphaAddOneUnit : SevenRealCubicInt)
  rw [ht, SevenRealCubicInt.alphaAddOneUnit_val]
  simp [relativeNorm, QuadraticAlgebra.norm_def, SevenCyclotomicDegreeSixInt.zeta,
    show (1 : SevenCyclotomicDegreeSixInt.Ring) = ⟨1, 0⟩ from rfl]
  ring

/-- 第2位相の補正は実際に七乗ではない。
ノルムの射影対数が `(2,5)` であり、七乗なら零になることに反する。 -/
theorem GNRamifierTwist_two_not_seventh (hi : 2 ∈ (Finset.range 7).erase 0) :
    ¬ ∃ k : SevenCyclotomicDegreeSixInt.Ringˣ, GNRamifierTwist hi = k ^ 7 := by
  rintro ⟨k, hk⟩
  have hn := congrArg (Units.map relativeNorm) hk
  rw [GNRamifierTwist_two_norm hi, map_pow] at hn
  have hz := SevenRealCubicInt.projectiveLog_pow_seven (Units.map relativeNorm k)
  rw [← hn, SevenRealCubicInt.projectiveLog_alphaAddOne] at hz
  have hf := congrArg Prod.fst hz
  exact (by decide : (2 : ZMod 7) ≠ 0) hf

/-- 補正単元自身にも七乗根がある場合、比較した任意の単元の七乗根を移せる。
一般位相ではこの補正条件を省略しない。 -/
theorem unit_seventh_of_GN_source {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket septicRoot_spec x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction septicRoot_spec (by decide : Odd 7) (Q.generator i) = 1)
    (ε : SevenCyclotomicDegreeSixInt.Ringˣ) (β : SevenCyclotomicDegreeSixInt.Ring)
    (hA : GNPhaseFactor x u i ≠ 0)
    (hleft : GNPhaseFactor x u i = SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
      ((ε : SevenCyclotomicDegreeSixInt.Ring) * β ^ 7))
    (htwist : ∃ k : SevenCyclotomicDegreeSixInt.Ringˣ, GNRamifierTwist hi = k ^ 7) :
    ∃ k : SevenCyclotomicDegreeSixInt.Ringˣ, ε = k ^ 7 :=
  exists_unit_pow_of_same_class
    (sameUnitPowerClass_iff_quotient_eq.mpr (unit_class_of_GN_source Q hi hγ ε β hA hleft)) htwist

open SevenRealCubic SevenRealCubic.CurrentCarrierRamification
open SevenRealCubic.CurrentCarrierPower

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- 実在する current carrier receiver の単元を、GN source との等式を入力に比較する。
根や単元の同一性は要求しない。source の等式はこの定理では構成しない。 -/
theorem currentCarrier_unit_class_of_GN_source
    (c : CurrentCommonPrimeCyclotomicPacket h q) {x u v : ℤ}
    (Q : RamifiedPrincipalPowerPacket septicRoot_spec x u v) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction septicRoot_spec (by decide : Odd 7) (Q.generator i) = 1)
    (hsame : currentLinearCarrier c = GNPhaseFactor x u i) :
    ∃ ε : SevenCyclotomicDegreeSixInt.Ringˣ, ∃ β : SevenCyclotomicDegreeSixInt.Ring,
      currentLinearCarrier c = SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
        ((ε : SevenCyclotomicDegreeSixInt.Ring) * β ^ 7) ∧
      (ε : SevenCyclotomicDegreeSixInt.Ringˣ ⧸ unitPowerSubgroup SevenCyclotomicDegreeSixInt.Ring 7) =
        (GNRamifierTwist hi : SevenCyclotomicDegreeSixInt.Ringˣ ⧸
          unitPowerSubgroup SevenCyclotomicDegreeSixInt.Ring 7) ∧ Fermat7Equation a b d := by
  obtain ⟨w, β, hw, hfact, hfermat⟩ := currentCarrier_ramified_element_receiver c
  have hA : currentLinearCarrier c ≠ 0 := by
    intro hz
    apply currentLinearCarrier_not_mem_ramifiedPrime_sq c
    rw [hz]
    exact Ideal.zero_mem _
  have hf : currentLinearCarrier c = SevenCyclotomicDegreeSixInt.ramifiedUniformizer *
      ((hw.unit : SevenCyclotomicDegreeSixInt.Ring) * β ^ 7) := by
    rw [IsUnit.unit_spec]
    exact hfact.trans (mul_assoc _ _ _)
  refine ⟨hw.unit, β, hf, ?_, hfermat⟩
  exact unit_class_of_GN_source Q hi hγ hw.unit β (hsame ▸ hA) (hsame ▸ hf)

end

end DkMath.FLT.Kummer.SevenPrimaryNorm

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenPrimaryNorm
import DkMath.FLT.Kummer.GNRamifiedPrimary
import DkMath.FLT.Seven.SevenRamifiedFusionCyclotomicDegreeSixPID

#print "file: DkMath.FLT.Kummer.SevenPrimaryNormBridge"

/-!
# GN の一次単元を六次モデルの相対ノルムへ接続する

既存の整数冪基底写像の単射・全射を環同型に束ねる。
ノルムの値だけで元を同一視せず、円分整数環の元そのものを写してから
実三次ノルムを取る。この章では単元そのものの七乗性と降下はまだ主張しない。
-/

namespace DkMath.FLT.Kummer.SevenPrimaryNorm

open scoped NumberField
open DkMath.FLT.Seven DkMath.Lib.NumberTheory

noncomputable section

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : IsCyclotomicExtension {7} ℚ (CyclotomicField 7 ℚ) :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

/-- 既存の整数冪基底写像を、逆写像を持つ環同型として公開する。
Mathlib の選んだ原始根を、具体的六次モデルの `zeta` へ送る向き。 -/
def integralEquiv : 𝓞 (CyclotomicField 7 ℚ) ≃+* SevenCyclotomicDegreeSixInt.Ring :=
  RingEquiv.ofBijective SevenCyclotomicDegreeSixInt.ringOfIntegersToRing.toRingHom
    ⟨SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_injective,
      SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_surjective⟩

/-- 同型の位相を固定する生成元の等式。 -/
theorem integralEquiv_generator :
    integralEquiv SevenCyclotomicDegreeSixInt.cyclotomicIntegralGenerator =
      SevenCyclotomicDegreeSixInt.zeta :=
  SevenCyclotomicDegreeSixInt.ringOfIntegersToRing_cyclotomicIntegralGenerator

/-- 円分整数環上の相対ノルム。六次モデルの乗法的二次ノルムを同型で輸送する。 -/
def integralRelativeNorm : 𝓞 (CyclotomicField 7 ℚ) →* SevenRealCubicInt :=
  relativeNorm.comp integralEquiv.toMonoidHom

/-- 整数との合同を同型の先へ移す。整数の埋め込みも同じ写像で固定される。 -/
theorem integralEquiv_congruent_integer
    {x : 𝓞 (CyclotomicField 7 ℚ)} {n : ℤ}
    (h : (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ x - (n : _)) :
    (7 : SevenCyclotomicDegreeSixInt.Ring) ∣ integralEquiv x - (n : _) := by
  have hm := map_dvd integralEquiv.toRingHom h
  change integralEquiv (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ integralEquiv (x - (n : _)) at hm
  simpa only [map_ofNat, map_sub, map_intCast] using hm

/-- GN 側の円分整数環でも、整数と mod 7 で合同な単元の相対ノルムは七乗。 -/
theorem integralRelativeNorm_primary_unit_seventh
    (u : (𝓞 (CyclotomicField 7 ℚ))ˣ)
    (h : ∃ n : ℤ, (7 : 𝓞 (CyclotomicField 7 ℚ)) ∣ (u : _) - (n : _)) :
    ∃ v : SevenRealCubicIntˣ, Units.map integralRelativeNorm u = v ^ 7 := by
  obtain ⟨n, hn⟩ := h
  exact relativeNorm_primary_unit_seventh (Units.map integralEquiv.toMonoidHom u)
    ⟨n, integralEquiv_congruent_integer hn⟩

/-- 同じ GN 保存パケットの一次単元 δᵢ にノルム根を与える。
`γᵢ ≡ 1 mod λ` の正規化を入力に、既存の合同定理を実際に適用する。
追加の単元補題を仮定しないが、δᵢ 自身の七乗根はこの結論に含めない。 -/
theorem GN_primary_unit_relativeNorm_seventh
    {ζ : CyclotomicField 7 ℚ} {hζ : IsPrimitiveRoot ζ 7} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0)
    (hγ : ramifiedReduction hζ (by decide : Odd 7) (Q.generator i) = 1) :
    ∃ v : SevenRealCubicIntˣ,
      Units.map integralRelativeNorm (Q.primaryUnit hi) = v ^ 7 := by
  exact integralRelativeNorm_primary_unit_seventh (Q.primaryUnit hi)
    ⟨-u, Q.primaryUnit_congruent_integer (by decide : Odd 7) hi hγ⟩

end

end DkMath.FLT.Kummer.SevenPrimaryNorm

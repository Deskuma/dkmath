/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.GaloisPhaseOrbitNorm
import DkMath.Lib.NumberTheory.GaloisIdealNorm

#print "file: DkMath.Lib.NumberTheory.CyclotomicClassNorm"

/-!
# IRR-008: 円分体の軌道ノルムの消滅

全イデアル共役積の整数ノルム公式を、単元群で索引した既存の `orbitNorm` へ運ぶ。
類群の自明性・正則性を仮定しない。ω₀N(ω₁)=1 への代入で位相0だけを除去し、
非零軌道に残る p-torsion の消滅とは区別する。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPhaseGalois
open scoped NumberField
variable {K : Type*} [Field K] [NumberField K]
  {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

/-- 真の類群上の全共役ノルムは1。ℚの整数イデアルが主イデアルであることを使う。 -/
theorem orbitNorm_eq_one (w : ClassGroup (𝓞 K)) : orbitNorm (p := p) w = 1 := by
  let := IsCyclotomicExtension.isGalois {p} ℚ K
  have h := GaloisIdealNorm.classGroup_prod_eq_one w
  rw [orbitNorm]
  rw [← (IsCyclotomicExtension.Rat.galEquivZMod p K).symm.toEquiv.prod_comp
    (fun σ => ClassGroup.mulEquiv (GaloisIdealNorm.integerAut σ) w)] at h
  exact h

/-- 整数係数の位相族では正則性なしに位相0の障害が消える。非零位相は結論に含めない。 -/
theorem zero_obstruction_eq_one
    (hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p) (hodd : Odd p)
    (C : PhaseClassPacket (𝓞 K) p (Fin p)) (q : 𝓞 K) (A B : ℤ)
    (hq : (A : 𝓞 K) + B = (cyclotomicRamifiedPhase hζ hodd).lambda * q)
    (hf : ∀ i, C.factor i = (cyclotomicRamifiedPhase hζ hodd).quotient q B i)
    (hprod : ∏ i, C.obstruction i = 1) : C.obstruction 0 = 1 := by
  have h := zero_mul_orbitNorm hζ hodd C q A B hq hf hprod
  simpa only [orbitNorm_eq_one, mul_one] using h

/-- p-torsion のガロア固定部分は自明。N(w)=w^(p−1)=1 と w^p=1 を合成する。
全類群が自明であるとは述べず、非自明な指標成分の存在・次元は別に残す。 -/
theorem fixed_p_torsion_eq_one (w : ClassGroup (𝓞 K)) (ht : w ^ p = 1)
    (hf : ∀ a : (ZMod p)ˣ, ClassGroup.mulEquiv (sigma a) w = w) : w = 1 := by
  have hn := orbitNorm_eq_one (p := p) w
  simp only [orbitNorm, hf, Finset.prod_const, Finset.card_univ,
    ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)] at hn
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).pos
  have he : w ^ p = w := by rw [← hp, pow_succ, hn, one_mul]
  exact he.symm.trans ht

/-- p冪で消える固定類も自明。位数は互いに素な p^r と p−1 の両方を割る。 -/
theorem fixed_p_primary_eq_one (w : ClassGroup (𝓞 K)) (r : ℕ) (ht : w ^ (p ^ r) = 1)
    (hf : ∀ a : (ZMod p)ˣ, ClassGroup.mulEquiv (sigma a) w = w) : w = 1 := by
  have hn := orbitNorm_eq_one (p := p) w
  simp only [orbitNorm, hf, Finset.prod_const, Finset.card_univ,
    ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)] at hn
  have hc : Nat.Coprime p (p - 1) :=
    (Nat.coprime_self_sub_right (Fact.out : p.Prime).pos).mpr (Nat.coprime_one_right p)
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (hc.pow_left r)
    (orderOf_dvd_of_pow_eq_one ht) (orderOf_dvd_of_pow_eq_one hn)

/-- χ 固有の p-torsion 類の部分群。値 χ(a) は剰余体の標準代表による冪で作用する。
指数 p の部分だけを扱い、p冪で消える類全体の分類とは同一視しない。 -/
def characterComponent (χ : (ZMod p)ˣ →* (ZMod p)ˣ) : Subgroup (ClassGroup (𝓞 K)) where
  carrier := {w | w ^ p = 1 ∧ ∀ a, ClassGroup.mulEquiv (sigma a) w = w ^ (χ a).val.val}
  one_mem' := by simp
  mul_mem' hv hw := by
    refine ⟨by rw [mul_pow, hv.1, hw.1, one_mul], ?_⟩
    intro a
    rw [map_mul, hv.2 a, hw.2 a, mul_pow]
  inv_mem' hw := by
    refine ⟨by rw [inv_pow, hw.1, inv_one], ?_⟩
    intro a
    rw [map_inv, hw.2 a, inv_pow]

/-- 自明指標の p-torsion 成分は零部分群。非零指標の算術的分類への最初の境界。 -/
theorem trivial_characterComponent : characterComponent (K := K) (1 : (ZMod p)ˣ →* (ZMod p)ˣ) = ⊥ := by
  apply le_antisymm
  · intro w hw
    change w = 1
    apply fixed_p_torsion_eq_one w hw.1
    intro a
    simpa only [MonoidHom.one_apply, Units.val_one,
      ZMod.val_one'' (Fact.out : p.Prime).ne_one, pow_one] using hw.2 a
  · exact bot_le

end DkMath.Lib.NumberTheory.CyclotomicPhaseGalois

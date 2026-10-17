/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.CosmicRamifiedResidue
import DkMath.Lib.NumberTheory.CosmicRamifiedPacket

#print "file: DkMath.Lib.NumberTheory.CosmicRamifiedUnitNormalization"

/-!
# 分岐剰余を使う生成元と単元の正規化

`β=ε*γ^p` の γ は、同じ主イデアルの生成元の取り方で変えられる。
円分単元で γ の剰余の逆数を持ち上げ、γ を 1 mod λ に選び直す。
その補償を ε に移すので、β 自身もイデアル根も変わらない。
結果として ε の剰余は β の剰余、すなわち −i*u になる。

これは剰余一段での正規化である。ε が p 乗であることも、λ² やそれ以上での
合同条件も主張せず、単元群全体の p 乗写像の全射性も仮定しない。
-/

namespace DkMath.Lib.NumberTheory

open scoped BigOperators NumberField

/-- `β=ε*γ^p` を、同じ β と同伴な生成元のまま γ≡1 mod λ に正規化する。
非零な剰余 γ の逆数を大域的円分単元 e で持ち上げ、
`γ'=eγ`, `ε'=ε(e⁻¹)^p` と置く。従って剰余 ε' は β と一致する。 -/
theorem exists_residue_normalized_unit_mul_pow
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (hodd : Odd p)
    {β ε γ : 𝓞 K} (hβ : ¬ hζ.toInteger - 1 ∣ β) (hε : IsUnit ε)
    (hpow : β = ε * γ ^ p) :
    ∃ ε' γ' : 𝓞 K, IsUnit ε' ∧ Associated γ' γ ∧ β = ε' * γ' ^ p ∧
      ramifiedReduction hζ hodd γ' = 1 ∧
      ramifiedReduction hζ hodd ε' = ramifiedReduction hζ hodd β ∧
      ∃ e : (𝓞 K)ˣ, γ' = (e : 𝓞 K) * γ ∧ ε' = ε * (↑(e⁻¹) : 𝓞 K) ^ p := by
  let f := ramifiedReduction hζ hodd
  have hγ0 : f γ ≠ 0 := by
    intro h0
    apply hβ
    apply (ramifiedReduction_eq_zero_iff hζ hodd β).mp
    change f β = 0
    rw [hpow, map_mul, map_pow, h0, zero_pow hp.out.ne_zero, mul_zero]
  obtain ⟨e, he⟩ := exists_unit_lift_ramifiedResidue hζ hodd (Units.mk0 (f γ) hγ0)⁻¹
  have heγ : f (e : 𝓞 K) * f γ = 1 := by
    rw [he]
    simp [hγ0]
  let δ := (e : 𝓞 K) * γ
  let η := ε * (↑(e⁻¹) : 𝓞 K) ^ p
  have hη : IsUnit η := hε.mul ((e⁻¹).isUnit.pow p)
  have hnorm : β = η * δ ^ p := by
    have hcancel : η * δ ^ p = ε * γ ^ p := by
      calc
        _ = ε * ((↑(e⁻¹) : 𝓞 K) * (e : 𝓞 K)) ^ p * γ ^ p := by
          dsimp only [η, δ]
          simp only [mul_pow]
          ring
        _ = ε * γ ^ p := by simp
    exact hpow.trans hcancel.symm
  have hδ : f δ = 1 := by
    change f ((e : 𝓞 K) * γ) = 1
    rw [map_mul]
    exact heγ
  have hηred : f η = f β := by
    have h := congrArg f hnorm
    rw [map_mul, map_pow, hδ, one_pow, mul_one] at h
    exact h.symm
  refine ⟨η, δ, hη, ?_, hnorm, hδ, hηred, e, rfl, rfl⟩
  exact ⟨e⁻¹, by dsimp only [δ]; simp [mul_assoc, mul_comm]⟩

/-- 基底パケットの全剥離商の剰余を、同じ座標から読む。
原始性と正則性をこの合同式の追加仮定として課す必要はない。 -/
theorem RamifiedIdealPowerPacket.quotient_reduction
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) (hodd : Odd p)
    {i : ℕ} (hi : i ∈ (Finset.range p).erase 0) :
    ramifiedReduction hζ hodd (P.quotient i) = -(i : ZMod p) * (u : ZMod p) :=
  ramifiedReduction_stripped_phaseFactor hζ hodd P.prime_ge_three
    P.gap_divisible i (P.factor i hi).1

/-- 主イデアル化済みのパケットの生成元を、全非自明添字について同時に正規化する。
返すパケットの基底は入力と等しく、剥離商・イデアル根・GN の等式・付値を保持する。
追加されるのは `γᵢ≡1`, `εᵢ≡−i*u mod λ` という剰余一段の情報である。 -/
theorem RamifiedPrincipalPowerPacket.exists_residue_normalization
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (Q : RamifiedPrincipalPowerPacket hζ x u c) (hodd : Odd p) :
    ∃ Q' : RamifiedPrincipalPowerPacket hζ x u c,
      Q'.toRamifiedIdealPowerPacket = Q.toRamifiedIdealPowerPacket ∧
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q'.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q'.unitFactor i) = -(i : ZMod p) * (u : ZMod p) := by
  classical
  have hex (i : ℕ) : ∃ ε γ : 𝓞 K, i ∈ (Finset.range p).erase 0 →
      IsUnit ε ∧ Ideal.span ({γ} : Set (𝓞 K)) = Q.idealRoot i ∧
      Q.quotient i = ε * γ ^ p ∧ ramifiedReduction hζ hodd γ = 1 ∧
      ramifiedReduction hζ hodd ε = -(i : ZMod p) * (u : ZMod p) := by
    by_cases hi : i ∈ (Finset.range p).erase 0
    · obtain ⟨hε, hγ, hpow⟩ := Q.principal i hi
      obtain ⟨ε', γ', hε', hassoc, hpow', hγred, hεred, _⟩ :=
        exists_residue_normalized_unit_mul_pow hζ hodd (Q.factor i hi).2.1 hε hpow
      refine ⟨ε', γ', fun _ => ⟨hε', ?_, hpow', hγred, ?_⟩⟩
      · exact (Ideal.span_singleton_eq_span_singleton.mpr hassoc).trans hγ
      · exact hεred.trans (Q.toRamifiedIdealPowerPacket.quotient_reduction hodd hi)
    · exact ⟨1, 0, fun h => (hi h).elim⟩
  choose ε γ hdata using hex
  let Q' : RamifiedPrincipalPowerPacket hζ x u c := {
    toRamifiedIdealPowerPacket := Q.toRamifiedIdealPowerPacket
    unitFactor := ε
    generator := γ
    principal := fun i hi => ⟨(hdata i hi).1, (hdata i hi).2.1, (hdata i hi).2.2.1⟩ }
  exact ⟨Q', rfl, fun i hi => ⟨(hdata i hi).2.2.2.1, (hdata i hi).2.2.2.2⟩⟩

/-- 基底パケットから、類群条件を使って主イデアル化し、その後で剰余を正規化する。
この順序と基底への射影の等式により、剥離・冪抽出・生成元の選択を区別する。 -/
theorem RamifiedIdealPowerPacket.exists_residue_normalized_principal_extension
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]
    {ζ : K} {hζ : IsPrimitiveRoot ζ p} {x u c : ℤ}
    (P : RamifiedIdealPowerPacket hζ x u c) (hodd : Odd p)
    (hreg : Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))) :
    ∃ Q : RamifiedPrincipalPowerPacket hζ x u c,
      Q.toRamifiedIdealPowerPacket = P ∧
      ∀ i ∈ (Finset.range p).erase 0,
        ramifiedReduction hζ hodd (Q.generator i) = 1 ∧
        ramifiedReduction hζ hodd (Q.unitFactor i) = -(i : ZMod p) * (u : ZMod p) := by
  obtain ⟨Q, hQ⟩ := P.exists_principal_extension hreg
  obtain ⟨Q', hQ', hred⟩ := Q.exists_residue_normalization hodd
  exact ⟨Q', hQ'.trans hQ, hred⟩

end DkMath.Lib.NumberTheory

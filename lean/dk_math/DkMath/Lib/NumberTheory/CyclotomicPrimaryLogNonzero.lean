/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: retain the specified root and DkMath unit quotient and projector;
transport conjugates using the SAME baseCharacter equivalence, prove the actual
nonzero log evaluation, and supply hdetect internally without external imports.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryLogCriterion
import DkMath.Lib.NumberTheory.CyclotomicOmegaSquareProjector

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero"

/-!
# 同じ円分単元の ω² 射影に対する実際の非零評価

同じ rootField、同じ射影子、同じ primaryLog に対して Λ(e₂[1+ζ])=−h³λ²。
非零性を証明し、前段の hdetect を内部供給する。次元1は依然として入力である。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero

open CyclotomicTruncatedLog CyclotomicPrimaryLog CyclotomicPrimaryCongruence
open CyclotomicOmegaSquareProjector CyclotomicPrimaryUnitSpace CyclotomicKernelField
open CyclotomicKummerWeight CyclotomicKummerEquivariance KummerSelmerExact
open KummerSelmerUnitEquivariance CyclotomicPrimaryLogCriterion
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- 二項係数の整数恒等式。後の 1/2 の扱いに除算を導入しない。 -/
theorem two_mul_choose_two_add (a : ℕ) : 2 * a.choose 2 + a = a ^ 2 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    zify at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

section QRing

variable {Q : Type*} [CommRing Q]

/-- t³=0 の環での有限二項展開。 -/
theorem one_add_pow_trunc {t : Q} (ht : t ^ 3 = 0) (a : ℕ) :
    (1 + t) ^ a = 1 + (a : Q) * t + (a.choose 2 : Q) * t ^ 2 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination (n.choose 2 : Q) * ht

/-- 二項係数の整数恒等式を任意の可換環へ写す。 -/
theorem cast_choose_two (a : ℕ) : (2 : Q) * (a.choose 2 : Q) = (a : Q) ^ 2 - a := by
  have h := congrArg (Nat.cast : ℕ → Q) (two_mul_choose_two_add a)
  push_cast at h
  linear_combination h

/-- 標数 p と冪零性から、(2+s)^(p−1) を2次まで正確に計算する。 -/
theorem two_add_pow_sub_one [CharP Q p] (hp3 : 3 ≤ p) {h s : Q} (h2 : 2 * h = 1)
    (hs : s ^ 3 = 0) : (2 + s) ^ (p - 1) = 1 - h * s + h ^ 2 * s ^ 2 := by
  have hsp : s ^ p = 0 := pow_eq_zero_of_le hp3 hs
  have h2p : (2 : Q) ^ p = 2 := by
    have e : (ZMod.castHom (dvd_refl p) Q) 2 = (2 : Q) := map_ofNat _ 2
    rw [← e, ← map_pow, ZMod.pow_card]
  have hp1 : (2 + s) ^ p = 2 := by rw [add_pow_char, hsp, h2p, add_zero]
  have hA : (1 - h * s + h ^ 2 * s ^ 2) * (2 + s) = 2 := by
    linear_combination (-s + h * s ^ 2) * h2 + h ^ 2 * hs
  have hsucc : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  calc (2 + s) ^ (p - 1)
      = (2 + s) ^ (p - 1) * (h * ((1 - h * s + h ^ 2 * s ^ 2) * (2 + s))) := by
          rw [hA, mul_comm h 2, h2, mul_one]
    _ = h * (1 - h * s + h ^ 2 * s ^ 2) * ((2 + s) ^ (p - 1) * (2 + s)) := by ring
    _ = h * (1 - h * s + h ^ 2 * s ^ 2) * 2 := by rw [← pow_succ, hsucc, hp1]
    _ = 1 - h * s + h ^ 2 * s ^ 2 := by linear_combination (1 - h * s + h ^ 2 * s ^ 2) * h2

/-- 上の正確な冪計算に切断対数を適用する。 -/
theorem tlog_two_add_pow_sub_one [CharP Q p] (hp3 : 3 ≤ p) {h s : Q} (h2 : 2 * h = 1)
    (hs : s ^ 3 = 0) : tlog h ((2 + s) ^ (p - 1)) = -(h * s) + (h ^ 2 - h ^ 3) * s ^ 2 := by
  rw [two_add_pow_sub_one (p := p) hp3 h2 hs, tlog]
  linear_combination (2 * h ^ 4 - h ^ 5 * s) * hs

/-- 共役された同じ円分単元 1+ζ^a の評価に使う環の式。 -/
theorem tlog_conj_eval [CharP Q p] (hp3 : 3 ≤ p) {h t : Q} (h2 : 2 * h = 1)
    (ht : t ^ 3 = 0) (a : ℕ) :
    tlog h ((1 + (1 + t) ^ a) ^ (p - 1)) =
      -(h * a) * t + (h ^ 2 * a - h ^ 3 * (a : Q) ^ 2) * t ^ 2 := by
  set T : Q := (a.choose 2 : Q) with hTdef
  have hT : 2 * T = (a : Q) ^ 2 - a := cast_choose_two a
  have hs : (1 + t) ^ a = 1 + (a : Q) * t + T * t ^ 2 := one_add_pow_trunc ht a
  have hs3 : ((a : Q) * t + T * t ^ 2) ^ 3 = 0 := by
    have : ((a : Q) * t + T * t ^ 2) ^ 3 = t ^ 3 * ((a : Q) + T * t) ^ 3 := by ring
    rw [this, ht, zero_mul]
  have : (1 + (1 + t) ^ a) = 2 + ((a : Q) * t + T * t ^ 2) := by rw [hs]; ring
  rw [this, tlog_two_add_pow_sub_one (p := p) hp3 h2 hs3]
  linear_combination (h * T * t ^ 2) * h2 + (-(h ^ 2 * t ^ 2)) * hT +
    ((h ^ 2 - h ^ 3) * (2 * (a : Q) * T + T ^ 2 * t)) * ht

end QRing

section GenericField

variable {F : Type*} [Field F] [NumberField F] [IsCyclotomicExtension {p} ℚ F]
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)

private theorem two_coprime (hp5 : 5 ≤ p) : Nat.Coprime 2 p := by
  apply Nat.Coprime.symm
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  have := Nat.le_of_dvd (by decide : 0 < 2) hd
  omega

/-- 実際の整数環単元 1+ζ。 -/
def cyclotomicUnit (hp5 : 5 ≤ p) : (𝓞 F)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (Fact.out : p.Prime).two_le
    (two_coprime hp5)).unit

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
/-- 選んだ単元の値は同じ指定根の 1+ζ。 -/
theorem cyclotomicUnit_val (hp5 : 5 ≤ p) : (cyclotomicUnit hζ hp5 : 𝓞 F) = 1 + hζ.toInteger := by
  simpa only [cyclotomicUnit, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one] using
    (hζ.toInteger_isPrimitiveRoot.geom_sum_isUnit (Fact.out : p.Prime).two_le
      (two_coprime hp5)).unit_spec

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
/-- 同じ指定根を3次商へ写すと 1+λ になる。 -/
theorem mk_integerRoot : Ideal.Quotient.mk (ramifiedIdeal hζ ^ 3) hζ.toInteger =
    1 + parameter hζ := by
  rw [parameter, ← map_one (Ideal.Quotient.mk _), ← map_add, add_sub_cancel]

/-- 整数環上の実際の自己同型による共役単元の評価。 -/
theorem unitLog_conjugate (hp5 : 5 ≤ p) (σ : 𝓞 F ≃+* 𝓞 F) (a : ℕ)
    (hσ : σ hζ.toInteger = hζ.toInteger ^ a) :
    unitLog hζ hp5 (Additive.ofMul (Units.map σ.toMonoidHom (cyclotomicUnit hζ hp5))) =
      -(half hζ hp5 * a) * parameter hζ +
        (half hζ hp5 ^ 2 * a - half hζ hp5 ^ 3 * (a : ResidueCube hζ) ^ 2) * parameter hζ ^ 2 := by
  let := residueCharP hζ hp5
  rw [unitLog_apply]
  have hcoe : ((Units.map σ.toMonoidHom (cyclotomicUnit hζ hp5) : (𝓞 F)ˣ) : 𝓞 F) =
      σ (1 + hζ.toInteger) := by
    change σ (cyclotomicUnit hζ hp5 : 𝓞 F) = _
    rw [cyclotomicUnit_val]
  rw [hcoe, map_add, map_one, hσ, map_add, map_one, map_pow, mk_integerRoot]
  exact tlog_conj_eval (p := p) (by omega) (two_mul_half hζ hp5) (parameter_cube hζ) a

/-- 非自明な1次指標の有限体単元上の和は零。 -/
theorem sum_units_val (hp5 : 5 ≤ p) : ∑ d : (ZMod p)ˣ, (d : ZMod p) = 0 := by
  have h := FiniteField.sum_pow_units (K := ZMod p) 1
  simp only [pow_one, ZMod.card] at h
  rw [h, ite_eq_right]
  intro hdvd
  have := Nat.le_of_dvd Nat.one_pos hdvd
  omega

/-- 逆元による全単元の並べ替えから、逆数の和も零。 -/
theorem sum_units_inv (hp5 : 5 ≤ p) : ∑ d : (ZMod p)ˣ, (d : ZMod p)⁻¹ = 0 := by
  calc ∑ d : (ZMod p)ˣ, (d : ZMod p)⁻¹ = ∑ d : (ZMod p)ˣ, ((d⁻¹ : (ZMod p)ˣ) : ZMod p) :=
        Finset.sum_congr rfl fun d _ => (Units.val_inv_eq_inv_val d).symm
    _ = ∑ d : (ZMod p)ˣ, (d : ZMod p) :=
        Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ (fun _ => rfl)
    _ = 0 := sum_units_val (p := p) hp5

/-- 単元の個数 p−1 は標数 p で −1。 -/
theorem sum_units_one : ∑ _d : (ZMod p)ˣ, (1 : ZMod p) = -1 := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units p, nsmul_eq_mul, mul_one,
    Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one, ZMod.natCast_self, zero_sub]

/-- 平均を取る際の実際の正規化係数は −1。 -/
theorem card_units_inv : ((Nat.card (ZMod p)ˣ : ZMod p))⁻¹ = -1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units p, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one,
    ZMod.natCast_self, zero_sub, inv_neg, inv_one]

/-- 同じスカラー写像による重み付き和を計算し、線形項を消去する。 -/
theorem e2_sum (hp5 : 5 ≤ p) :
    scalarMap hζ hp5 ((Nat.card (ZMod p)ˣ : ZMod p))⁻¹ *
      ∑ d : (ZMod p)ˣ, scalarMap hζ hp5 (((d : ZMod p) ^ 2)⁻¹) *
        (-(half hζ hp5 * ((d : ZMod p).val : ResidueCube hζ)) * parameter hζ +
          (half hζ hp5 ^ 2 * ((d : ZMod p).val : ResidueCube hζ) -
            half hζ hp5 ^ 3 * ((d : ZMod p).val : ResidueCube hζ) ^ 2) * parameter hζ ^ 2) =
      -(half hζ hp5 ^ 3 * parameter hζ ^ 2) := by
  simp only [half]
  set ι := scalarMap hζ hp5 with hι
  set t := parameter hζ
  have hval : ∀ d : (ZMod p)ˣ, ((d : ZMod p).val : ResidueCube hζ) = ι d := fun d =>
    (scalarMap_apply hζ hp5 d).symm
  have hsummand : ∀ d : (ZMod p)ˣ,
      ι (((d : ZMod p) ^ 2)⁻¹) *
        (-(ι 2⁻¹ * ((d : ZMod p).val : ResidueCube hζ)) * t +
          ((ι 2⁻¹) ^ 2 * ((d : ZMod p).val : ResidueCube hζ) -
            (ι 2⁻¹) ^ 3 * ((d : ZMod p).val : ResidueCube hζ) ^ 2) * t ^ 2) =
      ι (-(2⁻¹ * (d : ZMod p)⁻¹)) * t + ι ((2⁻¹) ^ 2 * (d : ZMod p)⁻¹ - (2⁻¹) ^ 3) * t ^ 2 := by
    intro d
    have hd : (d : ZMod p) ≠ 0 := d.ne_zero
    have e1 : ((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) = (d : ZMod p)⁻¹ := by
      field_simp
    have e2 : ((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hd)
    rw [hval d]
    have : ι (-(2⁻¹ * (d : ZMod p)⁻¹)) = -(ι (((d : ZMod p) ^ 2)⁻¹) * (ι 2⁻¹ * ι d)) := by
      rw [← e1]; simp only [map_neg, map_mul]; ring
    rw [this]
    have : ι ((2⁻¹) ^ 2 * (d : ZMod p)⁻¹ - (2⁻¹) ^ 3) =
        ι (((d : ZMod p) ^ 2)⁻¹) * ((ι 2⁻¹) ^ 2 * ι d - (ι 2⁻¹) ^ 3 * (ι d) ^ 2) := by
      rw [← e1]
      conv_lhs => rw [show ((2 : ZMod p)⁻¹) ^ 3 = (2⁻¹) ^ 3 * (((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) ^ 2)
        by rw [e2, mul_one]]
      simp only [map_sub, map_mul, map_pow]; ring
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun d _ => hsummand d), Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, ← map_sum, ← map_sum]
  have s1 : ∑ d : (ZMod p)ˣ, -(2⁻¹ * (d : ZMod p)⁻¹) = 0 := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_units_inv (p := p) hp5, mul_zero, neg_zero]
  have s2 : ∑ d : (ZMod p)ˣ, ((2 : ZMod p)⁻¹ ^ 2 * (d : ZMod p)⁻¹ - 2⁻¹ ^ 3) = 2⁻¹ ^ 3 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_units_inv (p := p) hp5, mul_zero, Finset.sum_const,
      Finset.card_univ, ZMod.card_units p, nsmul_eq_mul, Nat.cast_sub (Fact.out : p.Prime).one_le, Nat.cast_one,
      ZMod.natCast_self]
    ring
  rw [s1, s2, card_units_inv (p := p), map_zero, zero_mul, zero_add, map_neg, map_one, map_pow]
  ring

end GenericField

section RootField

variable {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ p)
local instance : NumberField (rootField ζ) := rootField_numberField ζ

/-- 円分単元類の同じ ω² 射影。 -/
def projectedCyclotomicUnit (hp5 : 5 ≤ p) : weightSquareSpace hζ :=
  letI := rootField_isCyclotomic hζ
  ⟨omegaSquareProjector hζ (Additive.ofMul
      (cyclotomicUnit (baseRoot_primitive hζ) hp5 : UnitClass (𝓞 (rootField ζ)) p)),
    omegaSquareProjector_mem hζ _⟩

/-- 指定根の Galois 指標と整数環作用が実際に同じ冪を与える。 -/
theorem integerAut_root (d : (ZMod p)ˣ) :
    (integerAut ((characterEquiv hζ).symm d)).integers (baseRoot_primitive hζ).toInteger =
      (baseRoot_primitive hζ).toInteger ^ (d : ZMod p).val := by
  apply NumberField.RingOfIntegers.coe_injective
  exact characterEquiv_symm_root hζ d

/-- 同じ大域単元の射影に対する具体的な評価。 -/
theorem primaryLog_projectedCyclotomicUnit (hp5 : 5 ≤ p) :
    letI := rootField_isCyclotomic hζ
    primaryLog (baseRoot_primitive hζ) hp5 (projectedCyclotomicUnit hζ hp5) =
      -(half (baseRoot_primitive hζ) hp5 ^ 3 * parameter (baseRoot_primitive hζ) ^ 2) := by
  let := rootField_isCyclotomic hζ
  change primaryLog (baseRoot_primitive hζ) hp5
    (omegaSquareProjector hζ (Additive.ofMul
      (cyclotomicUnit (baseRoot_primitive hζ) hp5 : UnitClass (𝓞 (rootField ζ)) p))) = _
  rw [omegaSquareProjector_apply_units, primaryLog_smul, map_sum]
  simp only [primaryLog_smul]
  have he : ∀ d : (ZMod p)ˣ,
      primaryLog (baseRoot_primitive hζ) hp5
        (unitClassLinearMap p (integerAut ((characterEquiv hζ).symm d))
          (Additive.ofMul (cyclotomicUnit (baseRoot_primitive hζ) hp5 :
            UnitClass (𝓞 (rootField ζ)) p))) =
      -(half (baseRoot_primitive hζ) hp5 * (d : ZMod p).val) * parameter (baseRoot_primitive hζ) +
        (half (baseRoot_primitive hζ) hp5 ^ 2 * (d : ZMod p).val -
          half (baseRoot_primitive hζ) hp5 ^ 3 * ((d : ZMod p).val :
            ResidueCube (baseRoot_primitive hζ)) ^ 2) * parameter (baseRoot_primitive hζ) ^ 2 := by
    intro d
    change unitLog (baseRoot_primitive hζ) hp5 (Additive.ofMul
      (Units.map (integerAut ((characterEquiv hζ).symm d)).integers.toMonoidHom
        (cyclotomicUnit (baseRoot_primitive hζ) hp5))) = _
    exact unitLog_conjugate (baseRoot_primitive hζ) hp5 _ _ (integerAut_root hζ d)
  simp only [he]
  exact e2_sum (baseRoot_primitive hζ) hp5

/-- h は実際に可逆なスカラー。Q が整域であるとは仮定しない。 -/
theorem half_cube_parameter_sq_ne_zero (hp5 : 5 ≤ p) :
    letI := rootField_isCyclotomic hζ
    half (baseRoot_primitive hζ) hp5 ^ 3 * parameter (baseRoot_primitive hζ) ^ 2 ≠ 0 := by
  let := rootField_isCyclotomic hζ
  intro hzero
  apply parameter_sq_ne_zero (baseRoot_primitive hζ)
  have h := congrArg (fun z : ResidueCube (baseRoot_primitive hζ) => 2 ^ 3 * z) hzero
  have he : (2 : ResidueCube (baseRoot_primitive hζ)) ^ 3 *
      (half (baseRoot_primitive hζ) hp5 ^ 3 * parameter (baseRoot_primitive hζ) ^ 2) =
        parameter (baseRoot_primitive hζ) ^ 2 := by
    rw [← mul_assoc, ← mul_pow, two_mul_half, one_pow, one_mul]
  rwa [he, mul_zero] at h

/-- 実際の大域単元の ω² 射影が、同じ Λ により検出される。 -/
theorem primaryLog_projectedCyclotomicUnit_ne_zero (hp5 : 5 ≤ p) :
    letI := rootField_isCyclotomic hζ
    primaryLog (baseRoot_primitive hζ) hp5 (projectedCyclotomicUnit hζ hp5) ≠ 0 := by
  let := rootField_isCyclotomic hζ
  rw [primaryLog_projectedCyclotomicUnit, neg_ne_zero]
  exact half_cube_parameter_sq_ne_zero hζ hp5

/-- 同じ実際の ω² 単元空間に非零元が存在する。 -/
theorem projectedCyclotomicUnit_ne_zero (hp5 : 5 ≤ p) :
    projectedCyclotomicUnit hζ hp5 ≠ 0 := by
  let := rootField_isCyclotomic hζ
  intro h
  apply primaryLog_projectedCyclotomicUnit_ne_zero hζ hp5
  simp [h]

/-- 同じ固有空間そのものが零でない。有限次元性を追加仮定しない。 -/
theorem weightSquareSpace_ne_bot (hp5 : 5 ≤ p) : weightSquareSpace hζ ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨projectedCyclotomicUnit hζ hp5, (projectedCyclotomicUnit hζ hp5).property, ?_⟩
  intro hz
  exact projectedCyclotomicUnit_ne_zero hζ hp5 (Subtype.ext hz)

/-- 非零評価 hdetect を内部供給し、残条件を実際の同じ空間の次元1へ減らす。 -/
theorem primaryWeightSquareSpace_eq_bot_of_rank_one (hp5 : 5 ≤ p)
    (hrank : Module.finrank (ZMod p) (weightSquareSpace hζ) = 1) :
    primaryWeightSquareSpace hζ = ⊥ :=
  primaryWeightSquareSpace_eq_bot_of_rank_one_of_detection hζ hp5 hrank
    (projectedCyclotomicUnit hζ hp5) (primaryLog_projectedCyclotomicUnit_ne_zero hζ hp5)

end RootField
end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryLogNonzero

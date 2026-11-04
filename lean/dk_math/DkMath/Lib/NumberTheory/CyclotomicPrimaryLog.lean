/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: retain the specified root and field; descend to DkMath UnitClass,
and derive zero on the actual localPowerSpace without external theorem imports.
-/

import DkMath.Lib.NumberTheory.CyclotomicPrimaryCongruence
import DkMath.Lib.NumberTheory.CyclotomicTruncatedLog

#print "file: DkMath.Lib.NumberTheory.CyclotomicPrimaryLog"

/-!
# 同じ単元商上の primary logarithm

Q=𝓞 F/(ζ−1)³ 上で Λ([u])=tlog(1/2, u^(p−1)) を構成する。
p≥5 から char Q=p を導き、p 乗を零へ送ることを証明してから商へ降ろす。
局所 p 乗類は実際に ker Λ に入る。Λ の固有空間上の単射性は未証明。
-/

namespace DkMath.Lib.NumberTheory.CyclotomicPrimaryLog

open CyclotomicPrimaryCongruence CyclotomicPrimaryUnitSpace CyclotomicTruncatedLog
open KummerSelmerExact DkMath.Lib.Algebra
open scoped NumberField
noncomputable section

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [NumberField F]
    [IsCyclotomicExtension {p} ℚ F] {ζ : F} (hζ : IsPrimitiveRoot ζ p)

/-- 指定した根の同じ分岐イデアルによる3次商。 -/
abbrev ResidueCube := 𝓞 F ⧸ ramifiedIdeal hζ ^ 3

/-- 商における同じ局所パラメータ λ。 -/
def parameter : ResidueCube hζ := Ideal.Quotient.mk _ (hζ.toInteger - 1)

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
theorem parameter_cube : parameter hζ ^ 3 = 0 := by
  rw [parameter, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, ramifiedIdeal,
    Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

/-- λ² は3次商で消えない。後続の非零評価に必要な算術的事実。 -/
theorem parameter_sq_ne_zero : parameter hζ ^ 2 ≠ 0 := by
  rw [parameter, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, ramifiedIdeal,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hζ.zeta_sub_one_prime'.ne_zero hζ.zeta_sub_one_prime'.not_isUnit]
  omega

theorem natCast_eq_zero (hp5 : 5 ≤ p) : (p : ResidueCube hζ) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
  exact natCast_mem_ramifiedIdeal_pow hζ 3 (by omega)

/-- 3次商は零環でない。同じ分岐素点が真の素イデアルであることを使う。 -/
instance residueCubeNontrivial : Nontrivial (ResidueCube hζ) :=
  Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have hle := Ideal.pow_le_self (I := ramifiedIdeal hζ) (n := 3) (by norm_num)
    rw [h, top_le_iff] at hle
    exact (ramifiedPlace hζ).isPrime.ne_top hle)

/-- 分岐公式から導いた標数。新しい標数仮定を要求しない。 -/
abbrev residueCharP (hp5 : 5 ≤ p) : CharP (ResidueCube hζ) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (natCast_eq_zero hζ hp5)

/-- Fp のスカラーを3次商へ送る実際の環準同型。 -/
def scalarMap (hp5 : 5 ≤ p) : ZMod p →+* ResidueCube hζ :=
  letI := residueCharP hζ hp5
  ZMod.castHom (dvd_refl p) _

theorem scalarMap_apply (hp5 : 5 ≤ p) (a : ZMod p) :
    scalarMap hζ hp5 a = (a.val : ResidueCube hζ) := by
  let := residueCharP hζ hp5
  rw [scalarMap, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- 商の中の 1/2。 -/
def half (hp5 : 5 ≤ p) : ResidueCube hζ := scalarMap hζ hp5 (2⁻¹)

theorem two_mul_half (hp5 : 5 ≤ p) : 2 * half hζ hp5 = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  rw [half, ← map_ofNat (scalarMap hζ hp5) 2, ← map_mul, mul_inv_cancel₀ h2, map_one]

omit [NumberField F] [IsCyclotomicExtension {p} ℚ F] in
theorem parameterIdeal_cube (a : ResidueCube hζ) (ha : a ∈ Ideal.span {parameter hζ})
    (b : ResidueCube hζ) (hb : b ∈ Ideal.span {parameter hζ})
    (c : ResidueCube hζ) (hc : c ∈ Ideal.span {parameter hζ}) : a * b * c = 0 := by
  rw [Ideal.mem_span_singleton] at ha hb hc
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨c', rfl⟩ := hc
  calc
    _ = parameter hζ ^ 3 * (a' * b' * c') := by ring
    _ = 0 := by rw [parameter_cube, zero_mul]

/-- 単元を p−1 乗してから、同じ3次商へ写す。 -/
def residuePower : (𝓞 F)ˣ →* ResidueCube hζ :=
  (powMonoidHom (p - 1)).comp
    ((Ideal.Quotient.mk _).toMonoidHom.comp (Units.coeHom _))

theorem residuePower_sub_one_mem (u : (𝓞 F)ˣ) :
    residuePower hζ u - 1 ∈ Ideal.span {parameter hζ} := by
  have hx := unit_pow_sub_one_mem_ramifiedIdeal hζ u
  rw [ramifiedIdeal, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  change (Ideal.Quotient.mk _ (u : 𝓞 F)) ^ (p - 1) - 1 ∈ _
  rw [← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_sub, hy, map_mul,
    Ideal.mem_span_singleton]
  exact ⟨_, rfl⟩

/-- 単元群からの加法準同型。 -/
def unitLog (hp5 : 5 ≤ p) : Additive (𝓞 F)ˣ →+ ResidueCube hζ :=
  tlogHom (parameterIdeal_cube hζ) (two_mul_half hζ hp5)
    (residuePower hζ) (residuePower_sub_one_mem hζ)

theorem unitLog_apply (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ) :
    unitLog hζ hp5 (Additive.ofMul u) =
      tlog (half hζ hp5) ((Ideal.Quotient.mk _ (u : 𝓞 F)) ^ (p - 1)) := rfl

/-- 商への降下条件は標数 p と加法性から証明する。 -/
theorem unitLog_pow (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ) :
    unitLog hζ hp5 (Additive.ofMul (u ^ p)) = 0 := by
  change unitLog hζ hp5 (p • Additive.ofMul u) = 0
  rw [map_nsmul, nsmul_eq_mul, natCast_eq_zero hζ hp5, zero_mul]

/-- 実際の p 乗部分群を核に含むことを用いて UnitClass へ降ろす。 -/
def primaryLog (hp5 : 5 ≤ p) : Additive (UnitClass (𝓞 F) p) →+ ResidueCube hζ :=
  (QuotientGroup.lift (powerSubgroup (𝓞 F)ˣ p)
    (unitLog hζ hp5).toMultiplicativeRight (by
      rintro _ ⟨u, rfl⟩
      change unitLog hζ hp5 (Additive.ofMul (u ^ p)) = 0
      exact unitLog_pow hζ hp5 u)).toAdditive

theorem primaryLog_mk (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ) :
    primaryLog hζ hp5 (Additive.ofMul (u : UnitClass (𝓞 F) p)) =
      unitLog hζ hp5 (Additive.ofMul u) := rfl

/-- 同じ単元の3次合同から Λ の零化へ。 -/
theorem primaryLog_mk_eq_zero_of_congruence (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ)
    (hu : (u : 𝓞 F) ^ (p - 1) - 1 ∈ ramifiedIdeal hζ ^ 3) :
    primaryLog hζ hp5 (Additive.ofMul (u : UnitClass (𝓞 F) p)) = 0 := by
  rw [primaryLog_mk, unitLog_apply]
  have h : (Ideal.Quotient.mk (ramifiedIdeal hζ ^ 3) (u : 𝓞 F)) ^ (p - 1) = 1 := by
    rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  rw [h, tlog_one]

/-- 実際の局所冪条件から、合同式を新規入力にせず Λ([u])=0 を得る。 -/
theorem primaryLog_mk_eq_zero_of_local_power (hp5 : 5 ≤ p) (u : (𝓞 F)ˣ)
    (hu : Additive.ofMul (u : UnitClass (𝓞 F) p) ∈ localPowerSpace F p) :
    primaryLog hζ hp5 (Additive.ofMul (u : UnitClass (𝓞 F) p)) = 0 :=
  primaryLog_mk_eq_zero_of_congruence hζ hp5 u
    (pow_sub_one_mem_ramifiedIdeal_cube_of_local_power hζ hp5 u hu)

/-- 代表元を選ばない、局所冪空間全体についての零化。 -/
theorem primaryLog_eq_zero_of_mem_localPowerSpace (hp5 : 5 ≤ p)
    (x : Additive (UnitClass (𝓞 F) p)) (hx : x ∈ localPowerSpace F p) :
    primaryLog hζ hp5 x = 0 := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (powerSubgroup (𝓞 F)ˣ p) x.toMul
  have he : Additive.ofMul (u : UnitClass (𝓞 F) p) = x := congrArg Additive.ofMul hu
  rw [← he] at hx ⊢
  exact primaryLog_mk_eq_zero_of_local_power hζ hp5 u hx

/-- Fp スカラーに関する実際の線形性（商側への環写像を明示）。 -/
theorem primaryLog_smul (hp5 : 5 ≤ p) (a : ZMod p)
    (x : Additive (UnitClass (𝓞 F) p)) :
    primaryLog hζ hp5 (a • x) = scalarMap hζ hp5 a * primaryLog hζ hp5 x := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, scalarMap_apply]

end
end DkMath.Lib.NumberTheory.CyclotomicPrimaryLog

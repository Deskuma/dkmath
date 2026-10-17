/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.GNKummerUnitAdapter
import DkMath.FLT.Three.PrimitiveCubicDescent
import DkMath.Lib.NumberTheory.EisensteinCyclotomic

#print "file: DkMath.FLT.Kummer.ThreeEisensteinBridge"

/-!
# GN・Kummer の三乗根を既存 FLT3 の同じ剥離商へ運ぶ

`ζ=τ²` を選ぶと、第2位相は `a+ζ²b=a−τb`、その分岐因子は
`ζ²−1=−(1+τ)` となる。両方の符号が消え、既存の
`α=(1+τ)β` と比較して **同じ β** が三乗であることを得る。

三次円分整数環の類数条件は、既存 Eisenstein 環の Euclidean 構造を
実際の環同型で輸送して証明する。FLT3 の完成済み不可能性定理も、
従来の単元セクター排除による `beta_eq_cube` も証明には使用しない。
-/

namespace DkMath.FLT.Kummer

open scoped NumberField
open DkMath.FLT.Three DkMath.NumberTheory.TraceOneQuadratic

/-- 六乗根型の基底から三乗根を固定する。 -/
def eisensteinZeta : EisensteinInt := eisensteinTau ^ 2

/-- 第2位相は `−τ`。根を取り違えると剥離商の符号が変わる。 -/
theorem eisensteinZeta_sq : eisensteinZeta ^ 2 = -eisensteinTau := by
  ext <;> norm_num [eisensteinZeta, eisensteinTau, tau, pow_succ]

/-- 第2位相の分岐因子は既存の分岐因子の負元。 -/
theorem eisensteinZeta_sq_sub_one :
    eisensteinZeta ^ 2 - 1 = -eisensteinRamifier := by
  rw [eisensteinZeta_sq, eisensteinRamifier]
  ring

/-- Kummer 第2位相と既存の符号付き座標を元として比較する。 -/
theorem eisenstein_second_phase (a b : ℤ) :
    -((a : EisensteinInt) + eisensteinZeta ^ 2 * (b : EisensteinInt)) =
      Three.eisensteinCoord (-a) b := by
  rw [eisensteinZeta_sq]
  change -((⟨a, 0⟩ : EisensteinInt) + -eisensteinTau * ⟨b, 0⟩) = _
  ext <;> simp [Three.eisensteinCoord, eisensteinTau, tau]

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {3} ℚ K] {ζ : K}

/-- 環同型は `τ²` を選択した原始三乗根に送る。 -/
theorem eisensteinCyclotomicEquiv_zeta (hζ : IsPrimitiveRoot ζ 3) :
    DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ eisensteinZeta = hζ.toInteger := by
  change DkMath.Lib.NumberTheory.eisensteinToCyclotomic hζ eisensteinZeta = _
  norm_num [DkMath.Lib.NumberTheory.eisensteinToCyclotomic,
    DkMath.Lib.NumberTheory.eisensteinEval, eisensteinZeta, eisensteinTau, tau, pow_two]

/-- 環同型で PID を輸送するので、三次では類数仮定を残す必要がない。 -/
theorem cubic_classGroup_card_eq_one (hζ : IsPrimitiveRoot ζ 3) :
    Fintype.card (ClassGroup (𝓞 K)) = 1 := by
  let e := DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ
  let : IsPrincipalIdealRing (𝓞 K) := IsPrincipalIdealRing.of_surjective e e.surjective
  simpa only [Fintype.card_eq_nat_card] using card_classGroup_eq_one (R := 𝓞 K)

/-- 元の三次方程式から GN・イデアル・単元合同を経て Eisenstein の因子表示を得る。
外部の単元補題・類数・三乗根の存在を追加仮定として要求しない。 -/
theorem exists_eisenstein_factor_eq_ramifier_mul_cube
    (hζ : IsPrimitiveRoot ζ 3) {a b c : ℤ}
    (hc0 : c ≠ 0) (heq : a ^ 3 + b ^ 3 = c ^ 3)
    (hprim : IsCoprime a b) (hcase : (3 : ℤ) ∣ c) :
    ∃ θ : EisensteinInt, Three.eisensteinCoord (-a) b = eisensteinRamifier * θ ^ 3 := by
  let e := DkMath.Lib.NumberTheory.eisensteinCyclotomicEquiv hζ
  have hreg : Nat.Coprime 3 (Fintype.card (ClassGroup (𝓞 K))) := by
    rw [cubic_classGroup_card_eq_one hζ]
    exact Nat.coprime_one_right 3
  obtain ⟨θ, hθ⟩ := exists_GN_cubic_factor_eq_zeta_sub_one_mul_cube hζ hc0 heq hprim hcase
    hreg (i := 2) (by decide)
  refine ⟨e.symm θ, ?_⟩
  apply e.injective
  have hz : e eisensteinZeta = hζ.toInteger := eisensteinCyclotomicEquiv_zeta hζ
  have hphase := congrArg e (eisenstein_second_phase a b)
  have hram := congrArg e eisensteinZeta_sq_sub_one
  simp only [map_neg, map_add, map_mul, map_pow, map_intCast, hz] at hphase
  simp only [map_sub, map_pow, map_one, map_neg, hz] at hram
  rw [← hphase, hθ, map_mul, map_pow, e.apply_symm_apply]
  rw [hram]
  ring

/-- 既存パケットの座標自体が原始的であることを復元する。
共通因子 d は `carrier` と `residual` の gcd=3 を割る。一方 d=3 なら
9 がノルムを割り、`residual % 9=3` と矛盾する。この証明は単元を解析しない。 -/
theorem signedThreeAdicPacket_coordinates_coprime {a b c : ℕ}
    (p : SignedThreeAdicPacket a b c) : IsCoprime p.alpha.fst p.alpha.snd := by
  let d := Int.gcd p.alpha.fst p.alpha.snd
  have hr : (d : ℤ) ∣ p.alpha.fst := Int.gcd_dvd_left _ _
  have hs : (d : ℤ) ∣ p.alpha.snd := Int.gcd_dvd_right _ _
  have hcarrier : d ∣ p.carrier := by
    have h := dvd_sub hs hr
    rw [p.alpha_signed_gap] at h
    exact_mod_cast h
  have hnorm : (d : ℤ) ∣ norm p.alpha := by
    simp only [DkMath.NumberTheory.TraceOneQuadratic.norm, neg_mul, one_mul, sub_neg_eq_add]
    exact dvd_add (dvd_add (dvd_pow hr (by decide)) (dvd_mul_of_dvd_left hr _))
      (dvd_pow hs (by decide))
  have hres : d ∣ p.residual := by
    rw [p.alpha_norm] at hnorm
    exact_mod_cast hnorm
  have hd3 : d ∣ 3 := by
    rw [← p.gcd_eq_three]
    exact Nat.dvd_gcd hcarrier hres
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
  · exact h
  · have h3r : (3 : ℤ) ∣ p.alpha.fst := by simpa [h] using hr
    have h3s : (3 : ℤ) ∣ p.alpha.snd := by simpa [h] using hs
    obtain ⟨r, hr⟩ := h3r
    obtain ⟨s, hs⟩ := h3s
    have h9 : (9 : ℤ) ∣ (p.residual : ℤ) := by
      rw [← p.alpha_norm]
      refine ⟨r ^ 2 + r * s + s ^ 2, ?_⟩
      simp only [DkMath.NumberTheory.TraceOneQuadratic.norm, neg_mul, one_mul, sub_neg_eq_add]
      rw [hr, hs]
      ring
    have h9nat : 9 ∣ p.residual := by exact_mod_cast h9
    have hz := Nat.mod_eq_zero_of_dvd h9nat
    rw [p.residual_mod_nine] at hz
    contradiction

/-- 既存パケットの符号付き座標から、Kummer に入力する三次方程式を復元する。
元の三つの向きは既存パケットに保持され、この恒等式で一つの向きへ統一される。 -/
theorem signedThreeAdicPacket_cubic_equation {a b c : ℕ}
    (p : SignedThreeAdicPacket a b c) :
    (-p.alpha.fst) ^ 3 + p.alpha.snd ^ 3 = (p.distinguished : ℤ) ^ 3 := by
  calc
    _ = (p.alpha.snd - p.alpha.fst) * norm p.alpha := by
      simp only [DkMath.NumberTheory.TraceOneQuadratic.norm]
      ring
    _ = (p.carrier : ℤ) * (p.residual : ℤ) := by
      rw [p.alpha_signed_gap, p.alpha_norm]
    _ = (p.distinguished : ℤ) ^ 3 := by exact_mod_cast p.factorization

/-- **指定された既存の剥離商**が、GN・円分イデアル・Kummer 単元補題の経路で三乗になる。
剥離商を選び直さず、非零の同じ分岐因子を消去する。全ての既存の向きを扱う。 -/
theorem exists_cube_eq_stripped_beta (hζ : IsPrimitiveRoot ζ 3)
    {a b c : ℕ} (q : EisensteinRamifierStrippedPacket a b c) :
    ∃ θ : EisensteinInt, q.beta = θ ^ 3 := by
  let p := q.powerSplit.packet
  have hprim : IsCoprime (-p.alpha.fst) p.alpha.snd :=
    (signedThreeAdicPacket_coordinates_coprime p).neg_left
  obtain ⟨θ, hθ⟩ := exists_eisenstein_factor_eq_ramifier_mul_cube hζ
    (by exact_mod_cast (ne_of_gt p.distinguished_pos))
    (signedThreeAdicPacket_cubic_equation p) hprim
    (by exact_mod_cast p.three_dvd_distinguished)
  have hcoord : Three.eisensteinCoord (- -p.alpha.fst) p.alpha.snd = p.alpha := by
    ext <;> simp [Three.eisensteinCoord]
  rw [hcoord] at hθ
  refine ⟨θ, ?_⟩
  have hram : eisensteinRamifier ≠ 0 := by
    intro hz
    have hn := eisenstein_ramifier_norm
    rw [hz] at hn
    norm_num [DkMath.NumberTheory.TraceOneQuadratic.norm] at hn
  exact mul_left_cancel₀ hram (q.alpha_eq.symm.trans hθ)

end DkMath.FLT.Kummer

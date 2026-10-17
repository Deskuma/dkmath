/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.FiveKummerUnit

#print "file: DkMath.FLT.Kummer.FiveGNSameBeta"

/-!
# GN・Kummer から同じ GoldenInt 剥離商の五乗根へ

円分イデアルを主イデアル化する類数条件と五次単元補題を実際に供給する。
相対ノルムを取り、黄金比共役を戻し、既存パケットが剥離したのと同じ
`2+φ` を消去する。根の存在・単元補題・類数条件は追加仮定にしない。
-/

namespace DkMath.FLT.Kummer

open scoped NumberField
open DkMath.FLT.Five

variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {5} ℚ K] {ζ : K}

/-- 五次では PID と実装した単元補題を供給し、未解析単元を残さない。 -/
theorem exists_GN_quintic_factor_eq_zeta_sub_one_mul_fifth
    (hζ : IsPrimitiveRoot ζ 5) {a b c : ℤ}
    (hc0 : c ≠ 0) (heq : a ^ 5 + b ^ 5 = c ^ 5)
    (hprim : IsCoprime a b) (hcase : (5 : ℤ) ∣ c) :
    ∃ θ : 𝓞 K, (a : 𝓞 K) + hζ.toInteger * (b : 𝓞 K) =
      (hζ.toInteger - 1) * θ ^ 5 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hreg : Nat.Coprime 5 (Fintype.card (ClassGroup (𝓞 K))) := by
    rw [quintic_classGroup_card_eq_one]
    exact Nat.coprime_one_right 5
  simpa only [pow_one] using
    exists_GN_factor_eq_zeta_sub_one_mul_pow_of_unit_criterion hζ (by decide) (by decide)
      hc0 heq hprim hcase hreg (quintic_kummer_unit_power_criterion hζ) (i := 1) (by decide)

/-- パケットの平方境界から、元の符号付き座標で分岐側の条件を復元する。 -/
theorem five_dvd_result_of_stripped_coordinates {u v w : ℕ}
    (q : SignedGoldenRamifierStrippedPacket u v w) {a b c : ℤ}
    (heq : a ^ 5 + b ^ 5 = c ^ 5)
    (hcoords : q.alpha = ⟨a ^ 2 + b ^ 2, -(a * b)⟩) : (5 : ℤ) ∣ c := by
  have hpair := q.alpha_eq.symm.trans hcoords
  have hM := congrArg GoldenInt.fst hpair
  have hN := congrArg GoldenInt.snd hpair
  dsimp only at hM hN
  have hb : (a + b) ^ 2 = (5 : ℤ) ^ 8 * (q.exceptional.powerSplit.a : ℤ) ^ 10 := by
    calc
      (a + b) ^ 2 = q.exceptional.M - 2 * q.exceptional.N := by rw [hM, hN]; ring
      _ = _ := q.exceptional.tenth_boundary
  have h5sq : (5 : ℤ) ∣ (a + b) ^ 2 := by
    refine ⟨5 ^ 7 * (q.exceptional.powerSplit.a : ℤ) ^ 10, ?_⟩
    rw [hb]
    ring
  have hgap := (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5sq
  have h5pow := hgap.trans (Odd.add_dvd_pow_add_pow a b (by decide : Odd 5))
  rw [heq] at h5pow
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5pow

/-- 指定された元と平方境界の対応を保って、同じ β に根を返す。 -/
theorem exists_fifth_eq_stripped_beta_of_coordinates (hζ : IsPrimitiveRoot ζ 5)
    {u v w : ℕ} (q : SignedGoldenRamifierStrippedPacket u v w) {a b c : ℤ}
    (hc0 : c ≠ 0) (heq : a ^ 5 + b ^ 5 = c ^ 5) (hprim : IsCoprime a b)
    (hcoords : q.alpha = ⟨a ^ 2 + b ^ 2, -(a * b)⟩) :
    ∃ θ : GoldenInt, q.beta = θ ^ 5 := by
  obtain ⟨θ, hθ⟩ := exists_GN_quintic_factor_eq_zeta_sub_one_mul_fifth hζ hc0 heq hprim
    (five_dvd_result_of_stripped_coordinates q heq hcoords)
  have hN := congrArg (fiveGoldenRelativeNorm hζ) hθ
  rw [fiveGoldenRelativeNorm_phase, map_mul, fiveGoldenRelativeNorm_ramifier, map_pow] at hN
  rw [← hcoords] at hN
  have hC := congrArg goldenConjRingEquiv hN
  simp only [map_mul, map_pow] at hC
  change goldenConj (goldenConj q.alpha) = goldenConj (goldenConj goldenTau) *
    goldenConj (fiveGoldenRelativeNorm hζ θ) ^ 5 at hC
  rw [goldenConj_invol, goldenConj_invol] at hC
  refine ⟨goldenConj (fiveGoldenRelativeNorm hζ θ), ?_⟩
  have ht : goldenTau ≠ 0 := by decide +kernel
  exact mul_left_cancel₀ ht (q.alpha_eq_tau_mul.symm.trans hC)

/-- 両方の signed orientation から円分入力を構成する。
q が保存する元の反例・平方境界と同じ β を扱う。向きは選び直さない。 -/
theorem exists_fifth_eq_stripped_beta_via_GN_in (hζ : IsPrimitiveRoot ζ 5)
    {u v w : ℕ} (q : SignedGoldenRamifierStrippedPacket u v w) :
    ∃ θ : GoldenInt, q.beta = θ ^ 5 := by
  let p := q.exceptional.powerSplit.fiveAdic.normal.pack
  have heq : (u : ℤ) ^ 5 + (v : ℤ) ^ 5 = (w : ℤ) ^ 5 := by exact_mod_cast p.hEq
  cases q.exceptional.source with
  | difference hM hN _ =>
    have heq' : (w : ℤ) ^ 5 + (-(v : ℤ)) ^ 5 = (u : ℤ) ^ 5 := by
      linear_combination -heq
    have hprim : IsCoprime (w : ℤ) (-(v : ℤ)) := by
      apply IsCoprime.neg_right
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa using (coprime_y_z_of_counterexamplePack p).symm
    apply exists_fifth_eq_stripped_beta_of_coordinates hζ q
      (by exact_mod_cast ne_of_gt p.hx) heq' hprim
    rw [q.alpha_eq, hM, hN]
    congr 1 <;> ring
  | sum hM hN _ =>
    have hprim : IsCoprime (u : ℤ) (v : ℤ) := by
      apply Int.isCoprime_iff_nat_coprime.mpr
      simpa using p.hxy
    apply exists_fifth_eq_stripped_beta_of_coordinates hζ q
      (by exact_mod_cast ne_of_gt p.hz) heq hprim
    rw [q.alpha_eq, hM, hN]

set_option backward.isDefEq.respectTransparency false in
/-- 具体的五次円分体を供給した、追加仮定のない同じ β の五乗根復元。 -/
theorem exists_fifth_eq_stripped_beta_via_GN {u v w : ℕ}
    (q : SignedGoldenRamifierStrippedPacket u v w) : ∃ θ : GoldenInt, q.beta = θ ^ 5 := by
  let : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
    CyclotomicField.isCyclotomicExtension 5 ℚ
  exact exists_fifth_eq_stripped_beta_via_GN_in
    (IsCyclotomicExtension.zeta_spec 5 ℚ (CyclotomicField 5 ℚ)) q

end DkMath.FLT.Kummer

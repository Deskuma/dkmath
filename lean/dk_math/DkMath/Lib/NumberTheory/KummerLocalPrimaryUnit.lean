/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from anthropics/fermats-last-theorem,
P2M/Sol/S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.lean.
Upstream blob: 89f85644f3cc853c293396363bd290c9ff81a237
Modified: standalone Dedekind-domain theorem, actual field-valued local root,
DkMath namespace and textbook boundary. No upstream theorem is imported.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Algebra.CharP.Lemmas

#print "file: DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit"

/-!
# 同じ単元の局所 p 乗性から、同じ素点での3次の合同へ

u^(p-1)-1∈v と p∈v² の住所を保ち、実際の完備体の p 乗根を使って
u^(p-1)-1∈v³ を証明する。p 乗根の付値が1であることから出発し、
二項展開の中間項の p 可除性と正規化整数付値の離散性を使う。
これは単元類の消滅ではなく、その算術的検出に必要な具体的な合同である。
-/

namespace DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Finset
noncomputable section

private lemma zm0_eq_one_of_pow_eq_one {x : ℤᵐ⁰} (hx : x ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n = 1) : x = 1 := by
  rw [← exp_log hx, ← exp_nsmul, ← exp_zero, exp_inj] at h
  rw [← exp_log hx, ← exp_zero, exp_inj]
  have h' : (n : ℤ) * x.log = 0 := by rw [← nsmul_eq_mul]; exact h
  exact (mul_eq_zero.mp h').resolve_left (Int.natCast_ne_zero.mpr hn)

private lemma zm0_le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← exp_log hx, ← exp_zero, exp_lt_exp] at h
    rw [← exp_log hx, exp_le_exp]
    omega

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- 同じ素点における局所 p 乗根から、単元の p−1 乗の3次合同を得る。 -/
theorem pow_sub_one_mem_cube_of_local_pow
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (𝔭 : HeightOneSpectrum R) (u : Rˣ)
    (hz1 : (u : R) ^ (p - 1) - 1 ∈ 𝔭.asIdeal)
    (hp2 : (p : R) ∈ 𝔭.asIdeal ^ 2)
    (hloc : ∃ v : (𝔭.adicCompletion K)ˣ,
      (v : 𝔭.adicCompletion K) ^ p = algebraMap R (𝔭.adicCompletion K) (u : R)) :
    (u : R) ^ (p - 1) - 1 ∈ 𝔭.asIdeal ^ 3 := by
  obtain ⟨v, hv⟩ := hloc
  -- 整数環の埋め込みと付値の正規化を一致させる。
  have hwR : ∀ r : R, Valued.v ((algebraMap R (𝔭.adicCompletion K)) r)
      = 𝔭.intValuation r := by
    intro r
    have h1 : (algebraMap R (𝔭.adicCompletion K)) r = ((algebraMap R K r : K) :
        𝔭.adicCompletion K) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  -- 整数環単元と局所根の付値は1になる。
  have hu1 : 𝔭.intValuation (u : R) = 1 := by
    refine le_antisymm (intValuation_le_one 𝔭 _) ?_
    have humul : 𝔭.intValuation (u : R) * 𝔭.intValuation ((u⁻¹ : Rˣ) : R) = 1 := by
      rw [← Valuation.map_mul, Units.mul_inv, Valuation.map_one]
    calc (1 : ℤᵐ⁰) = 𝔭.intValuation (u : R) * 𝔭.intValuation ((u⁻¹ : Rˣ) : R) :=
          humul.symm
    _ ≤ 𝔭.intValuation (u : R) * 1 :=
          mul_le_mul' le_rfl (intValuation_le_one 𝔭 _)
    _ = 𝔭.intValuation (u : R) := mul_one _
  have hwu : Valued.v ((algebraMap R (𝔭.adicCompletion K)) (u : R)) = 1 := by
    rw [hwR]; exact hu1
  -- 同じ局所根の冪等式を体の元の等式として使う。
  have hv' : (v : 𝔭.adicCompletion K) ^ p
      = (algebraMap R (𝔭.adicCompletion K)) (u : R) := hv
  have hwv : Valued.v (v : 𝔭.adicCompletion K) = 1 := by
    have hpow : (Valued.v (v : 𝔭.adicCompletion K)) ^ p = 1 := by
      rw [← map_pow, hv', hwu]
    have hne : Valued.v (v : 𝔭.adicCompletion K) ≠ 0 := by
      simp
    exact zm0_eq_one_of_pow_eq_one hne hp.ne_zero hpow
  -- p−1乗を取り、1からの誤差を調べる。
  set y : 𝔭.adicCompletion K := (v : 𝔭.adicCompletion K) ^ (p - 1) with hy_def
  set h : 𝔭.adicCompletion K := y - 1 with hh_def
  have hwy : Valued.v y = 1 := by rw [hy_def, map_pow, hwv, one_pow]
  have hwh_le : Valued.v h ≤ 1 := by
    calc Valued.v h ≤ max (Valued.v y) (Valued.v (1 : 𝔭.adicCompletion K)) :=
          Valuation.map_sub _ _ _
    _ ≤ 1 := by rw [hwy, map_one]; exact max_le le_rfl le_rfl
  -- 二項展開の中間項を p でまとめる。
  have hyp_eq : y ^ p = (algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1)) := by
    rw [hy_def, ← pow_mul, mul_comm, pow_mul, hv', ← map_pow]
  set S : 𝔭.adicCompletion K :=
    ∑ k ∈ Ioo 0 p, (1 : 𝔭.adicCompletion K) ^ (k - 1) * h ^ (p - k - 1)
      * ((p.choose k / p : ℕ) : 𝔭.adicCompletion K) with hS_def
  have hident : y ^ p = 1 + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by
    have hyh : (1 : 𝔭.adicCompletion K) + h = y := by rw [hh_def]; ring
    calc y ^ p = ((1 : 𝔭.adicCompletion K) + h) ^ p := by rw [hyh]
    _ = 1 ^ p + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by
          rw [add_pow_prime_eq hp]
    _ = 1 + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by rw [one_pow]
  have hzL : (algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)
      = h ^ p + (p : 𝔭.adicCompletion K) * h * S := by
    rw [map_sub, map_one, ← hyp_eq, hident]; ring
  -- 係数和の各整数係数の付値を抑える。
  have hwnat : ∀ n : ℕ, Valued.v ((n : 𝔭.adicCompletion K)) ≤ 1 := by
    intro n
    have hcast : ((n : 𝔭.adicCompletion K)) = (algebraMap R (𝔭.adicCompletion K)) (n : R) := by
      rw [map_natCast]
    rw [hcast, hwR]; exact intValuation_le_one 𝔭 _
  have hwS : Valued.v S ≤ 1 := by
    rw [hS_def]
    refine Valuation.map_sum_le _ ?_
    intro k _
    calc Valued.v ((1 : 𝔭.adicCompletion K) ^ (k - 1) * h ^ (p - k - 1)
          * ((p.choose k / p : ℕ) : 𝔭.adicCompletion K))
        = (Valued.v (1 : 𝔭.adicCompletion K)) ^ (k - 1) * (Valued.v h) ^ (p - k - 1)
          * Valued.v (((p.choose k / p : ℕ) : 𝔭.adicCompletion K)) := by
          rw [map_mul, map_mul, map_pow, map_pow]
    _ ≤ 1 := by
          rw [map_one, one_pow, one_mul]
          exact mul_le_one' (pow_le_one' hwh_le _) (hwnat _)
  have hwp2 : Valued.v ((p : 𝔭.adicCompletion K)) ≤ exp (-2 : ℤ) := by
    have hcast : ((p : 𝔭.adicCompletion K)) = (algebraMap R (𝔭.adicCompletion K)) ((p : ℕ) : R) := by
      rw [map_natCast]
    rw [hcast, hwR]
    have h2 := (intValuation_le_pow_iff_mem 𝔭 ((p : ℕ) : R) 2).mpr hp2
    simpa using h2
  have hwz_lt : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)) < 1 := by
    rw [hwR]; exact (intValuation_lt_one_iff_mem 𝔭 _).mpr hz1
  have hwp_lt : Valued.v ((p : 𝔭.adicCompletion K)) < 1 :=
    lt_of_le_of_lt hwp2 (by rw [← exp_zero, exp_lt_exp]; omega)
  -- 離散付値により誤差は一様化元一個分以上小さい。
  have hwh_lt : Valued.v h < 1 := by
    rcases lt_or_eq_of_le hwh_le with hlt | heq
    · exact hlt
    · exfalso
      have h1 : Valued.v (h ^ p) = 1 := by rw [map_pow, heq, one_pow]
      have h2 : Valued.v ((p : 𝔭.adicCompletion K) * h * S) < 1 := by
        calc Valued.v ((p : 𝔭.adicCompletion K) * h * S)
            = Valued.v ((p : 𝔭.adicCompletion K)) * Valued.v h * Valued.v S := by
              rw [map_mul, map_mul]
        _ ≤ Valued.v ((p : 𝔭.adicCompletion K)) * 1 * 1 :=
              mul_le_mul' (mul_le_mul' le_rfl heq.le) hwS
        _ = Valued.v ((p : 𝔭.adicCompletion K)) := by rw [mul_one, mul_one]
        _ < 1 := hwp_lt
      have h3 : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)) = 1 := by
        rw [hzL, Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h2), h1]
      exact absurd h3 (ne_of_lt hwz_lt)
  have hwh_le' : Valued.v h ≤ exp (-1 : ℤ) := zm0_le_exp_neg_one_of_lt_one hwh_lt
  -- 各項の付値を3次の閾値以下にする。
  have hfinal : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1))
      ≤ exp (-3 : ℤ) := by
    rw [hzL]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [map_pow]
      have hb1 : (Valued.v h) ^ p ≤ (exp (-1 : ℤ)) ^ p := pow_le_pow_left' hwh_le' p
      have hb2 : (exp (-1 : ℤ)) ^ p = exp (-(p : ℤ)) := by
        rw [← exp_nsmul]
        congr 1
        rw [nsmul_eq_mul]
        ring
      rw [hb2] at hb1
      exact le_trans hb1 (by rw [exp_le_exp]; omega)
    · calc Valued.v ((p : 𝔭.adicCompletion K) * h * S)
          = Valued.v ((p : 𝔭.adicCompletion K)) * Valued.v h * Valued.v S := by
            rw [map_mul, map_mul]
      _ ≤ exp (-2 : ℤ) * exp (-1 : ℤ) * 1 :=
            mul_le_mul' (mul_le_mul' hwp2 hwh_le') hwS
      _ = exp (-3 : ℤ) := by rw [mul_one, ← exp_add]; norm_num
  -- 最後に完備体の不等式を元の同じイデアルの所属へ戻す。
  have hle : 𝔭.intValuation ((u : R) ^ (p - 1) - 1) ≤ exp (-(3 : ℕ) : ℤ) := by
    rw [← hwR]
    simpa using hfinal
  exact (intValuation_le_pow_iff_mem 𝔭 _ 3).mp hle

end
end DkMath.Lib.NumberTheory.KummerLocalPrimaryUnit

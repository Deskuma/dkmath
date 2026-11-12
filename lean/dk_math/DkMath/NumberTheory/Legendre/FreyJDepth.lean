/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.Legendre.FreyJCentralSeat
import DkMath.Lib.NumberTheory.FreyPrimeValuation
import DkMath.Lib.NumberTheory.PolynomialHenselDigit

#print "file: DkMath.NumberTheory.Legendre.FreyJDepth"

/-!
# NOTE-008: 中央席の素数冪深度を j へ輸送する

Qₙ=n²+n+1 と q∣Qₙ に対し、q は2でも n(n+1) の素因子でもない。
従って j=256Qₙ³/(n²(n+1)²) の分母と256の付値は0となり、v_q(j)=3v_q(Qₙ)。
剰余曲線の j=0 より精密な、有限の素数冪住所の深さを保存する式である。
Hensel の一意な次桁へ進む場合だけ q≠3 を要求する。付値等式自体は q=3 も含む。
素数の存在、無限分枝、Legendre 予想、複素乗法は結論に含めない。
-/
namespace DkMath.NumberTheory.Legendre.FreyC4CentralSeat
open DkMath.Lib.NumberTheory

/-- 中央席の素因子における j の正確な付値。256と分母の両方を監査する。 -/
theorem rationalJ_valuation {n q : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hd : q ∣ centralSeat n) :
    padicValRat q (rationalJ n hn) = 3 * (padicValNat q (centralSeat n) : ℤ) := by
  let : Fact q.Prime := ⟨hq⟩
  have hq2 := divisor_ne_two hd
  obtain ⟨hqn, hqs⟩ := prime_not_dvd_coordinates hq hd
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsQ : (n : ℚ) + 1 ≠ 0 := by positivity
  have hQ : (centralSeat n : ℚ) ≠ 0 := by
    have : 0 < centralSeat n := by unfold centralSeat; omega
    exact_mod_cast this.ne'
  have hvn : padicValRat q (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hqn, Int.natCast_zero]
  have hvs : padicValRat q ((n : ℚ) + 1) = 0 := by
    have h : padicValRat q ((n + 1 : ℕ) : ℚ) = (padicValNat q (n + 1) : ℤ) :=
      padicValRat.of_nat
    rw [padicValNat.eq_zero_of_not_dvd hqs, Int.natCast_zero] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hv256 : padicValRat q (256 : ℚ) = 0 := by
    rw [show (256 : ℚ) = 2 ^ 8 by norm_num, padicValRat.pow,
      show padicValRat q (2 : ℚ) = (padicValNat q 2 : ℤ) from padicValRat.of_nat,
      FreyPrimeValuation.valuation_two_eq_zero hq2]
    norm_num
  rw [rationalJ_eq, padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hQ))
      (mul_ne_zero (pow_ne_zero _ hnQ) (pow_ne_zero _ hsQ)),
    padicValRat.mul (by norm_num : (256 : ℚ) ≠ 0) (pow_ne_zero _ hQ),
    padicValRat.mul (pow_ne_zero _ hnQ) (pow_ne_zero _ hsQ), padicValRat.pow,
    padicValRat.pow, padicValRat.pow, hv256, hvn, hvs, padicValRat.of_nat]
  ring

/-- 素数冪住所の厳密な深度 k は j の厳密な深度3kへ移る。 -/
theorem rationalJ_exact_depth {n q k : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hd : q ∣ centralSeat n) (hk : padicValNat q (centralSeat n) = k) :
    padicValRat q (rationalJ n hn) = 3 * (k : ℤ) := by
  rw [rationalJ_valuation hn hq hd, hk]

/-- 同じ定量的橋は旧支持 q≤n を保持する。 -/
theorem rationalJ_depth_of_mem_support {n q : ℕ} (hn : 0 < n)
    (hs : q ∈ squareOffsetPrimeSupport n (n + 1)) :
    q ≤ n ∧ padicValRat q (rationalJ n hn) = 3 * (padicValNat q (centralSeat n) : ℤ) := by
  obtain ⟨hq, hqn, hd⟩ := mem_primeSupport_iff.mp hs
  exact ⟨hqn, rationalJ_valuation hn hq hd⟩

/-- 中央席の整数多項式。負の代表も扱う Hensel API への入口。 -/
noncomputable def centralPolynomial : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.X + 1

/-- 中央席の自然数表示と整数多項式の評価は同じである。 -/
theorem centralPolynomial_eval (n : ℕ) : centralPolynomial.eval (n : ℤ) = (centralSeat n : ℤ) := by
  simp [centralPolynomial, centralSeat]

/-- q≠3 の中央席素因子は単純根。微分2n+1が0なら、4Qₙ=(2n+1)²+3よりq∣3。 -/
theorem centralPolynomial_derivative_not_dvd {n q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hd : q ∣ centralSeat n) : ¬ (q : ℤ) ∣ centralPolynomial.derivative.eval (n : ℤ) := by
  have hder : centralPolynomial.derivative.eval (n : ℤ) = 2 * (n : ℤ) + 1 := by
    simp [centralPolynomial, Polynomial.derivative_add, Polynomial.derivative_pow]
  rw [hder]
  intro hb
  have hQ : (q : ℤ) ∣ (n : ℤ) ^ 2 + n + 1 := by exact_mod_cast hd
  have h3 : (q : ℤ) ∣ 3 := by
    convert dvd_sub (dvd_mul_of_dvd_right hQ 4) (dvd_pow hb (by decide : 2 ≠ 0)) using 1
    ring
  have : q ∣ 3 := by exact_mod_cast h3
  exact hq3 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp this)

/-- 正の有限深度ごとの一意な次桁。q=3の分岐例外を単純根と混ぜない。 -/
theorem existsUnique_central_next_digit {n q k : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hk : 1 ≤ k) (hd : q ^ k ∣ centralSeat n) :
    ∃! t : Fin q, (q : ℤ) ^ (k + 1) ∣ centralPolynomial.eval ((n : ℤ) + (q : ℤ) ^ k * t.val) := by
  have hroot : q ∣ centralSeat n := (dvd_pow_self _ (by omega)).trans hd
  apply existsUnique_polynomial_powLift_digit centralPolynomial (n : ℤ) hq hk
  · rw [centralPolynomial_eval]
    exact_mod_cast hd
  · exact centralPolynomial_derivative_not_dvd hq hq3 hroot

/-- 整除による有限証明書から正確な付値を読む。次の冪が割らない条件を保持する。 -/
theorem rationalJ_depth_of_exact_divisibility {n q k : ℕ} (hn : 0 < n)
    (hq : q.Prime) (hk : 1 ≤ k) (hd : q ^ k ∣ centralSeat n)
    (hnext : ¬ q ^ (k + 1) ∣ centralSeat n) :
    padicValRat q (rationalJ n hn) = 3 * (k : ℤ) := by
  apply rationalJ_exact_depth hn hq ((dvd_pow_self _ (by omega)).trans hd)
  rw [Nat.padicValNat_def]
  exact multiplicity_eq_of_dvd_of_not_dvd hd hnext

/-- 一意な上昇桁以外を選ぶと有限深度kを実現し、その同じ住所でj深度3kを得る。
これは有限段の構成であり、無限分枝や素数の存在は要求しない。 -/
theorem exists_central_exact_jDepth {n q k : ℕ} (hn : 0 < n) (hq : q.Prime)
    (hq3 : q ≠ 3) (hk : 1 ≤ k) (hd : q ^ k ∣ centralSeat n) :
    ∃ s : Fin q, ∃ hpos : 0 < n + q ^ k * s.val,
      q ^ k ∣ centralSeat (n + q ^ k * s.val) ∧
      ¬ q ^ (k + 1) ∣ centralSeat (n + q ^ k * s.val) ∧
      padicValRat q (rationalJ (n + q ^ k * s.val) hpos) = 3 * (k : ℤ) := by
  have hroot : q ∣ centralSeat n := (dvd_pow_self _ (by omega)).trans hd
  have hdi : (q : ℤ) ^ k ∣ centralPolynomial.eval (n : ℤ) := by
    rw [centralPolynomial_eval]
    exact_mod_cast hd
  obtain ⟨s, hs, hsnext⟩ := exists_polynomial_exact_depth_digit centralPolynomial (n : ℤ)
    hq hk hdi (centralPolynomial_derivative_not_dvd hq hq3 hroot)
  have he : ((n + q ^ k * s.val : ℕ) : ℤ) = (n : ℤ) + (q : ℤ) ^ k * s.val := by push_cast; rfl
  rw [← he, centralPolynomial_eval] at hs hsnext
  have hdn : q ^ k ∣ centralSeat (n + q ^ k * s.val) := by exact_mod_cast hs
  have hnn : ¬ q ^ (k + 1) ∣ centralSeat (n + q ^ k * s.val) := by exact_mod_cast hsnext
  have hp : 0 < n + q ^ k * s.val := by omega
  exact ⟨s, hp, hdn, hnn, rationalJ_depth_of_exact_divisibility hp hq hk hdn hnn⟩

end DkMath.NumberTheory.Legendre.FreyC4CentralSeat

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.GNSourceTransport
import DkMath.Lib.Cosmic.GTailCyclotomic
import DkMath.FLT.Kummer.SevenUnitPowerClassBridge
import DkMath.FLT.Seven.SevenRamifiedFusionGlobalOrientedPrimeFactorization

/-!
# GN source 保存原理：位相変換と係数環の境界

現在の carrier を実三次係数の GN 因子として正確に位置付ける。
位相の Galois 変換は係数も変え、整数係数への降下を自動では供給しない。
同じ位相で整数 source へ降りる条件を、二次代数の係数の一意性で検査する。
-/

open scoped BigOperators NumberField
open DkMath.FLT.Seven DkMath.Lib.Cosmic DkMath.CosmicFormula

namespace DkMath.FLT.Kummer.SevenPrimaryNorm

noncomputable section

/-- 実三次係数の GN 線形 source。整数係数のパケットとは係数の型が異なる。 -/
def realGNSource (x u : SevenRealCubicInt) (i : ℕ) : SevenCyclotomicDegreeSixInt.Ring :=
  phaseSource (SevenCyclotomicDegreeSixInt.zeta ^ i)
    (SevenCyclotomicDegreeSixInt.ofReal x) (SevenCyclotomicDegreeSixInt.ofReal u)

/-- 実三次の端点 a,b は gap=a-b, parameter=b として GN の同じ元を与える。 -/
theorem realGNSource_sub_coordinates (a b : SevenRealCubicInt) (i : ℕ) :
    realGNSource (a - b) b i = SevenCyclotomicDegreeSixInt.ofReal a -
      SevenCyclotomicDegreeSixInt.zeta ^ i * SevenCyclotomicDegreeSixInt.ofReal b := by
  rw [realGNSource, map_sub, phaseSource_sub_coordinates]

/-- 整数 GN source は、実三次 source の整数係数への制限に厳密に一致する。 -/
theorem GNPhaseFactor_eq_realGNSource (x u : ℤ) (i : ℕ) :
    GNPhaseFactor x u i = realGNSource (x : SevenRealCubicInt) (u : SevenRealCubicInt) i := by
  simp only [GNPhaseFactor, realGNSource, phaseSource, map_add, map_mul, map_sub,
    map_one, map_pow, map_intCast, integralEquiv_septicRoot]

/-- 六次 Galois 回転は ζ を ζ² に送ると同時に、実三次係数も回転する。 -/
theorem rotate_realGNSource (x u : SevenRealCubicInt) (i : ℕ) :
    SevenCyclotomicDegreeSixInt.rotateEquiv (realGNSource x u i) =
      realGNSource (SevenRealCubicInt.rotateEquiv x) (SevenRealCubicInt.rotateEquiv u) (2 * i) := by
  simp only [realGNSource, phaseSource, map_add, map_mul, map_sub, map_one, map_pow,
    SevenCyclotomicDegreeSixInt.rotateEquiv_zeta, SevenCyclotomicDegreeSixInt.rotateEquiv_ofReal,
    ← pow_mul]

/-- 二次共役は実係数を固定し、位相添字を6倍する。全体の source の像の等式である。 -/
theorem star_realGNSource (x u : SevenRealCubicInt) (i : ℕ) :
    star (realGNSource x u i) = realGNSource x u (6 * i) := by
  have hr (a : SevenRealCubicInt) : star (SevenCyclotomicDegreeSixInt.ofReal a) =
      SevenCyclotomicDegreeSixInt.ofReal a := by
    ext <;> simp [SevenCyclotomicDegreeSixInt.ofReal, QuadraticAlgebra.algebraMap_eq]
  have hz : star SevenCyclotomicDegreeSixInt.zeta = SevenCyclotomicDegreeSixInt.zeta ^ 6 := by
    rw [← SevenCyclotomicDegreeSixInt.zetaInv_eq_pow_six]
    ext <;> simp [SevenCyclotomicDegreeSixInt.zeta, SevenCyclotomicDegreeSixInt.zetaInv]
  simp only [realGNSource, phaseSource, star_add, star_mul, star_sub, star_one,
    star_pow, hr, hz, ← pow_mul]
  ring

/-- 非自明な七次位相の二次代数における虚座標は非零。
ノルム1と奇数位数を使い、実数側に属すれば1になることを排除する。 -/
theorem zeta_pow_im_ne_zero {i : ℕ} (hi : i ∈ (Finset.range 7).erase 0) :
    (SevenCyclotomicDegreeSixInt.zeta ^ i).im ≠ 0 := by
  intro hz
  have hs : star (SevenCyclotomicDegreeSixInt.zeta ^ i) =
      SevenCyclotomicDegreeSixInt.zeta ^ i := by
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_star, hz, mul_zero, add_zero]
    · simp only [QuadraticAlgebra.im_star, hz, neg_zero]
  have hN : QuadraticAlgebra.norm (SevenCyclotomicDegreeSixInt.zeta ^ i) = 1 := by
    rw [map_pow]
    have h1 : QuadraticAlgebra.norm SevenCyclotomicDegreeSixInt.zeta = 1 := by
      simp [QuadraticAlgebra.norm_def, SevenCyclotomicDegreeSixInt.zeta]
    rw [h1, one_pow]
  have hn := QuadraticAlgebra.algebraMap_norm_eq_mul_star (SevenCyclotomicDegreeSixInt.zeta ^ i)
  rw [hN, map_one, hs] at hn
  have h2 : (SevenCyclotomicDegreeSixInt.zeta ^ i) ^ 2 = 1 := by
    simpa only [pow_two] using hn.symm
  have h7 : (SevenCyclotomicDegreeSixInt.zeta ^ i) ^ 7 = 1 := by
    rw [← pow_mul, Nat.mul_comm i 7, pow_mul, SevenCyclotomicDegreeSixInt.zeta_pow_seven, one_pow]
  have he : SevenCyclotomicDegreeSixInt.zeta ^ i = 1 := by
    calc
      SevenCyclotomicDegreeSixInt.zeta ^ i =
          ((SevenCyclotomicDegreeSixInt.zeta ^ i) ^ 2) ^ 3 * SevenCyclotomicDegreeSixInt.zeta ^ i := by
        rw [h2, one_pow, one_mul]
      _ = (SevenCyclotomicDegreeSixInt.zeta ^ i) ^ 7 := by ring
      _ = 1 := h7
  have hd := SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot.dvd_of_pow_eq_one i he
  have hi0 := (Finset.mem_erase.mp hi).1
  have hi7 := Finset.mem_range.mp (Finset.mem_erase.mp hi).2
  exact hi0 (Nat.eq_zero_of_dvd_of_lt hd hi7)

/-- 同じ非自明位相では、実係数の二つの端点も元の等式から一意に復元できる。 -/
theorem real_phase_endpoints_unique (a b c d : SevenRealCubicInt) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) :
    (SevenCyclotomicDegreeSixInt.ofReal a - SevenCyclotomicDegreeSixInt.zeta ^ i *
      SevenCyclotomicDegreeSixInt.ofReal b =
     SevenCyclotomicDegreeSixInt.ofReal c - SevenCyclotomicDegreeSixInt.zeta ^ i *
      SevenCyclotomicDegreeSixInt.ofReal d) ↔ a = c ∧ b = d := by
  constructor
  · intro he
    have him := congrArg QuadraticAlgebra.im he
    simp only [SevenCyclotomicDegreeSixInt.ofReal, QuadraticAlgebra.algebraMap_eq,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul,
      mul_zero, add_zero, zero_add, zero_sub] at him
    have hb : b = d := mul_left_cancel₀ (zeta_pow_im_ne_zero hi) (neg_inj.mp him)
    refine ⟨?_, hb⟩
    rw [hb] at he
    exact SevenCyclotomicDegreeSixInt.ofReal_injective (sub_left_inj.mp he)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- gap 座標を端点 `(x+u,u)` に戻す。両係数は実三次環内に留まる。 -/
theorem realGNSource_eq_endpoints (x u : SevenRealCubicInt) (i : ℕ) :
    realGNSource x u i = SevenCyclotomicDegreeSixInt.ofReal (x + u) -
      SevenCyclotomicDegreeSixInt.zeta ^ i * SevenCyclotomicDegreeSixInt.ofReal u := by
  simp only [realGNSource, phaseSource, map_add]
  ring

/-- 同じ非自明位相で整数 GN source と一致するための正確な係数条件。
位相の値の一致だけで、実三次係数を整数に置き換えることはできない。 -/
theorem real_phase_eq_integer_GN_iff (a b : SevenRealCubicInt) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) (x u : ℤ) :
    (SevenCyclotomicDegreeSixInt.ofReal a - SevenCyclotomicDegreeSixInt.zeta ^ i *
      SevenCyclotomicDegreeSixInt.ofReal b = GNPhaseFactor x u i) ↔
      a = (x : SevenRealCubicInt) + (u : SevenRealCubicInt) ∧ b = (u : SevenRealCubicInt) := by
  rw [GNPhaseFactor_eq_realGNSource, realGNSource_eq_endpoints]
  exact real_phase_endpoints_unique a b ((x : SevenRealCubicInt) + (u : SevenRealCubicInt))
    (u : SevenRealCubicInt) hi

/-- 整数 source の存在は、両端点が実際に整数の像に属すことと同値。
多項式の base change と、係数の整数への降下の違いを型と命題で固定する。 -/
theorem exists_integer_GN_source_iff (a b : SevenRealCubicInt) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) :
    (∃ x u : ℤ, SevenCyclotomicDegreeSixInt.ofReal a - SevenCyclotomicDegreeSixInt.zeta ^ i *
      SevenCyclotomicDegreeSixInt.ofReal b = GNPhaseFactor x u i) ↔
      (∃ m : ℤ, a = (m : SevenRealCubicInt)) ∧ (∃ n : ℤ, b = (n : SevenRealCubicInt)) := by
  constructor
  · rintro ⟨x, u, h⟩
    obtain ⟨ha, hb⟩ := (real_phase_eq_integer_GN_iff a b hi x u).mp h
    exact ⟨⟨x + u, by simpa only [Int.cast_add] using ha⟩, ⟨u, hb⟩⟩
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨m - n, n, (real_phase_eq_integer_GN_iff a b hi (m - n) n).mpr ⟨?_, hn⟩⟩
    rw [hm, Int.cast_sub]
    ring

/-- 非自明な実三次 GN source は、実三次係数で評価した GN 全体の因子である。 -/
theorem realGNSource_dvd_GN (x u : SevenRealCubicInt) {i : ℕ}
    (hi : i ∈ (Finset.range 7).erase 0) :
    realGNSource x u i ∣ GTail 7 1
      (SevenCyclotomicDegreeSixInt.ofReal x) (SevenCyclotomicDegreeSixInt.ofReal u) := by
  rw [DkMath.NumberTheory.GapFocusing.GN_eq_nontrivial_phase_prod_range
    (by decide : 0 < 7) SevenCyclotomicDegreeSixInt.zeta_isPrimitiveRoot]
  exact Finset.dvd_prod_of_mem _ hi

open SevenRealCubic SevenRealCubic.CurrentCarrierRamification

/-- 現在の三つの位相アドレスは非自明添字 1,4,5 に対応する。 -/
theorem current_phase_index_mem (i : Fin 3) :
    phaseInverseExponent i ∈ (Finset.range 7).erase 0 := by
  fin_cases i <;> decide

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- 現在の source は、実三次 gap と実三次 parameter を持つ GN source に等しい。
この等式には整数への降下や新しい packet の存在を仮定しない。 -/
theorem currentLinearCarrier_eq_realGNSource (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c = realGNSource (SevenRealCubicInt.rotateEquiv p.rho - p.rho)
      p.rho (phaseInverseExponent c.phase) := by
  rw [realGNSource_sub_coordinates]
  rfl

/-- 同じ現在の因子が、実三次係数の GN 七次多項式を割る。
整数 GN パケットへ移ったと解釈してはならない。 -/
theorem currentLinearCarrier_dvd_real_GN (c : CurrentCommonPrimeCyclotomicPacket h q) :
    currentLinearCarrier c ∣ GTail 7 1
      (SevenCyclotomicDegreeSixInt.ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho))
      (SevenCyclotomicDegreeSixInt.ofReal p.rho) := by
  rw [currentLinearCarrier_eq_realGNSource]
  apply realGNSource_dvd_GN
  exact current_phase_index_mem c.phase

/-- 現在の実三次 GN 全体は既存の軌道商そのもの。
有限幾何和の等式であり、gap の値での割り算を使わない。 -/
theorem current_real_GN_eq_orbitQuotient (p : DirectRealCubicRootPacket source r) :
    GTail 7 1
      (SevenCyclotomicDegreeSixInt.ofReal (SevenRealCubicInt.rotateEquiv p.rho - p.rho))
      (SevenCyclotomicDegreeSixInt.ofReal p.rho) =
      SevenCyclotomicDegreeSixInt.ofReal (directOrbitQuotient p) := by
  rw [GTail_one_eq_GTailCyclotomicShell]
  simp only [GTailCyclotomicShell, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, directOrbitQuotient, SevenRealCubicInt.seventhQuotient, map_add, map_mul, map_pow,
    map_sub, sub_add_cancel]
  norm_num
  ring

/-- 現在の residue packet が持つ非自明な比は、rho が整数の像であることを排除する。
整数なら Galois 回転で固定され、商が1になってしまう。 -/
theorem current_rho_not_integer (c : CurrentCommonPrimeCyclotomicPacket h q) (n : ℤ) :
    p.rho ≠ (n : SevenRealCubicInt) := by
  intro hn
  let : Fact q.Prime := ⟨c.residue.q_prime⟩
  have hr : SevenRealCubicInt.rotateEquiv p.rho = p.rho := by
    rw [hn, map_intCast]
  apply c.tau_ne_one
  rw [c.tau_eq]
  apply Units.ext
  change c.residue.evalReal (SevenRealCubicInt.rotateEquiv p.rho) / c.residue.evalReal p.rho = 1
  rw [hr, div_self c.residue.rho_ne_zero]

/-- 現在の選択位相を固定したまま、整数 GN source と同一視する経路は存在しない。
位相を変える場合や、実三次係数の一般化 GN パケットを排除する結論ではない。 -/
theorem currentLinearCarrier_ne_integer_GN_same_phase
    (c : CurrentCommonPrimeCyclotomicPacket h q) (x u : ℤ) :
    currentLinearCarrier c ≠ GNPhaseFactor x u (phaseInverseExponent c.phase) := by
  intro he
  have hi : phaseInverseExponent c.phase ∈ (Finset.range 7).erase 0 := by
    exact current_phase_index_mem c.phase
  have he' : SevenCyclotomicDegreeSixInt.ofReal (SevenRealCubicInt.rotateEquiv p.rho) -
      SevenCyclotomicDegreeSixInt.zeta ^ phaseInverseExponent c.phase *
      SevenCyclotomicDegreeSixInt.ofReal p.rho = GNPhaseFactor x u (phaseInverseExponent c.phase) := he
  exact current_rho_not_integer c u
    ((real_phase_eq_integer_GN_iff (SevenRealCubicInt.rotateEquiv p.rho) p.rho hi x u).mp he').2

end

end DkMath.FLT.Kummer.SevenPrimaryNorm

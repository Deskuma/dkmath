/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenCurrentPrimary
import DkMath.FLT.Seven.SevenRealCubicRotationFixed

/-!
# 深い Galois gap から、現在の一次単元の七乗根へ

回転固定性から rho の整数合同を回復し、同じ一次単元 delta に輸送する。
既存の整数合同版七次 Kummer 単元補題が delta=kappa^7 を与える。
theta=kappa*gamma として同じ source の単元を除くが、根の主イデアルは変わらない。
この操作は厳密降下でも、新しい FLT 解の構成でもない。
-/

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm
open DkMath.FLT.Seven.SevenRealCubic
open DkMath.FLT.Seven.SevenRealCubic.CurrentCarrierRamification

namespace DkMath.FLT.Kummer.SevenRealGN

noncomputable section
open SevenCyclotomicDegreeSixInt

/-- 実三次回転固定性があると、RealPrimary の合同先は整数へ降りる。
delta≡-x と x≡n から delta≡-n を作り、同じ delta を保つ。 -/
theorem realPrimary_integer_congruence_of_rotation_fixed (x : R)
    (hrot : (7 : R) ∣ SevenRealCubicInt.rotateEquiv x - x)
    (delta : Cˣ) (hdelta : RealPrimary delta (-x)) :
    ∃ n : ℤ, (7 : C) ∣ (delta : C) - (n : C) := by
  obtain ⟨n, hn⟩ := SevenRealCubicInt.rotation_fixed_mod_seven_integer x hrot
  have hm := map_dvd ofReal hn
  have hr : (7 : C) ∣ ofReal x - (n : C) := by
    simpa only [map_ofNat, map_sub, map_intCast] using hm
  have hd : (7 : C) ∣ (delta : C) + ofReal x := by
    simpa only [RealPrimary, map_neg, sub_neg_eq_add] using hdelta
  refine ⟨-n, ?_⟩
  rw [Int.cast_neg, sub_neg_eq_add]
  convert dvd_sub hd hr using 1
  ring

/-- 整数合同へ輸送した同じ単元に、証明済みの七次 Kummer 単元補題を適用する。
単元 criterion を追加引数として仮定していない。 -/
theorem realPrimary_seventh_of_rotation_fixed (x : R)
    (hrot : (7 : R) ∣ SevenRealCubicInt.rotateEquiv x - x)
    (delta : Cˣ) (hdelta : RealPrimary delta (-x)) :
    ∃ kappa : Cˣ, delta = kappa ^ 7 :=
  concrete_kummer_unit_power_criterion delta
    (realPrimary_integer_congruence_of_rotation_fixed x hrot delta hdelta)

variable {a b d : ℕ} {source : CounterexamplePack a b d}
variable {r : PrimitiveCounterexampleRamifiedProvenance source}
variable {p : DirectRealCubicRootPacket source r}
variable {h : DirectOrbitCanonicalCommonFactorPacket p} {q : ℕ}

/-- 現在の実三次 gap は7で割れる。axis^32 のうち axis^3 だけで十分である。 -/
theorem current_rotation_gap_seven_dvd (p : DirectRealCubicRootPacket source r) :
    (7 : R) ∣ SevenRealCubicInt.rotateEquiv p.rho - p.rho := by
  let v := SevenRealCubicInt.thetaSevenUnit_isUnit.unit
  have he : (7 : R) = SevenRealCubicInt.eisensteinAxis ^ 3 * (v : R) := by
    simpa only [v, IsUnit.unit_spec] using SevenRealCubicInt.seven_eq_eisensteinAxis_cube_mul_unit
  have hd : (7 : R) ∣ SevenRealCubicInt.eisensteinAxis ^ 3 := by
    refine ⟨(↑v⁻¹ : R), ?_⟩
    rw [he, mul_assoc]
    have hc : (v : R) * (↑v⁻¹ : R) = 1 := v.val_inv
    rw [hc, mul_one]
  exact hd.trans ((pow_dvd_pow _ (by decide : 3 ≤ 32)).trans (directOrbit_gap_axis_pow32_dvd p))

/-- 現在の rho は整数に等しいのではなく、mod 7 で整数に合同する。 -/
theorem current_rho_congruent_integer (p : DirectRealCubicRootPacket source r) :
    ∃ n : ℤ, (7 : R) ∣ p.rho - (n : R) :=
  SevenRealCubicInt.rotation_fixed_mod_seven_integer p.rho (current_rotation_gap_seven_dvd p)

/-- 現在の parameter を持つ任意の一次パケットの、同じ delta の七乗根。
receiver がどの一次正規化を返しても、parameter が同じなら適用できる。 -/
theorem current_primary_packet_unit_seventh (p : DirectRealCubicRootPacket source r)
    (Q : PrimaryPacket) (hparam : Q.parameter = p.rho) :
    ∃ kappa : Cˣ, Q.delta = kappa ^ 7 := by
  apply realPrimary_seventh_of_rotation_fixed p.rho (current_rotation_gap_seven_dvd p) Q.delta
  rw [← hparam]
  exact Q.primary

/-- 元の receiver の補正単元 epsilon*T_j^-1 も、根の選択によらず七乗。
一次合同のためには剰余正規化が必要だが、七乗剰余類はその取り替えで変わらない。
Q.delta=kappa^7 と Q.delta=(epsilon*T_j^-1)*t^-7 から同じ t を使って戻す。 -/
theorem current_corrected_unit_seventh (c : CurrentCommonPrimeCyclotomicPacket h q)
    (epsilon : Cˣ) (beta : C)
    (hf : currentLinearCarrier c = ramifiedUniformizer * ((epsilon : C) * beta ^ 7)) :
    ∃ kappa : Cˣ, epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹ = kappa ^ 7 := by
  obtain ⟨t, Q, _, hparam, _, _, _, hdelta, _, _⟩ := exists_current_primary_extension c epsilon beta hf
  obtain ⟨kappa, hkappa⟩ := current_primary_packet_unit_seventh p Q hparam
  have he : (epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹) * t⁻¹ ^ 7 = kappa ^ 7 :=
    hdelta.symm.trans hkappa
  refine ⟨kappa * t, ?_⟩
  calc
    epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹ =
        ((epsilon * (GNRamifierTwist (current_phase_index_mem c.phase))⁻¹) * t⁻¹ ^ 7) * t ^ 7 := by group
    _ = kappa ^ 7 * t ^ 7 := by rw [he]
    _ = (kappa * t) ^ 7 := (mul_pow _ _ _).symm

/-- 現在の一次パケットでは、実ノルム二成分と共役位相一成分がすべて消える。 -/
theorem current_primary_packet_obstruction_zero (p : DirectRealCubicRootPacket source r)
    (Q : PrimaryPacket) (hparam : Q.parameter = p.rho) :
    normCoordinates Q.delta = 0 ∧ phaseCharacter Q.delta = 1 :=
  (unit_seventh_iff_obstruction Q.delta).mp (current_primary_packet_unit_seventh p Q hparam)

/-- 同じパケットの単元を根へ吸収する。返すのは同じ source の等式であり、
delta=1 の PrimaryPacket ではない。後者の一次合同は一般には保たれない。 -/
theorem PrimaryPacket.unit_absorption (Q : PrimaryPacket) (kappa : Cˣ)
    (hkappa : Q.delta = kappa ^ 7) :
    Q.source = (zeta ^ Q.phase - 1) * (((kappa : C) * Q.gamma) ^ 7) ∧
      Ideal.span ({(kappa : C) * Q.gamma} : Set C) = Ideal.span ({Q.gamma} : Set C) ∧
      ¬ ramifiedUniformizer ∣ (kappa : C) * Q.gamma := by
  refine ⟨?_, Ideal.span_singleton_mul_left_unit kappa.isUnit Q.gamma, ?_⟩
  · change realGNSource Q.gap Q.parameter Q.phase = _
    rw [Q.factor, hkappa]
    change (zeta ^ Q.phase - 1) * ((kappa : C) ^ 7 * Q.gamma ^ 7) = _
    rw [mul_pow]
  · intro hd
    apply Q.root_away
    have hm := dvd_mul_of_dvd_right hd (↑kappa⁻¹ : C)
    have hc : (↑kappa⁻¹ : C) * (kappa : C) = 1 := kappa.inv_val
    simpa only [← mul_assoc, hc, one_mul] using hm

/-- 単元の吸収も根の主イデアルを減らさない。次の厳密降下には別の算術操作が必要。 -/
theorem PrimaryPacket.unit_absorption_no_measure_drop (Q : PrimaryPacket) (kappa : Cˣ)
    (m : Ideal C → ℕ) :
    ¬ m (Ideal.span ({(kappa : C) * Q.gamma} : Set C)) < m (Ideal.span ({Q.gamma} : Set C)) := by
  rw [Ideal.span_singleton_mul_left_unit kappa.isUnit Q.gamma]
  exact Nat.lt_irrefl _

/-- 実際の current receiver の Q.delta の七乗根を取り、同じ carrier の単元を除く。
Q、kappa、theta と theta=kappa*Q.gamma の等式で来歴を保持する。
現在の common-prime packet の仮定、元の Fermat 方程式、根の非分岐性を残す。 -/
theorem currentCarrier_unit_free_factor_receiver (c : CurrentCommonPrimeCyclotomicPacket h q) :
    ∃ Q : PrimaryPacket, ∃ kappa : Cˣ, ∃ theta : C,
      Q.gap = SevenRealCubicInt.rotateEquiv p.rho - p.rho ∧ Q.parameter = p.rho ∧
      Q.phase = phaseInverseExponent c.phase ∧ Q.source = currentLinearCarrier c ∧
      Q.delta = kappa ^ 7 ∧ theta = (kappa : C) * Q.gamma ∧
      currentLinearCarrier c = (zeta ^ phaseInverseExponent c.phase - 1) * theta ^ 7 ∧
      Ideal.span ({theta} : Set C) = Ideal.span ({Q.gamma} : Set C) ∧
      ¬ ramifiedUniformizer ∣ theta ∧ Fermat7Equation a b d := by
  obtain ⟨epsilon, beta, _, hext, hFermat⟩ := currentCarrier_primary_packet_receiver c
  obtain ⟨t, Q, hgap, hparam, hphase, hsource, _, _, _, _⟩ := hext
  obtain ⟨kappa, hkappa⟩ := current_primary_packet_unit_seventh p Q hparam
  have ha := Q.unit_absorption kappa hkappa
  refine ⟨Q, kappa, (kappa : C) * Q.gamma, hgap, hparam, hphase, hsource,
    hkappa, rfl, ?_, ha.2.1, ha.2.2, hFermat⟩
  rw [← hsource, ← hphase]
  exact ha.1

/-- 現在の rho は mod 7 では回転固定でも、元としては回転固定でない。
current packet の非自明な剰余比 tau を使い、合同と等式を区別する。 -/
theorem current_rotation_ne_self (c : CurrentCommonPrimeCyclotomicPacket h q) :
    SevenRealCubicInt.rotateEquiv p.rho ≠ p.rho := by
  intro hr
  let : Fact q.Prime := ⟨c.residue.q_prime⟩
  apply c.tau_ne_one
  rw [c.tau_eq]
  apply Units.ext
  change c.residue.evalReal (SevenRealCubicInt.rotateEquiv p.rho) / c.residue.evalReal p.rho = 1
  rw [hr, div_self c.residue.rho_ne_zero]

/-- 単元除去後の根を、そのまま次の実三次 parameter と見なすことはできない。
もし theta が実三次環の像なら、非自明位相の端点の一意性から rotate(rho)=rho
となり、現在の非自明な tau に反する。別の source 変換の存在までは排除しない。 -/
theorem current_unit_free_root_not_real (c : CurrentCommonPrimeCyclotomicPacket h q)
    (theta : C)
    (hf : currentLinearCarrier c = (zeta ^ phaseInverseExponent c.phase - 1) * theta ^ 7) :
    ¬ ∃ v : R, theta = ofReal v := by
  rintro ⟨v, hv⟩
  have he : ofReal (SevenRealCubicInt.rotateEquiv p.rho) -
      zeta ^ phaseInverseExponent c.phase * ofReal p.rho =
      ofReal (-(v ^ 7)) - zeta ^ phaseInverseExponent c.phase * ofReal (-(v ^ 7)) := by
    change currentLinearCarrier c = _
    rw [hf, hv]
    simp only [map_neg, map_pow]
    ring
  obtain ⟨ha, hb⟩ := (real_phase_endpoints_unique _ _ _ _ (current_phase_index_mem c.phase)).mp he
  exact current_rotation_ne_self c (ha.trans hb.symm)

end

end DkMath.FLT.Kummer.SevenRealGN

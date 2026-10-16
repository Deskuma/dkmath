/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.SevenRealPrimaryUnit
import DkMath.Lib.Algebra.RootUnitGauge

/-!
# 実三次 GN 保存の四定理

source、係数環、単元七乗剰余類、反復可能な不変データを固定する。
実際に構成する遷移は冪根の単元倍による取り替えである。
新しい FLT 解の生成や厳密降下の遷移を、この保存定理で代用しない。
-/

open DkMath.FLT.Seven DkMath.FLT.Kummer.SevenPrimaryNorm DkMath.Lib.Algebra

namespace DkMath.FLT.Kummer.SevenRealGN

noncomputable section

/-- 実三次係数を持つ非零 GN 一因子の、正規化済み七乗分解。
一次合同と剥離根の非分岐性は証明フィールドとして保持する。
全 GN の完全冪や FLT 方程式は、この局所パケットのフィールドではない。 -/
structure PrimaryPacket where
  gap : R
  parameter : R
  phase : ℕ
  phase_mem : phase ∈ (Finset.range 7).erase 0
  delta : Cˣ
  gamma : C
  source_ne_zero : realGNSource gap parameter phase ≠ 0
  factor : realGNSource gap parameter phase =
    (SevenCyclotomicDegreeSixInt.zeta ^ phase - 1) * ((delta : C) * gamma ^ 7)
  primary : RealPrimary delta (-parameter)
  root_away : ¬ SevenCyclotomicDegreeSixInt.ramifiedUniformizer ∣ gamma

/-- パケットの source を同じ実三次係数で評価する。 -/
def PrimaryPacket.source (P : PrimaryPacket) : C := realGNSource P.gap P.parameter P.phase

/-- 許容される根の取り替え。t 自身の合同ではなく、t⁷≡1 mod 7 を要求する。 -/
def AllowedGauge := {t : Cˣ // (7 : C) ∣ (t : C) ^ 7 - 1}

/-- 恒等的な取り替えも許容される。許容性と厳密減少は別の条件である。 -/
def identityGauge : AllowedGauge := ⟨1, by simp⟩

/-- 逆の取り替えも許容され、同じ係数の一次合同を戻せる。 -/
def inverseGauge (t : AllowedGauge) : AllowedGauge :=
  ⟨t.val⁻¹, dvd_unit_inv_pow_sub_one 7 t.val 7 t.property⟩

/-- 根付き単位による非自明な根の取り替え。ζ⁷=1 なので一次合同は保たれる。 -/
def zetaGauge : AllowedGauge :=
  ⟨SevenCyclotomicDegreeSixInt.zetaUnit, by
    change (7 : C) ∣ SevenCyclotomicDegreeSixInt.zeta ^ 7 - 1
    rw [SevenCyclotomicDegreeSixInt.zeta_pow_seven, sub_self]
    exact dvd_zero _⟩

/-- 実際の次パケットを構成する。根は t 倍、単元は t⁻⁷ 倍。
source の積等式・実三次一次合同・根の非分岐性をすべて証明し直す。 -/
def regauge (P : PrimaryPacket) (t : AllowedGauge) : PrimaryPacket where
  gap := P.gap
  parameter := P.parameter
  phase := P.phase
  phase_mem := P.phase_mem
  delta := P.delta * t.val⁻¹ ^ 7
  gamma := (t.val : C) * P.gamma
  source_ne_zero := P.source_ne_zero
  factor := P.factor.trans (root_unit_gauge_identity _ _ P.delta t.val 7)
  primary := dvd_regauged_unit_sub 7 (SevenCyclotomicDegreeSixInt.ofReal (-P.parameter))
    P.delta t.val 7 P.primary t.property
  root_away := by
    intro hd
    apply P.root_away
    have hm := dvd_mul_of_dvd_right hd (↑t.val⁻¹ : C)
    have hc : (↑t.val⁻¹ : C) * (t.val : C) = 1 := t.val.inv_val
    simpa only [← mul_assoc, hc, one_mul] using hm

/-- 保存定理1：source と分解の等式は同じ元として保持される。 -/
theorem source_preservation (P : PrimaryPacket) (t : AllowedGauge) :
    (regauge P t).source = P.source ∧
    P.source = (SevenCyclotomicDegreeSixInt.zeta ^ (regauge P t).phase - 1) *
      (((regauge P t).delta : C) * (regauge P t).gamma ^ 7) :=
  ⟨rfl, (regauge P t).factor⟩

/-- 保存定理2：実三次係数と位相を保ち、同じ parameter との一次合同も保つ。 -/
theorem coefficient_ring_preservation (P : PrimaryPacket) (t : AllowedGauge) :
    (regauge P t).gap = P.gap ∧ (regauge P t).parameter = P.parameter ∧
    (regauge P t).phase = P.phase ∧ RealPrimary (regauge P t).delta (-P.parameter) :=
  ⟨rfl, rfl, rfl, (regauge P t).primary⟩

/-- 保存定理3：実際の単元七乗商と、障害の三成分がともに一致する。 -/
theorem unit_class_preservation (P : PrimaryPacket) (t : AllowedGauge) :
    ((regauge P t).delta : Cˣ ⧸ unitPowerSubgroup C 7) = (P.delta : Cˣ ⧸ unitPowerSubgroup C 7) ∧
    unitObstruction (regauge P t).delta = unitObstruction P.delta := by
  have hs : SameUnitPowerClass 7 (regauge P t).delta P.delta := ⟨t.val⁻¹, rfl⟩
  exact ⟨sameUnitPowerClass_iff_quotient_eq.mp hs,
    unitObstruction_eq_of_same_class _ _ hs⟩

/-- 根の主イデアルも保存する。根の単元倍という遷移の算術的な限界を示す。 -/
theorem root_ideal_preservation (P : PrimaryPacket) (t : AllowedGauge) :
    Ideal.span ({(regauge P t).gamma} : Set C) = Ideal.span ({P.gamma} : Set C) :=
  Ideal.span_singleton_mul_left_unit t.val.isUnit P.gamma

/-- 反復時に比較する不変データ。一次合同と root_away は各パケット自身が証明を持つ。 -/
@[ext] structure ConservedData where
  gap : R
  parameter : R
  phase : ℕ
  source : C
  unitClass : Cˣ ⧸ unitPowerSubgroup C 7
  obstruction : (ZMod 7 × ZMod 7) × rootsOfUnity 7 C
  rootIdeal : Ideal C

/-- 同じ係数環と source に付随する不変データを取り出す。 -/
def snapshot (P : PrimaryPacket) : ConservedData :=
  ⟨P.gap, P.parameter, P.phase, P.source, P.delta, unitObstruction P.delta, Ideal.span {P.gamma}⟩

/-- 一段でデータ全体が保たれることを、各保存補題から組み立てる。 -/
theorem snapshot_regauge (P : PrimaryPacket) (t : AllowedGauge) : snapshot (regauge P t) = snapshot P := by
  apply ConservedData.ext
  · rfl
  · rfl
  · rfl
  · exact (source_preservation P t).1
  · exact (unit_class_preservation P t).1
  · exact (unit_class_preservation P t).2
  · exact root_ideal_preservation P t

/-- 任意の有限列の許容取り替えを、実際のパケットに順次適用する。 -/
def iterate (P : PrimaryPacket) : List AllowedGauge → PrimaryPacket
  | [] => P
  | t :: ts => iterate (regauge P t) ts

/-- 保存定理4：どの有限長の反復でも、同じ不変データと各段の一次合同が保たれる。
この反復は正規化であり、次の FLT 解や小さい測度を構成する定理ではない。 -/
theorem iterated_invariant_preservation (P : PrimaryPacket) (ts : List AllowedGauge) :
    snapshot (iterate P ts) = snapshot P ∧
    RealPrimary (iterate P ts).delta (-P.parameter) ∧
    ¬ SevenCyclotomicDegreeSixInt.ramifiedUniformizer ∣ (iterate P ts).gamma := by
  have he : snapshot (iterate P ts) = snapshot P := by
    induction ts generalizing P with
    | nil => rfl
    | cons t ts ih => exact (ih (regauge P t)).trans (snapshot_regauge P t)
  have hp : (iterate P ts).parameter = P.parameter := congrArg ConservedData.parameter he
  refine ⟨he, ?_, (iterate P ts).root_away⟩
  rw [← hp]
  exact (iterate P ts).primary

/-- この正規化反復は、根の主イデアルから定まるどの自然数測度も厳密には減らさない。
保存反復の構成を、降下の完成と取り違えないための明示的な境界。 -/
theorem no_ideal_measure_drop (P : PrimaryPacket) (ts : List AllowedGauge) (m : Ideal C → ℕ) :
    ¬ m (Ideal.span ({(iterate P ts).gamma} : Set C)) < m (Ideal.span ({P.gamma} : Set C)) := by
  have hi : Ideal.span ({(iterate P ts).gamma} : Set C) = Ideal.span ({P.gamma} : Set C) :=
    congrArg ConservedData.rootIdeal (iterated_invariant_preservation P ts).1
  rw [hi]
  exact Nat.lt_irrefl _

/-- 任意の実三次単元 b から局所パケットを構成する。x=0,u=-b,gamma=1。
全 GN の完全冪や FLT 反例を持つと主張せず、保存遷移が空でないことを示す。 -/
def packetOfRealUnit (b : Rˣ) : PrimaryPacket where
  gap := 0
  parameter := -(b : R)
  phase := 1
  phase_mem := by decide
  delta := Units.map SevenCyclotomicDegreeSixInt.ofReal.toMonoidHom b
  gamma := 1
  source_ne_zero := by
    have he : realGNSource 0 (-(b : R)) 1 =
        (SevenCyclotomicDegreeSixInt.zeta - 1) * SevenCyclotomicDegreeSixInt.ofReal (b : R) := by
      simp only [realGNSource, DkMath.Lib.Cosmic.phaseSource, map_zero, map_neg, pow_one]
      ring
    rw [he]
    exact mul_ne_zero (sub_ne_zero.mpr SevenCyclotomicDegreeSixInt.zeta_ne_one)
      (b.isUnit.map SevenCyclotomicDegreeSixInt.ofReal).ne_zero
  factor := by
    change realGNSource 0 (-(b : R)) 1 =
      (SevenCyclotomicDegreeSixInt.zeta ^ 1 - 1) *
        (SevenCyclotomicDegreeSixInt.ofReal (b : R) * (1 : C) ^ 7)
    simp only [realGNSource, DkMath.Lib.Cosmic.phaseSource, map_zero, map_neg, pow_one, one_pow, mul_one]
    ring
  primary := by
    change (7 : C) ∣ SevenCyclotomicDegreeSixInt.ofReal (b : R) -
      SevenCyclotomicDegreeSixInt.ofReal (- -(b : R))
    rw [neg_neg, sub_self]
    exact dvd_zero _
  root_away := by
    rintro ⟨w, hw⟩
    have hh := congrArg SevenCyclotomicDegreeSixInt.ramifiedEval hw
    rw [map_one, map_mul, SevenCyclotomicDegreeSixInt.ramifiedEval_uniformizer, zero_mul] at hh
    exact (by decide : (1 : ZMod 7) ≠ 0) hh

end

end DkMath.FLT.Kummer.SevenRealGN

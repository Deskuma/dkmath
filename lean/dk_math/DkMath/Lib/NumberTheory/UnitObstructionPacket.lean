/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealPowerObstruction
import DkMath.Lib.Algebra.UnitPowerClass

#print "file: DkMath.Lib.NumberTheory.UnitObstructionPacket"

/-!
# IRR-004: 選んだ単元と単元比の冪障害

理想類が消えた後に残る単元を、実際の単元冪商群に記録する。
全単元が p 乗という過剰な仮定ではなく、必要な単元・比だけの消滅を要求する。
完全な Selmer 完全列の構成・完全性はこのファイルでは主張しない。
-/

namespace DkMath.Lib.NumberTheory

open DkMath.Lib.Algebra

/-- 特定の単元 u の、単元 p 乗部分群による剰余類。 -/
def unitPowerObstruction {R : Type*} [CommRing R] (p : ℕ) (u : Rˣ) :
    Rˣ ⧸ unitPowerSubgroup R p := u

/-- 剰余類の消滅は、同じ単元 u の具体的な p 乗根の存在と同値。 -/
theorem unitPowerObstruction_eq_one_iff {R : Type*} [CommRing R] {p : ℕ} (u : Rˣ) :
    unitPowerObstruction p u = 1 ↔ ∃ t : Rˣ, u = t ^ p := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (QuotientGroup.eq_one_iff u).mp h
    exact ⟨t, ht.symm⟩
  · rintro ⟨t, ht⟩
    exact (QuotientGroup.eq_one_iff u).mpr ⟨t, ht.symm⟩

/-- 元とその同じ単元倍 p 乗表示。unit の選択と根を捨てない。 -/
structure UnitObstructionPacket (R : Type*) [CommRing R] (p : ℕ) (Q : R) where
  unit : Rˣ
  root : R
  equation : Q = unit * root ^ p

namespace UnitObstructionPacket
variable {R : Type*} [CommRing R] {p : ℕ} {Q Q' : R}

/-- この分解に残った単元の実際の剰余類。 -/
def obstruction (U : UnitObstructionPacket R p Q) : Rˣ ⧸ unitPowerSubgroup R p :=
  unitPowerObstruction p U.unit

/-- 必要な単元が p 乗である場合、初めて Q 自身の p 乗根を得る。 -/
theorem exists_power_of_trivial (U : UnitObstructionPacket R p Q) (h : U.obstruction = 1) :
    ∃ b : R, Q = b ^ p := by
  obtain ⟨t, ht⟩ := (unitPowerObstruction_eq_one_iff U.unit).mp h
  refine ⟨(t : R) * U.root, ?_⟩
  calc
    Q = (U.unit : R) * U.root ^ p := U.equation
    _ = ((t : R) * U.root) ^ p := by rw [ht, Units.val_pow_eq_pow_val, mul_pow]

/-- 異なる二因子から得た、選んだ係数単元の比の障害。 -/
def ratioObstruction (U : UnitObstructionPacket R p Q) (V : UnitObstructionPacket R p Q') :
    Rˣ ⧸ unitPowerSubgroup R p := unitPowerObstruction p (U.unit / V.unit)

/-- 比の正規化には、この比の p 乗根だけを要求すればよい。 -/
theorem ratio_trivial_iff (U : UnitObstructionPacket R p Q) (V : UnitObstructionPacket R p Q') :
    U.ratioObstruction V = 1 ↔ ∃ t : Rˣ, U.unit / V.unit = t ^ p :=
  unitPowerObstruction_eq_one_iff _

/-- 固定した非零 Q の分解を変更しても、単元の剰余類は不変。
整閉性・p≠0・Q≠0 は根の比較に必要なので明示する。 -/
theorem obstruction_independent [IsDomain R] [IsIntegrallyClosed R]
    (U V : UnitObstructionPacket R p Q) (hp : p ≠ 0) (hQ : Q ≠ 0) :
    U.obstruction = V.obstruction := by
  apply sameUnitPowerClass_iff_quotient_eq.mp
  exact sameUnitPowerClass_of_fixed_extraction U.unit V.unit hp hQ one_ne_zero
    (by simpa using U.equation) (by simpa using V.equation)

/-- Q 自身が p 乗なら、残った単元の類も1になる。 -/
theorem trivial_of_power [IsDomain R] [IsIntegrallyClosed R]
    (U : UnitObstructionPacket R p Q) (hp : p ≠ 0) (hQ : Q ≠ 0) {b : R} (hb : Q = b ^ p) :
    U.obstruction = 1 := by
  let V : UnitObstructionPacket R p Q := ⟨1, b, by simpa using hb⟩
  rw [U.obstruction_independent V hp hQ]
  change unitPowerObstruction p 1 = 1
  exact (unitPowerObstruction_eq_one_iff _).mpr ⟨1, by simp⟩

end UnitObstructionPacket

/-- イデアル障害が消えた後も、同じイデアル根の生成元と単元 packet を保持する。 -/
theorem IdealPowerObstruction.exists_unit_packet
    {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} {Q : R}
    (E : IdealPowerObstruction R p Q) (h : E.obstruction = 1) :
    ∃ U : UnitObstructionPacket R p Q, Ideal.span ({U.root} : Set R) = (E.root : Ideal R) := by
  obtain ⟨u, b, hb, he⟩ := E.exists_unit_generator h
  exact ⟨⟨u, b, he⟩, hb⟩

end DkMath.Lib.NumberTheory

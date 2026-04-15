/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchAFringeDescent

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchAPrimitiveStrongProvider"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
`PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget` の強化版。

weak 版と同じ入力を受け、返り値だけ
`∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t`
へ強める。

付録:
- restore/arithmetic 層で `¬ p ∣ t'` を維持できるなら、
  packet descent strong version の家主となる self-contained target。
- weak 版から strong へ強化するには、restore が concrete に何を返すかの性質が必須。
-/
abbrev PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∀ {q : ℕ}, Nat.Prime q →
      q ∣ s →
      ¬ q ∣ t →
      Nat.Coprime q y →
      q ≠ p →
      ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
`PrimeGe5BranchAPrimitiveWieferichPacketTarget` の強化版。

weak 版と同じ入力を受け、返り値だけ
`∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t`
へ強める。
-/
abbrev PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget : Prop :=
  ∀ {p x y z t s : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    Nat.Coprime t y →
    Nat.Coprime s y →
    ¬ p ∣ s →
    ¬ p ∣ t →
    y ^ (p - 1) ≡ 1 [MOD p ^ 2] →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
strong wieferich 版から weak wieferich 版への緩和橋。
-/
theorem primeGe5BranchAPrimitiveWieferichPacket_of_strong
    (hStrong : PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget) :
    PrimeGe5BranchAPrimitiveWieferichPacketTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
  rcases hStrong hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich with
    ⟨pkt', hlt, _hpt'⟩
  exact ⟨pkt', hlt⟩

/--
strong restore 版から strong wieferich 版を得る橋。

ここが主戦場。既存の
`primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore`
の strong 平行版として、wieferich descent route を strong へ lifting する。

付録:
- Zsigmondy / arithmetic / restore を chaining して
  `¬ p ∣ pkt'.t` を失わない packet を構成。
- これが成功すれば、primitive route の entire chain が strong になる。
-/
theorem primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong
    (hZ : PrimeGe5BranchAPrimitiveZsigmondyTarget)
    (hArith : PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget)
    (hRestoreS : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget) :
    PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
  -- Step 1: hZ から distinguished prime q を取り出す
  rcases hZ hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich with
    ⟨q, hqprime, hqGN, hqgap⟩
  -- Step 2: hArith で q ∣ s, ¬ q ∣ t, Coprime q y, q ≠ p を得る
  rcases hArith hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqGN hqgap with
    ⟨hqs, hqt, hcop_qy, hq_ne_p⟩
  -- Step 3: restore_witness_properties_default で RestoreWitnessProperties を作る
  have hData := restore_witness_properties_default
    hpack hp_dvd_gap hgap hsGN hsx hqprime hqs hqt hcop_qy hq_ne_p
  -- Step 4: hRestoreS に流し、pkt' と hlt, hpt' を得る
  rcases hRestoreS hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p with
    ⟨pkt', hlt, hpt'⟩
  exact ⟨pkt', hlt, hpt'⟩

/--
strong wieferich 版から strong descent 版への橋。

これは薄い wrapper で済む。
weak 版 `primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket` の strong 平行版。
-/
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacketStrong
    (hWiefS : PrimeGe5BranchAPrimitiveWieferichPacketStrongTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t
  have hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
    primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN
  rcases hWiefS hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich with
    ⟨pkt', hlt, hpt'⟩
  exact ⟨pkt', hlt, hpt'⟩

/--
必要なら 1 本でまとめた exported theorem。
-/
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_zsigmondy_arithmetic_restore
    (hZ : PrimeGe5BranchAPrimitiveZsigmondyTarget)
    (hArith : PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget)
    (hRestoreS : PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget := by
  apply primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacketStrong
  exact primeGe5BranchAPrimitiveWieferichPacketStrong_of_zsigmondy_arithmetic_and_restoreStrong
    hZ hArith hRestoreS

end DkMath.FLT

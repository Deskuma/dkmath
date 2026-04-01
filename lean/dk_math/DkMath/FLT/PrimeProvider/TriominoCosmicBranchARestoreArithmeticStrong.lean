/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.PrimeProvider.TriominoCosmicBranchAPrimitiveStrongProvider

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
`PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget` の強化版。

weak 版は pkt'.z < z を返すのみだが、
strong版ではさらに ¬ p ∣ pkt'.t を保持した packet を返す。

本戦場：ここだけを埋めればよい。
-/
abbrev PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget : Prop :=
  ∀ {p z x' y' z' : ℕ},
    PrimeGe5CounterexamplePack p x' y' z' →
    p ∣ (z' - y') →
    z' < z →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p,
      pkt'.z < z ∧ ¬ p ∣ pkt'.t

/--
主戦場の bridge: weak arithmetic core + strong packet packaging → strong restore.

この橋は no-sorry ✅。
-/
theorem primeGe5BranchAPrimitivePacketRestoreFromArithmeticStrong_of_arithmeticCore_and_packetStrong
    (hArithCore : PrimeGe5BranchAPrimitiveRestoreArithmeticCoreTarget)
    (hPackStrong : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget) :
    PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx
    hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
    q hqprime hqs hqt hcop_qy hq_ne_p
  have ⟨x', y', z', hpack', hp_dvd_gap', hz'lt⟩ :=
    hArithCore (p := p) (x := x) (y := y) (z := z) (t := t) (s := s)
      hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t hWieferich
      hqprime hqs hqt hcop_qy hq_ne_p
  exact hPackStrong hpack' hp_dvd_gap' hz'lt

/--
Open kernel: packet packaging strong provider.

既存 weak packet route から ¬ p ∣ pkt'.t を retrieve する手段。
-/
theorem primeGe5BranchAPrimitiveRestorePacketPackagingStrong
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hz'lt
  sorry

end DkMath.FLT

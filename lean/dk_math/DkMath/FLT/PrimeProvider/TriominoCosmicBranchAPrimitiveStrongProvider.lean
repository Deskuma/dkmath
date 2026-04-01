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

/-- `PrimeGe5BranchAPrimitiveWieferichPacketTarget` から `StrongTarget` への橋。

既存 `primeGe5BranchAPrimitivePacketDescent_of_wieferichPacket` を強化して
`∃ pkt', pkt'.z < z ∧ ¬ p ∣ pkt'.t` を返す。
-/
theorem primeGe5BranchAPrimitivePacketDescentStrong_of_wieferichPacket
    (hWief : PrimeGe5BranchAPrimitiveWieferichPacketTarget) :
    PrimeGe5BranchAPrimitivePacketDescentStrongTarget := by
  intro p x y z t s hpack hp_dvd_gap hgap hsGN hsx hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t
  rcases hWief hpack hp_dvd_gap hgap hsGN hsx
      hcop_ts hcop_ty hcop_sy hp_not_dvd_s hp_not_dvd_t
      (primeGe5BranchANormalForm_y_wieferich_mod_p_sq hpack hp_dvd_gap hgap hsGN) with
    ⟨pkt', hz'_lt⟩
  have hpt' : ¬ p ∣ pkt'.t := by
    sorry
  exact ⟨pkt', hz'_lt, hpt'⟩

end DkMath.FLT

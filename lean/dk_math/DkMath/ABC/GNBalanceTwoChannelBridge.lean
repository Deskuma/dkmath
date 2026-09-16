/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.TwoChannel
import DkMath.ABC.GNBalanceDepthTransport

#print "file: DkMath.ABC.GNBalanceTwoChannelBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# ABC/GN bridge to the stable two-channel kernel

The existing support/depth orientation is preserved: the left channel is
support mass and the right channel is depth mass.  This is a coordinate bridge
only; it does not identify the GN balance with the differently oriented outer
ABC balance.
-/

namespace DkMath.ABC

open DkMath.Lib.TwoChannel
open DkMath.CosmicFormulaBinom

theorem GNChannelMass_eq_twoChannel_mass (T : Triple) (p : ℕ) :
    GNChannelMass T p =
      mass (GNChannelSupportMass T p) (GNChannelDepthMass T p) := by
  rfl

theorem GNChannelBalance_eq_twoChannel_balance (T : Triple) (p : ℕ) :
    GNChannelBalance T p =
      balance (GNChannelSupportMass T p) (GNChannelDepthMass T p) := by
  rfl

theorem GNChannelSupportMass_eq_twoChannel_reconstruction
    (T : Triple) (p : ℕ) :
    GNChannelSupportMass T p =
      (mass (GNChannelSupportMass T p) (GNChannelDepthMass T p) +
        balance (GNChannelSupportMass T p) (GNChannelDepthMass T p)) / 2 := by
  exact left_eq_half_mass_add_balance
    (GNChannelSupportMass T p) (GNChannelDepthMass T p)

theorem GNChannelDepthMass_eq_twoChannel_reconstruction
    (T : Triple) (p : ℕ) :
    GNChannelDepthMass T p =
      (mass (GNChannelSupportMass T p) (GNChannelDepthMass T p) -
        balance (GNChannelSupportMass T p) (GNChannelDepthMass T p)) / 2 := by
  exact right_eq_half_mass_sub_balance
    (GNChannelSupportMass T p) (GNChannelDepthMass T p)

/-! The local BCAL successor law has the generic right-channel orientation. -/

theorem GNNonExceptionalLocalMass_eq_twoChannel_mass
    (p a b q : ℕ) :
    GNNonExceptionalLocalMass p a b q =
      mass (Real.log (q : ℝ))
        ((((GN p a b).factorization q : ℝ) - 1) * Real.log (q : ℝ)) := by
  unfold GNNonExceptionalLocalMass mass
  ring

theorem GNNonExceptionalLocalBalance_eq_twoChannel_balance
    (p a b q : ℕ) :
    GNNonExceptionalLocalBalance p a b q =
      balance (Real.log (q : ℝ))
        ((((GN p a b).factorization q : ℝ) - 1) * Real.log (q : ℝ)) := by
  unfold GNNonExceptionalLocalBalance balance
  ring

end DkMath.ABC

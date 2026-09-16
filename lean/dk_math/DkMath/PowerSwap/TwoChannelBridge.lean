/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.TwoChannel
import DkMath.PowerSwap.Contours

#print "file: DkMath.PowerSwap.TwoChannelBridge"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
# PowerSwap bridge to the stable two-channel kernel

The existing `gapU`, `gapV`, `gapP`, and `gapQ` definitions are retained.  This
module only identifies their sum/difference coordinates with the neutral
`DkMath.Lib.TwoChannel` kernel.
-/

namespace DkMath.PowerSwap

open DkMath.Lib.TwoChannel

theorem gapP_eq_twoChannel_center (x y : ℝ) :
    gapP x y = center (gapU x y) (gapV x y) := by
  rfl

theorem gapQ_eq_twoChannel_balance (x y : ℝ) :
    gapQ x y = balance (gapU x y) (gapV x y) := by
  rfl

theorem gapU_eq_gapP_add_half_gapQ (x y : ℝ) :
    gapU x y = gapP x y + gapQ x y / 2 := by
  simpa [gapP_eq_twoChannel_center, gapQ_eq_twoChannel_balance] using
    (left_eq_center_add_half_balance (gapU x y) (gapV x y))

theorem gapV_eq_gapP_sub_half_gapQ (x y : ℝ) :
    gapV x y = gapP x y - gapQ x y / 2 := by
  simpa [gapP_eq_twoChannel_center, gapQ_eq_twoChannel_balance] using
    (right_eq_center_sub_half_balance (gapU x y) (gapV x y))

end DkMath.PowerSwap

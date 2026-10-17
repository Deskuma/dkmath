/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.Cosmic.CoreNested
import DkMath.Lib.Cosmic.GTailTransport

#print "file: DkMath.Lib.Cosmic.CoreNestedTransport"

/-!
# Independent axes of transport

Changing the base/increment path and changing a binomial term selection
both preserve Big. The selected Body alone need not equal the difference Core.
The bridge subtracts the same starting power from the existing selection balance.
-/

namespace DkMath.Lib.Cosmic

open DkMath.CosmicFormula

variable {R : Type*} [CommRing R]

/-- Every selection represents the same endpoint as the nested Core. -/
theorem selected_balance_eq_pow_add_powerCore (d : ℕ) (S : Finset ℕ) (base step : R) :
    selectedGap d S step base + selectedBody d S step base =
      base ^ d + powerCore d base step := by
  rw [← selectedGap_add_selectedBody, pow_add_powerCore, add_comm step base]

/-- Subtracting the fixed starting power gives Core for any term selection. -/
theorem powerCore_eq_selected_balance_sub (d : ℕ) (S : Finset ℕ) (base step : R) :
    powerCore d base step =
      selectedGap d S step base + selectedBody d S step base - base ^ d := by
  rw [selected_balance_eq_pow_add_powerCore, add_sub_cancel_left]

/-- The two path segments may independently choose arbitrary Body selections. -/
theorem selected_nested_transport (d : ℕ) (S T U : Finset ℕ) (base a b : R) :
    selectedGap d S (a + b) base + selectedBody d S (a + b) base - base ^ d =
      (selectedGap d T a base + selectedBody d T a base - base ^ d) +
        (selectedGap d U b (base + a) + selectedBody d U b (base + a) -
          (base + a) ^ d) := by
  simpa only [← powerCore_eq_selected_balance_sub] using powerCore_split d base a b

end DkMath.Lib.Cosmic

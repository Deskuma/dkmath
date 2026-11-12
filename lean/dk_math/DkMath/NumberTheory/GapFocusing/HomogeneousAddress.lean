/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.HomogeneousCyclotomicAddress
import DkMath.NumberTheory.GapFocusing.PrimeOrder

#print "file: DkMath.NumberTheory.GapFocusing.HomogeneousAddress"

/-!
[DkMath.Lib] GN-LIB-006b: the 3 support/appearance definitions and 12 neutral
address theorems are owned by `Lib.NumberTheory.HomogeneousCyclotomicAddress`.
Historical names and bodies are preserved. This entrance retains only the
two bridges to the existing Zsigmondy primitive-prime carrier below.
-/

namespace DkMath.NumberTheory.GapFocusing

/-- The existing Zsigmondy notion and first homogeneous layer appearance
coincide under the natural-number subtraction and denominator hypotheses. -/
theorem primitivePrimeDivisor_iff_firstLayerAppearance
    {q a b n : ℕ} [Fact q.Prime] (hab : b ≤ a) (hn : 0 < n) (hb : ¬q ∣ b) :
    DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q ↔
      FirstLayerAppearance q a b n := by
  have hbZ : ¬(q : ℤ) ∣ (b : ℤ) := by exact_mod_cast hb
  rw [primitivePrimeDivisor_iff_primeOrder_eq hab hn hb,
    firstLayerAppearance_iff_primeOrder_eq q a b hn hbZ]

/-- Above degree one, an existing primitive prime gives first layer appearance
without an extra coordinate coprimality assumption. -/
theorem primitivePrimeDivisor_firstLayerAppearance
    {q a b n : ℕ} (hab : b ≤ a) (hn : 1 < n)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor a b n q) :
    FirstLayerAppearance q a b n := by
  let : Fact q.Prime := ⟨hprim.prime⟩
  have hb := (primitivePrimeDivisor_not_dvd_coordinates hab hn hprim).2
  exact (primitivePrimeDivisor_iff_firstLayerAppearance hab (by omega) hb).mp hprim

end DkMath.NumberTheory.GapFocusing

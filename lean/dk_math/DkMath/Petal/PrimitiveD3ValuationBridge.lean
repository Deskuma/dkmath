/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.ZsigmondyD3Bridge

#print "file: DkMath.Petal.PrimitiveD3ValuationBridge"

/-!
# Petal Primitive D3 Valuation Bridge

This file is the first Petal-facing bridge from the `d = 3` Zsigmondy witness
to the honest squarefree/no-lift valuation layer.

It does not prove squarefreeness.  It only says that once the caller supplies
`Squarefree (GN 3 (c - b) b)`, the same primitive divisor `q` already shared by
Zsigmondy, Petal, and PrimitiveBeam has `padicValNat <= 1` in `c^3 - b^3`.

The file also exposes the strictly weaker local no-lift version:
`¬ q^2 ∣ GN 3 (c - b) b` is enough for the same bound for that particular `q`.
-/

namespace DkMath
namespace Petal

open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.PrimitiveBeam

/--
Local no-lift on `GN3` turns the shared `d = 3` primitive witness into the
valuation bound on the difference body.

This is weaker than squarefree `GN3`: it only asks that the selected witness
`q` does not lift to `q^2` on the `GN3` side.
-/
theorem primitiveD3_padicValNat_le_one_of_noLift_GN
    {c b q : ℕ} (hbc : b < c)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hNoLift : ¬ q ^ 2 ∣ GN 3 (c - b) b) :
    padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
  exact
    primitive_prime_padic_bound_diff_of_noLift_GN
      (q := q) (a := c) (b := b) (d := 3)
      (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
      (by norm_num)
      (by norm_num)
      hbc
      hNoLift

/--
Squarefree `GN3` turns the shared `d = 3` primitive witness into the honest
valuation bound on the difference body.

This is a wrapper around the existing `PrimitiveBeam` squarefree theorem.  The
Petal contribution is only the `BoundaryD3Reduced` vocabulary and the
Zsigmondy-to-PrimitiveBeam witness conversion.
-/
theorem primitiveD3_padicValNat_le_one_of_squarefree_GN
    {c b q : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
    (hprim : DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q)
    (hG_sq : Squarefree (GN 3 (c - b) b)) :
    padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
  exact
    primitive_prime_padic_bound_diff_of_squarefree_GN
      (q := q) (a := c) (b := b) (d := 3)
      Nat.prime_three
      (by norm_num)
      hbc
      hb
      hcop
      hred
      (primitivePrimeFactorOfDiffPow_of_primitivePrimeDivisor_d3 hprim)
      hG_sq

/--
Existence form for the local no-lift route: on the reduced cubic branch, if the
selected shared witness has no `q^2` lift on `GN3`, then it has valuation at
most one in the difference body.
-/
theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_noLift_GN
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
    (hNoLift :
      ∀ {q : ℕ}, DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q →
        ¬ q ^ 2 ∣ GN 3 (c - b) b) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
        PrimitivePrimeFactorOfDiffPow q c b 3 ∧
          AnchoredS0Carrier q c b q ∧
            padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
  rcases exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
      hbc hb hcop hred with
    ⟨q, hprim, hprimitive, hcarrier⟩
  exact
    ⟨q, hprim, hprimitive, hcarrier,
      primitiveD3_padicValNat_le_one_of_noLift_GN
        hbc hprim (hNoLift hprim)⟩

/--
Existence form: on the reduced cubic branch, if the `GN3` side is squarefree,
there is a single witness `q` that is simultaneously Zsigmondy-primitive,
PrimitiveBeam-primitive, Petal-anchored, and valuation-bounded.
-/
theorem exists_primitiveD3_padicValNat_le_one_of_boundaryD3Reduced_of_squarefree_GN
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b)
    (hG_sq : Squarefree (GN 3 (c - b) b)) :
    ∃ q : ℕ,
      DkMath.Zsigmondy.PrimitivePrimeDivisor c b 3 q ∧
        PrimitivePrimeFactorOfDiffPow q c b 3 ∧
          AnchoredS0Carrier q c b q ∧
            padicValNat q (c ^ 3 - b ^ 3) ≤ 1 := by
  rcases exists_primitivePrimeFactorOfDiffPow_d3_of_boundaryD3Reduced
      hbc hb hcop hred with
    ⟨q, hprim, hprimitive, hcarrier⟩
  exact
    ⟨q, hprim, hprimitive, hcarrier,
      primitiveD3_padicValNat_le_one_of_squarefree_GN
        hbc hb hcop hred hprim hG_sq⟩

end Petal
end DkMath

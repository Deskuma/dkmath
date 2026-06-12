/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Petal.Anchor
import DkMath.Petal.GcdBridge

#print "file: DkMath.Petal.BoundaryD3"

/-!
# Petal Boundary D3

This file records the degree-three boundary behavior of the Petal detector
`S0_nat`.

The central observation is that, on the cubic Petal face, the prime `3` is
exactly the contact component between the boundary gap `c - b` and `S0_nat`.
-/

namespace DkMath
namespace Petal

open DkMath.FLT.PetalDetect

/-- The degree-three boundary branch: `3` divides the boundary gap. -/
def BoundaryD3Branch (c b : ℕ) : Prop :=
  3 ∣ c - b

/-- The degree-three reduced branch: `3` does not divide the boundary gap. -/
def BoundaryD3Reduced (c b : ℕ) : Prop :=
  ¬ 3 ∣ c - b

/-- Every cubic Petal coordinate lies on either the boundary branch or the reduced branch. -/
theorem boundaryD3Branch_or_reduced (c b : ℕ) :
    BoundaryD3Branch c b ∨ BoundaryD3Reduced c b := by
  by_cases h : 3 ∣ c - b
  · exact Or.inl h
  · exact Or.inr h

/-- The reduced branch is not the boundary branch. -/
theorem not_boundaryD3Branch_of_reduced
    {c b : ℕ} (h : BoundaryD3Reduced c b) :
    ¬ BoundaryD3Branch c b :=
  h

/--
On the degree-three boundary branch, `3` divides the Petal detector `S0_nat`.
-/
theorem three_dvd_S0_nat_of_three_dvd_sub
    {c b : ℕ} (hbc : b < c) (h3 : 3 ∣ c - b) :
    3 ∣ S0_nat c b := by
  rcases h3 with ⟨k, hk⟩
  have hc_eq : c = 3 * k + b := by
    calc
      c = (c - b) + b := (Nat.sub_add_cancel hbc.le).symm
      _ = 3 * k + b := by rw [hk]
  refine ⟨b ^ 2 + 3 * k * b + 3 * k ^ 2, ?_⟩
  rw [hc_eq]
  unfold S0_nat
  ring

/--
If `3` divides `S0_nat`, then `3` must divide the boundary gap.
-/
theorem three_dvd_sub_of_three_dvd_S0_nat
    {c b : ℕ} (hbc : b < c) (h3S0 : 3 ∣ S0_nat c b) :
    3 ∣ c - b := by
  by_contra h3sub
  exact (three_not_dvd_S0_nat_of_not_dvd_sub hbc h3sub) h3S0

/--
The cubic Petal detector has `3` exactly on the boundary branch.
-/
theorem three_dvd_S0_nat_iff_three_dvd_sub
    {c b : ℕ} (hbc : b < c) :
    3 ∣ S0_nat c b ↔ 3 ∣ c - b :=
  ⟨three_dvd_sub_of_three_dvd_S0_nat hbc,
    three_dvd_S0_nat_of_three_dvd_sub hbc⟩

/-- On the reduced branch, `3` does not divide `S0_nat`. -/
theorem boundaryD3Reduced_three_not_dvd_S0_nat
    {c b : ℕ} (hbc : b < c) (h : BoundaryD3Reduced c b) :
    ¬ 3 ∣ S0_nat c b :=
  three_not_dvd_S0_nat_of_not_dvd_sub hbc h

/-- On the boundary branch, `3` divides `S0_nat`. -/
theorem boundaryD3Branch_three_dvd_S0_nat
    {c b : ℕ} (hbc : b < c) (h : BoundaryD3Branch c b) :
    3 ∣ S0_nat c b :=
  three_dvd_S0_nat_of_three_dvd_sub hbc h

/--
In coprime Petal coordinates, the reduced branch makes the boundary gap
coprime to `S0_nat`.
-/
theorem boundaryD3Reduced_coprime_sub_S0_nat
    {c b : ℕ} (hbc : b < c) (hcop : Nat.Coprime c b)
    (h : BoundaryD3Reduced c b) :
    Nat.Coprime (c - b) (S0_nat c b) :=
  coprime_sub_S0_nat_of_coprime_of_not_dvd_three hbc hcop h

/--
On the reduced branch, the primitive S0 witness can be read as an anchored
S0 carrier without unfolding the branch definition.
-/
theorem exists_anchoredS0Carrier_of_boundaryD3Reduced
    {c b : ℕ} (hbc : b < c) (hb : 0 < b)
    (hcop : Nat.Coprime c b) (hred : BoundaryD3Reduced c b) :
    ∃ q : ℕ, AnchoredS0Carrier q c b q ∧ ¬ q ∣ c - b :=
  exists_anchoredS0Carrier_of_not_three_dvd_sub hbc hb hcop hred

end Petal
end DkMath

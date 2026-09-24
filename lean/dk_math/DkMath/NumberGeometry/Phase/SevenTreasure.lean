/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.Phase.TwoPrime
import Mathlib.Tactic

#print "file: DkMath.NumberGeometry.Phase.SevenTreasure"

/-!
# Seven / fourteen-phase calibration

This file is the pure `p = 7` specialization of the general signed phase
layer. It does not import the FLT/Seven carrier; that one-way calibration is
owned by a separate bridge module.
-/

namespace DkMath.NumberGeometry.Phase

open TwoPrimePhase

/-- A positive primitive fourteen-phase packet. -/
abbrev FourteenPhase
    (R : Type*) [CommRing R] [NoZeroDivisors R] :=
  TwoPrimePhase R 7

namespace FourteenPhase

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- The canonical complex fourteen-phase packet. -/
noncomputable def complexFourteenPhase : FourteenPhase ℂ :=
  complexTwoPrimePhase 7 (by norm_num)

/-- The canonical complex fourteen-phase completes its full turn. -/
theorem complexFourteenPhase_fullTurn :
    complexFourteenPhase.eta ^ 14 = 1 := by
  exact complexFourteenPhase.fullTurn

/-- The canonical complex fourteen-phase reaches the half-turn. -/
theorem complexFourteenPhase_halfTurn :
    complexFourteenPhase.eta ^ 7 = -1 := by
  exact complexFourteenPhase.halfTurn


/-- The seven even phases as a finite sector. -/
noncomputable def evenSector (P : FourteenPhase R) : Finset R := by
  classical
  exact Finset.univ.image P.evenPhaseFin

/-- The seven odd phases as a finite sector. -/
noncomputable def oddSector (P : FourteenPhase R) : Finset R := by
  classical
  exact Finset.univ.image P.oddPhaseFin

/-- The even sector has exactly seven elements. -/
theorem evenSector_card (P : FourteenPhase R) : P.evenSector.card = 7 := by
  classical
  rw [evenSector, Finset.card_image_of_injective]
  · simp
  · exact P.evenPhaseFin_injective

/-- The odd sector has exactly seven elements. -/
theorem oddSector_card (P : FourteenPhase R) : P.oddSector.card = 7 := by
  classical
  rw [oddSector, Finset.card_image_of_injective]
  · simp
  · exact P.oddPhaseFin_injective

/-- The even and odd sectors are disjoint. -/
theorem evenSector_disjoint_oddSector (P : FourteenPhase R) :
    Disjoint P.evenSector P.oddSector := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hy
  rcases Finset.mem_image.mp hx with ⟨i, -, hi⟩
  rcases Finset.mem_image.mp hy with ⟨j, -, hj⟩
  exact P.evenPhaseFin_ne_oddPhaseFin i j (hi.trans hj.symm)

/-- The complete fourteen-phase sector is the union of the even and odd sectors. -/
noncomputable def sector (P : FourteenPhase R) : Finset R := by
  classical
  exact P.evenSector ∪ P.oddSector

/-- The complete sector has exactly fourteen elements, namely seven plus seven. -/
theorem sector_card (P : FourteenPhase R) : P.sector.card = 14 := by
  classical
  rw [sector, Finset.card_union_of_disjoint P.evenSector_disjoint_oddSector,
    P.evenSector_card, P.oddSector_card]

/-- An even phase multiple satisfies the seventh-power difference equation. -/
theorem even_seventh_equation (P : FourteenPhase R) (j : ℕ) (Y : R) :
    (P.evenPhase j * Y) ^ 7 - Y ^ 7 = 0 :=
  P.even_signed_equation j Y

/-- An odd phase multiple satisfies the seventh-power sum equation. -/
theorem odd_seventh_equation (P : FourteenPhase R) (j : ℕ) (Y : R) :
    (P.oddPhase j * Y) ^ 7 + Y ^ 7 = 0 :=
  P.odd_signed_equation j Y

/-- The squared generator of a fourteen-phase packet is primitive of order seven. -/
theorem zeta_isPrimitiveRoot_seven (P : FourteenPhase R) :
    IsPrimitiveRoot P.zeta 7 :=
  P.zeta_isPrimitiveRoot (by norm_num)

end FourteenPhase

end DkMath.NumberGeometry.Phase

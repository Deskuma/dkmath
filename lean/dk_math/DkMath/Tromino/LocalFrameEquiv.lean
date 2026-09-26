/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Tromino.FourColorCell
import DkMath.Tromino.BoundarySignature

namespace DkMath.Tromino

open DkMath.Polyomino
open DkMath.Polyomino.Tromino

/-! A finite 3+1 frame over the additive V4 carrier. -/

structure TrominoExchangeFrame where
  Panel : Type
  instFintype : Fintype Panel
  instDecidableEq : DecidableEq Panel
  colorEquiv : Panel ≃ TrominoState
  gap : Panel

instance (F : TrominoExchangeFrame) : Fintype F.Panel := F.instFintype
instance (F : TrominoExchangeFrame) : DecidableEq F.Panel := F.instDecidableEq

def frameColor (F : TrominoExchangeFrame) (p : F.Panel) : TrominoState :=
  F.colorEquiv p

def frameBody (F : TrominoExchangeFrame) : Finset F.Panel :=
  Finset.univ.erase F.gap

def frameDelta (F : TrominoExchangeFrame) (p : F.Panel) : TrominoState :=
  frameColor F F.gap + frameColor F p

theorem frame_panel_card (F : TrominoExchangeFrame) :
    Fintype.card F.Panel = 4 := by
  calc
    Fintype.card F.Panel = Fintype.card TrominoState :=
      Fintype.card_congr F.colorEquiv
    _ = Nat.card TrominoState := Fintype.card_eq_nat_card
    _ = 4 := card_state

theorem frame_body_card (F : TrominoExchangeFrame) :
    (frameBody F).card = 3 := by
  rw [frameBody, Finset.card_erase_of_mem (Finset.mem_univ F.gap)]
  simp [frame_panel_card F]

theorem frame_gap_not_mem_body (F : TrominoExchangeFrame) :
    F.gap ∉ frameBody F := by
  simp [frameBody]

theorem frame_delta_eq_zero_iff (F : TrominoExchangeFrame) (p : F.Panel) :
    frameDelta F p = 0 ↔ p = F.gap := by
  constructor
  · intro h
    apply F.colorEquiv.injective
    apply add_left_cancel (a := frameColor F F.gap)
    calc
      frameColor F F.gap + frameColor F p = 0 := h
      _ = frameColor F F.gap + frameColor F F.gap :=
        (state_add_self (frameColor F F.gap)).symm
  · intro h
    subst p
    exact state_add_self _

theorem frame_mem_body_iff_delta_ne_zero (F : TrominoExchangeFrame)
    (p : F.Panel) :
    p ∈ frameBody F ↔ frameDelta F p ≠ 0 := by
  rw [frameBody, Finset.mem_erase]
  simp [frame_delta_eq_zero_iff F p]

theorem frame_delta_image_body (F : TrominoExchangeFrame) :
    (frameBody F).image (frameDelta F) =
      Finset.filter (fun x : TrominoState => x ≠ 0) Finset.univ := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (frame_mem_body_iff_delta_ne_zero F p).1 hp⟩
  · intro hx
    have hx0 : x ≠ 0 := (Finset.mem_filter.mp hx).2
    let p : F.Panel := F.colorEquiv.symm (frameColor F F.gap + x)
    have hpdelta : frameDelta F p = x := by
      simp only [frameDelta, frameColor, p, Equiv.apply_symm_apply]
      rw [← add_assoc, state_add_self, zero_add]
    refine Finset.mem_image.mpr ⟨p, ?_, hpdelta⟩
    exact (frame_mem_body_iff_delta_ne_zero F p).2 (by simpa [hpdelta] using hx0)

theorem frame_delta_body_is_nonzero (F : TrominoExchangeFrame)
    {p : F.Panel} (hp : p ∈ frameBody F) :
    frameDelta F p = deltaA ∨ frameDelta F p = deltaB ∨
      frameDelta F p = deltaC := by
  exact nonzeroState_eq_deltaA_or_deltaB_or_deltaC _
    ((frame_mem_body_iff_delta_ne_zero F p).1 hp)

structure TrominoExchangeFrameEquiv (G E : TrominoExchangeFrame) where
  panelEquiv : G.Panel ≃ E.Panel
  map_gap : panelEquiv G.gap = E.gap
  map_delta : ∀ p, frameDelta E (panelEquiv p) = frameDelta G p

theorem frame_equiv_mem_body_iff (φ : TrominoExchangeFrameEquiv G E)
    (p : G.Panel) :
    φ.panelEquiv p ∈ frameBody E ↔ p ∈ frameBody G := by
  rw [frame_mem_body_iff_delta_ne_zero E, frame_mem_body_iff_delta_ne_zero G]
  rw [φ.map_delta]

theorem frame_equiv_delta_classification (φ : TrominoExchangeFrameEquiv G E)
    {p : G.Panel} (hp : p ∈ frameBody G) :
    frameDelta E (φ.panelEquiv p) = deltaA ∨
      frameDelta E (φ.panelEquiv p) = deltaB ∨
      frameDelta E (φ.panelEquiv p) = deltaC := by
  rw [φ.map_delta]
  exact frame_delta_body_is_nonzero G hp

def localExchange (F : TrominoExchangeFrame) (p : F.Panel)
    (x : TrominoState) : TrominoState :=
  exchange (frameDelta F p) x

theorem localExchange_conjugate (φ : TrominoExchangeFrameEquiv G E)
    (p : G.Panel) (x : TrominoState) :
    localExchange E (φ.panelEquiv p) x = localExchange G p x := by
  simp [localExchange, φ.map_delta]

abbrev GaussianPanel := {c : Cell // c ∈ block2}

def gaussianGap : GaussianPanel :=
  ⟨(1, 1), by simp [block2]⟩

def gaussianPanel00 : GaussianPanel :=
  ⟨(0, 0), by simp [block2]⟩
def gaussianPanel10 : GaussianPanel :=
  ⟨(1, 0), by simp [block2]⟩
def gaussianPanel01 : GaussianPanel :=
  ⟨(0, 1), by simp [block2]⟩

def gaussianColorInv (s : TrominoState) : GaussianPanel :=
  if s = 0 then gaussianPanel00 else
    if s = deltaA then gaussianPanel10 else
      if s = deltaB then gaussianPanel01 else gaussianGap

def gaussianColorEquiv : GaussianPanel ≃ TrominoState where
  toFun := fun c => atomicColor c.1
  invFun := gaussianColorInv
  left_inv := by
    intro c
    fin_cases c <;> decide
  right_inv := by
    intro s
    fin_cases s <;> decide

def gaussianExchangeFrame : TrominoExchangeFrame where
  Panel := GaussianPanel
  instFintype := inferInstance
  instDecidableEq := inferInstance
  colorEquiv := gaussianColorEquiv
  gap := gaussianGap

theorem gaussian_gap_eq_11 : gaussianGap.1 = (1, 1) := rfl

theorem gaussian_color_00 : frameColor gaussianExchangeFrame gaussianPanel00 = 0 := by
  decide

theorem gaussian_color_10 :
    frameColor gaussianExchangeFrame gaussianPanel10 = deltaA := by
  decide

theorem gaussian_color_01 :
    frameColor gaussianExchangeFrame gaussianPanel01 = deltaB := by
  decide

theorem gaussian_color_gap :
    frameColor gaussianExchangeFrame gaussianExchangeFrame.gap = deltaC := by
  decide

theorem gaussian_delta_00 :
    frameDelta gaussianExchangeFrame gaussianPanel00 = deltaC := by
  decide

theorem gaussian_delta_10 :
    frameDelta gaussianExchangeFrame gaussianPanel10 = deltaB := by
  decide

theorem gaussian_delta_01 :
    frameDelta gaussianExchangeFrame gaussianPanel01 = deltaA := by
  decide

abbrev eisensteinPanel := TrominoState

abbrev eisensteinExchangeFrame : TrominoExchangeFrame :=
  {
  Panel := eisensteinPanel
  instFintype := inferInstance
  instDecidableEq := inferInstance
  colorEquiv := Equiv.refl TrominoState
  gap := (0 : eisensteinPanel)
}

theorem eisenstein_gap_eq_zero : eisensteinExchangeFrame.gap = (0 : eisensteinPanel) := rfl

theorem eisenstein_delta (p : eisensteinPanel) :
    frameDelta eisensteinExchangeFrame p = p := by
  change (0 : TrominoState) + p = p
  simp

theorem eisenstein_body_iff (p : eisensteinPanel) :
    p ∈ frameBody eisensteinExchangeFrame ↔ p ≠ (0 : eisensteinPanel) := by
  rw [frame_mem_body_iff_delta_ne_zero]
  rw [eisenstein_delta]

def stateTranslateEquiv (a : TrominoState) : TrominoState ≃ TrominoState where
  toFun := fun x => a + x
  invFun := fun x => a + x
  left_inv := by
    intro x
    calc
      a + (a + x) = (a + a) + x := by rw [add_assoc]
      _ = x := by rw [state_add_self, zero_add]
  right_inv := by
    intro x
    calc
      a + (a + x) = (a + a) + x := by rw [add_assoc]
      _ = x := by rw [state_add_self, zero_add]

def gaussianEisensteinPanelEquiv :
    gaussianExchangeFrame.Panel ≃ eisensteinExchangeFrame.Panel :=
  gaussianExchangeFrame.colorEquiv.trans
    (stateTranslateEquiv (frameColor gaussianExchangeFrame gaussianExchangeFrame.gap))

theorem gaussianEisensteinPanelEquiv_apply (p : gaussianExchangeFrame.Panel) :
    gaussianEisensteinPanelEquiv p = frameDelta gaussianExchangeFrame p := rfl

def gaussianEisensteinFrameEquiv :
    TrominoExchangeFrameEquiv gaussianExchangeFrame eisensteinExchangeFrame where
  panelEquiv := gaussianEisensteinPanelEquiv
  map_gap := by
    change gaussianEisensteinPanelEquiv gaussianExchangeFrame.gap =
      (0 : TrominoState)
    rw [gaussianEisensteinPanelEquiv_apply]
    exact (frame_delta_eq_zero_iff gaussianExchangeFrame _).2 rfl
  map_delta := by
    intro p
    rw [eisenstein_delta, gaussianEisensteinPanelEquiv_apply]

theorem gaussianEisensteinFrameEquiv_maps_gap :
    gaussianEisensteinFrameEquiv.panelEquiv gaussianExchangeFrame.gap =
      eisensteinExchangeFrame.gap :=
  gaussianEisensteinFrameEquiv.map_gap

theorem gaussianEisensteinFrameEquiv_maps_delta (p : gaussianExchangeFrame.Panel) :
    frameDelta eisensteinExchangeFrame
        (gaussianEisensteinFrameEquiv.panelEquiv p) =
      frameDelta gaussianExchangeFrame p :=
  gaussianEisensteinFrameEquiv.map_delta p

end DkMath.Tromino

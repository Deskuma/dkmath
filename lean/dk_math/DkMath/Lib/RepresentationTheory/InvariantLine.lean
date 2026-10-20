/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.EllipticTorsionGaloisStable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

#print "file: DkMath.Lib.RepresentationTheory.InvariantLine"

/-!
# 二次元表現の既約性と、安定直線の不存在

二次元空間の真の非零部分空間は一次元に限られる。従って既存のIsIrreducibleを
「群作用が保存する一次元部分空間がない」という条件へ翻訳できる。
非零性は次元2から供給し、零表現を既約と呼ぶことはしない。
これは判定条件の同値であり、特定の表現で安定直線が存在しないことの証明ではない。
-/
namespace DkMath.Lib.RepresentationTheory
open Module
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- 二次元の真の非零部分空間はちょうど一次元である。 -/
theorem proper_nonzero_iff_finrank_one (hd : Module.finrank k V = 2) (N : Submodule k V) :
    (N ≠ ⊥ ∧ N ≠ ⊤) ↔ Module.finrank k N = 1 := by
  constructor
  · intro hN
    have hpos : Module.finrank k N ≠ 0 := fun h => hN.1 (Submodule.finrank_eq_zero.mp h)
    have hlt := Submodule.finrank_lt hN.2
    rw [hd] at hlt
    omega
  · intro hN
    constructor
    · intro hb
      rw [hb, finrank_bot] at hN
      omega
    · intro ht
      rw [ht, finrank_top, hd] at hN
      omega

/-- 二次元表現の既約性は、安定な一次元部分空間の不存在と同値である。 -/
theorem isIrreducible_iff_no_stable_line (ρ : Representation k G V) (hd : Module.finrank k V = 2) :
    IsIrreducible ρ ↔ ¬ ∃ L : Submodule k V, Module.finrank k L = 1 ∧ IsStable ρ L := by
  constructor
  · rintro h ⟨L, hdim, hstable⟩
    have hp := (proper_nonzero_iff_finrank_one hd L).mpr hdim
    rcases h.2 L hstable with hb | ht
    · exact hp.1 hb
    · exact hp.2 ht
  · intro h
    have hn : Nontrivial V := Module.finrank_pos_iff.mp (by rw [hd]; decide)
    refine ⟨hn, fun L hstable => ?_⟩
    by_contra hL
    push Not at hL
    exact h ⟨L, (proper_nonzero_iff_finrank_one hd L).mp hL, hstable⟩

end DkMath.Lib.RepresentationTheory

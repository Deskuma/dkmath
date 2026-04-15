/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberTheory.UniqueFactorizationGN

#print "file: DkMath.Samples.UniqueFactorizationGNFacade"

open DkMath.NumberTheory

/--
最終推奨入口
`unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK`
の最小呼び出し形（入力をそのまま受ける版）。
-/
example {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcMVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q m = padicValNat q (boundaryProd x u))
    (hExcKVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q n = padicValNat q (kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcMVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q m = padicValNat q (boundaryProd x u))
    (hNonExcKVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q n = padicValNat q (kernelRight d x u))
    (hNonExcBridge : NonExceptionalBridgeEntrance d x u)
    (hNonExcBoundary : NonExceptionalBoundaryEntrance d x u) :
    m = n := by
  exact
    unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hm hn hd2 hx hu
      hExcMVal hExcKVal hExcVal
      hNonExcMVal hNonExcKVal hNonExcBridge
      hNonExcBoundary

/--
`hNonExcVal` と `hNonExcNotDvdBoundaryProd` から
facade 入口を組み立てて最終推奨入口へ接続する最小例。
-/
example {d x u m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0)
    (hd2 : 2 ≤ d) (hx : 0 < x) (hu : 0 < u)
    (hExcMVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q m = padicValNat q (boundaryProd x u))
    (hExcKVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q n = padicValNat q (kernelRight d x u))
    (hExcVal : ∀ q : ℕ, Nat.Prime q → q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcMVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q m = padicValNat q (boundaryProd x u))
    (hNonExcKVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q n = padicValNat q (kernelRight d x u))
    (hNonExcVal : ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d →
      padicValNat q (boundaryProd x u) = padicValNat q (kernelRight d x u))
    (hNonExcNotDvdBoundaryProd :
      ∀ q : ℕ, Nat.Prime q → ¬ q ∣ d → ¬ q ∣ boundaryProd x u) :
    m = n := by
  have hNonExcBridge : NonExceptionalBridgeEntrance d x u :=
    nonExceptionalBridgeEntrance_of_nonExcVal
      (d := d) (x := x) (u := u) hNonExcVal
  have hNonExcBoundary : NonExceptionalBoundaryEntrance d x u :=
    nonExceptionalBoundaryEntrance_of_not_dvd_boundaryProd
      (d := d) (x := x) (u := u) hNonExcNotDvdBoundaryProd
  exact
    unique_factorization_nat_e2e_autoGNVal_nonExcFacade_boundaryFacade_autoExcNonExcMK
      (d := d) (x := x) (u := u) (m := m) (n := n)
      hm hn hd2 hx hu
      hExcMVal hExcKVal hExcVal
      hNonExcMVal hNonExcKVal hNonExcBridge
      hNonExcBoundary

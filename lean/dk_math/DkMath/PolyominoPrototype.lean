/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import Mathlib

namespace DkMath
namespace Polyomino

/-
※以下の記述での形式化だと、面積しか語らないので
  Cell や PolyominoType の定義は不要。
  これらの定義は Tromino.lean に移動した。
-/

-- Number Name of squares in various polyominoes

def mono : ℕ := 1
def bino : ℕ := 2
def trio : ℕ := 3
def tetro : ℕ := 4
def penta : ℕ := 5
def hexa : ℕ := 6
def hepta : ℕ := 7
def octo : ℕ := 8
def nano : ℕ := 9
def deca : ℕ := 10
def undeca : ℕ := 11
def dodeca : ℕ := 12
def trideca : ℕ := 13
def tetradeca : ℕ := 14  -- quaddecagon
def pentadeca : ℕ := 15  -- quindecagon


-- Polyomino counting functions

-- 1-5
def monomino (n : ℕ) : ℕ := n * mono
def domino (n : ℕ) : ℕ := n * (monomino bino)
def triomino (n : ℕ) : ℕ := n * (monomino trio)
def tetromino (n : ℕ) : ℕ := n * (monomino tetro)
def pentomino (n : ℕ) : ℕ := n * (monomino penta)
-- 6-10
def hexomino (n : ℕ) : ℕ := n * (monomino hexa)
def heptomino (n : ℕ) : ℕ := n * (monomino hepta)
def octomino (n : ℕ) : ℕ := n * (monomino octo)
def nanomino (n : ℕ) : ℕ := n * (monomino nano)
def decomino (n : ℕ) : ℕ := n * (monomino deca)
-- 11-15
def undecomino (n : ℕ) : ℕ := n * (monomino undeca)
def dodecomino (n : ℕ) : ℕ := n * (monomino dodeca)
def tridecomino (n : ℕ) : ℕ := n * (monomino trideca)
def tetradecomino (n : ℕ) : ℕ := n * (monomino tetradeca)
def pentadecomino (n : ℕ) : ℕ := n * (monomino pentadeca)
-- General n-omino
def general_omino (n : ℕ) (k : ℕ) : ℕ := n * (monomino k)

-- Polyomino counting lemmas

lemma domino_eq_two_monomino (n : ℕ) : domino n = n * monomino bino := by
  simp [domino, monomino]

lemma triomino_eq_three_monomino (n : ℕ) : triomino n = n * monomino trio := by
  simp [triomino, monomino]

lemma tetromino_eq_four_monomino (n : ℕ) : tetromino n = n * monomino tetro := by
  simp [tetromino, monomino]

-- omino area functions

def omino_area (x : ℕ) (y : ℕ) : ℕ :=
  x * y

def omino_square (n : ℕ) : ℕ :=
  omino_area n n

lemma omino_area_eq (n k : ℕ) : omino_area n k = n * k := by
  simp [omino_area]

lemma omino_square_eq (n : ℕ) : omino_square n = n * n := by
  simp [omino_square, omino_area]

lemma omino_square_eq_area (n : ℕ) : omino_square n = omino_area n n := by
  simp [omino_square, omino_area]

-- Tromino L shape and space square area
def L_tromino_area : ℕ := triomino 1 + monomino 1

lemma L_tromino_area_eq_four : L_tromino_area = 2 * 2 := by
  simp [L_tromino_area, triomino, monomino, mono, trio]

lemma omino_square_four_eq_L_tromino_area : omino_square 2 = L_tromino_area := by
  simp [omino_square, L_tromino_area, triomino, monomino, mono, trio, omino_area]


end Polyomino
end DkMath

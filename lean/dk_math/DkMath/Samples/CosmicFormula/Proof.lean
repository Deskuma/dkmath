/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Samples.CosmicFormula.Defs

/-! # 宇宙式 Cosmic Formula
恒等式 $N+1=(P+1)^2$ の証明
-/

namespace DkMath.Sample
namespace CosmicFormula

/--
宇宙式の恒等式の証明
N + 1 = (P + 1)^2
-/
theorem CosmicFormulaN
  (x : ℕ) :
  N x + 1 = (P x + 1) ^ 2 := by
    unfold P N
    -- ⊢ P x * (P x + 2) + 1 = (x + 1) ^ 2
    unfold P
    -- ⊢ x * (x + 2) + 1 = (x + 1) ^ 2
    ring

/--
宇宙式の相殺ゼロの証明
(P + 1)^2 - (N + 1) = 0
-/
theorem CosmicFormulaN_eq_zero (x : ℕ) :
    (P x + 1) ^ 2 - (N x + 1) = 0 := by
  rw [← CosmicFormulaN x]  -- ⊢ N x + 1 - (N x + 1) = 0
  exact Eq.symm (Nat.eq_sub_of_add_eq' rfl)
  -- Nat.eq_sub_of_add_eq' {a b c : ℕ} (h : b + c = a) : c = a - b

/--
宇宙式の単位残差の証明
(P + 1)^2 - N = 1
-/
theorem CosmicFormulaN_eq_one (x : ℕ) :
    (P x + 1) ^ 2 - N x = 1 := by
  rw [← CosmicFormulaN x]  -- ⊢ N x + 1 - N x = 1
  exact Nat.add_sub_self_left (N x) 1
  -- Nat.add_sub_self_left (a b : ℕ) : a + b - a = b

/--
N = N' = x(x+2) = (x^2)+(x*2)
-/
theorem N_eq_N' (x : ℕ) :
    N x = N' x := by
  unfold N N'
  unfold P
  ring

/-
N=(P+1)^2-1
N=(y+1)(y-1)=y(y+1)-(y+1)=y^2+y-y-1=y^2-1
y=(P+1)
-/

theorem CosmicFormulaN_sub_one
  (x : ℕ) :
  N x = (P x + 1) ^ 2 - 1 := by
  rw [← CosmicFormulaN x]
  exact Nat.add_sub_cancel (N x) 1

--  ---------------------------------------------------------------------------

theorem CosmicFormulaN_eq_zero'
  (x : ℕ) :
  (P x + 1) ^ 2 - (N x + 1) = 0 := by
    unfold P N
    unfold P
    refine Eq.symm (Nat.eq_sub_of_add_eq ?_)
    ring

theorem CosmicFormulaN_eq_one'
  (x : ℕ) :
  (P x + 1) ^ 2 - N x = 1 := by
    unfold P N
    unfold P
    refine Eq.symm (Nat.eq_sub_of_add_eq ?_)
    ring

#check CosmicFormulaN
-- DkMath.CosmicFormula.CosmicFormulaN (x : ℕ) : N x + 1 = (P x + 1) ^ 2
#print axioms CosmicFormulaN
-- 'DkMath.CosmicFormula.CosmicFormulaN' depends on axioms: [propext]

-- 整数
theorem NZ_eq_NZ' (x : ℤ) :
    NZ x = NZ' x := by
  unfold NZ NZ'
  unfold PZ
  ring

/--
宇宙式の恒等式の証明（整数版）
NZ + 1 = (PZ + 1)^2
-/
theorem CosmicFormulaZ
  (x : ℤ) :
  NZ x + 1 = (PZ x + 1) ^ 2 := by
    unfold PZ NZ
    -- ⊢ PZ x * (PZ x + 2) + 1 = (x + 1) ^ 2
    unfold PZ
    -- ⊢ x * (x + 2) + 1 = (x + 1) ^ 2
    ring

/--
宇宙式の恒等式の自然数版と整数版の同値証明（引数が自然数）
N + 1 = (P + 1)^2 ↔ NZ + 1 = (PZ + 1)^2
-/
theorem CosmicFormulaN_iff_Z
  (x : ℕ) :
  N x + 1 = (P x + 1) ^ 2 ↔ NZ x + 1 = (PZ x + 1) ^ 2 := by
    unfold P N PZ NZ
    -- ⊢ P x * (P x + 2) + 1 = (x + 1) ^ 2 ↔ PZ ↑x * (PZ ↑x + 2) + 1 = (↑x + 1) ^ 2
    unfold P PZ
    -- ⊢ x * (x + 2) + 1 = (x + 1) ^ 2 ↔ ↑x * (↑x + 2) + 1 = (↑x + 1) ^ 2
    ring_nf

-- 複素数
theorem NC_eq_NC' (s : ℂ) :
    NC s = NC' s := by
  unfold NC NC'
  unfold PC
  ring

-- 実数
theorem NR_eq_NR' (x : ℝ) :
    NR x = NR' x := by
  unfold NR NR'
  unfold PR
  ring


end CosmicFormula
end DkMath.Sample

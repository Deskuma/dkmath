/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeGrid

#print "file: DkMath.FLT.Seven.GTailEisensteinCyclotomicPrimeJoin"

/-!
# Joint generation of the twelve q43 prime addresses

The explicit quadratic split proves the sum of the two source extensions is
exactly the selected kernel. Bounded source powers give one-way lower bounds
for mixed products, without identifying individual extensions or exact depths.
-/

namespace DkMath.FLT.Seven.GTailPrimeJoin

open DkMath.NumberTheory.TraceOneQuadratic DkMath.Lib.NumberTheory
open GTailCommonReceiver GTailPrimeGrid

local instance : Fact (Nat.Prime 43) := ⟨by decide⟩

/-- The coefficient remainder after choosing an integer lift of the row root. -/
def rowRemainder (e : Fin 2) (x : Carrier) : SevenCyclotomicDegreeSixInt.Ring :=
  x.re + (eisenstein43Root e).val * x.im

/-- The source quadratic generator minus the chosen natural representative. -/
def rowDifference (e : Fin 2) : TraceOneInt (-1) := tau (-1) - (eisenstein43Root e).val

/-- Every receiver element splits into two separately typed source contributions. -/
theorem coordinate_decomposition (e : Fin 2) (x : Carrier) :
    x = fromCyclotomic (rowRemainder e x) +
      fromEisenstein (rowDifference e) * fromCyclotomic x.im := by
  have hd : fromEisenstein (rowDifference e) =
      (QuadraticAlgebra.omega : Carrier) - ((eisenstein43Root e).val : Carrier) := by
    unfold rowDifference
    rw [map_sub, map_natCast, fromEisenstein_tau]
  rw [hd]
  apply QuadraticAlgebra.ext <;>
    simp only [rowRemainder, fromCyclotomic, QuadraticAlgebra.algebraMap_eq,
      QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast] <;> ring

/-- The row difference belongs to the actual Eisenstein source kernel. -/
theorem rowDifference_mem (e : Fin 2) :
    rowDifference e ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) := by
  change eisensteinResidueRingHom (eisenstein43Root e) (eisenstein43Root_relation e) _ = 0
  simp [rowDifference, map_sub, eisensteinResidueRingHom_tau]

/-- Kernel membership makes the coefficient remainder lie in the column source kernel. -/
theorem rowRemainder_mem (e : Fin 2) (j : Fin 6) (x : Carrier) (hx : x ∈ M e j) :
    rowRemainder e x ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j := by
  change evR43 j (rowRemainder e x) = 0
  change evR43 j x.re + eisenstein43Root e * evR43 j x.im = 0 at hx
  simpa [rowRemainder] using hx

/-- Extension of the row source prime, independent of the column. -/
def A (e : Fin 2) : Ideal Carrier :=
  Ideal.map fromEisenstein
    (eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e))

/-- Extension of the column source prime, independent of the row. -/
def B (j : Fin 6) : Ideal Carrier :=
  Ideal.map fromCyclotomic
    (sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j)

/-- Both separately extended source primes lie in the grid kernel. -/
theorem sup_le_M (e : Fin 2) (j : Fin 6) : A e ⊔ B j ≤ M e j :=
  sup_le (map_eisenstein_le e j) (map_cyclotomic_le e j)

/-- The coordinate split puts every kernel element in the joint source extension. -/
theorem M_le_sup (e : Fin 2) (j : Fin 6) : M e j ≤ A e ⊔ B j := by
  intro x hx
  have hy : fromCyclotomic (rowRemainder e x) ∈ B j :=
    Ideal.mem_map_of_mem fromCyclotomic (rowRemainder_mem e j x hx)
  have hd : fromEisenstein (rowDifference e) ∈ A e :=
    Ideal.mem_map_of_mem fromEisenstein (rowDifference_mem e)
  rw [coordinate_decomposition e x]
  exact (A e ⊔ B j).add_mem ((show B j ≤ A e ⊔ B j from le_sup_right) hy)
    ((show A e ≤ A e ⊔ B j from le_sup_left)
      ((A e).mul_mem_right (fromCyclotomic x.im) hd))

/-- Each of the twelve prime kernels is generated jointly by its two source primes. -/
theorem M_eq_map_eisenstein_sup_map_cyclotomic (e : Fin 2) (j : Fin 6) :
    M e j = A e ⊔ B j := le_antisymm (M_le_sup e j) (sup_le_M e j)

/-- The joint extension at the first address is the unchanged Step034 kernel. -/
theorem M43_eq_sup : M43 = A 0 ⊔ B 0 := by
  rw [← M_zero_zero, M_eq_map_eisenstein_sup_map_cyclotomic]

/-- Source powers zero through two map to powers of the row extension. -/
theorem eisenstein_mem_A_pow (e : Fin 2) (n : Fin 3) (z : TraceOneInt (-1))
    (hz : z ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) ^ n.val) :
    fromEisenstein z ∈ A e ^ n.val := by
  rw [A, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem fromEisenstein hz

/-- Bounded row-source power support gives a lower bound in the common kernel. -/
theorem eisenstein_mem_M_pow (e : Fin 2) (j : Fin 6) (n : Fin 3) (z : TraceOneInt (-1))
    (hz : z ∈ eisensteinResidueIdeal (eisenstein43Root e) (eisenstein43Root_relation e) ^ n.val) :
    fromEisenstein z ∈ M e j ^ n.val :=
  (show A e ^ n.val ≤ M e j ^ n.val from pow_le_pow_left' (map_eisenstein_le e j) n.val)
    (eisenstein_mem_A_pow e n z hz)

/-- Source powers zero through two map to powers of the column extension. -/
theorem cyclotomic_mem_B_pow (j : Fin 6) (n : Fin 3) (u : SevenCyclotomicDegreeSixInt.Ring)
    (hu : u ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j ^ n.val) :
    fromCyclotomic u ∈ B j ^ n.val := by
  rw [B, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem fromCyclotomic hu

/-- Bounded column-source power support gives a lower bound in the common kernel. -/
theorem cyclotomic_mem_M_pow (e : Fin 2) (j : Fin 6) (n : Fin 3)
    (u : SevenCyclotomicDegreeSixInt.Ring)
    (hu : u ∈ sixRootKernel (11 : ZMod 43) (by decide) (by decide) (by decide) j ^ n.val) :
    fromCyclotomic u ∈ M e j ^ n.val :=
  (show B j ^ n.val ≤ M e j ^ n.val from pow_le_pow_left' (map_cyclotomic_le e j) n.val)
    (cyclotomic_mem_B_pow j n u hu)

end DkMath.FLT.Seven.GTailPrimeJoin

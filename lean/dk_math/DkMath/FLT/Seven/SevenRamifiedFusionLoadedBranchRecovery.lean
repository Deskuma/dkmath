/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Seven.SevenRamifiedFusionRealPairLoadAllocation

#print "file: DkMath.FLT.Seven.SevenRamifiedFusionLoadedBranchRecovery"

namespace DkMath.FLT.Seven

noncomputable section

set_option linter.style.longLine false

namespace RamifiedSignedRootRoutingPacket

open SevenRealCubicInt

local instance branchRecoveryGCDMonoid :
    GCDMonoid SevenRealCubicInt :=
  IsBezout.toGCDDomain SevenRealCubicInt

/-- Projections of the first scalar cell into distinct pair cores remain
coprime. -/
theorem realPairLoad21_pairwiseCoprime
    (p : RamifiedSignedRootRoutingPacket) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (p.realPairLoad21 i)
          (p.realPairLoad21 j)) := by
  intro i j hij
  exact
    (p.signedDepth.realPairCores_pairwiseCoprime hij).mono
      (GCDMonoid.gcd_dvd_right _ _)
      (GCDMonoid.gcd_dvd_right _ _)

/-- Projections of the second scalar cell into distinct pair cores remain
coprime. -/
theorem realPairLoad22_pairwiseCoprime
    (p : RamifiedSignedRootRoutingPacket) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (p.realPairLoad22 i)
          (p.realPairLoad22 j)) := by
  intro i j hij
  exact
    (p.signedDepth.realPairCores_pairwiseCoprime hij).mono
      (GCDMonoid.gcd_dvd_right _ _)
      (GCDMonoid.gcd_dvd_right _ _)

private theorem exists_three_associated_seventh_roots
    (load : Fin 3 → SevenRealCubicInt)
    (hcop :
      Pairwise
        (fun i j : Fin 3 =>
          IsCoprime (load i) (load j)))
    (t : SevenRealCubicInt)
    (hproduct :
      Associated (t ^ 7)
        (load 0 * (load 1 * load 2))) :
    ∃ roots : Fin 3 → SevenRealCubicInt,
      ∀ i, Associated (roots i ^ 7) (load i) := by
  have h01 : IsCoprime (load 0) (load 1) :=
    hcop (by decide)
  have h02 : IsCoprime (load 0) (load 2) :=
    hcop (by decide)
  have h12 : IsCoprime (load 1) (load 2) :=
    hcop (by decide)
  rcases exists_associated_pow_of_associated_pow_mul
      (h01.mul_right h02) hproduct with
    ⟨root0, hroot0⟩
  have hproduct1 :
      Associated (t ^ 7)
        (load 1 * (load 0 * load 2)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct
  rcases exists_associated_pow_of_associated_pow_mul
      (h01.symm.mul_right h12) hproduct1 with
    ⟨root1, hroot1⟩
  have hproduct2 :
      Associated (t ^ 7)
        (load 2 * (load 0 * load 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hproduct
  rcases exists_associated_pow_of_associated_pow_mul
      (h02.symm.mul_right h12.symm) hproduct2 with
    ⟨root2, hroot2⟩
  let roots : Fin 3 → SevenRealCubicInt :=
    ![root0, root1, root2]
  refine ⟨roots, ?_⟩
  intro i
  fin_cases i
  · exact hroot0
  · exact hroot1
  · exact hroot2

/-- Explicit seventh-power absorption witnesses for both routed scalar
load families. -/
structure RealPairLoadPowerAbsorption
    (p : RamifiedSignedRootRoutingPacket) where
  load21Root : Fin 3 → SevenRealCubicInt
  load22Root : Fin 3 → SevenRealCubicInt
  load21Associated :
    ∀ i,
      Associated (load21Root i ^ 7)
        (p.realPairLoad21 i)
  load22Associated :
    ∀ i,
      Associated (load22Root i ^ 7)
        (p.realPairLoad22 i)

/-- If both unresolved row-two routing cells are seventh powers, their
canonical PID gcd allocations split individually as seventh powers in
all three pair cores. -/
theorem nonempty_realPairLoadPowerAbsorption_of_row2_cells
    (p : RamifiedSignedRootRoutingPacket)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    Nonempty (RealPairLoadPowerAbsorption p) := by
  rcases h21 with ⟨a, ha⟩
  rcases h22 with ⟨b, hb⟩
  have hscalar21 :
      p.row2Load21Scalar =
        (a : SevenRealCubicInt) ^ 7 := by
    simp [row2Load21Scalar, ha, Nat.cast_pow]
  have hscalar22 :
      p.row2Load22Scalar =
        (b : SevenRealCubicInt) ^ 7 := by
    simp [row2Load22Scalar, hb, Nat.cast_pow]
  have hproduct21 :
      Associated ((a : SevenRealCubicInt) ^ 7)
        (p.realPairLoad21 0 *
          (p.realPairLoad21 1 * p.realPairLoad21 2)) := by
    have h :=
      (Associated.of_eq hscalar21).symm.trans
        p.realPairLoad21_product_associated.symm
    simpa [mul_assoc] using h
  have hproduct22 :
      Associated ((b : SevenRealCubicInt) ^ 7)
        (p.realPairLoad22 0 *
          (p.realPairLoad22 1 * p.realPairLoad22 2)) := by
    have h :=
      (Associated.of_eq hscalar22).symm.trans
        p.realPairLoad22_product_associated.symm
    simpa [mul_assoc] using h
  rcases exists_three_associated_seventh_roots
      p.realPairLoad21 p.realPairLoad21_pairwiseCoprime
      (a : SevenRealCubicInt) hproduct21 with
    ⟨roots21, hroots21⟩
  rcases exists_three_associated_seventh_roots
      p.realPairLoad22 p.realPairLoad22_pairwiseCoprime
      (b : SevenRealCubicInt) hproduct22 with
    ⟨roots22, hroots22⟩
  exact ⟨⟨roots21, roots22, hroots21, hroots22⟩⟩

/-- Seventh-power absorption witnesses for the load fields of one loaded
split.  Indexing this companion by the loaded packet lets the subsequent
absorption theorem use those fields directly. -/
structure RealPairLoadedLoadPowerAbsorption
    (p : RamifiedSignedRootRoutingPacket)
    (loaded : RealPairLoadedPowerSplit p) where
  load21Root : Fin 3 → SevenRealCubicInt
  load22Root : Fin 3 → SevenRealCubicInt
  load21Associated :
    ∀ i,
      Associated (load21Root i ^ 7)
        (loaded.load21 i)
  load22Associated :
    ∀ i,
      Associated (load22Root i ^ 7)
        (loaded.load22 i)

private theorem RealPairLoadedPowerSplit.load21_dvd_core
    {p : RamifiedSignedRootRoutingPacket}
    (loaded : RealPairLoadedPowerSplit p) (i : Fin 3) :
    loaded.load21 i ∣ p.signedDepth.realPairCore i := by
  have hproduct :
      loaded.load21 i ∣
        loaded.load21 i * loaded.load22 i *
          loaded.residualRoot i ^ 7 := by
    refine ⟨loaded.load22 i * loaded.residualRoot i ^ 7, ?_⟩
    ring
  exact hproduct.trans (loaded.coreAssociated i).dvd

private theorem RealPairLoadedPowerSplit.load22_dvd_core
    {p : RamifiedSignedRootRoutingPacket}
    (loaded : RealPairLoadedPowerSplit p) (i : Fin 3) :
    loaded.load22 i ∣ p.signedDepth.realPairCore i := by
  have hproduct :
      loaded.load22 i ∣
        loaded.load21 i * loaded.load22 i *
          loaded.residualRoot i ^ 7 := by
    refine ⟨loaded.load21 i * loaded.residualRoot i ^ 7, ?_⟩
    ring
  exact hproduct.trans (loaded.coreAssociated i).dvd

private theorem RealPairLoadedPowerSplit.load21_pairwiseCoprime
    {p : RamifiedSignedRootRoutingPacket}
    (loaded : RealPairLoadedPowerSplit p) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (loaded.load21 i) (loaded.load21 j)) := by
  intro i j hij
  exact
    (p.signedDepth.realPairCores_pairwiseCoprime hij).mono
      (loaded.load21_dvd_core i)
      (loaded.load21_dvd_core j)

private theorem RealPairLoadedPowerSplit.load22_pairwiseCoprime
    {p : RamifiedSignedRootRoutingPacket}
    (loaded : RealPairLoadedPowerSplit p) :
    Pairwise
      (fun i j : Fin 3 =>
        IsCoprime (loaded.load22 i) (loaded.load22 j)) := by
  intro i j hij
  exact
    (p.signedDepth.realPairCores_pairwiseCoprime hij).mono
      (loaded.load22_dvd_core i)
      (loaded.load22_dvd_core j)

/-- Under the Branch-A cell hypotheses, even the abstract load fields of
any valid loaded split are individually seventh powers up to units. -/
theorem RealPairLoadedPowerSplit.nonempty_loadPowerAbsorption_of_row2_cells
    {p : RamifiedSignedRootRoutingPacket}
    (loaded : RealPairLoadedPowerSplit p)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    Nonempty (RealPairLoadedLoadPowerAbsorption p loaded) := by
  rcases h21 with ⟨a, ha⟩
  rcases h22 with ⟨b, hb⟩
  have hscalar21 :
      p.row2Load21Scalar =
        (a : SevenRealCubicInt) ^ 7 := by
    simp [row2Load21Scalar, ha, Nat.cast_pow]
  have hscalar22 :
      p.row2Load22Scalar =
        (b : SevenRealCubicInt) ^ 7 := by
    simp [row2Load22Scalar, hb, Nat.cast_pow]
  have hproduct21 :
      Associated ((a : SevenRealCubicInt) ^ 7)
        (loaded.load21 0 *
          (loaded.load21 1 * loaded.load21 2)) := by
    have h :=
      (Associated.of_eq hscalar21).symm.trans
        loaded.load21Product.symm
    simpa [mul_assoc] using h
  have hproduct22 :
      Associated ((b : SevenRealCubicInt) ^ 7)
        (loaded.load22 0 *
          (loaded.load22 1 * loaded.load22 2)) := by
    have h :=
      (Associated.of_eq hscalar22).symm.trans
        loaded.load22Product.symm
    simpa [mul_assoc] using h
  rcases exists_three_associated_seventh_roots
      loaded.load21 loaded.load21_pairwiseCoprime
      (a : SevenRealCubicInt) hproduct21 with
    ⟨roots21, hroots21⟩
  rcases exists_three_associated_seventh_roots
      loaded.load22 loaded.load22_pairwiseCoprime
      (b : SevenRealCubicInt) hproduct22 with
    ⟨roots22, hroots22⟩
  exact ⟨⟨roots21, roots22, hroots21, hroots22⟩⟩

/-- Loaded residual roots and absorbed load roots combine into seventh
roots for the original pair cores.  This is the explicit recovery of the
conditional Branch A conclusion through the unconditional loaded split. -/
def RealPairLoadedPowerSplit.absorb
    {p : RamifiedSignedRootRoutingPacket}
    (loaded : RealPairLoadedPowerSplit p)
    (loads : RealPairLoadedLoadPowerAbsorption p loaded) :
    RamifiedSignedRootDepthPacket.RealPairCoreAssociatedPowerSplit
      p.signedDepth := by
  let root : Fin 3 → SevenRealCubicInt :=
    fun i =>
      loads.load21Root i * loads.load22Root i *
        loaded.residualRoot i
  have hassociated :
      ∀ i,
        Associated (root i ^ 7)
          (p.signedDepth.realPairCore i) := by
    intro i
    have hpowers :
        Associated
          (loads.load21Root i ^ 7 *
            loads.load22Root i ^ 7 *
            loaded.residualRoot i ^ 7)
          (loaded.load21 i * loaded.load22 i *
            loaded.residualRoot i ^ 7) :=
      (loads.load21Associated i).mul_mul
        (loads.load22Associated i) |>.mul_mul Associated.rfl
    have hcore :
        Associated
          (loaded.load21 i * loaded.load22 i *
            loaded.residualRoot i ^ 7)
          (p.signedDepth.realPairCore i) :=
      loaded.coreAssociated i
    have hpow :
        root i ^ 7 =
          loads.load21Root i ^ 7 *
            loads.load22Root i ^ 7 *
            loaded.residualRoot i ^ 7 := by
      simp only [root]
      ring
    exact (Associated.of_eq hpow).trans
      (hpowers.trans hcore)
  exact {
    root0 := root 0
    root1 := root 1
    root2 := root 2
    associated0 := hassociated 0
    associated1 := hassociated 1
    associated2 := hassociated 2 }

/-- Event-10 recovery theorem: seventh-power routing cells let the
unconditional loaded split absorb both scalar load families and recover
the ordinary three-core associated seventh-power split. -/
theorem nonempty_realPairCoreAssociatedPowerSplit_via_loaded_absorption
    (p : RamifiedSignedRootRoutingPacket)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    Nonempty
      (RamifiedSignedRootDepthPacket.RealPairCoreAssociatedPowerSplit
        p.signedDepth) := by
  rcases p.nonempty_realPairLoadedPowerSplit with ⟨loaded⟩
  rcases loaded.nonempty_loadPowerAbsorption_of_row2_cells h21 h22 with
    ⟨loads⟩
  exact ⟨loaded.absorb loads⟩

/-- The explicit canonical gcd-load absorption witnesses and the recovered
Branch-A core split are simultaneously available under the same two cell
hypotheses. -/
theorem nonempty_realPairLoadAbsorption_and_corePowerSplit
    (p : RamifiedSignedRootRoutingPacket)
    (h21 : ∃ a : ℕ, p.routing.c21 = a ^ 7)
    (h22 : ∃ b : ℕ, p.routing.c22 = b ^ 7) :
    Nonempty
      (RealPairLoadPowerAbsorption p ×
        RamifiedSignedRootDepthPacket.RealPairCoreAssociatedPowerSplit
          p.signedDepth) := by
  rcases p.nonempty_realPairLoadPowerAbsorption_of_row2_cells h21 h22 with
    ⟨loads⟩
  rcases
      p.nonempty_realPairCoreAssociatedPowerSplit_via_loaded_absorption
        h21 h22 with
    ⟨cores⟩
  exact ⟨⟨loads, cores⟩⟩

end RamifiedSignedRootRoutingPacket

end

end DkMath.FLT.Seven

import DkMath.ABC.GNExcessCubicSquarefulPell

/-!
Research scratch: uniqueness of the squarefree-times-square norm allocation.
This file assumes scalar norm data; it constructs no Eisenstein factors.
-/

namespace Scratch.ABCEisensteinLanding

open DkMath.ABC

theorem nat_squarefree_square_decomposition_unique
    {T d B G : ℕ} (hT : Squarefree T) (hB : Squarefree B)
    (hd : d ≠ 0) (hG : G ≠ 0)
    (heq : T * d ^ 2 = B * G ^ 2) :
    B = T ∧ G = d := by
  have hT0 : T ≠ 0 := hT.ne_zero
  have hB0 : B ≠ 0 := hB.ne_zero
  have hv (q : ℕ) : B.factorization q = T.factorization q ∧
      G.factorization q = d.factorization q := by
    have ht := hT.natFactorization_le_one q
    have hb := hB.natFactorization_le_one q
    have he := congrArg (fun n : ℕ => n.factorization q) heq
    simp only [Nat.factorization_mul hT0 (pow_ne_zero _ hd),
      Nat.factorization_mul hB0 (pow_ne_zero _ hG),
      Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul] at he
    omega
  exact ⟨Nat.eq_of_factorization_eq hB0 hT0 (fun q => (hv q).1),
    Nat.eq_of_factorization_eq hG hd (fun q => (hv q).2)⟩

theorem shell_squarefree_norm_allocation
    {X D a B G : ℕ}
    (ha : a ∈ GNExcessCubicRealizedLargeModulusShellWitnessSpace X D)
    (hB : Squarefree B) (hG : G ≠ 0)
    (hNorm : a ^ 2 + 3 * a + 3 = B * G ^ 2) :
    B = oddPart (GNExcessCubicFullRepeatedModulus a) *
        GNExcessCubicComplement a ∧
    G = evenPart (GNExcessCubicFullRepeatedModulus a) := by
  let M := GNExcessCubicFullRepeatedModulus a
  let S := GNExcessCubicComplement a
  have hMS : (M, S) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hT :=
    GNExcessCubicRealizedLargeModulusShellIncidencePair_squarefree_pellParameter hMS
  have hdecomp :=
    (GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hMS).1
  have hprod : M * S = a ^ 2 + 3 * a + 3 :=
    (GNExcessCubicRealizedLargeModulusShellWitness_complement_packet ha).2.2.2.2.2.1
  have hd : evenPart M ≠ 0 := by
    intro hz
    rw [hz] at hdecomp
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hdecomp
    rw [hdecomp, zero_mul] at hprod
    omega
  apply nat_squarefree_square_decomposition_unique hT hB hd hG
  calc
    (oddPart M * S) * (evenPart M) ^ 2 =
        (oddPart M * (evenPart M) ^ 2) * S := by ring
    _ = M * S := congrArg (fun z : ℕ => z * S) hdecomp.symm
    _ = a ^ 2 + 3 * a + 3 := hprod
    _ = B * G ^ 2 := hNorm

#print axioms nat_squarefree_square_decomposition_unique
#print axioms shell_squarefree_norm_allocation

end Scratch.ABCEisensteinLanding

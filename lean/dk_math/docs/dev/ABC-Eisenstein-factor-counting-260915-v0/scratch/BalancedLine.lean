import Mathlib

namespace Scratch

theorem eisenstein_norm_coordinate_bound (x y : ℤ) :
    x ^ 2 + y ^ 2 ≤ 2 * (x ^ 2 - x * y + y ^ 2) := by
  nlinarith [sq_nonneg (x - y)]

theorem coeff_one_solution_difference
    {Q R b c b' c' : ℤ}
    (hcop : IsCoprime Q R)
    (h1 : b * Q + c * R = 1)
    (h2 : b' * Q + c' * R = 1) :
    ∃ k : ℤ,
      b' - b = k * R ∧
      c' - c = -k * Q := by
  obtain ⟨u, v, huv⟩ := hcop
  have hdelta : (b' - b) * Q + (c' - c) * R = 0 := by
    linarith
  let k : ℤ := (b' - b) * v - (c' - c) * u
  refine ⟨k, ?_, ?_⟩
  · dsimp [k]
    have hA : (b' - b) * (u * Q + v * R) = b' - b := by
      rw [huv, mul_one]
    have hB : (b' - b) * u * Q + (c' - c) * u * R = 0 := by
      linear_combination u * hdelta
    nlinarith [hA, hB]
  · dsimp [k]
    have hA : (c' - c) * (u * Q + v * R) = c' - c := by
      rw [huv, mul_one]
    have hB : (b' - b) * v * Q + (c' - c) * v * R = 0 := by
      linear_combination v * hdelta
    nlinarith [hA, hB]

end Scratch

#print axioms Scratch.coeff_one_solution_difference
#print axioms Scratch.eisenstein_norm_coordinate_bound

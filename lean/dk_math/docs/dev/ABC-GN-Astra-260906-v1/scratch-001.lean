import DkMath.ABC.GNExcessCubicPrimitivePell

/-!
# ASTRA-001: elementary separation of norm-minus-three solutions

Research-only scratch, outside the production import graph. The determinant
argument keeps all quantities integral and avoids algebraic number fields.
-/

namespace DkMath.ABC.ASTRA001Scratch

/-- Eliminating the common conic parameter gives an exact determinant identity. -/
theorem conic_cross_identity {T y₁ y₂ d₁ d₂ : ℤ}
    (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
    (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2) :
    (y₂ * d₁) ^ 2 + 3 * d₁ ^ 2 = (y₁ * d₂) ^ 2 + 3 * d₂ ^ 2 := by
  have h₁' := congrArg (fun z : ℤ => z * d₂ ^ 2) h₁
  have h₂' := congrArg (fun z : ℤ => z * d₁ ^ 2) h₂
  nlinarith only [h₁', h₂']

/-- Positive solutions with coefficient at least two have `y >= 2d`. -/
theorem conic_y_lower {T y d : ℤ} (hT : 2 ≤ T) (hy : 0 ≤ y) (hd : 0 < d)
    (h : y ^ 2 + 3 = 4 * T * d ^ 2) : 2 * d ≤ y := by
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hmul : 2 * d ^ 2 ≤ T * d ^ 2 := mul_le_mul_of_nonneg_right hT (sq_nonneg d)
  nlinarith

/-- Distinct positive solutions cannot have squared denominators within a factor two. -/
theorem conic_no_close_denominators {T y₁ y₂ d₁ d₂ : ℤ}
    (hT : 2 ≤ T) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂)
    (hd₁ : 0 < d₁) (horder : d₁ < d₂)
    (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
    (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2) :
    2 * d₁ ^ 2 ≤ d₂ ^ 2 := by
  have hc := conic_cross_identity h₁ h₂
  have hlow₁ := conic_y_lower hT hy₁ hd₁ h₁
  have hlow₂ := conic_y_lower hT hy₂ (lt_trans hd₁ horder) h₂
  have hA : 0 ≤ y₂ * d₁ := mul_nonneg hy₂ (le_of_lt hd₁)
  have hB : 0 ≤ y₁ * d₂ := mul_nonneg hy₁ (by omega)
  have hsq : d₁ ^ 2 < d₂ ^ 2 := by nlinarith
  have hcross : y₁ * d₂ < y₂ * d₁ := by nlinarith [sq_nonneg (y₁ * d₂ - y₂ * d₁)]
  have hstep : y₁ * d₂ + 1 ≤ y₂ * d₁ := by omega
  have hbLow : 2 * d₁ * d₂ ≤ y₁ * d₂ := mul_le_mul_of_nonneg_right hlow₁ (by omega)
  have habLow : 2 * (y₁ * d₂) + 1 ≤ (y₂ * d₁) ^ 2 - (y₁ * d₂) ^ 2 := by
    nlinarith [sq_nonneg (y₂ * d₁ - y₁ * d₂ - 1)]
  nlinarith [mul_nonneg (show 0 ≤ d₁ by omega) (show 0 ≤ d₂ - d₁ by omega)]

/-- For positive natural witnesses the rational conic parameter is impossible. -/
theorem cubic_parameter_ge_two {a T d : ℕ}
    (h : (2 * a + 3) ^ 2 + 3 = 4 * T * d ^ 2) : 2 ≤ T := by
  by_contra hnot
  have hcases : T = 0 ∨ T = 1 := by omega
  rcases hcases with rfl | rfl
  · simp at h
  · have heq : a ^ 2 + 3 * a + 3 = d ^ 2 := by nlinarith
    exact cubicQuadratic_ne_square a d heq

/-- A dyadic shell contains at most one positive solution for fixed `T,r`. -/
theorem conic_shell_unique {T r D y₁ y₂ d₁ d₂ : ℕ}
    (hT : 2 ≤ T) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
    (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2)
    (hlo₁ : D ≤ r * d₁ ^ 2) (hhi₁ : r * d₁ ^ 2 < 2 * D)
    (hlo₂ : D ≤ r * d₂ ^ 2) (hhi₂ : r * d₂ ^ 2 < 2 * D) :
    y₁ = y₂ ∧ d₁ = d₂ := by
  have hone (y₁ y₂ d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (ho : d₁ < d₂)
      (h₁ : y₁ ^ 2 + 3 = 4 * T * d₁ ^ 2)
      (h₂ : y₂ ^ 2 + 3 = 4 * T * d₂ ^ 2)
      (hlo : D ≤ r * d₁ ^ 2) (hhi : r * d₂ ^ 2 < 2 * D) : False := by
    have hgapZ := conic_no_close_denominators
      (T := (T : ℤ)) (y₁ := (y₁ : ℤ)) (y₂ := (y₂ : ℤ))
      (d₁ := (d₁ : ℤ)) (d₂ := (d₂ : ℤ))
      (by exact_mod_cast hT) (by positivity) (by positivity)
      (by exact_mod_cast hd₁) (by exact_mod_cast ho)
      (by exact_mod_cast h₁) (by exact_mod_cast h₂)
    have hgap : 2 * d₁ ^ 2 ≤ d₂ ^ 2 := by exact_mod_cast hgapZ
    have hmul := Nat.mul_le_mul_left r hgap
    nlinarith
  have hd : d₁ = d₂ := by
    rcases lt_trichotomy d₁ d₂ with ho | he | ho
    · exact False.elim (hone y₁ y₂ d₁ d₂ hd₁ ho h₁ h₂ hlo₁ hhi₂)
    · exact he
    · exact False.elim (hone y₂ y₁ d₂ d₁ hd₂ ho h₂ h₁ hlo₂ hhi₁)
  refine ⟨?_, hd⟩
  subst d₂
  nlinarith

/-- The exact production witness fiber, refined by the canonical cube-core. -/
noncomputable def shellFiber (X D T r : ℕ) : Finset ℕ :=
  (GNExcessCubicRealizedLargeModulusShellPellParameterFiber X D T).filter
    (fun a => oddPart (GNExcessCubicFullRepeatedModulus a) = r)

/-- Two members of the same refined production fiber coincide. -/
theorem shellFiber_subsingleton (X D T r : ℕ) :
    ∀ a ∈ shellFiber X D T r, ∀ b ∈ shellFiber X D T r, a = b := by
  intro a ha b hb
  obtain ⟨haT, har⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbT, hbr⟩ := Finset.mem_filter.mp hb
  have haW := (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp haT).1
  have hbW := (mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mp hbT).1
  have haP := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet haT
  have hbP := GNExcessCubicRealizedLargeModulusShellPellParameterFiber_primitive_packet hbT
  have haI : (GNExcessCubicFullRepeatedModulus a, GNExcessCubicComplement a) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨a, haW, rfl⟩
  have hbI : (GNExcessCubicFullRepeatedModulus b, GNExcessCubicComplement b) ∈
      GNExcessCubicRealizedLargeModulusShellIncidencePairSpace X D :=
    Finset.mem_image.mpr ⟨b, hbW, rfl⟩
  have haC := GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet haI
  have hbC := GNExcessCubicRealizedLargeModulusShellIncidencePair_squareful_packet hbI
  have haS := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp haW
  have hbS := mem_GNExcessCubicRealizedLargeModulusShellWitnessSpace_iff.mp hbW
  have hra : GNExcessCubicFullRepeatedModulus a =
      r * (evenPart (GNExcessCubicFullRepeatedModulus a)) ^ 2 := by
    simpa only [har] using haC.1
  have hrb : GNExcessCubicFullRepeatedModulus b =
      r * (evenPart (GNExcessCubicFullRepeatedModulus b)) ^ 2 := by
    simpa only [hbr] using hbC.1
  have hu := conic_shell_unique (cubic_parameter_ge_two haP.2.2.1) haP.1 hbP.1
    haP.2.2.1 hbP.2.2.1
    (le_of_le_of_eq haS.2.1 hra) (lt_of_eq_of_lt hra.symm haS.2.2)
    (le_of_le_of_eq hbS.2.1 hrb) (lt_of_eq_of_lt hrb.symm hbS.2.2)
  omega

/-- The candidate bound two holds, with the stronger elementary bound one. -/
theorem shellFiber_card_le_one (X D T r : ℕ) : (shellFiber X D T r).card ≤ 1 :=
  Finset.card_le_one.mpr (shellFiber_subsingleton X D T r)

theorem shellFiber_card_le_two (X D T r : ℕ) : (shellFiber X D T r).card ≤ 2 :=
  (shellFiber_card_le_one X D T r).trans (by decide)

/-- Canonical `(r,S)` coordinates are injective inside a shell. -/
theorem shell_pair_injective (X D : ℕ) :
    Set.InjOn (fun a => (oddPart (GNExcessCubicFullRepeatedModulus a),
        GNExcessCubicComplement a))
      (GNExcessCubicRealizedLargeModulusShellWitnessSpace X D : Set ℕ) := by
  intro a ha b hb hab
  have hr := congrArg Prod.fst hab
  have hS := congrArg Prod.snd hab
  dsimp only at hr hS
  let r := oddPart (GNExcessCubicFullRepeatedModulus a)
  let T := r * GNExcessCubicComplement a
  refine shellFiber_subsingleton X D T r a ?_ b ?_
  · apply Finset.mem_filter.mpr
    exact ⟨mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr
      ⟨ha, rfl⟩, rfl⟩
  · apply Finset.mem_filter.mpr
    refine ⟨mem_GNExcessCubicRealizedLargeModulusShellPellParameterFiber_iff.mpr
      ⟨hb, ?_⟩, hr.symm⟩
    dsimp [T, r]
    rw [hr, hS]

/-- An exact Mordell-curve transport retaining the varying coefficients. -/
theorem mordell_transport {y S r u : ℤ}
    (h : y ^ 2 + 3 = 4 * S * r ^ 3 * u ^ 2) :
    (4 * S * u ^ 2 * y) ^ 2 =
      (4 * S * u ^ 2 * r) ^ 3 - 48 * S ^ 2 * u ^ 4 := by
  have hm := congrArg (fun z : ℤ => 16 * S ^ 2 * u ^ 4 * z) h
  nlinarith only [hm]

/-- Norm in the fixed Eisenstein ring, written in its two integer coordinates. -/
def eisensteinNorm (m n : ℤ) : ℤ := m ^ 2 - m * n + n ^ 2

/-- Multiplication by a square in `ℤ[ω]`; this is an identity, not existence
of a factorization with given norms. -/
theorem eisenstein_square_product_norm (m n b c : ℤ) :
    eisensteinNorm (b * (m ^ 2 - n ^ 2) - c * (2 * m * n - n ^ 2))
      (b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n)) =
        eisensteinNorm b c * (eisensteinNorm m n) ^ 2 := by
  unfold eisensteinNorm
  ring

/-- The coefficient-one condition in the fixed Eisenstein factorization
forces a primitive pair of quadratic coefficients. -/
theorem eisenstein_coefficient_coprime {m n b c : ℤ}
    (h : b * (2 * m * n - n ^ 2) + c * (m ^ 2 - 2 * m * n) = 1) :
    IsCoprime (2 * m * n - n ^ 2) (m ^ 2 - 2 * m * n) := by
  exact ⟨b, c, h⟩

end DkMath.ABC.ASTRA001Scratch

#print axioms DkMath.ABC.ASTRA001Scratch.conic_no_close_denominators
#print axioms DkMath.ABC.ASTRA001Scratch.shellFiber_card_le_one
#print axioms DkMath.ABC.ASTRA001Scratch.shell_pair_injective
#print axioms DkMath.ABC.ASTRA001Scratch.mordell_transport
#print axioms DkMath.ABC.ASTRA001Scratch.eisenstein_square_product_norm

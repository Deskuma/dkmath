import DkMath.FLT.Seven.PrimeTraceOneDirectRealCubicOrbit

/- Research certificates for astra-001; deliberately outside the production facade. -/
namespace DkMath.FLT.Seven.Astra001

open SevenRealCubicInt
noncomputable section
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def rotateUnit (u : SevenRealCubicIntˣ) : SevenRealCubicIntˣ :=
  Units.map rotateEquiv.toMonoidHom u

@[simp] theorem rotateUnit_val (u : SevenRealCubicIntˣ) :
    (rotateUnit u : SevenRealCubicInt) = rotateEquiv (u : SevenRealCubicInt) := rfl

def classRotate (c : ZMod 7 × ZMod 7) : ZMod 7 × ZMod 7 :=
  (4*c.1, c.1+2*c.2)

theorem linear_rotate (x : SevenRealCubicInt) :
    thetaLinearModSeven (rotateEquiv x) = 4 * thetaLinearModSeven x := by
  simp [thetaLinearModSeven, rotateEquiv, rotateHom]
  have h7 : (7 : ZMod 7) = 0 := by decide
  linear_combination -(3 * (x.thd : ZMod 7)) * h7

theorem square_rotate (x : SevenRealCubicInt) :
    thetaSquareModSeven (rotateEquiv x) =
      thetaLinearModSeven x + 2 * thetaSquareModSeven x := by
  simp [thetaSquareModSeven, thetaLinearModSeven, rotateEquiv, rotateHom]
  have h7 : (7 : ZMod 7) = 0 := by decide
  linear_combination -(x.thd : ZMod 7) * h7

theorem nilpotentX_rotate (u : SevenRealCubicIntˣ) :
    unitNilpotentX (rotateUnit u) = 4 * unitNilpotentX u := by
  unfold unitNilpotentX
  rw [rotateUnit_val, linear_rotate]
  change _ / thetaResidue (rotateEquiv (u : SevenRealCubicInt)) = _
  rw [thetaResidue_rotateEquiv]
  dsimp [thetaResidue]
  ring

theorem nilpotentY_rotate (u : SevenRealCubicIntˣ) :
    unitNilpotentY (rotateUnit u) = unitNilpotentX u + 2*unitNilpotentY u := by
  unfold unitNilpotentX unitNilpotentY
  rw [rotateUnit_val, square_rotate]
  change _ / thetaResidue (rotateEquiv (u : SevenRealCubicInt)) = _
  rw [thetaResidue_rotateEquiv]
  dsimp [thetaResidue]
  ring

theorem projectiveLog_rotate (u : SevenRealCubicIntˣ) :
    projectiveLog (Additive.ofMul (rotateUnit u)) =
      classRotate (projectiveLog (Additive.ofMul u)) := by
  rw [projectiveLog_apply, projectiveLog_apply, nilpotentX_rotate, nilpotentY_rotate]
  apply Prod.ext
  · rfl
  · change _ = unitNilpotentX u + 2 * (unitNilpotentY u - unitNilpotentX u ^ 2 / 2)
    have hi : (2 : ZMod 7)⁻¹ = 4 :=
      ZMod.inv_eq_of_mul_eq_one 7 2 4 (by decide)
    simp only [div_eq_mul_inv, hi]
    have h7 : (7 : ZMod 7) = 0 := by decide
    linear_combination -(8 * unitNilpotentX u ^ 2) * h7

theorem classRotate_order_three (c : ZMod 7 × ZMod 7) :
    classRotate (classRotate (classRotate c)) = c := by
  revert c
  decide

theorem classRotate_norm_zero (c : ZMod 7 × ZMod 7) :
    c + classRotate c + classRotate (classRotate c) = 0 := by
  revert c
  decide

theorem all_edge_classes :
    projectiveLog (Additive.ofMul orbitUnit01Unit) = (0,5) ∧
    projectiveLog (Additive.ofMul (rotateUnit orbitUnit01Unit)) = (0,3) ∧
    projectiveLog (Additive.ofMul (rotateUnit (rotateUnit orbitUnit01Unit))) = (0,6) := by
  refine ⟨orbitUnit01_projectiveLog, ?_, ?_⟩
  · rw [projectiveLog_rotate, orbitUnit01_projectiveLog]
    decide
  · rw [projectiveLog_rotate, projectiveLog_rotate, orbitUnit01_projectiveLog]
    decide

theorem norm_orbitUnit01 : norm orbitUnit01 = 1 := by
  rw [orbitUnit01, pairAxisUnit_one]
  norm_num [SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow,
    SevenRealCubicInt.norm, alpha, alphaAddOneInv,
    thetaSevenUnit, eisensteinAxisUnitInv, mul, pow_succ]

theorem orbit_units_product :
    orbitUnit01 * rotateEquiv orbitUnit01 * rotateEquiv (rotateEquiv orbitUnit01) = 1 := by
  rw [mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm, norm_orbitUnit01]
  rfl

def orbitW (a : ℕ) : SevenRealCubicInt := eisensteinAxis^5 * thetaSevenUnit * (a : SevenRealCubicInt)^2

theorem norm_orbitW (a : ℕ) : norm (orbitW a) = 7^5 * (a : ℤ)^6 := by
  have hu : norm thetaSevenUnit = -1 := by
    norm_num [thetaSevenUnit, SevenRealCubicInt.norm, eisensteinAxisUnitInv, mul, pow_succ]
  simp only [orbitW, SevenRealCubicInt.norm_mul, SevenRealCubicInt.norm_pow,
    norm_eisensteinAxis, hu]
  have ha : norm (a : SevenRealCubicInt) = (a : ℤ)^3 := by
    exact norm_intCast a
  rw [ha]
  ring

theorem three_edges {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    rotateEquiv p.rho ^ 7 - p.rho ^ 7 = orbitUnit01 * orbitW r.summit.gapRoot ^ 7 ∧
    rotateEquiv (rotateEquiv p.rho) ^ 7 - rotateEquiv p.rho ^ 7 =
      rotateEquiv orbitUnit01 * rotateEquiv (orbitW r.summit.gapRoot) ^ 7 ∧
    p.rho ^ 7 - rotateEquiv (rotateEquiv p.rho) ^ 7 =
      rotateEquiv (rotateEquiv orbitUnit01) *
        rotateEquiv (rotateEquiv (orbitW r.summit.gapRoot)) ^ 7 := by
  have h := directRealCubicOrbit_source_difference_factorization (r := r)
  simp only [directRealCubicOrbitSource, ite_true, one_ne_zero, ite_false] at h
  rw [p.source_eq_pow, map_pow] at h
  change rotateEquiv p.rho ^ 7 - p.rho ^ 7 = orbitUnit01 * orbitW r.summit.gapRoot ^ 7 at h
  have h1 := congrArg rotateEquiv h
  simp only [map_sub, map_mul, map_pow] at h1
  have h2 := congrArg rotateEquiv h1
  simp only [map_sub, map_mul, map_pow, rotateEquiv_three] at h2
  exact ⟨h, h1, h2⟩

theorem norm_gap_formula (a b c : ℤ) :
    norm (rotateEquiv (⟨a,b,c⟩ : SevenRealCubicInt) - ⟨a,b,c⟩) =
      7 * (b^3 + 4*b^2*c + 3*b*c^2 - c^3) := by
  norm_num [rotateEquiv, rotateHom, SevenRealCubicInt.norm]
  ring

theorem theta_dvd_rotate_gap (rho : SevenRealCubicInt) :
    eisensteinAxis ∣ rotateEquiv rho - rho := by
  rw [eisensteinAxis_dvd_iff_thetaConstModSeven_eq_zero]
  change thetaResidue (rotateEquiv rho - rho) = 0
  rw [map_sub, thetaResidue_rotateEquiv, sub_self]

theorem direct_quotient_core {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    ∃ core : SevenRealCubicInt,
      seventhQuotient (rotateEquiv p.rho) p.rho = eisensteinAxis^3 * core ∧
      ¬eisensteinAxis ∣ core :=
  exists_seventhQuotient_core_exactDepth_three _ _ p.not_eisensteinAxis_dvd
    (theta_dvd_rotate_gap p.rho)

theorem direct_root_dvd_residual {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    p.rho ∣ (r.summit.residualRoot : SevenRealCubicInt) := by
  refine ⟨rotateEquiv p.rho * rotateEquiv (rotateEquiv p.rho), ?_⟩
  change ((r.summit.residualRoot : ℤ) : SevenRealCubicInt) = _
  rw [← p.norm_eq_residualRoot, ← mul_rotateEquiv_mul_rotateEquiv_sq_eq_norm]
  ring

theorem direct_roots_coprime {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    IsCoprime p.rho (rotateEquiv p.rho) := by
  have hcop : IsCoprime (r.summit.gapRoot : SevenRealCubicInt)
      (r.summit.residualRoot : SevenRealCubicInt) := by
    have h : IsCoprime (r.summit.gapRoot : ℤ) (r.summit.residualRoot : ℤ) :=
      Int.isCoprime_iff_nat_coprime.mpr (by simpa using r.gap_residual_coprime)
    simpa using h.map (Int.castRingHom SevenRealCubicInt)
  apply isCoprime_of_prime_dvd
  · rintro ⟨h, _⟩
    exact p.not_eisensteinAxis_dvd (h ▸ dvd_zero _)
  · intro q hq hq0 hq1
    have hqB := hq0.trans (direct_root_dvd_residual p)
    have hqW : q ∣ orbitW r.summit.gapRoot := by
      have hqD := dvd_sub (dvd_pow hq1 (by decide : 7 ≠ 0))
        (dvd_pow hq0 (by decide : 7 ≠ 0))
      rw [(three_edges p).1] at hqD
      have hqpow := (hq.dvd_mul.mp hqD).resolve_left
        (fun h => hq.not_isUnit (isUnit_of_dvd_unit h orbitUnit01_isUnit))
      exact hq.dvd_of_dvd_pow hqpow
    have hqA : q ∣ (r.summit.gapRoot : SevenRealCubicInt) := by
      rw [orbitW] at hqW
      rcases hq.dvd_mul.mp hqW with ht | ha
      · rcases hq.dvd_mul.mp ht with ht | hu
        · have hassoc := hq.associated_of_dvd eisensteinAxis_prime (hq.dvd_of_dvd_pow ht)
          exact (p.not_eisensteinAxis_dvd (hassoc.dvd_iff_dvd_left.mp hq0)).elim
        · exact (hq.not_isUnit (isUnit_of_dvd_unit hu thetaSevenUnit_isUnit)).elim
      · exact hq.dvd_of_dvd_pow ha
    exact hq.not_isUnit (hcop.isUnit_of_dvd' hqA hqB)

theorem common_prime_of_gap_quotient {x y q : SevenRealCubicInt}
    (hxy : IsCoprime x y) (hq : Prime q)
    (hgap : q ∣ x - y) (hh : q ∣ seventhQuotient x y) :
    Associated q eisensteinAxis := by
  have hy : ¬ q ∣ y := by
    intro h
    have hx : q ∣ x := by simpa using dvd_add hgap h
    exact hq.not_isUnit (hxy.isUnit_of_dvd' hx h)
  have hrem := hgap.trans (gap_dvd_seventhQuotient_sub_seven_mul_pow_six x y)
  have hprod : q ∣ 7*y^6 := by simpa using dvd_sub hh hrem
  have hseven := (hq.dvd_mul.mp hprod).resolve_right
    (fun h => hy (hq.dvd_of_dvd_pow h))
  rw [seven_eq_eisensteinAxis_cube_mul_unit] at hseven
  have htheta := (hq.dvd_mul.mp hseven).resolve_right
    (fun h => hq.not_isUnit (isUnit_of_dvd_unit h thetaSevenUnit_isUnit))
  exact hq.associated_of_dvd eisensteinAxis_prime (hq.dvd_of_dvd_pow htheta)

theorem direct_gap_theta32 {x y z : ℕ} {source : CounterexamplePack x y z}
    {r : PrimitiveCounterexampleRamifiedProvenance source}
    (p : DirectRealCubicRootPacket source r) :
    eisensteinAxis ^ 32 ∣ rotateEquiv p.rho - p.rho := by
  obtain ⟨h, heq, hn⟩ := direct_quotient_core p
  have hedge := (three_edges p).1
  rw [pow_seven_sub_pow_seven_factorization, heq] at hedge
  have hfac :
      eisensteinAxis^3 * ((rotateEquiv p.rho-p.rho)*h) =
      eisensteinAxis^3 * (eisensteinAxis^32 *
        (orbitUnit01 * thetaSevenUnit^7 * (r.summit.gapRoot : SevenRealCubicInt)^14)) := by
    calc
      _ = (rotateEquiv p.rho-p.rho) * (eisensteinAxis^3*h) := by ring
      _ = _ := hedge.trans (by unfold orbitW; ring)
  have hcancel := mul_left_cancel₀ (pow_ne_zero 3 eisensteinAxis_prime.ne_zero) hfac
  exact eisensteinAxis_prime.pow_dvd_of_dvd_mul_right 32 hn ⟨_, hcancel⟩

def realH7 (s t : ℝ) : ℝ :=
  s^6+s^5*t+s^4*t^2+s^3*t^3+s^2*t^4+s*t^5+t^6

theorem realH7_ge_seven (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    7*(s*t)^3 ≤ realH7 s t := by
  have heq : realH7 s t - 7*(s*t)^3 =
      (s^3-t^3)^2 + s*t*(s^2-t^2)^2 + s^2*t^2*(s-t)^2 := by
    unfold realH7
    ring
  have hn : 0 ≤ (s^3-t^3)^2 + s*t*(s^2-t^2)^2 + s^2*t^2*(s-t)^2 := by
    positivity
  linarith only [heq, hn]

theorem realH7_ge_gap (l r : ℝ) : (l-r)^6 ≤ 64*realH7 l r := by
  have heq : 64*realH7 l r - (l-r)^6 =
      7*(l+r)^6 + 35*(l+r)^4*(l-r)^2 + 21*(l+r)^2*(l-r)^4 := by
    unfold realH7
    ring
  have hn : 0 ≤ 7*(l+r)^6 + 35*(l+r)^4*(l-r)^2 + 21*(l+r)^2*(l-r)^4 := by
    positivity
  linarith only [heq, hn]

#print axioms projectiveLog_rotate
#print axioms all_edge_classes
#print axioms orbit_units_product
#print axioms norm_orbitW
#print axioms three_edges
#print axioms norm_gap_formula
#print axioms direct_quotient_core
#print axioms direct_roots_coprime
#print axioms common_prime_of_gap_quotient
#print axioms direct_gap_theta32
#print axioms realH7_ge_seven
#print axioms realH7_ge_gap

end
end DkMath.FLT.Seven.Astra001

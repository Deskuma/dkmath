/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.NumberGeometry.GaugeTransition

namespace DkMath.NumberGeometry
noncomputable section

/-!
# Prime-labelled square-mass transitions

`PrimeScaleStep` is the first discrete arithmetic layer over the continuous
`MassScalesBy` relation.  Prime labels remain explicit natural numbers; no
number-theory-specific geometry or downstream prime-chain structure is used.
-/

/-- A prime-labelled transition between two relative square-mass gauges. -/
def PrimeScaleStep
    (p : ℕ) (K1 K2 : TwoPointKernel) : Prop :=
  Nat.Prime p ∧ MassScalesBy (p : ℝ) K1 K2

namespace PrimeScaleStep

/-- The natural-number label of a prime scale step is prime. -/
theorem prime
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2) :
    Nat.Prime p :=
  h.1

/-- The gauge relation carried by a prime scale step. -/
theorem massScalesBy
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2) :
    MassScalesBy (p : ℝ) K1 K2 :=
  h.2

/-- An active source makes the prime label of a transition intrinsic. -/
theorem label_unique
    {p q : ℕ} {K1 K2 : TwoPointKernel}
    (hK1 : K1.Active)
    (hp : PrimeScaleStep p K1 K2)
    (hq : PrimeScaleStep q K1 K2) :
    p = q := by
  have hcast : (p : ℝ) = (q : ℝ) :=
    MassScalesBy.factor_unique hK1 hp.massScalesBy hq.massScalesBy
  exact_mod_cast hcast

/-- A prime scale step preserves activity from an active source. -/
theorem target_active
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2)
    (h1 : K1.Active) :
    K2.Active := by
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast h.prime.pos
  have h1_pos : 0 < massGauge K1 :=
    (massGauge_pos_iff_active K1).2 h1
  have h2_pos : 0 < massGauge K2 := by
    rw [h.massScalesBy]
    exact mul_pos hp_pos h1_pos
  exact (massGauge_pos_iff_active K2).1 h2_pos

end PrimeScaleStep

/-- A prime shell promotes directly to a prime-labelled retarget step. -/
theorem primeScaleStep_retarget_of_onNatShell
    {p : ℕ} (hp : Nat.Prime p)
    (K : TwoPointKernel) {P : Point}
    (hP : OnNatShell K p P) :
    PrimeScaleStep p K (K.retarget P) := by
  exact ⟨hp, massScalesBy_retarget_of_onNatShell K hP⟩

namespace PrimeScaleStep

/-- A prime-labelled step has its squared-distance interpretation. -/
theorem dist_sq_eq_prime_mul_dist_sq
    {p : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleStep p K1 K2) :
    dist K2.source K2.target ^ 2 =
      (p : ℝ) * dist K1.source K1.target ^ 2 := by
  exact (massScalesBy_iff_dist_sq (p : ℝ) K1 K2).mp h.massScalesBy

/-- A prime-labelled natural transition cannot split into two non-unit natural labels. -/
theorem irreducible
    {p a b : ℕ} {K1 K2 K3 : TwoPointKernel}
    (hp13 : PrimeScaleStep p K1 K3)
    (h12 : MassScalesBy (a : ℝ) K1 K2)
    (h23 : MassScalesBy (b : ℝ) K2 K3)
    (hK1 : K1.Active) :
    a = 1 ∨ b = 1 := by
  have h13 : MassScalesBy ((a : ℝ) * (b : ℝ)) K1 K3 :=
    MassScalesBy.trans h12 h23
  have hcast : (p : ℝ) = (a : ℝ) * (b : ℝ) :=
    MassScalesBy.factor_unique hK1 hp13.massScalesBy h13
  have hnat : p = a * b := by
    exact_mod_cast hcast
  have hprime_mul : Nat.Prime (a * b) := by
    rw [← hnat]
    exact hp13.prime
  rcases Nat.prime_mul_iff.mp hprime_mul with ⟨_, hb⟩ | ⟨_, ha⟩
  · exact Or.inr hb
  · exact Or.inl ha

end PrimeScaleStep

/-- A finite chain of explicit prime-labelled gauge steps. -/
inductive PrimeScaleChain :
    TwoPointKernel → TwoPointKernel → List ℕ → Prop
  | nil (K : TwoPointKernel) : PrimeScaleChain K K []
  | cons
      {p : ℕ} {K1 K2 K3 : TwoPointKernel} {ps : List ℕ}
      (hStep : PrimeScaleStep p K1 K2)
      (hTail : PrimeScaleChain K2 K3 ps) :
      PrimeScaleChain K1 K3 (p :: ps)

namespace PrimeScaleChain

/-- The product of prime labels gives the total chain scale. -/
theorem massScalesBy_prod
    {K1 K2 : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K1 K2 ps) :
    MassScalesBy ((ps.prod : ℕ) : ℝ) K1 K2 := by
  induction h with
  | nil K =>
      simpa using massScalesBy_refl K
  | @cons p K1 K2 K3 ps hStep hTail ih =>
      have hcomp :
          MassScalesBy ((p : ℝ) * (ps.prod : ℝ)) K1 K3 :=
        MassScalesBy.trans hStep.massScalesBy ih
      simpa [List.prod_cons, Nat.cast_mul] using hcomp

/-- An active source makes every endpoint of a prime chain active. -/
theorem target_active
    {K1 K2 : TwoPointKernel} {ps : List ℕ}
    (h : PrimeScaleChain K1 K2 ps)
    (h1 : K1.Active) :
    K2.Active := by
  induction h with
  | nil K => exact h1
  | @cons p K1 K2 K3 ps hStep hTail ih =>
      exact ih (hStep.target_active h1)

/-- Repeated equal prime labels produce the corresponding prime power scale. -/
theorem massScalesBy_pow
    {p : ℕ} {k : ℕ} {K1 K2 : TwoPointKernel}
    (h : PrimeScaleChain K1 K2 (List.replicate k p)) :
    MassScalesBy ((p ^ k : ℕ) : ℝ) K1 K2 := by
  simpa [List.prod_replicate] using massScalesBy_prod h

end PrimeScaleChain

end
end DkMath.NumberGeometry

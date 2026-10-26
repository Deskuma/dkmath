import DkMath.FLT.FreyFiniteKernelReduction

#print "file: Note032LocalReductionSmoke"

/-! Source37の同じ整数商標的への局所還元接続。特異核側の仮定と滑らかな側を区別する。 -/
namespace Note032LocalReductionSmoke
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open DkMath.FLT.Frey DkMath.Lib.NumberTheory EllipticTorsionRepresentation ValuationInertia
open EllipticGoodReductionSeparation DkMath.Lib.RepresentationTheory
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
noncomputable local instance {α : Type*} : DecidableEq α := Classical.decEq _

/-- 37点核の付値環モデルの一般ファイバーは同じ既存標的。 -/
theorem source37_same_local_target (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    (S.residualValuationKernelModel L hl (by decide : Nat.Prime 2) (by decide) A hA).map A.subtype =
      S.residualKernelModel L hl :=
  S.residual_valuation_kernel_model_map (by decide) L hl (by decide) (by decide) A hA

/-- 同じ一次元直線の二つの還元の側を内部供給。 -/
theorem source37_kernel_cases (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    L ≤ S.residualZeroComponent A ∨ Disjoint L (S.residualZeroComponent A) :=
  S.residual_line_smooth_or_disjoint L hl A

/-- 特異核側の7進剰余一致。Disjointを結論へ隠さない。 -/
theorem source37_singular_residue (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 7) (hd : Disjoint L (S.residualZeroComponent A)) :
    (S.residualValuationKernelModel L hl (by decide : Nat.Prime 7) (by decide) A hA).map (residue A) =
      (S.valuationModel A).map (residue A) :=
  S.residual_valuation_kernel_residue_eq_of_disjoint L hl (by decide) (by decide) A hA hd

/-- 既存整数標的の2進c₄は、核の分岐に依らず単元。 -/
theorem source37_target_c4_odd (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    ¬ (2 : ℤ) ∣ (S.residualIntegerKernelModel L hl hs).c₄ :=
  S.residual_integer_target_c4_odd (by decide) L hl hs

/-- 同じ整数標的の正式な2進最小性。2進乗法的還元までは結論しない。 -/
theorem source37_target_minimal_at_two (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L) :
    IsMinimal (FreyLocalReduction.LocalRing 2)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_minimal_at_two (by decide) L hl hs

/-- 悪い5上でも、核の分岐に依らず同じ標的は最小。 -/
theorem source37_target_minimal_at_bad_five (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    (hbad : (5 : ℤ) ∣ S.a * S.b * S.c) :
    IsMinimal (FreyLocalReduction.LocalRing 5)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_minimal_at_bad_small_prime (by decide) L hl hs
    (by decide) (by decide) (by decide) hbad

/-- 特異核側の悪い奇素数では、同じ標的の正式な乗法的還元へ接続する。 -/
theorem source37_target_multiplicative (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (hs : IsStable S.residualRepresentation L)
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hqp : q ≠ 37)
    (hbad : (q : ℤ) ∣ S.a * S.b * S.c) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A q) (hd : Disjoint L (S.residualZeroComponent A)) :
    HasMultiplicativeReduction (FreyLocalReduction.LocalRing q)
      ((S.residualIntegerKernelModel L hl hs).map (Int.castRingHom ℚ)) :=
  S.residual_integer_target_multiplicative_of_disjoint (by decide) L hl hs hq2 hqp hbad A hA hd

/-- 滑らかな核の還元像は37点を保つ。同じ源・同じLを使う。 -/
theorem source37_smooth_kernel_card (S : Source 37) (L : Submodule (ZMod 37) S.ResidualSpace)
    (hl : Module.finrank (ZMod 37) L = 1) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) (hle : L ≤ S.residualZeroComponent A) :
    Nat.card (S.residualSmoothKernelReduction L A hle).range = 37 :=
  S.residual_smooth_kernel_range_card L hl (by decide : Nat.Prime 2) (by decide) A hA hle

end Note032LocalReductionSmoke

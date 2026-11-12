import DkMath.FLT.FreyModEightIrreducibility

#print "file: Note032ModEightIrreducibilitySmoke"

/-! 032-004の公開終点。指数37で住所・幾何providerなしに同じ表現へ接続する。 -/
namespace Note032ModEightIrreducibilitySmoke
open DkMath.FLT.Frey DkMath.Lib.NumberTheory ValuationInertia ValuationFrobenius
open EllipticGoodReductionSeparation
open DkMath.Lib.RepresentationTheory LocalFixedCofixed
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 同じ住所と同じFrobeniusが、同じ残余空間の外側の全ての点で枝交換する。 -/
theorem source37_local_witness (S : Source 37) (ha8 : S.a % 8 = 3) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), LiesOverPrime A 2 ∧
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), IsFrobeniusAt A σ 2 ∧
        ∀ P : S.ResidualSpace, ¬ HasSmoothReduction (S.valuationModel A) P.val →
          HasSmoothReduction (S.valuationModel A) (S.residualRepresentation σ P + P).val :=
  S.residual_exists_dyadic_frobenius_branch_swap_of_a_mod_eight (by decide) ha8

/-- hno・既約性・全安定直線排除を住所なしで確認する。Sourceの存在は主張しない。 -/
theorem source37_closed_profile (S : Source 37) (ha8 : S.a % 8 = 3) :
    (¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
      S.IsGaloisStable L ∧ IsCofixedOn S.residualRepresentation L) ∧
      S.ResidualIsIrreducible ∧
      (¬ ∃ L : Submodule (ZMod 37) S.ResidualSpace, Module.finrank (ZMod 37) L = 1 ∧
        S.IsGaloisStable L) :=
  ⟨S.residual_no_cofixed_line_of_a_mod_eight (by decide) ha8,
    S.residual_isIrreducible_of_a_mod_eight (by decide) ha8,
    S.residual_no_stable_line_of_a_mod_eight (by decide) ha8⟩

/-- 可約性を仮定した場合だけ、mod4の二択から7側を残す。 -/
theorem source37_remaining_branch (S : Source 37) (ha4 : (4 : ℤ) ∣ S.a + 1)
    (hred : ¬ S.ResidualIsIrreducible) : S.a % 8 = 7 :=
  S.residual_a_mod_eight_eq_seven_of_not_irreducible (by decide) ha4 hred

/-- 選択した同じSourceについて、元の反例との共通因子・符号付き置換を保持する。 -/
theorem counterexample37_trace (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (he : a ^ 37 + b ^ 37 = c ^ 37) :
    let S := Source.ofCounterexample 37 Fact.out (by decide) a b c ha hb hc he
    4 ∣ S.a + 1 ∧ Even S.b ∧
      (∃ R : PrimitiveReduction 37 a b c, OrientationTrace R.A R.B R.C S.a S.b S.c) ∧
      (S.ResidualIsIrreducible ∨ S.a % 8 = 7) :=
  Source.ofCounterexample_residual_irreducible_or_seven (by decide) a b c ha hb hc he

end Note032ModEightIrreducibilitySmoke

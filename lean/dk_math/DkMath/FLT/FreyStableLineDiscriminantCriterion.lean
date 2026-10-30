/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

import DkMath.FLT.FreyFiniteKernelDiscriminantDepth
import DkMath.FLT.FreySplitDyadic
import DkMath.FLT.FreyStableLineLocalGlobal

#print "file: DkMath.FLT.FreyStableLineDiscriminantCriterion"

/-!
# 2上の判別式深さから大域安定直線を一本へ絞る

前段で、`p ≥ 5` の安定一次元核は 2 上の零成分 `E₀[p]` と一致することを証明した。
この章ではその局所同定を、Frey 残余表現の既約性判定と `Even S.b` の大域二択へ接続する。

ここで得られるのは「探索すべき安定直線を `E₀[p]` 一本へ縮約する」ことである。
`E₀[p]` が大域的に非安定であること、したがって `hno` や FLT が成立することは、
このファイルでは仮定も結論もしない。
-/

namespace DkMath.FLT.Frey.Source

open DkMath.Lib.NumberTheory
open DkMath.Lib.RepresentationTheory
open DkMath.Lib.NumberTheory.ValuationInertia

variable {p : ℕ} [Fact p.Prime] (S : Source p)

/-- [DkMath.Lib] 既約性は、2上の零成分直線が大域安定でないことと同値である。

左から右は `residual_isIrreducible_iff_no_stable_line` に零成分の一次元性を入れる。
右から左は任意の安定一次元核を `residual_stable_line_eq_zeroComponent_at_two` で
零成分へ同定する。従って、この同値は `hno` や Cofixed 性を仮定せずに成立する。
-/
theorem residual_irreducible_iff_zeroComponent_not_stable_at_two (hp5 : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    S.ResidualIsIrreducible ↔
      ¬ S.IsGaloisStable (S.residualZeroComponent A) := by
  constructor
  · intro hirr hstable
    apply (S.residual_isIrreducible_iff_no_stable_line.mp hirr)
    exact ⟨S.residualZeroComponent A,
      S.residualZeroComponent_finrank_eq_one_at_two hp5 A hA, hstable⟩
  · intro hnot
    apply S.residual_isIrreducible_iff_no_stable_line.mpr
    rintro ⟨L, hl, hs⟩
    have heq := S.residual_stable_line_eq_zeroComponent_at_two hp5 L hl hs A hA
    exact hnot (heq ▸ hs)

/-- [DkMath.Lib] `Even S.b` のもとで、`hno` は零成分直線の非安定性へ縮約できる。

安定一次元核は `residual_stable_line_cofixed_of_oriented` により Cofixed でもある。
したがって、零成分が安定なら、それ自身が hno に反する Cofixed 直線になる。
逆向きは、任意の安定 Cofixed 直線を前段の局所同定へ送る。
-/
theorem residual_hno_iff_zeroComponent_not_stable_at_two (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ¬ S.IsGaloisStable (S.residualZeroComponent A) := by
  constructor
  · intro hno hstable
    have hline := S.residualZeroComponent_finrank_eq_one_at_two hp5 A hA
    have hcofixed := S.residual_stable_line_cofixed_of_oriented hp5 hbe
      (S.residualZeroComponent A) hline hstable
    exact hno ⟨S.residualZeroComponent A, hline, hstable, hcofixed⟩
  · intro hnot
    rintro ⟨L, hline, hstable, hcofixed⟩
    have heq := S.residual_stable_line_eq_zeroComponent_at_two hp5 L hline hstable A hA
    exact hnot (heq ▸ hstable)

/-- [DkMath.Lib] `hno` は、`E₀[p]` から外へ出る大域ガロア元の存在と同値である。

脱出元は `σ` と `P ∈ E₀[p]` を明示し、`ρ σ P ∉ E₀[p]` と記述する。
これは既存の全空間上の escape 条件より探索領域を狭めるが、実際の `σ` の存在を
構成する定理ではない。
-/
theorem residual_hno_iff_exists_zeroComponent_line_escape (hp5 : 5 ≤ p) (hbe : Even S.b)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        ∃ P : S.ResidualSpace,
          P ∈ S.residualZeroComponent A ∧
            S.residualRepresentation σ P ∉ S.residualZeroComponent A := by
  rw [S.residual_hno_iff_zeroComponent_not_stable_at_two hp5 hbe A hA]
  constructor
  · intro hnot
    change ¬ DkMath.Lib.RepresentationTheory.IsStable
      S.residualRepresentation (S.residualZeroComponent A) at hnot
    unfold DkMath.Lib.RepresentationTheory.IsStable at hnot
    rcases not_forall.mp hnot with ⟨σ, hσ⟩
    rcases not_forall.mp hσ with ⟨P, hP⟩
    rcases not_imp.mp hP with ⟨hPmem, hout⟩
    exact ⟨σ, P, hPmem, hout⟩
  · rintro ⟨σ, P, hP, hout⟩ hstable
    exact hout (hstable σ P hP)

/-- [DkMath.Lib] `a ≡ 7 mod 8` では、零成分脱出元は 2 上の分解群外にある。

`residual_zeroComponent_escape_not_decomposition_of_seven` は差分形
`ρ σ P - P ∉ E₀[p]` を受け取るため、`P ∈ E₀[p]` と部分加群の加法閉性で、
本章の点外れ形 `ρ σ P ∉ E₀[p]` へ変換してから適用する。逆向きは分解群外条件を
忘れて、直前の hno-escape 同値へ戻す。この定理は脱出元の存在そのものを証明しない。
-/
theorem residual_hno_iff_exists_zeroComponent_line_escape_outside_decomposition_of_seven
    (hp5 : 5 ≤ p) (hbe : Even S.b) (ha8 : S.a % 8 = 7)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : LiesOverPrime A 2) :
    (¬ ∃ L : Submodule (ZMod p) S.ResidualSpace,
      Module.finrank (ZMod p) L = 1 ∧ S.IsGaloisStable L ∧
        IsCofixedOn S.residualRepresentation L) ↔
      ∃ σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ),
        σ ∉ A.decompositionSubgroup ℚ ∧
        ∃ P : S.ResidualSpace,
          P ∈ S.residualZeroComponent A ∧
            S.residualRepresentation σ P ∉ S.residualZeroComponent A := by
  constructor
  · intro hno
    obtain ⟨σ, P, hP, hout⟩ :=
      (S.residual_hno_iff_exists_zeroComponent_line_escape hp5 hbe A hA).mp hno
    have hdiff : S.residualRepresentation σ P - P ∉ S.residualZeroComponent A := by
      intro hmem
      apply hout
      simpa only [sub_add_cancel] using (S.residualZeroComponent A).add_mem hmem hP
    have hσ := S.residual_zeroComponent_escape_not_decomposition_of_seven hp5 ha8 A hA hdiff
    exact ⟨σ, hσ, P, hP, hout⟩
  · rintro ⟨σ, _, P, hP, hout⟩
    apply (S.residual_hno_iff_exists_zeroComponent_line_escape hp5 hbe A hA).mpr
    exact ⟨σ, P, hP, hout⟩

end DkMath.FLT.Frey.Source

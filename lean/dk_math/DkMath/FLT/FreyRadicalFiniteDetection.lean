/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.FreyCommonProjectionTopology
import DkMath.Lib.NumberTheory.InertiaRadicalKernelTopology

#print "file: DkMath.FLT.FreyRadicalFiniteDetection"

/-! # 全根固定 tail の消滅から有限段核包含を抽出
新しい有限段消滅仮定を置かず、開核とコンパクト性を消費する。 -/
namespace DkMath.FLT.Frey.Source
open DkMath.Lib.NumberTheory DkMath.Lib.RepresentationTheory
open EllipticTorsionRepresentation ValuationInertia
attribute [local instance 2000] Submodule.module
noncomputable section
variable {p : ℕ} [Fact p.Prime] {S : Source p}
    {L : Submodule (ZMod p) S.ResidualSpace} {n : ℕ} (T : S.ResidualCyclicStage L n)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hp5 : 5 ≤ p) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (haddr : q = 2 ∨ (q : ℤ) ∣ S.a * S.b * S.c) (hA : LiesOverPrime A q)
include hp5 hq hqp haddr hA

/-- ある実際の有限段の根核が、元の共通射影核に含まれる。 -/
theorem ResidualCyclicStage.exists_radical_kernel_le_common :
    ∃ M : ℕ, (InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA M).ker ≤
      (T.fixedKernelCommonProjection A hp5 hq hqp haddr hA).ker := by
  let := InertiaRadical.inertia_compactSpace A
  apply CompactKernel.exists_subset_open
    (fun M => ((InertiaRadical.character (Fact.out : p.Prime) hq hqp.symm A hA M).ker : Set _))
    (InertiaRadical.character_kernel_isClosed (Fact.out : p.Prime) hq hqp.symm A hA)
    (InertiaRadical.character_kernel_antitone (Fact.out : p.Prime) hq hqp.symm A hA)
    _ (T.commonProjection_kernel_isOpen A hp5 hq hqp haddr hA)
  intro σ hs
  apply T.allRadicals_commonProjection_eq_one A hp5 hq hqp haddr hA σ
  exact (InertiaRadical.forall_character_kernel_iff_all_radicals
    (Fact.out : p.Prime) hq hqp.symm A hA σ).mp (Set.mem_iInter.mp hs)
end
end DkMath.FLT.Frey.Source


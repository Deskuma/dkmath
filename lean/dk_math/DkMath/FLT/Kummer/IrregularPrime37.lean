/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.FLT.Kummer.ObstructedState
import DkMath.Lib.NumberTheory.CyclotomicRamifiedPhase
import DkMath.Lib.NumberTheory.BernoulliPrime37
import DkMath.Lib.Cosmic.GNPrime37

#print "file: DkMath.FLT.Kummer.IrregularPrime37"

/-!
# IRR-001〜005 を37次円分整数環で読む

二項係数と Bernoulli の有限計算は無条件に証明する。
このサンプルで類群全体の37-torsionを構成したり、特定の GN 位相の類が非自明と
証明したりはしない。Bernoulli 非正則対と類群を結ぶ判定定理は別の境界である。
入力 State が与えられた場合のイデアル根・全障害の積・三項関係は正則性なしに追跡する。
-/

namespace DkMath.FLT.Kummer.IrregularPrime37

open DkMath.Lib.NumberTheory
open scoped NumberField

local instance prime37 : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- 実際の37次円分体。抽象的な位相ラベルだけを使うモデルとは区別する。 -/
abbrev Cyclotomic37 := CyclotomicField 37 ℚ

local instance cyclotomic37 : IsCyclotomicExtension {37} ℚ Cyclotomic37 :=
  CyclotomicField.isCyclotomicExtension 37 ℚ

/-- ζ↦1 の剰余写像と λ=1−ζ を持つ実際の37次位相 packet。 -/
noncomputable def phase37 : RamifiedPhasePacket (𝓞 Cyclotomic37) 37 :=
  cyclotomicRamifiedPhase (IsCyclotomicExtension.zeta_spec 37 ℚ Cyclotomic37) (by decide)

/-- 正則性や単元 criterion を要求しない37次の観測状態。 -/
noncomputable def observe {m : ℕ} (E : RegularDescent.State phase37 (m + 1)) :
    IrregularDescent.ObstructedState phase37 m := IrregularDescent.ofState (by decide) E

/-- 類群全体の37-torsionが残る場合でも、仮想 State の位相障害の積は1である。 -/
theorem product_obstruction_one {m : ℕ} (E : RegularDescent.State phase37 (m + 1)) :
    (∏ i, (observe E).phases.obstruction i) = 1 :=
  (observe E).product_obstruction_one (by decide)

/-- この族だけの類消滅を追加できれば、重み付き後続状態まで運べる。
大域的な Conditions を偽装して供給する必要はない。 -/
theorem exists_weighted_of_phase_trivial {m : ℕ} (E : RegularDescent.State phase37 (m + 1))
    (h : ∀ i, (observe E).phases.obstruction i = 1) :
    Nonempty (IrregularDescent.WeightedObstructedState phase37 m) :=
  (observe E).exists_weighted (by decide) (by decide) h

/-- 非自明37-torsionの証人が別途得られた場合、従来 Conditions の類群欄とは両立しない。
この含意は Bernoulli 計算だけからその証人を作るものではない。 -/
theorem conditions_incompatible_with_torsion
    (h : HasClassGroupPTorsion (𝓞 Cyclotomic37) 37) : ¬ RegularDescent.Conditions phase37 := by
  intro C
  exact hasClassGroupPTorsion_iff_not_torsionFree.mp h C.class_group

end DkMath.FLT.Kummer.IrregularPrime37

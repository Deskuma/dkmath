/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Adapted from Definitions/Def_FLTPrelim_Ramification.lean,
blob 718a9af252c4f10631ff70d4152977f046dccd0b.
Modified: retain only valuation interfaces in a DkMath namespace.
-/

import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

#print "file: DkMath.Lib.NumberTheory.ValuationInertia"

/-!
# 付値環の素数上の住所と、全ガロア群における慣性群

Lの付値環Aがq上にあるとは、qがAの非単元となることをいう。
慣性群はまずAを保存するdecomposition subgroup内で定義される。
その部分群包含による像を取って、L全体の自己同型群の部分群として公開する。
この像を取る操作を省くと、有限慣性元の持ち上げと表現の局所条件の群が一致しない。
-/
namespace DkMath.Lib.NumberTheory.ValuationInertia
variable {L : Type*} [Field L]

/-- qが付値環Aの非単元であるという有限素点の住所。使用時にはq.Primeを別に要求する。 -/
def LiesOverPrime (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

/-- 剰余体への作用の核を、分解群の包含によって全ガロア群の部分群へ写す。 -/
noncomputable def inertiaSubgroupIn (A : ValuationSubring L) (K : Type*) [Field K] [Algebra K L] :
    Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end DkMath.Lib.NumberTheory.ValuationInertia

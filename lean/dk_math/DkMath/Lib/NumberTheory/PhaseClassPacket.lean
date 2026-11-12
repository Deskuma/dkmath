/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Lib.NumberTheory.IdealPowerObstruction

#print "file: DkMath.Lib.NumberTheory.PhaseClassPacket"

/-! # IRR-002: 位相ごとの実際のイデアル根と類を記録する

類群の任意の p-torsion を位相へ割り当てるのではなく、各因子のイデアル根を保持する。
類群全体の非正則性と、特定の位相の障害の非自明性を混同しない。
-/

namespace DkMath.Lib.NumberTheory

/-- 各位相の値と、その値を生成する主イデアルの p 乗根。 -/
structure PhaseClassPacket (R : Type*) [CommRing R] [IsDedekindDomain R]
    (p : ℕ) (ι : Type*) where
  factor : ι → R
  power : ∀ i, IdealPowerObstruction R p (factor i)

namespace PhaseClassPacket
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {p : ℕ} {ι : Type*}

/-- 位相 i の障害は記録した根から決まる。 -/
noncomputable def obstruction (P : PhaseClassPacket R p ι) (i : ι) : ClassGroup R :=
  (P.power i).obstruction

/-- 正則・非正則に関係なく、各位相の類は p-torsion に入る。 -/
theorem torsion (P : PhaseClassPacket R p ι) (i : ι) : P.obstruction i ^ p = 1 :=
  (P.power i).torsion

/-- 正則性を供給した場合だけ、全位相の類を一律に消せる。 -/
theorem trivial_of_torsionFree (P : PhaseClassPacket R p ι)
    (hfree : classGroupPTorsionFreeAt R p) (i : ι) : P.obstruction i = 1 :=
  (P.power i).trivial_of_torsionFree hfree

/-- 全ての根を元として抽出するために必要なのは、この族についての障害消滅。
類群全体の正則性を仮定する必要はない。 -/
theorem exists_roots_of_trivial (P : PhaseClassPacket R p ι)
    (h : ∀ i, P.obstruction i = 1) :
    ∃ (u : ι → Rˣ) (b : ι → R), ∀ i, P.factor i = u i * b i ^ p := by
  have hi (i : ι) : ∃ (u : Rˣ) (b : R), P.factor i = u * b ^ p := by
    obtain ⟨u, b, _, he⟩ := (P.power i).exists_unit_generator (h i)
    exact ⟨u, b, he⟩
  choose u b hb using hi
  exact ⟨u, b, hb⟩

end PhaseClassPacket
end DkMath.Lib.NumberTheory

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Units.NPUnit

#print "file: DkMath.FLT.PetalCoreUnit"

namespace DkMath.FLT

/-- Phase-03 skeleton: Petal 側の中核単位。 -/
structure PetalCoreUnit where
  base : DkMath.NP
deriving DecidableEq, Repr

/-- NP から PetalCoreUnit への埋め込み。 -/
def ofNP (x : DkMath.NP) : PetalCoreUnit := ⟨x⟩

/-- PetalCoreUnit の `succ`（NP 側の `succ` を継承）。 -/
def coreSucc (u : PetalCoreUnit) : PetalCoreUnit :=
  ⟨DkMath.succ u.base⟩

/-- 値の観測（ℚ）も NP 側を継承。 -/
def coreVal (u : PetalCoreUnit) : ℚ :=
  DkMath.val u.base

/-- 周期インデックス（phase-03 では自然数で保持）。 -/
abbrev PeriodIndex := ℕ

/--
調和点（skeleton）:
偶数回の `succ` で位相ビットを保存する観測点。
-/
def HarmonicPoint (u : PetalCoreUnit) : Prop :=
  ∃ k : PeriodIndex, 0 < k ∧ (Nat.iterate coreSucc (2 * k) u).base.p = u.base.p

/--
例外位相（skeleton）:
ここでは簡易に back-phase (`p = true`) を例外相として置く。
-/
def isExceptionalPhase (u : PetalCoreUnit) : Prop :=
  u.base.p = true

lemma coreSucc_val (u : PetalCoreUnit) :
    coreVal (coreSucc u) = coreVal u + (1 / 2 : ℚ) := by
  simpa [coreSucc, coreVal] using DkMath.val_succ u.base

lemma harmonicPoint_ofNP (x : DkMath.NP) : HarmonicPoint (ofNP x) := by
  refine ⟨1, by decide, ?_⟩
  simp [ofNP, coreSucc, DkMath.succ_succ]

lemma notExceptional_ofNP_zero : ¬ isExceptionalPhase (ofNP DkMath.zero) := by
  simp [isExceptionalPhase, ofNP, DkMath.zero, DkMath.N]

end DkMath.FLT

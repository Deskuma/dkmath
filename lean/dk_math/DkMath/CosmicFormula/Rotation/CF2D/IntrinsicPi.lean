import DkMath.CosmicFormula.Rotation.CF2D.IntrinsicPolygon

/-!
# 面積候補の上限による内在的定数

前段で構成した数列 `A_n` は単調非減少かつ 4 以下である。実数の完備性を
使い、その値域の上限を `intrinsicPi` と定める。初項が 2 なので上限は正で、
単調収束定理により `A_n` はこの上限へ収束する。

定義と本ファイルの証明は標準の三角関数や円周率を参照しない。既存の円周率との
比較は別の bridge に置く。
-/
namespace DkMath.CosmicFormula.Rotation.CF2D
open Filter
open scoped Topology

/--
面積候補の値域の上限 `sup {A_n | n ∈ ℕ}`。
この定義は実数の順序完備性に基づき、標準の円周率を参照しない。
-/
noncomputable def intrinsicPi : ℝ := sSup (Set.range areaApprox)

/--
`A_n ≤ 4` による値域の上方有界性。上限の順序的性質に必要となる。
-/
theorem areaApprox_bddAbove : BddAbove (Set.range areaApprox) :=
  ⟨4, by rintro _ ⟨n, rfl⟩; exact areaApprox_le_four n⟩

/--
各面積候補はその値域の上限以下である。
-/
theorem areaApprox_le_intrinsicPi (n : ℕ) : areaApprox n ≤ intrinsicPi :=
  le_csSup areaApprox_bddAbove ⟨n, rfl⟩

/--
すべての面積候補に共通する上界 4 は、その上限の上界でもある。
-/
theorem intrinsicPi_le_four : intrinsicPi ≤ 4 := by
  apply csSup_le (Set.range_nonempty areaApprox)
  rintro _ ⟨n, rfl⟩
  exact areaApprox_le_four n

/--
`A_0 = 2` と上限の性質から、内在的定数は正である。
-/
theorem intrinsicPi_pos : 0 < intrinsicPi := by
  have h := areaApprox_le_intrinsicPi 0
  rw [areaApprox_zero] at h
  linarith

/--
単調非減少かつ上方有界な実数列は、その値域の上限 `intrinsicPi` に収束する。
-/
theorem tendsto_areaApprox_intrinsicPi : Tendsto areaApprox atTop (𝓝 intrinsicPi) := by
  simpa only [intrinsicPi, sSup_range] using tendsto_atTop_ciSup areaApprox_monotone areaApprox_bddAbove

end DkMath.CosmicFormula.Rotation.CF2D

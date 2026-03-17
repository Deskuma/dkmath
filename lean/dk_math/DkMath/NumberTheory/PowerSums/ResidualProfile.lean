/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- NumberTheory.PowerSums module: Residual profile examples with multiple body options

import Mathlib
import DkMath.NumberTheory.PowerSums.Basic
import DkMath.NumberTheory.PowerSums.ObservedMin

namespace DkMath
namespace NumberTheory
namespace PowerSums

/-!
## Residual Profile Examples (Same Big, Different Body)

Examples where the same Big value admits multiple Body choices,
leading to different observed minimum profiles for the residuals.
-/

/-! ### Sample 1: Cubic (d=3), Big = 216 -/

/-- 観測固定用の `Big` 値。 -/
def candidateBig : ℕ := 216

/-- 候補 `Body₁`。残差は `91`。 -/
def candidateBody₁ : ℕ := 125

/-- 候補 `Body₂`。残差は `64`。 -/
def candidateBody₂ : ℕ := 152

/-- 同じ Big でも Body の取り方で residual は変わる。 -/
theorem candidate_residuals_split :
    candidateBig - candidateBody₁ = 91 ∧
    candidateBig - candidateBody₂ = 64 := by
  constructor <;> norm_num [candidateBig, candidateBody₁, candidateBody₂]

/-- `Body₁ = 125` 側では residual `91` が 2 項の 3 乗和で観測できる。 -/
theorem candidate_fill_body₁_exact_two :
    FillableByPowSumExact 3 (candidateBig - candidateBody₁) 2 := by
  refine ⟨![3, 4], ?_⟩
  norm_num [candidateBig, candidateBody₁]

/-- `Body₁ = 125` 側の residual `91` は 1 項の 3 乗和では埋まらない。 -/
theorem candidate_fill_body₁_not_exact_one :
    ¬ FillableByPowSumExact 3 (candidateBig - candidateBody₁) 1 := by
  intro h
  rcases h with ⟨f, hf⟩
  have h91 : (f 0) ^ 3 = 91 := by
    simpa [candidateBig, candidateBody₁] using hf
  have hle : f 0 ≤ 4 := by
    by_contra hgt
    have hge5 : 5 ≤ f 0 := by omega
    have h125le : 125 ≤ (f 0) ^ 3 := by
      simpa using (Nat.pow_le_pow_left hge5 3)
    omega
  interval_cases h0 : f 0 <;> norm_num [h0] at h91

/-- `91` は 1 項の立方和では埋まらない（明示版）。 -/
theorem not_fillable_cube_91_exact_one :
    ¬ FillableByPowSumExact 3 91 1 :=
  candidate_fill_body₁_not_exact_one

/-- `Body₂ = 152` 側では residual `64` が 1 項の 3 乗和で観測できる。 -/
theorem candidate_fill_body₂_exact_one :
    FillableByPowSumExact 3 (candidateBig - candidateBody₂) 1 := by
  refine ⟨fun _ => 4, ?_⟩
  norm_num [candidateBig, candidateBody₂]

/-- 同じ `Big = 216` の候補ペアで、観測上の最小項数候補が分かれる。 -/
theorem candidate_same_big_observed_min_split :
    candidateBody₁ ≠ candidateBody₂ ∧
    FillableByPowSumExact 3 (candidateBig - candidateBody₁) 2 ∧
    ¬ FillableByPowSumExact 3 (candidateBig - candidateBody₁) 1 ∧
    FillableByPowSumExact 3 (candidateBig - candidateBody₂) 1 := by
  refine ⟨?_, candidate_fill_body₁_exact_two, candidate_fill_body₁_not_exact_one,
    candidate_fill_body₂_exact_one⟩
  norm_num [candidateBody₁, candidateBody₂]

/-- 候補ペアの residual で observed minimum profile が分かれる。 -/
theorem candidate_same_big_observed_min_profile :
    ObservedMinTwo 3 (candidateBig - candidateBody₁) ∧
    ObservedMinOne 3 (candidateBig - candidateBody₂) := by
  refine ⟨?_, ?_⟩
  · exact ⟨candidate_fill_body₁_not_exact_one, candidate_fill_body₁_exact_two⟩
  · exact candidate_fill_body₂_exact_one

/-- 主観測ペア `91/64` の observed minimum profile。 -/
theorem observed_min_profile_91_64 :
    ObservedMinTwo 3 91 ∧ ObservedMinOne 3 64 := by
  simpa [candidateBig, candidateBody₁, candidateBody₂] using
    candidate_same_big_observed_min_profile

/-- 主観測ペア `91/64` の residual 差は `27`。 -/
theorem observed_min_gap_91_64_eq_27 :
    91 - 64 = 27 := by
  norm_num

/-- Body の差も含めた候補ペアの observed minimum profile。 -/
theorem candidate_same_big_observed_min_split_profile :
    candidateBody₁ ≠ candidateBody₂ ∧
    ObservedMinTwo 3 (candidateBig - candidateBody₁) ∧
    ObservedMinOne 3 (candidateBig - candidateBody₂) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [candidateBody₁, candidateBody₂]
  · exact ⟨candidate_fill_body₁_not_exact_one, candidate_fill_body₁_exact_two⟩
  · exact candidate_fill_body₂_exact_one

/-! ### Sample 2: Square (d=2), Big = 25 -/

/-- 第2標本の固定 `Big`。 -/
def candidateBigSq : ℕ := 25

/-- `Body₁` 側の residual は `13`。 -/
def candidateBodySq₁ : ℕ := 12

/-- `Body₂` 側の residual は `9`。 -/
def candidateBodySq₂ : ℕ := 16

/-- 第2標本の residual 分岐。 -/
theorem candidate_sq_residuals_split :
    candidateBigSq - candidateBodySq₁ = 13 ∧
    candidateBigSq - candidateBodySq₂ = 9 := by
  constructor <;> norm_num [candidateBigSq, candidateBodySq₁, candidateBodySq₂]

/-- `13 = 2^2 + 3^2` なので 2 項の平方和で埋まる。 -/
theorem candidate_sq_fill_body₁_exact_two :
    FillableByPowSumExact 2 (candidateBigSq - candidateBodySq₁) 2 := by
  refine ⟨![2, 3], ?_⟩
  norm_num [candidateBigSq, candidateBodySq₁]

/-- `13` は 1 項の平方では埋まらない。 -/
theorem candidate_sq_fill_body₁_not_exact_one :
    ¬ FillableByPowSumExact 2 (candidateBigSq - candidateBodySq₁) 1 := by
  intro h
  rcases h with ⟨f, hf⟩
  have h13 : (f 0) ^ 2 = 13 := by
    simpa [candidateBigSq, candidateBodySq₁] using hf
  have hle : f 0 ≤ 3 := by
    by_contra hgt
    have hge4 : 4 ≤ f 0 := by omega
    have h16le : 16 ≤ (f 0) ^ 2 := by
      simpa using (Nat.pow_le_pow_left hge4 2)
    omega
  interval_cases h0 : f 0 <;> norm_num [h0] at h13

/-- `9 = 3^2` なので 1 項の平方和で埋まる。 -/
theorem candidate_sq_fill_body₂_exact_one :
    FillableByPowSumExact 2 (candidateBigSq - candidateBodySq₂) 1 := by
  refine ⟨fun _ => 3, ?_⟩
  norm_num [candidateBigSq, candidateBodySq₂]

/-- 第2標本でも same Big で observed minimum profile が分岐する。 -/
theorem candidate_sq_same_big_observed_min_split_profile :
    candidateBodySq₁ ≠ candidateBodySq₂ ∧
    ObservedMinTwo 2 (candidateBigSq - candidateBodySq₁) ∧
    ObservedMinOne 2 (candidateBigSq - candidateBodySq₂) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [candidateBodySq₁, candidateBodySq₂]
  · exact ⟨candidate_sq_fill_body₁_not_exact_one, candidate_sq_fill_body₁_exact_two⟩
  · exact candidate_sq_fill_body₂_exact_one

/-! ### Sample 3: Cubic (d=3), Big = 64 -/

/-- 第3標本の固定 `Big`。 -/
def candidateBigCube₂ : ℕ := 64

/-- `Body₁` 側の residual は `35`。 -/
def candidateBodyCube₂₁ : ℕ := 29

/-- `Body₂` 側の residual は `27`。 -/
def candidateBodyCube₂₂ : ℕ := 37

/-- 第3標本の residual 分岐。 -/
theorem candidate_cube₂_residuals_split :
    candidateBigCube₂ - candidateBodyCube₂₁ = 35 ∧
    candidateBigCube₂ - candidateBodyCube₂₂ = 27 := by
  constructor <;> norm_num [candidateBigCube₂, candidateBodyCube₂₁, candidateBodyCube₂₂]

/-- `35 = 2^3 + 3^3` なので 2 項の立方和で埋まる。 -/
theorem candidate_cube₂_fill_body₁_exact_two :
    FillableByPowSumExact 3 (candidateBigCube₂ - candidateBodyCube₂₁) 2 := by
  refine ⟨![2, 3], ?_⟩
  norm_num [candidateBigCube₂, candidateBodyCube₂₁]

/-- `35` は 1 項の立方では埋まらない。 -/
theorem candidate_cube₂_fill_body₁_not_exact_one :
    ¬ FillableByPowSumExact 3 (candidateBigCube₂ - candidateBodyCube₂₁) 1 := by
  intro h
  rcases h with ⟨f, hf⟩
  have h35 : (f 0) ^ 3 = 35 := by
    simpa [candidateBigCube₂, candidateBodyCube₂₁] using hf
  have hle : f 0 ≤ 3 := by
    by_contra hgt
    have hge4 : 4 ≤ f 0 := by omega
    have h64le : 64 ≤ (f 0) ^ 3 := by
      simpa using (Nat.pow_le_pow_left hge4 3)
    omega
  interval_cases h0 : f 0 <;> norm_num [h0] at h35

/-- `27 = 3^3` なので 1 項の立方和で埋まる。 -/
theorem candidate_cube₂_fill_body₂_exact_one :
    FillableByPowSumExact 3 (candidateBigCube₂ - candidateBodyCube₂₂) 1 := by
  refine ⟨fun _ => 3, ?_⟩
  norm_num [candidateBigCube₂, candidateBodyCube₂₂]

/-- 第3標本でも same Big で observed minimum profile が分岐する。 -/
theorem candidate_cube₂_same_big_observed_min_split_profile :
    candidateBodyCube₂₁ ≠ candidateBodyCube₂₂ ∧
    ObservedMinTwo 3 (candidateBigCube₂ - candidateBodyCube₂₁) ∧
    ObservedMinOne 3 (candidateBigCube₂ - candidateBodyCube₂₂) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [candidateBodyCube₂₁, candidateBodyCube₂₂]
  · exact ⟨candidate_cube₂_fill_body₁_not_exact_one, candidate_cube₂_fill_body₁_exact_two⟩
  · exact candidate_cube₂_fill_body₂_exact_one

/-- 第3標本の profile 本体（Body 不等号条件を除く）。 -/
theorem candidate_cube₂_same_big_observed_min_profile :
    ObservedMinTwo 3 (candidateBigCube₂ - candidateBodyCube₂₁) ∧
    ObservedMinOne 3 (candidateBigCube₂ - candidateBodyCube₂₂) := by
  refine ⟨?_, ?_⟩
  · exact ⟨candidate_cube₂_fill_body₁_not_exact_one, candidate_cube₂_fill_body₁_exact_two⟩
  · exact candidate_cube₂_fill_body₂_exact_one

/-! ### Sample 4: Cubic (d=3), Big = 125 -/

/-- 第4標本の固定 `Big`。 -/
def candidateBigCube₃ : ℕ := 125

/-- `Body₁` 側の residual は `65`。 -/
def candidateBodyCube₃₁ : ℕ := 60

/-- `Body₂` 側の residual は `64`。 -/
def candidateBodyCube₃₂ : ℕ := 61

/-- 第4標本の residual 分岐。 -/
theorem candidate_cube₃_residuals_split :
    candidateBigCube₃ - candidateBodyCube₃₁ = 65 ∧
    candidateBigCube₃ - candidateBodyCube₃₂ = 64 := by
  constructor <;> norm_num [candidateBigCube₃, candidateBodyCube₃₁, candidateBodyCube₃₂]

/-- `65 = 1^3 + 4^3` なので 2 項の立方和で埋まる。 -/
theorem candidate_cube₃_fill_body₁_exact_two :
    FillableByPowSumExact 3 (candidateBigCube₃ - candidateBodyCube₃₁) 2 := by
  refine ⟨![1, 4], ?_⟩
  norm_num [candidateBigCube₃, candidateBodyCube₃₁]

/-- `65` は 1 項の立方では埋まらない。 -/
theorem candidate_cube₃_fill_body₁_not_exact_one :
    ¬ FillableByPowSumExact 3 (candidateBigCube₃ - candidateBodyCube₃₁) 1 := by
  intro h
  rcases h with ⟨f, hf⟩
  have h65 : (f 0) ^ 3 = 65 := by
    simpa [candidateBigCube₃, candidateBodyCube₃₁] using hf
  have hle : f 0 ≤ 4 := by
    by_contra hgt
    have hge5 : 5 ≤ f 0 := by omega
    have h125le : 125 ≤ (f 0) ^ 3 := by
      simpa using (Nat.pow_le_pow_left hge5 3)
    omega
  interval_cases h0 : f 0 <;> norm_num [h0] at h65

/-- `64 = 4^3` なので 1 項の立方和で埋まる。 -/
theorem candidate_cube₃_fill_body₂_exact_one :
    FillableByPowSumExact 3 (candidateBigCube₃ - candidateBodyCube₃₂) 1 := by
  refine ⟨fun _ => 4, ?_⟩
  norm_num [candidateBigCube₃, candidateBodyCube₃₂]

/-- 第4標本でも same Big で observed minimum profile が分岐する。 -/
theorem candidate_cube₃_same_big_observed_min_split_profile :
    candidateBodyCube₃₁ ≠ candidateBodyCube₃₂ ∧
    ObservedMinTwo 3 (candidateBigCube₃ - candidateBodyCube₃₁) ∧
    ObservedMinOne 3 (candidateBigCube₃ - candidateBodyCube₃₂) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [candidateBodyCube₃₁, candidateBodyCube₃₂]
  · exact ⟨candidate_cube₃_fill_body₁_not_exact_one, candidate_cube₃_fill_body₁_exact_two⟩
  · exact candidate_cube₃_fill_body₂_exact_one

/-- 第4標本の profile 本体（Body 不等号条件を除く）。 -/
theorem candidate_cube₃_same_big_observed_min_profile :
    ObservedMinTwo 3 (candidateBigCube₃ - candidateBodyCube₃₁) ∧
    ObservedMinOne 3 (candidateBigCube₃ - candidateBodyCube₃₂) := by
  refine ⟨?_, ?_⟩
  · exact ⟨candidate_cube₃_fill_body₁_not_exact_one, candidate_cube₃_fill_body₁_exact_two⟩
  · exact candidate_cube₃_fill_body₂_exact_one

/-! ### Summary: Three samples for d = 3 -/

/--
立方次数 `d = 3` において、same Big に対する observed minimum profile の分岐が
独立な 3 標本で再現する。
-/
theorem cube_observed_min_split_reproduced_three_samples :
    (ObservedMinTwo 3 (candidateBig - candidateBody₁) ∧
      ObservedMinOne 3 (candidateBig - candidateBody₂)) ∧
    (ObservedMinTwo 3 (candidateBigCube₂ - candidateBodyCube₂₁) ∧
      ObservedMinOne 3 (candidateBigCube₂ - candidateBodyCube₂₂)) ∧
    (ObservedMinTwo 3 (candidateBigCube₃ - candidateBodyCube₃₁) ∧
      ObservedMinOne 3 (candidateBigCube₃ - candidateBodyCube₃₂)) := by
  refine ⟨candidate_same_big_observed_min_profile,
    candidate_cube₂_same_big_observed_min_profile,
    candidate_cube₃_same_big_observed_min_profile⟩

end PowerSums
end NumberTheory
end DkMath

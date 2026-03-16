import Mathlib
import DkMath.Samples.LPS.BigFamily
import DkMath.Samples.LPS.BigFamilyInt
import DkMath.Samples.LPS.PowerSwap
import DkMath.Samples.LPS.GapFillRank

namespace DkMath
namespace Samples
namespace BigFamilyExamples

/-! ## 反転指数交点 `16` の標本 -/

/-- `2^4 = 4^2` は PowerSwap の基本標本。 -/
theorem powerSwap_2_4 : PowerSwap 2 4 :=
  powerSwap_two_four

/-- 同じ `16` は 2 乗 1 項 (`4^2`) で埋まる。 -/
theorem fillable_pow2_16_exact_one : FillableByPowSumExact 2 16 1 :=
  fillable_sq_16_exact_one

/-- 同じ `16` は 4 乗 1 項 (`2^4`) でも埋まる。 -/
theorem fillable_pow4_16_exact_one : FillableByPowSumExact 4 16 1 := by
  refine ⟨fun _ => 2, ?_⟩
  simp

/-- Big-family (`ℕ`) 側での `16` 観測。 -/
example : BigFamily.big 2 3 1 = 16 := by
  norm_num [BigFamily.big]

/-- Big-family (`ℤ`) 側での `16` 観測。 -/
example : BigFamilyInt.big 2 3 1 = 16 := by
  norm_num [BigFamilyInt.big]

/-! ## 三乗補正 `216` の標本 -/

/-- `216 = 6^3` は 1 項の 3 乗和。 -/
theorem fillable_cube_216_exact_one_sample : FillableByPowSumExact 3 216 1 :=
  fillable_cube_216_exact_one

/-- `216 = 3^3 + 4^3 + 5^3` は 3 項の 3 乗和。 -/
theorem fillable_cube_216_exact_three_sample : FillableByPowSumExact 3 216 3 :=
  fillable_cube_216_exact_three

/-- 同じ値 `216` が異なる filling を持つことの数式確認。 -/
example : (6 : ℕ) ^ 3 = 3 ^ 3 + 4 ^ 3 + 5 ^ 3 := by
  norm_num

/-! ## residual 観測（差分の同次数和） -/

/-- 差分 `6^3 - 5^3` は `3^3 + 4^3` に一致する。 -/
theorem residual_cube_6_5_eq_two_cubes_nat :
    (6 : ℕ) ^ 3 - 5 ^ 3 = 3 ^ 3 + 4 ^ 3 := by
  norm_num

/-- 上の差分は 3 乗 2 項で埋まる。 -/
theorem residual_cube_6_5_fillable_exact_two :
    FillableByPowSumExact 3 ((6 : ℕ) ^ 3 - 5 ^ 3) 2 := by
  refine ⟨![3, 4], ?_⟩
  norm_num

/-- `ℤ`-Big-family 観測での差分形。 -/
theorem residual_big_minus_core_eq_two_cubes_int :
    BigFamilyInt.big 3 5 1 - BigFamilyInt.core 3 5 1 =
      (3 : ℤ) ^ 3 + 4 ^ 3 := by
  norm_num [BigFamilyInt.big, BigFamilyInt.core]

/-! ## FillRank 変動探索の候補ペア（同じ Big, 異なる Body） -/

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

/--
Observed minimum profile at degree `d`.

- `ObservedMinOne d n`: `n` is fillable by one `d`-th power.
- `ObservedMinTwo d n`: `n` is not fillable by one `d`-th power,
  but is fillable by two `d`-th powers.

This is a lightweight observational notion, weaker than a full `FillRank`.
-/
/-
TODO:
If observed minimum profiles are reused across multiple LPS sample files,
promote `ObservedMinOne/Two` to `GapFillRank.lean`.
-/
def ObservedMinOne (d n : ℕ) : Prop :=
  FillableByPowSumExact d n 1

/-- Lightweight observational minimum profile at count `2`. -/
def ObservedMinTwo (d n : ℕ) : Prop :=
  ¬ FillableByPowSumExact d n 1 ∧ FillableByPowSumExact d n 2

/-- 候補ペアの residual で observed minimum profile が分かれる。 -/
theorem candidate_same_big_observed_min_profile :
    ObservedMinTwo 3 (candidateBig - candidateBody₁) ∧
    ObservedMinOne 3 (candidateBig - candidateBody₂) := by
  refine ⟨?_, ?_⟩
  · exact ⟨candidate_fill_body₁_not_exact_one, candidate_fill_body₁_exact_two⟩
  · exact candidate_fill_body₂_exact_one

/-- Body の差も含めた候補ペアの observed minimum profile。 -/
theorem candidate_same_big_observed_min_split_profile :
    candidateBody₁ ≠ candidateBody₂ ∧
    ObservedMinTwo 3 (candidateBig - candidateBody₁) ∧
    ObservedMinOne 3 (candidateBig - candidateBody₂) := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [candidateBody₁, candidateBody₂]
  · exact ⟨candidate_fill_body₁_not_exact_one, candidate_fill_body₁_exact_two⟩
  · exact candidate_fill_body₂_exact_one

/-! ## 第2標本（平方版）：same Big, different observed minimum profiles -/

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

/-! ## 第3標本（立方版）：same Big, different observed minimum profiles -/

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

/-! ## 三平方補正項族（整数版） -/

/--
`(2m)^2 + (2n)^2 + (m^2+n^2-1)^2 = (m^2+n^2+1)^2`

三平方補正項族の基本恒等式（`ℤ` 版）。
-/
theorem three_square_correction_family (m n : ℤ) :
    (2 * m) ^ 2 + (2 * n) ^ 2 + (m ^ 2 + n ^ 2 - 1) ^ 2 =
      (m ^ 2 + n ^ 2 + 1) ^ 2 := by
  ring

end BigFamilyExamples
end Samples
end DkMath

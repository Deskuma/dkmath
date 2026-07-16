/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
import DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat

#print "file: DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction"

namespace DkMath.Collatz

/-!
# Fixed low-window obstruction

A fixed low binary window cannot distinguish a sufficiently long finite
all-ones word from its 2-adic all-ones continuation.  This module turns that
observation into a parameterized positive closed-signature edge.  It rejects
only the concrete low signature defined below; it does not reject finite
signatures carrying an upper boundary or a dynamically decreasing rank.
-/

/-! ## The all-ones source and its first two successors -/

/-- A positive odd word whose visible low `r` bits are all one. -/
noncomputable def rawAllOnesWitness (r : ℕ) : OddNat := by
  refine ⟨2 ^ (r + 2) - 1, ?_⟩
  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
  omega

@[simp]
theorem rawAllOnesWitness_val (r : ℕ) :
    (rawAllOnesWitness r).1 = 2 ^ (r + 2) - 1 := rfl

/-- First residual odd word after removing the visible factor two. -/
def rawAllOnesFirstTargetValue (r : ℕ) : ℕ :=
  3 * 2 ^ (r + 1) - 1

/-- Second residual odd word on the same height-one channel. -/
def rawAllOnesSecondTargetValue (r : ℕ) : ℕ :=
  9 * 2 ^ r - 1

private theorem rawAllOnes_three_mul_add_one
    (r : ℕ) :
    3 * (rawAllOnesWitness r).1 + 1 =
      2 * rawAllOnesFirstTargetValue r := by
  simp only [rawAllOnesWitness_val, rawAllOnesFirstTargetValue]
  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
  omega

private theorem rawAllOnes_firstTarget_odd
    (r : ℕ) : rawAllOnesFirstTargetValue r % 2 = 1 := by
  unfold rawAllOnesFirstTargetValue
  rw [show r + 1 = r + 1 by rfl, pow_succ]
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  omega

/-- The all-ones source lies on the exact height-one channel. -/
theorem s_rawAllOnesWitness_eq_one (r : ℕ) :
    s (rawAllOnesWitness r) = 1 := by
  have hne : rawAllOnesFirstTargetValue r ≠ 0 := by
    unfold rawAllOnesFirstTargetValue
    have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
    omega
  have hv := (DkMath.ABC.padic_val_two_of_even
    (rawAllOnesFirstTargetValue r)).2 hne
  change v2 (3 * (rawAllOnesWitness r).1 + 1) = 1
  rw [rawAllOnes_three_mul_add_one]
  simpa [v2,
    v2_odd _ (rawAllOnes_firstTarget_odd r)] using hv

/-- Exact first accelerated successor of the all-ones source. -/
theorem T_rawAllOnesWitness_val (r : ℕ) :
    (T (rawAllOnesWitness r)).1 = rawAllOnesFirstTargetValue r := by
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
    (s_rawAllOnesWitness_eq_one r)]
  rw [rawAllOnes_three_mul_add_one]
  simp

private theorem rawAllOnes_firstTarget_three_mul_add_one
    (r : ℕ) :
    3 * rawAllOnesFirstTargetValue r + 1 =
      2 * rawAllOnesSecondTargetValue r := by
  simp only [rawAllOnesFirstTargetValue, rawAllOnesSecondTargetValue]
  rw [show r + 1 = r + 1 by rfl, pow_succ]
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  omega

private theorem rawAllOnes_secondTarget_odd
    {r : ℕ} (hr : 1 ≤ r) : rawAllOnesSecondTargetValue r % 2 = 1 := by
  unfold rawAllOnesSecondTargetValue
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [show 1 + q = q + 1 by omega, pow_succ]
  have hp : 0 < 2 ^ q := pow_pos (by norm_num) _
  omega

/-- The first successor remains on the exact height-one channel. -/
theorem s_T_rawAllOnesWitness_eq_one
    {r : ℕ} (hr : 1 ≤ r) :
    s (T (rawAllOnesWitness r)) = 1 := by
  have hne : rawAllOnesSecondTargetValue r ≠ 0 := by
    unfold rawAllOnesSecondTargetValue
    have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
    omega
  have hv := (DkMath.ABC.padic_val_two_of_even
    (rawAllOnesSecondTargetValue r)).2 hne
  change v2 (3 * (T (rawAllOnesWitness r)).1 + 1) = 1
  rw [T_rawAllOnesWitness_val,
    rawAllOnes_firstTarget_three_mul_add_one]
  simpa [v2,
    v2_odd _ (rawAllOnes_secondTarget_odd hr)] using hv

/-- Exact second accelerated successor, used to audit the target growth flag. -/
theorem T_T_rawAllOnesWitness_val
    {r : ℕ} (hr : 1 ≤ r) :
    (T (T (rawAllOnesWitness r))).1 = rawAllOnesSecondTargetValue r := by
  rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one _
    (s_T_rawAllOnesWitness_eq_one hr)]
  rw [T_rawAllOnesWitness_val,
    rawAllOnes_firstTarget_three_mul_add_one]
  simp

/-! ## Width, residue, and upper-carry audit -/

/-- Exact width of the finite all-ones source word. -/
theorem bitWidth_rawAllOnesWitness
    (r : ℕ) :
    bitWidth (rawAllOnesWitness r).1 = r + 2 := by
  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
  have hlo : 2 ^ (r + 1) ≤ (rawAllOnesWitness r).1 := by
    rw [rawAllOnesWitness_val,
      show r + 2 = (r + 1) + 1 by omega, pow_succ]
    omega
  have hhi : (rawAllOnesWitness r).1 < 2 ^ ((r + 1) + 1) := by
    rw [rawAllOnesWitness_val,
      show (r + 1) + 1 = r + 2 by omega]
    have hpow : 0 < 2 ^ (r + 2) := pow_pos (by norm_num) _
    omega
  have h := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
  omega

/-- Exact width of the first all-ones successor. -/
theorem bitWidth_T_rawAllOnesWitness
    (r : ℕ) :
    bitWidth (T (rawAllOnesWitness r)).1 = r + 3 := by
  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
  have hlo : 2 ^ (r + 2) ≤ (T (rawAllOnesWitness r)).1 := by
    rw [T_rawAllOnesWitness_val]
    unfold rawAllOnesFirstTargetValue
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
    omega
  have hhi : (T (rawAllOnesWitness r)).1 < 2 ^ ((r + 2) + 1) := by
    rw [T_rawAllOnesWitness_val]
    unfold rawAllOnesFirstTargetValue
    have hpow : 2 ^ ((r + 2) + 1) = 4 * 2 ^ (r + 1) := by
      rw [show (r + 2) + 1 = (r + 1) + 2 by omega, pow_add]
      norm_num [Nat.mul_comm]
    rw [hpow]
    omega
  have h := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
  omega

/-- Exact width of the second all-ones successor. -/
theorem bitWidth_T_T_rawAllOnesWitness
    {r : ℕ} (hr : 1 ≤ r) :
    bitWidth (T (T (rawAllOnesWitness r))).1 = r + 4 := by
  have hp : 2 ≤ 2 ^ r := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hr
    rw [show 1 + q = q + 1 by omega, pow_succ]
    have hq : 0 < 2 ^ q := pow_pos (by norm_num) _
    omega
  have hlo : 2 ^ (r + 3) ≤ (T (T (rawAllOnesWitness r))).1 := by
    rw [T_T_rawAllOnesWitness_val hr]
    unfold rawAllOnesSecondTargetValue
    rw [pow_add]
    norm_num
    omega
  have hhi : (T (T (rawAllOnesWitness r))).1 < 2 ^ ((r + 3) + 1) := by
    rw [T_T_rawAllOnesWitness_val hr]
    unfold rawAllOnesSecondTargetValue
    rw [show (r + 3) + 1 = r + 4 by omega, pow_add]
    norm_num
    omega
  have h := bitWidth_eq_add_one_of_pow_le_lt hlo hhi
  omega

/-- The first edge increases binary width by exactly one. -/
theorem bitWidth_T_rawAllOnesWitness_eq_add_one
    (r : ℕ) :
    bitWidth (T (rawAllOnesWitness r)).1 =
      bitWidth (rawAllOnesWitness r).1 + 1 := by
  rw [bitWidth_T_rawAllOnesWitness, bitWidth_rawAllOnesWitness]

/-- The second edge also increases binary width by exactly one. -/
theorem bitWidth_T_T_rawAllOnesWitness_eq_add_one
    {r : ℕ} (hr : 1 ≤ r) :
    bitWidth (T (T (rawAllOnesWitness r))).1 =
      bitWidth (T (rawAllOnesWitness r)).1 + 1 := by
  rw [bitWidth_T_T_rawAllOnesWitness hr, bitWidth_T_rawAllOnesWitness]

private theorem mul_add_pred_mod_self
    {m c : ℕ} (hm : 0 < m) :
    (c * m + (m - 1)) % m = m - 1 := by
  have hlt : m - 1 < m := by omega
  simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]

/-- The source shows an all-ones residue in every fixed lower `r`-window. -/
theorem rawAllOnesWitness_mod_pow
    (r : ℕ) :
    (rawAllOnesWitness r).1 % 2 ^ r = 2 ^ r - 1 := by
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  have hval : (rawAllOnesWitness r).1 =
      3 * 2 ^ r + (2 ^ r - 1) := by
    rw [rawAllOnesWitness_val,
      show r + 2 = r + 2 by rfl, pow_add]
    norm_num
    omega
  rw [hval]
  exact mul_add_pred_mod_self hp

/-- The first target has the same all-ones lower `r`-window. -/
theorem T_rawAllOnesWitness_mod_pow
    (r : ℕ) :
    (T (rawAllOnesWitness r)).1 % 2 ^ r = 2 ^ r - 1 := by
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  have hval : (T (rawAllOnesWitness r)).1 =
      5 * 2 ^ r + (2 ^ r - 1) := by
    rw [T_rawAllOnesWitness_val]
    unfold rawAllOnesFirstTargetValue
    rw [show r + 1 = r + 1 by rfl, pow_add]
    norm_num
    omega
  rw [hval]
  exact mul_add_pred_mod_self hp

/-- The source own-width raw step crosses the next binary boundary. -/
theorem stateUpperCarry_rawAllOnesWitness_eq_two
    (r : ℕ) :
    stateUpperCarry (rawAllOnesWitness r).1 = 2 := by
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry
    (rawAllOnesWitness r)
  rw [s_rawAllOnesWitness_eq_one,
    bitWidth_T_rawAllOnesWitness_eq_add_one] at hbalance
  omega

/-- The first target also has own-width upper carry two. -/
theorem stateUpperCarry_T_rawAllOnesWitness_eq_two
    {r : ℕ} (hr : 1 ≤ r) :
    stateUpperCarry (T (rawAllOnesWitness r)).1 = 2 := by
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry
    (T (rawAllOnesWitness r))
  rw [s_T_rawAllOnesWitness_eq_one hr,
    bitWidth_T_T_rawAllOnesWitness_eq_add_one hr] at hbalance
  omega

/-! ## The audited finite low signature -/

/-- Coarse 2-adic height class retained by the low signature. -/
inductive RawLowHeightClass where
  | one
  | atLeastTwo
  deriving DecidableEq, Fintype

/--
The deliberately fixed observation under audit.  It contains only a lower
`r`-bit residue, own-width upper carry, the split `s = 1` versus `s ≥ 2`, and
whether the next accelerated step increases width.  No absolute width or
upper-boundary coordinate is retained.
-/
structure FixedLowRawSignature (r : ℕ) where
  residue : Fin (2 ^ r)
  upperCarry : Fin 3
  heightClass : RawLowHeightClass
  widthGrowth : Bool
  deriving DecidableEq, Fintype

/-- The four-coordinate finite observation of one positive odd state. -/
noncomputable def fixedLowRawSignature
    (r : ℕ) (x : OddNat) : FixedLowRawSignature r where
  residue := ⟨x.1 % 2 ^ r, Nat.mod_lt _ (pow_pos (by norm_num) _)⟩
  upperCarry := ⟨stateUpperCarry x.1,
    upperCarry3n1_lt_three_of_lt_pow (lt_pow_bitWidth (by
      have hodd := x.2
      omega))⟩
  heightClass := if s x = 1 then .one else .atLeastTwo
  widthGrowth := decide (bitWidth (T x).1 = bitWidth x.1 + 1)

/-- The all-ones edge is closed under every coordinate of the audited fixed
low signature. -/
theorem fixedLowRawSignature_T_rawAllOnesWitness_eq
    {r : ℕ} (hr : 1 ≤ r) :
    fixedLowRawSignature r (T (rawAllOnesWitness r)) =
      fixedLowRawSignature r (rawAllOnesWitness r) := by
  unfold fixedLowRawSignature
  congr 1
  · apply Fin.ext
    exact T_rawAllOnesWitness_mod_pow r |>.trans
      (rawAllOnesWitness_mod_pow r).symm
  · apply Fin.ext
    change stateUpperCarry (T (rawAllOnesWitness r)).1 =
      stateUpperCarry (rawAllOnesWitness r).1
    rw [stateUpperCarry_T_rawAllOnesWitness_eq_two hr,
      stateUpperCarry_rawAllOnesWitness_eq_two]
  · simp [s_T_rawAllOnesWitness_eq_one hr,
      s_rawAllOnesWitness_eq_one]
  · simp [bitWidth_T_rawAllOnesWitness_eq_add_one,
      bitWidth_T_T_rawAllOnesWitness_eq_add_one hr]

/-- Signed binary-width change on an arbitrary concrete edge. -/
def rawSignedWidthWeight (a b : OddNat) : ℤ :=
  (bitWidth b.1 : ℤ) - bitWidth a.1

/-- The closed-signature all-ones edge has positive realized weight `+1`. -/
theorem rawSignedWidthWeight_rawAllOnesWitness_eq_one
    (r : ℕ) :
    rawSignedWidthWeight (rawAllOnesWitness r)
      (T (rawAllOnesWitness r)) = 1 := by
  unfold rawSignedWidthWeight
  rw [bitWidth_T_rawAllOnesWitness_eq_add_one]
  omega

/-- Every realized accelerated odd edge increases binary width by at most one. -/
theorem rawSignedWidthWeight_T_le_one (x : OddNat) :
    rawSignedWidthWeight x (T x) ≤ 1 := by
  unfold rawSignedWidthWeight
  have hbalance := bitWidth_T_add_height_eq_bitWidth_add_upperCarry x
  have hheight := s_pos x
  have hxpos : 0 < x.1 := by
    have hodd := x.2
    omega
  have hcarry : stateUpperCarry x.1 ≤ 2 :=
    upperCarry3n1_le_two_of_lt_pow (lt_pow_bitWidth hxpos)
  omega

/-! ## First strict upper-boundary enrichment -/

/-- The exact normalized leading two-bit word of a positive natural. -/
def normalizedTopTwoBits (x : ℕ) : ℕ :=
  upperPrefix 2 x

/-- The all-ones source has normalized leading word `11₂`. -/
theorem normalizedTopTwoBits_rawAllOnesWitness_eq_three
    {r : ℕ} (hr : 1 ≤ r) :
    normalizedTopTwoBits (rawAllOnesWitness r).1 = 3 := by
  unfold normalizedTopTwoBits upperPrefix
  rw [bitWidth_rawAllOnesWitness r]
  have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
  have hpow : 2 ^ (r + 2) = 4 * 2 ^ r := by
    rw [pow_add]
    norm_num [Nat.mul_comm]
  rw [show r + 2 - 2 = r by omega]
  apply Nat.div_eq_of_lt_le
  · rw [rawAllOnesWitness_val, hpow]
    omega
  · rw [rawAllOnesWitness_val, hpow]
    omega

/-- Its height-one target has normalized leading word `10₂`. -/
theorem normalizedTopTwoBits_T_rawAllOnesWitness_eq_two
    {r : ℕ} (hr : 1 ≤ r) :
    normalizedTopTwoBits (T (rawAllOnesWitness r)).1 = 2 := by
  unfold normalizedTopTwoBits upperPrefix
  rw [bitWidth_T_rawAllOnesWitness]
  have hp : 0 < 2 ^ (r + 1) := pow_pos (by norm_num) _
  rw [show r + 3 - 2 = r + 1 by omega]
  apply Nat.div_eq_of_lt_le
  · rw [T_rawAllOnesWitness_val]
    unfold rawAllOnesFirstTargetValue
    omega
  · rw [T_rawAllOnesWitness_val]
    unfold rawAllOnesFirstTargetValue
    omega

/-- The normalized upper-boundary coordinate separates the cp-333 positive
closed edge.  This alone does not construct a bounded potential. -/
theorem normalizedTopTwoBits_T_rawAllOnesWitness_ne
    {r : ℕ} (hr : 1 ≤ r) :
    normalizedTopTwoBits (T (rawAllOnesWitness r)).1 ≠
      normalizedTopTwoBits (rawAllOnesWitness r).1 := by
  rw [normalizedTopTwoBits_T_rawAllOnesWitness_eq_two hr,
    normalizedTopTwoBits_rawAllOnesWitness_eq_three hr]
  norm_num

/-- First experimental strict refinement: fixed low data plus normalized
leading two bits.  Reduction modulo four is representational only; the
normalized observation is already a two-bit word on positive states. -/
structure FixedLowUpperBoundarySignature (r : ℕ) where
  low : FixedLowRawSignature r
  topTwo : Fin 4
  deriving DecidableEq, Fintype

/-- Enriched finite observation used for the next projected-graph audit. -/
noncomputable def fixedLowUpperBoundarySignature
    (r : ℕ) (x : OddNat) : FixedLowUpperBoundarySignature r where
  low := fixedLowRawSignature r x
  topTwo := ⟨normalizedTopTwoBits x.1 % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The strict enrichment removes the known all-ones positive self-loop. -/
theorem fixedLowUpperBoundarySignature_T_rawAllOnesWitness_ne
    {r : ℕ} (hr : 1 ≤ r) :
    fixedLowUpperBoundarySignature r (T (rawAllOnesWitness r)) ≠
      fixedLowUpperBoundarySignature r (rawAllOnesWitness r) := by
  intro h
  have htop := congrArg FixedLowUpperBoundarySignature.topTwo h
  apply congrArg Fin.val at htop
  change normalizedTopTwoBits (T (rawAllOnesWitness r)).1 % 4 =
    normalizedTopTwoBits (rawAllOnesWitness r).1 % 4 at htop
  rw [normalizedTopTwoBits_T_rawAllOnesWitness_eq_two hr,
    normalizedTopTwoBits_rawAllOnesWitness_eq_three hr] at htop
  norm_num at htop

/-! ## Enriched projected-cycle audit

The old all-ones self-loop is gone, but the realized signature-pair graph still
has a positive cycle.  Its two edges come from different concrete states,
which is sufficient: projected potential inequalities are attached to
signature pairs and therefore telescope around the projected cycle.
-/

/-- An odd state congruent to three modulo four has exact height one. -/
theorem s_eq_one_of_mod_four_eq_three
    {x : OddNat} (hmod : x.1 % 4 = 3) :
    s x = 1 := by
  have hpos := s_pos x
  have hnot : ¬ 2 ≤ s x := by
    intro htwo
    have hdiv : 4 ∣ 3 * x.1 + 1 :=
      (rawHeightLabel_two_le_iff_four_dvd_threeNPlusOne x.1).mp htwo
    have hone :=
      (odd_four_dvd_three_mul_add_one_iff_mod_four_eq_one x.2).mp hdiv
    omega
  omega

/-- First exact edge identification in the enriched `r = 1` cycle audit. -/
theorem fixedLowUpperBoundarySignature_T_55_eq_39 :
    fixedLowUpperBoundarySignature 1 (T (⟨55, by decide⟩ : OddNat)) =
      fixedLowUpperBoundarySignature 1 (⟨39, by decide⟩ : OddNat) := by
  let a : OddNat := ⟨55, by decide⟩
  let b : OddNat := ⟨83, by decide⟩
  let c : OddNat := ⟨39, by decide⟩
  let d : OddNat := ⟨125, by decide⟩
  let e : OddNat := ⟨59, by decide⟩
  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hb : s b = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hc : s c = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hTa : T a = b := by
    apply Subtype.ext
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
    norm_num [a, b]
  have hTb : T b = d := by
    apply Subtype.ext
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one b hb]
    norm_num [b, d]
  have hTc : T c = e := by
    apply Subtype.ext
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one c hc]
    norm_num [c, e]
  have wb : bitWidth b.1 = 7 := by decide
  have wc : bitWidth c.1 = 6 := by decide
  have wd : bitWidth d.1 = 7 := by decide
  have we : bitWidth e.1 = 6 := by decide
  change fixedLowUpperBoundarySignature 1 (T a) =
    fixedLowUpperBoundarySignature 1 c
  rw [hTa]
  unfold fixedLowUpperBoundarySignature
  congr 1
  · unfold fixedLowRawSignature
    congr 1
    · apply Fin.ext
      norm_num [b, c]
    · apply Fin.ext
      norm_num [stateUpperCarry, upperCarry3n1, wb, wc, b, c]
    · simp [hb, hc]
    · simp [hTb, hTc, wb, wc, wd, we]
  · apply Fin.ext
    norm_num [normalizedTopTwoBits, upperPrefix, wb, wc, b, c]

/-- Second exact edge identification closing the enriched `r = 1` cycle. -/
theorem fixedLowUpperBoundarySignature_T_39_eq_55 :
    fixedLowUpperBoundarySignature 1 (T (⟨39, by decide⟩ : OddNat)) =
      fixedLowUpperBoundarySignature 1 (⟨55, by decide⟩ : OddNat) := by
  let a : OddNat := ⟨39, by decide⟩
  let b : OddNat := ⟨59, by decide⟩
  let c : OddNat := ⟨55, by decide⟩
  let d : OddNat := ⟨89, by decide⟩
  let e : OddNat := ⟨83, by decide⟩
  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hb : s b = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hc : s c = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hTa : T a = b := by
    apply Subtype.ext
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
    norm_num [a, b]
  have hTb : T b = d := by
    apply Subtype.ext
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one b hb]
    norm_num [b, d]
  have hTc : T c = e := by
    apply Subtype.ext
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one c hc]
    norm_num [c, e]
  have wb : bitWidth b.1 = 6 := by decide
  have wc : bitWidth c.1 = 6 := by decide
  have wd : bitWidth d.1 = 7 := by decide
  have we : bitWidth e.1 = 7 := by decide
  change fixedLowUpperBoundarySignature 1 (T a) =
    fixedLowUpperBoundarySignature 1 c
  rw [hTa]
  unfold fixedLowUpperBoundarySignature
  congr 1
  · unfold fixedLowRawSignature
    congr 1
    · apply Fin.ext
      norm_num [b, c]
    · apply Fin.ext
      norm_num [stateUpperCarry, upperCarry3n1, wb, wc, b, c]
    · simp [hb, hc]
    · simp [hTb, hTc, wb, wc, wd, we]
  · apply Fin.ext
    norm_num [normalizedTopTwoBits, upperPrefix, wb, wc, b, c]

/-- The `55 -> 83` realized edge has signed width `+1`. -/
theorem rawSignedWidthWeight_55_eq_one :
    rawSignedWidthWeight (⟨55, by decide⟩ : OddNat)
      (T (⟨55, by decide⟩ : OddNat)) = 1 := by
  let a : OddNat := ⟨55, by decide⟩
  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hTa : (T a).1 = 83 := by
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
    norm_num [a]
  unfold rawSignedWidthWeight
  rw [hTa]
  decide

/-- The `39 -> 59` realized edge has signed width zero. -/
theorem rawSignedWidthWeight_39_eq_zero :
    rawSignedWidthWeight (⟨39, by decide⟩ : OddNat)
      (T (⟨39, by decide⟩ : OddNat)) = 0 := by
  let a : OddNat := ⟨39, by decide⟩
  have ha : s a = 1 := s_eq_one_of_mod_four_eq_three (by decide)
  have hTa : (T a).1 = 59 := by
    rw [T_val_eq_three_mul_add_one_div_two_of_s_eq_one a ha]
    norm_num [a]
  unfold rawSignedWidthWeight
  rw [hTa]
  decide

/-- Global transition coverage contract for the first enriched signature. -/
def CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignature
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      OddNat (FixedLowUpperBoundarySignature 1)) : Prop :=
  (∀ x, C.Step x (T x)) ∧
    (∀ x, C.signature x = fixedLowUpperBoundarySignature 1 x) ∧
      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))

/-- The normalized top-two-bit enrichment rejects the old self-loop but still
admits the positive projected cycle witnessed by `55 -> 83` and `39 -> 59`.
Consequently it cannot support a global sound bounded potential. -/
theorem not_coversAllRawOddTransitionsWithFixedLowUpperBoundarySignature
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      OddNat (FixedLowUpperBoundarySignature 1)) :
    ¬ CoversAllRawOddTransitionsWithFixedLowUpperBoundarySignature C := by
  rintro ⟨hstep, hsignature, hweight⟩
  let a : OddNat := ⟨55, by decide⟩
  let b : OddNat := ⟨39, by decide⟩
  have hab : C.signature (T a) = C.signature b := by
    rw [hsignature, hsignature]
    exact fixedLowUpperBoundarySignature_T_55_eq_39
  have hba : C.signature (T b) = C.signature a := by
    rw [hsignature, hsignature]
    exact fixedLowUpperBoundarySignature_T_39_eq_55
  have hactualAB := C.actual_le_projected a (T a) (hstep a)
  have hactualBA := C.actual_le_projected b (T b) (hstep b)
  have hpotentialAB := C.projected_le_potential_diff
    (C.signature a) (C.signature b)
  have hpotentialBA := C.projected_le_potential_diff
    (C.signature b) (C.signature a)
  rw [hab] at hactualAB
  rw [hba] at hactualBA
  rw [hweight, rawSignedWidthWeight_55_eq_one] at hactualAB
  rw [hweight, rawSignedWidthWeight_39_eq_zero] at hactualBA
  linarith

/-!
`CoversAllRawOddTransitionsWithFixedLowSignature` is intentionally stronger
than observing a finite table: it requires the certificate relation and its
actual edge weight to cover every accelerated odd transition, while fixing the
signature to the arithmetic observation above.  The following obstruction is
therefore structural and uniform in `r`, not a bounded-search result.
-/

/-- Coverage contract for the specific audited low signature. -/
def CoversAllRawOddTransitionsWithFixedLowSignature
    {r : ℕ}
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      OddNat (FixedLowRawSignature r)) : Prop :=
  (∀ x, C.Step x (T x)) ∧
    (∀ x, C.signature x = fixedLowRawSignature r x) ∧
      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))

/--
No bounded potential certificate on the fixed low signature can soundly cover
all positive odd transitions.  The all-ones source gives a related edge of
weight `+1` whose endpoint signatures coincide, whereas the potential axiom
forces every such projected edge to have weight at most zero.

This does not exclude a finite signature with an absolute upper-boundary
coordinate or a separately proved decreasing rank.
-/
theorem not_coversAllRawOddTransitionsWithFixedLowSignature
    {r : ℕ} (hr : 1 ≤ r)
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      OddNat (FixedLowRawSignature r)) :
    ¬ CoversAllRawOddTransitionsWithFixedLowSignature C := by
  rintro ⟨hstep, hsignature, hweight⟩
  let x := rawAllOnesWitness r
  have hsig : C.signature (T x) = C.signature x := by
    rw [hsignature, hsignature]
    exact fixedLowRawSignature_T_rawAllOnesWitness_eq hr
  apply C.false_of_step_of_signature_eq_of_actualWeight_pos (hstep x) hsig
  rw [hweight, rawSignedWidthWeight_rawAllOnesWitness_eq_one]
  norm_num

/-!
The obstruction survives every coarsening computed solely from the fixed low
signature.  The theorem does not cover a strict refinement carrying new upper
boundary information.
-/

/-- Coverage contract for an arbitrary finite coarsening of the audited fixed
low signature. -/
def CoversAllRawOddTransitionsThroughFixedLowSignature
    {r : ℕ} {Signature : Type*} [Fintype Signature]
    (f : FixedLowRawSignature r → Signature)
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      OddNat Signature) : Prop :=
  (∀ x, C.Step x (T x)) ∧
    (∀ x, C.signature x = f (fixedLowRawSignature r x)) ∧
      (∀ x, C.actualWeight x (T x) = rawSignedWidthWeight x (T x))

/-- No finite factor of the fixed low signature can remove its positive
closed-edge obstruction. -/
theorem not_coversAllRawOddTransitionsThroughFixedLowSignature
    {r : ℕ} (hr : 1 ≤ r)
    {Signature : Type*} [Fintype Signature]
    (f : FixedLowRawSignature r → Signature)
    (C : RelationalFiniteSignedTransitionPotentialCertificate
      OddNat Signature) :
    ¬ CoversAllRawOddTransitionsThroughFixedLowSignature f C := by
  rintro ⟨hstep, hsignature, hweight⟩
  let x := rawAllOnesWitness r
  have hlow := fixedLowRawSignature_T_rawAllOnesWitness_eq hr
  have hsig : C.signature (T x) = C.signature x := by
    rw [hsignature, hsignature, hlow]
  apply C.false_of_step_of_signature_eq_of_actualWeight_pos (hstep x) hsig
  rw [hweight, rawSignedWidthWeight_rawAllOnesWitness_eq_one]
  norm_num

/-- Existential form: the audited fixed low signature admits no global sound
bounded-potential certificate. -/
theorem not_exists_fixedLowRawSignature_globalCertificate
    {r : ℕ} (hr : 1 ≤ r) :
    ¬ ∃ C : RelationalFiniteSignedTransitionPotentialCertificate
        OddNat (FixedLowRawSignature r),
      CoversAllRawOddTransitionsWithFixedLowSignature C := by
  rintro ⟨C, hC⟩
  exact not_coversAllRawOddTransitionsWithFixedLowSignature hr C hC

end DkMath.Collatz

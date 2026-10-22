/-
Copyright (c) 2026 Anthropic, PBC.
Copyright (c) 2026 D. and Wise Wolf.
SPDX-License-Identifier: Apache-2.0
License: RegularKummer/LICENSE
Upstream notices: RegularKummer/ANTHROPIC-NOTICE
Four-state orbit induction adapted from S_WeierstrassCurve_valuation_pow_eq_of_torsion_of_not_inZeroComponentAt,
blob 94e0bb0c302237deddfc439eca64e6321c1f553c.
Modified: same DkMath C,D, arbitrary characteristic-zero valuation-ring model; odd unit order,
not necessarily prime; integral torsion return replaces an assumed general zero-component subgroup.
-/
import DkMath.Lib.NumberTheory.EllipticIntegralReturn
#print "file: DkMath.Lib.NumberTheory.EllipticTorsionDepth"
/-!
# NOTE-031-002: 同じ奇数torsion点の全倍点を四状態で追う
滑らか、浅い同枝、浅い反対枝、臨界側の四状態を、実際の加法で遷移させる。
全有限倍点の整性は除法多項式から供給し、零成分部分群の一般構成を経由しない。
nP=Oの端点で付値の冪の関係を得る。臨界側から始まる奇数軌道は端点が有限となり矛盾する。
-/
namespace DkMath.Lib.NumberTheory.EllipticTorsionDepth
open WeierstrassCurve Affine Affine.Point EllipticCriticalCentre EllipticCriticalCentreAlgebra
open EllipticTangentDirections EllipticShallowSlope EllipticAdditionDepth EllipticOppositeDepth EllipticCriticalAddition
open EllipticCriticalPair EllipticIntegralReturn EllipticGoodReductionSeparation
variable {K : Type*} [Field K] {A : ValuationSubring K} (M : WeierstrassCurve A)
local notation "V" => M.map A.subtype
local notation "v" => A.valuation
/-- 滑らかに還元するn倍零点に近傍点を加える。有限座標の整性をnの単元性から供給し、
無限遠点の場合も同じ実際の点群で処理する。 -/
theorem smooth_torsion_add_preserves [CharZero K] [DecidableEq K] (C : CriticalCentre A (V)) (D : TangentDirections C)
    {n : ℕ} (hn : v (n : K) = 1) (P : (V).toAffine.Point) (hkill : n • P = 0)
    (hP : HasSmoothReduction M P) {x₂ y₂ : K} (h₂ : (V).toAffine.Nonsingular x₂ y₂)
    (hX₂ : v (x₂ - C.x) < 1) :
    ∃ (x₃ y₃ : K) (h₃ : (V).toAffine.Nonsingular x₃ y₃),
      P + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧ v (x₃ - C.x) < 1 ∧
      (v (equationDefect (V) C.x C.y) < v (x₂ - C.x) ^ 2 →
        v (x₃ - C.x) = v (x₂ - C.x) ∧ v (centreSlope C x₃ y₃ - centreSlope C x₂ y₂) < 1) ∧
      (v (x₂ - C.x) ^ 2 ≤ v (equationDefect (V) C.x C.y) →
        v (x₃ - C.x) ^ 2 ≤ v (equationDefect (V) C.x C.y)) := by
  cases P with
  | zero =>
    refine ⟨x₂, y₂, h₂, zero_add _, hX₂, fun _ => ⟨rfl, ?_⟩, fun ha => ha⟩
    rw [sub_self, _root_.map_zero]
    exact zero_lt_one
  | some x₁ y₁ h₁ =>
    have hx := EllipticTorsionValuationIntegrality.torsion_x_mem A M _ rfl hn h₁ hkill
    exact integral_smooth_add_preserves M C D h₁ h₂ hP hx hX₂
-- 状態遷移に伴う指数台帳。jは中心のずれを跨いだ回数を記録し、mは実際の倍点添字である。
section Helpers
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
private theorem cancel_strict_right {a b c : Γ₀} (h : a * c < b * c) : a < b := by
  by_contra hle
  exact absurd h (not_lt.mpr (mul_le_mul' (not_lt.mp hle) le_rfl))
private theorem power_injective {a b : Γ₀} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = b ^ n) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (ne_of_lt (pow_lt_pow_left₀ hab zero_le hn))
  · exact hab
  · exact absurd h (ne_of_gt (pow_lt_pow_left₀ hab zero_le hn))
private theorem advance_same_ledger {F L M N : Γ₀} {j m : ℕ} (hj : M ^ 2 * F ^ (2 * j) = L ^ (2 * m)) (hN : N = M * L) :
    N ^ 2 * F ^ (2 * j) = L ^ (2 * (m + 1)) := by
  rw [hN, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, ← hj, mul_pow]
  simp only [sq, mul_comm, mul_left_comm, mul_assoc]
private theorem enter_critical_ledger {F L M : Γ₀} {j m : ℕ} (hj : M ^ 2 * F ^ (2 * j) = L ^ (2 * m)) (hF : F = (M * L) ^ 2) :
    F ^ (2 * j + 1) = L ^ (2 * (m + 1)) := by
  calc F ^ (2 * j + 1) = F ^ (2 * j) * F := pow_succ F (2 * j)
    _ = F ^ (2 * j) * (M * L) ^ 2 := by rw [← hF]
    _ = (M ^ 2 * F ^ (2 * j)) * L ^ 2 := by simp only [sq, mul_comm, mul_left_comm, mul_assoc]
    _ = L ^ (2 * m) * L ^ 2 := by rw [hj]
    _ = L ^ (2 * (m + 1)) := by rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
private theorem cross_opposite_ledger {F L M N : Γ₀} {j m : ℕ} (hj : M ^ 2 * F ^ (2 * j) = L ^ (2 * m)) (hN : N * (M * L) = F)
    (hML : M * L ≠ 0) : F ^ (2 * j + 2) = L ^ (2 * (m + 1)) * N ^ 2 := by
  have key : F ^ (2 * j + 2) * (M * L) ^ 2 = L ^ (2 * (m + 1)) * N ^ 2 * (M * L) ^ 2 := by
    calc F ^ (2 * j + 2) * (M * L) ^ 2 = F ^ (2 * j) * F ^ 2 * (M * L) ^ 2 := by rw [pow_add]
      _ = (M ^ 2 * F ^ (2 * j)) * L ^ 2 * (N * (M * L)) ^ 2 := by
          rw [hN]; simp only [sq, mul_comm, mul_left_comm, mul_assoc]
      _ = L ^ (2 * m) * L ^ 2 * (N * (M * L)) ^ 2 := by rw [hj]
      _ = L ^ (2 * (m + 1)) * N ^ 2 * (M * L) ^ 2 := by
          rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
          simp only [sq, mul_comm, mul_left_comm, mul_assoc]
  exact mul_right_cancel₀ (pow_ne_zero 2 hML) key
private theorem continue_opposite_ledger {F L M N : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 2) = L ^ (2 * m) * M ^ 2) (hN : N * L = M) :
    F ^ (2 * j + 2) = L ^ (2 * (m + 1)) * N ^ 2 := by
  rw [hj, ← hN, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, mul_pow]
  simp only [sq, mul_comm, mul_left_comm, mul_assoc]
private theorem return_smooth_ledger {F L M : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 2) = L ^ (2 * m) * M ^ 2) (hM : M = L) :
    F ^ (2 * (j + 1)) = L ^ (2 * (m + 1)) := by
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, hj, hM, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
private theorem cross_same_ledger {F L M N : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 2) = L ^ (2 * m) * M ^ 2) (hN : N * M = L)
    (hM : M ≠ 0) : N ^ 2 * F ^ (2 * (j + 1)) = L ^ (2 * (m + 1)) := by
  have key : N ^ 2 * F ^ (2 * (j + 1)) * M ^ 2 = L ^ (2 * (m + 1)) * M ^ 2 := by
    calc N ^ 2 * F ^ (2 * (j + 1)) * M ^ 2 = (N * M) ^ 2 * F ^ (2 * j + 2) := by
          rw [show 2 * (j + 1) = 2 * j + 2 by ring, mul_pow]
          simp only [sq, mul_comm, mul_left_comm, mul_assoc]
      _ = L ^ 2 * (L ^ (2 * m) * M ^ 2) := by rw [hN, hj]
      _ = L ^ (2 * (m + 1)) * M ^ 2 := by
          rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
          simp only [sq, mul_comm, mul_left_comm, mul_assoc]
  exact mul_right_cancel₀ (pow_ne_zero 2 hM) key
private theorem leave_critical_ledger {F L N : Γ₀} {j m : ℕ} (hj : F ^ (2 * j + 1) = L ^ (2 * m)) (hN : (N * L) ^ 2 = F) :
    F ^ (2 * j + 2) = L ^ (2 * (m + 1)) * N ^ 2 := by
  rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, pow_succ, hj, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add,
    ← hN, mul_pow]
  simp only [sq, mul_comm, mul_left_comm, mul_assoc]
private theorem shallow_from_crossing {F N P : Γ₀} (hN : N * P = F) (hlt : P ^ 2 < F) (hF : 0 < F) : F < N ^ 2 := by
  have hP0 : 0 < P := by
    rcases eq_or_lt_of_le (zero_le : (0:Γ₀) ≤ P) with h0 | h0
    · rw [← h0, mul_zero] at hN; rw [hN] at hF; exact absurd hF (lt_irrefl _)
    · exact h0
  have h1 : P * P < N * P := by rw [hN, ← sq]; exact hlt
  have h2 : P < N := cancel_strict_right h1
  calc F = N * P := hN.symm
    _ < N * N := by
        have hN0 : 0 < N := lt_of_le_of_lt zero_le h2
        have := mul_lt_mul_of_pos_right h2 hN0
        rwa [mul_comm P N] at this
    _ = N ^ 2 := (sq N).symm
private theorem shallow_from_opposite_step {F L M N : Γ₀} (hN : N * L = M) (hF : F < M ^ 2) (hL1 : L < 1)
    (hML : M < L) : F < N ^ 2 ∧ N < 1 := by
  have hMN : M ≤ N := by
    rw [← hN]
    calc N * L ≤ N * 1 := mul_le_mul' le_rfl (le_of_lt hL1)
      _ = N := mul_one N
  constructor
  · calc F < M ^ 2 := hF
      _ ≤ N ^ 2 := pow_le_pow_left₀ zero_le hMN 2
  · have : N * L < 1 * L := by rw [hN, one_mul]; exact hML
    exact cancel_strict_right this
private theorem shallow_from_reversed_step {F L M N : Γ₀} (hN : N * M = L) (hF : F < L ^ 2) (hM1 : M < 1)
    (hLM : L < M) : F < N ^ 2 ∧ N < 1 := by
  have hLN : L ≤ N := by
    rw [← hN]
    calc N * M ≤ N * 1 := mul_le_mul' le_rfl (le_of_lt hM1)
      _ = N := mul_one N
  constructor
  · calc F < L ^ 2 := hF
      _ ≤ N ^ 2 := pow_le_pow_left₀ zero_le hLN 2
  · have : N * M < 1 * M := by rw [hN, one_mul]; exact hLM
    exact cancel_strict_right this
private theorem shallow_from_critical_step {F L N : Γ₀} (hN : (N * L) ^ 2 = F) (hF : F < L ^ 2) (hF0 : 0 < F) (hL1 : L < 1) :
    F < N ^ 2 ∧ N < 1 := by
  have hN1 : N < 1 := by
    have : (N * L) ^ 2 < (1 * L) ^ 2 := by rw [hN, one_mul]; exact hF
    by_contra hle
    have hle' : 1 * L ≤ N * L := mul_le_mul' (not_lt.mp hle) le_rfl
    exact absurd this (not_lt.mpr (pow_le_pow_left₀ zero_le hle' 2))
  have hN0 : 0 < N := by
    rcases eq_or_lt_of_le (zero_le : (0:Γ₀) ≤ N) with h0 | h0
    · rw [← h0, zero_mul, zero_pow two_ne_zero] at hN
      rw [← hN] at hF0
      exact absurd hF0 (lt_irrefl _)
    · exact h0
  refine ⟨?_, hN1⟩
  rw [← hN, mul_pow]
  calc N ^ 2 * L ^ 2 < N ^ 2 * 1 := by
        apply mul_lt_mul_of_pos_left _ (pow_pos hN0 2)
        exact pow_lt_one₀ zero_le hL1 two_ne_zero
    _ = N ^ 2 := mul_one _
end Helpers
/-- 単元の奇数nで零になる実際の有限点は浅く、その深さはF₀との有理比に制限される。
全倍点の座標整性を既存の除法多項式から供給し、実際の加法遷移で四状態の帰納を閉じる。
nの素数性は不要で、奇数・3以上・単元という条件だけを使う。 -/
theorem odd_torsion_depth [CharZero K] [DecidableEq K] (C : CriticalCentre A (V)) (D : TangentDirections C)
    {ℓ : ℕ} (hodd : Odd ℓ) (hℓ3 : 3 ≤ ℓ) (hunit : v (ℓ : K) = 1)
    {x y : K} (h : (V).toAffine.Nonsingular x y)
    (htor : ℓ • Point.some x y h = 0) (hX : v (x - C.x) < 1) :
    v (equationDefect (V) C.x C.y) < v (x - C.x) ^ 2 ∧
      ∃ j : ℕ, 1 ≤ j ∧ 2 * j < ℓ ∧ v (x - C.x) ^ ℓ = v (equationDefect (V) C.x C.y) ^ j := by
  classical
  have hkill : ∀ m : ℕ, ℓ • (m • Point.some x y h) = 0 := by
    intro m
    rw [smul_smul, Nat.mul_comm, ← smul_smul, htor, smul_zero]
  obtain ⟨vF, hvF⟩ : ∃ g, A.valuation (equationDefect (V) C.x C.y) = g := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ g, A.valuation (x - C.x) = g := ⟨_, rfl⟩
  rw [hvF, hL]
  have hvF1 : vF < 1 := hvF ▸ C.defect_small
  have hL1 : L < 1 := hL ▸ hX
  have hvF0 : 0 < vF := by
    rw [← hvF]
    exact (Valuation.pos_iff _).mpr C.defect_ne_zero
  have same_same : ∀ {a b c : K}, A.valuation (a - b) < 1 → A.valuation (b - c) < 1 →
      A.valuation (a - c) < 1 := by
    intro a b c h1 h2
    have := Valuation.map_add_lt A.valuation h1 h2
    rwa [show a - b + (b - c) = a - c by ring] at this
  have opp_same : ∀ {a b c : K}, A.valuation (a - b) = 1 → A.valuation (b - c) < 1 →
      A.valuation (a - c) = 1 := by
    intro a b c h1 h2
    have h2' : A.valuation (b - c) < A.valuation (a - b) := by rwa [h1]
    have := Valuation.map_add_eq_of_lt_left A.valuation h2'
    rw [show a - b + (b - c) = a - c by ring] at this
    rw [this, h1]
  have same_opp : ∀ {a b c : K}, A.valuation (a - b) < 1 → A.valuation (b - c) = 1 →
      A.valuation (a - c) = 1 := by
    intro a b c h1 h2
    have h1' : A.valuation (a - b) < A.valuation (b - c) := by rwa [h2]
    have := Valuation.map_add_eq_of_lt_right A.valuation h1'
    rw [show a - b + (b - c) = a - c by ring] at this
    rw [this, h2]
  rcases lt_or_ge vF (L ^ 2) with hsh | hanti
  · have hshR : A.valuation (equationDefect (V) C.x C.y) < A.valuation (x - C.x) ^ 2 := by
      rw [hvF, hL]; exact hsh
    -- 滑らか・同枝・反対枝・臨界側の四状態を、(m+1)P=mP+Pで同時に帰納する。
    have main : ∀ m : ℕ, 1 ≤ m →
        (HasSmoothReduction M (m • Point.some x y h) ∧ ∃ j : ℕ, vF ^ (2 * j) = L ^ (2 * m)) ∨
        (∃ (x' y' : K)
            (h' : (V).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - C.x) < 1 ∧
            vF < A.valuation (x' - C.x) ^ 2 ∧
            A.valuation ((y' - C.y) / (x' - C.x) - (y - C.y) / (x - C.x)) < 1 ∧
            ∃ j : ℕ, A.valuation (x' - C.x) ^ 2 * vF ^ (2 * j) = L ^ (2 * m)) ∨
        (∃ (x' y' : K)
            (h' : (V).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - C.x) < 1 ∧
            vF < A.valuation (x' - C.x) ^ 2 ∧
            A.valuation ((y' - C.y) / (x' - C.x) - (y - C.y) / (x - C.x)) = 1 ∧
            ∃ j : ℕ, vF ^ (2 * j + 2) = L ^ (2 * m) * A.valuation (x' - C.x) ^ 2) ∨
        (∃ (x' y' : K)
            (h' : (V).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - C.x) < 1 ∧
            A.valuation (x' - C.x) ^ 2 ≤ vF ∧
            ∃ j : ℕ, vF ^ (2 * j + 1) = L ^ (2 * m)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        refine Or.inr (Or.inl ⟨x, y, h, one_nsmul _, hX, ?_, ?_, 0, ?_⟩)
        · rw [hL]; exact hsh
        · rw [sub_self, Valuation.map_zero]; exact zero_lt_one
        · rw [hL]; simp
      | succ m hm ih =>
        rw [succ_nsmul]
        rcases ih with ⟨hE0, j, hj⟩ | ⟨x', y', h', hmP, hX', hsh', hbr', j, hj⟩ |
            ⟨x', y', h', hmP, hX', hsh', hbr', j, hj⟩ | ⟨x', y', h', hmP, hX', hanti', j, hj⟩
        · obtain ⟨x₃, y₃, h₃, hsum, hX₃, hshcl, -⟩ :=
            smooth_torsion_add_preserves M C D hunit
              (m • Point.some x y h) (hkill m) hE0 h hX
          obtain ⟨hlev₃, hbr₃⟩ := hshcl hshR
          rw [hL] at hlev₃
          refine Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, ?_, hbr₃, j, ?_⟩)
          · rw [hlev₃]; exact hsh
          · rw [hlev₃, show 2 * (m + 1) = 2 * m + 2 by ring, pow_add, ← hj]
            simp only [sq, mul_comm, mul_assoc]
        · have hshR' : A.valuation (equationDefect (V) C.x C.y) < A.valuation (x' - C.x) ^ 2 := by
            rw [hvF]; exact hsh'
          obtain ⟨x₃, y₃, h₃, hsum, hX₃, hci, hcii, hciii⟩ :=
            same_branch_add C D h' h hX' hX hshR' hshR hbr'
          rw [hvF, hL] at hci hcii hciii
          rw [hmP]
          rcases lt_trichotomy vF ((A.valuation (x' - C.x) * L) ^ 2) with hc | hc | hc
          · obtain ⟨hlev₃, hbr₃⟩ := hci hc
            refine Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, ?_, same_same hbr₃ hbr', j, advance_same_ledger hj hlev₃⟩)
            rw [hlev₃]; exact hc
          · exact Or.inr (Or.inr (Or.inr ⟨x₃, y₃, h₃, hsum, hX₃, hcii hc, j, enter_critical_ledger hj hc⟩))
          · obtain ⟨hlev₃, hbr₃⟩ := hciii hc
            have hML : A.valuation (x' - C.x) * L ≠ 0 := by
              intro h0
              rw [h0, mul_zero] at hlev₃
              exact absurd hlev₃ (ne_of_gt hvF0).symm
            exact Or.inr (Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, shallow_from_crossing hlev₃ hc hvF0,
              opp_same hbr₃ hbr', j, cross_opposite_ledger hj hlev₃ hML⟩))
        · have hshR' : A.valuation (equationDefect (V) C.x C.y) < A.valuation (x' - C.x) ^ 2 := by
            rw [hvF]; exact hsh'
          rw [hmP]
          rcases lt_trichotomy (A.valuation (x' - C.x)) L with hc | hc | hc
          · have hcR : A.valuation (x' - C.x) < A.valuation (x - C.x) := by rw [hL]; exact hc
            obtain ⟨x₃, y₃, h₃, hsum, hlev₃, hbr₃⟩ :=
              opposite_branch_add_of_depth_lt C
                h' h hX hcR hshR' hbr'
            rw [hL] at hlev₃
            obtain ⟨hsh₃, hX₃⟩ := shallow_from_opposite_step hlev₃ hsh' hL1 hc
            exact Or.inr (Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, hsh₃, same_opp hbr₃ hbr', j,
              continue_opposite_ledger hj hlev₃⟩))
          · have hcR : A.valuation (x' - C.x) = A.valuation (x - C.x) := by rw [hL]; exact hc
            have hE0 := (EllipticBranchComparison.add_of_opposite_branch M C D h' h hX' hX hcR hshR' hbr').1
            exact Or.inl ⟨hE0, j + 1, return_smooth_ledger hj hc⟩
          · have hbr'' : A.valuation ((y - C.y) / (x - C.x) - (y' - C.y) / (x' - C.x)) = 1 := by
              rw [Valuation.map_sub_swap]; exact hbr'
            have hcR : A.valuation (x - C.x) < A.valuation (x' - C.x) := by rw [hL]; exact hc
            obtain ⟨x₃, y₃, h₃, hsum, hlev₃, hbr₃⟩ :=
              opposite_branch_add_of_depth_lt C
                h h' hX' hcR hshR hbr''
            rw [add_comm] at hsum
            rw [hL] at hlev₃
            have hM0 : A.valuation (x' - C.x) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hc)
            obtain ⟨hsh₃, hX₃⟩ := shallow_from_reversed_step hlev₃ hsh hX' hc
            exact Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, hsh₃, hbr₃, j + 1, cross_same_ledger hj hlev₃ hM0⟩)
        · have hantiR : A.valuation (x' - C.x) ^ 2 ≤ A.valuation (equationDefect (V) C.x C.y) := by
            rw [hvF]; exact hanti'
          rw [hmP]
          obtain ⟨x₃, y₃, h₃, hsum, hlev₃, hbr₃⟩ :=
            critical_add_shallow C D
              h' h hX' hantiR hX hshR
          rw [hvF, hL] at hlev₃
          obtain ⟨hsh₃, hX₃⟩ := shallow_from_critical_step hlev₃ hsh hvF0 hL1
          exact Or.inr (Or.inr (Or.inl ⟨x₃, y₃, h₃, hsum, hX₃, hsh₃, hbr₃, j, leave_critical_ledger hj hlev₃⟩))
    -- nP=Oは有限座標の三状態を除き、滑らかな状態の冪の台帳だけを残す。
    have hfin := main ℓ (by omega)
    rw [htor] at hfin
    rcases hfin with ⟨-, j, hj⟩ | ⟨x', y', h', h0, -⟩ | ⟨x', y', h', h0, -⟩ | ⟨x', y', h', h0, -⟩
    · have hjℓ : vF ^ j = L ^ ℓ := by
        apply power_injective (n := 2) two_ne_zero
        rw [← pow_mul, ← pow_mul, mul_comm j 2, mul_comm ℓ 2, hj]
      refine ⟨hsh, j, ?_, ?_, hjℓ.symm⟩
      · by_contra hj0
        have hj0 : j = 0 := by omega
        rw [hj0, pow_zero] at hjℓ
        exact absurd hjℓ (ne_of_gt (pow_lt_one₀ zero_le hL1 (by omega)))
      · by_contra hle
        have hle : ℓ ≤ 2 * j := by omega
        have h1 : vF ^ j < (L ^ 2) ^ j := pow_lt_pow_left₀ hsh zero_le (by omega)
        rw [← pow_mul, hjℓ] at h1
        have h2 : L ^ (2 * j) ≤ L ^ ℓ := pow_le_pow_right_of_le_one' (le_of_lt hL1) hle
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    · exact absurd h0.symm (Point.some_ne_zero h')
    · exact absurd h0.symm (Point.some_ne_zero h')
    · exact absurd h0.symm (Point.some_ne_zero h')
  · exfalso
    have hantiR : A.valuation (x - C.x) ^ 2 ≤ A.valuation (equationDefect (V) C.x C.y) := by
      rw [hvF, hL]; exact hanti
    -- 臨界側から始まる場合は、奇数倍が有限の臨界側、偶数倍が滑らかな側へ交互に移る。
    have alt : ∀ m : ℕ, 1 ≤ m →
        (Odd m → ∃ (x' y' : K)
            (h' : (V).toAffine.Nonsingular x' y'),
            m • Point.some x y h = .some x' y' h' ∧ A.valuation (x' - C.x) < 1 ∧
            A.valuation (x' - C.x) ^ 2 ≤ A.valuation (equationDefect (V) C.x C.y)) ∧
        (Even m → HasSmoothReduction M (m • Point.some x y h)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        refine ⟨fun _ => ⟨x, y, h, one_nsmul _, hX, hantiR⟩, fun h1 => ?_⟩
        exact absurd h1 (by decide)
      | succ m hm ih =>
        rw [succ_nsmul]
        refine ⟨fun hodd => ?_, fun heven => ?_⟩
        · have hev : Even m := by
            rcases Nat.even_or_odd m with he | ho
            · exact he
            · exact absurd hodd (Nat.not_odd_iff_even.mpr (ho.add_one))
          obtain ⟨x₃, y₃, h₃, hsum, hX₃, -, hanticl⟩ :=
            smooth_torsion_add_preserves M C D hunit
              (m • Point.some x y h) (hkill m) (ih.2 hev) h hX
          exact ⟨x₃, y₃, h₃, hsum, hX₃, hanticl hantiR⟩
        · have hodd : Odd m := by
            rcases Nat.even_or_odd m with he | ho
            · exact absurd heven (Nat.not_even_iff_odd.mpr (he.add_one))
            · exact ho
          obtain ⟨x', y', h', hmP, hX', hanti'⟩ := ih.1 hodd
          rw [hmP]
          exact critical_pair_smooth M C D
            h' h hX' hanti' hX hantiR
    have hℓodd : Odd ℓ := hodd
    obtain ⟨x', y', h', h0, -⟩ := (alt ℓ (by omega)).1 hℓodd
    rw [htor] at h0
    exact absurd h0.symm (Point.some_ne_zero h')
/-- 一般ファイバーのモデル一致を明示し、同じC,Dと実際のtorsion点のまま深さの結論を輸送する。 -/
theorem odd_torsion_depth_of_model [CharZero K] [DecidableEq K]
    (E : WeierstrassCurve K) (hmodel : M.map A.subtype = E) (C : CriticalCentre A E) (D : TangentDirections C)
    {ℓ : ℕ} (hodd : Odd ℓ) (hℓ3 : 3 ≤ ℓ) (hunit : v (ℓ : K) = 1)
    {x y : K} (h : E.toAffine.Nonsingular x y)
    (htor : ℓ • Point.some x y h = 0) (hX : v (x - C.x) < 1) :
    v (equationDefect E C.x C.y) < v (x - C.x) ^ 2 ∧
      ∃ j : ℕ, 1 ≤ j ∧ 2 * j < ℓ ∧ v (x - C.x) ^ ℓ = v (equationDefect E C.x C.y) ^ j := by
  subst E
  exact odd_torsion_depth M C D hodd hℓ3 hunit h htor hX

end DkMath.Lib.NumberTheory.EllipticTorsionDepth

/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.CFBRC.TrigBridge.General
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Sum

#print "file: DkMath.CFBRC.TrigBridge.ClosedForm"

open scoped BigOperators

namespace DkMath.CFBRC.TrigBridge

noncomputable section

/--
`cfbrcR d X Θ` の choose 形式（複素和）。

`(X+iΘ)^d - (iΘ)^d` の二項展開から、`k=0` 項を取り除いた形。
各項に `X` が残るよう `k+1` で添字を振っている。
-/
def cfbrcClosed (d : ℕ) (X Θ : ℝ) : ℂ :=
  ∑ k ∈ Finset.range d,
    (X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) * (Nat.choose d (k + 1) : ℂ)

/--
`cfbrcClosed` を `Nat.choose` 行（係数先頭）として読み替えた一般形。

回帰テストで低次数の係数列を自動展開する際の基準補題として使う。
-/
lemma cfbrcClosed_choose_row (d : ℕ) (X Θ : ℝ) :
    cfbrcClosed d X Θ =
      ∑ k ∈ Finset.range d,
        (Nat.choose d (k + 1) : ℂ) * (X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) := by
  unfold cfbrcClosed
  refine Finset.sum_congr rfl ?_
  intro k hk
  ring

/--
`cfbrcR` は `cfbrcClosed`（choose 形式）に一致する。
-/
lemma cfbrcR_eq_cfbrcClosed (d : ℕ) (X Θ : ℝ) :
    cfbrcR d X Θ = cfbrcClosed d X Θ := by
  unfold cfbrcR cfbrc cfbrcClosed
  rw [add_pow]
  have hsplit :
      ∑ m ∈ Finset.range (d + 1),
          (X : ℂ) ^ m * (Complex.I * Θ) ^ (d - m) * (Nat.choose d m : ℂ)
        = (X : ℂ) ^ 0 * (Complex.I * Θ) ^ d * (Nat.choose d 0 : ℂ) +
          ∑ k ∈ Finset.range d,
            (X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) *
              (Nat.choose d (k + 1) : ℂ) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    have hsub : d - (k + 1) = d - 1 - k := by omega
    rw [hsub]
  rw [hsplit]
  simp

/--
`cfbrcClosed` の実部（raw 版）。

偶奇分離前の形として、複素位相項の実部をそのまま保持する。
-/
def cfbrcReClosedRaw (d : ℕ) (X Θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k)) * (Nat.choose d (k + 1) : ℝ)

/--
`cfbrcClosed` の虚部（raw 版）。

偶奇分離前の形として、複素位相項の虚部をそのまま保持する。
-/
def cfbrcImClosedRaw (d : ℕ) (X Θ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range d,
    X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k)) * (Nat.choose d (k + 1) : ℝ)

/--
`cfbrcRe` は `cfbrcReClosedRaw` に一致する。
-/
lemma cfbrcRe_eq_cfbrcReClosedRaw (d : ℕ) (X Θ : ℝ) :
    cfbrcRe d X Θ = cfbrcReClosedRaw d X Θ := by
  rw [cfbrcRe, cfbrcR_eq_cfbrcClosed, cfbrcClosed, cfbrcReClosedRaw, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hXRe : Complex.re ((X : ℂ) ^ (k + 1)) = X ^ (k + 1) := by
    simpa using ofReal_pow_re (d := k + 1) X
  have hXIm : Complex.im ((X : ℂ) ^ (k + 1)) = 0 := by
    simpa using ofReal_pow_im (d := k + 1) X
  calc
    Complex.re ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) *
        (Nat.choose d (k + 1) : ℂ))
      = Complex.re ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_re]
          simp
    _ = (X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k))) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_re]
          rw [hXRe, hXIm]
          ring
    _ = X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          ring

/--
`cfbrcIm` は `cfbrcImClosedRaw` に一致する。
-/
lemma cfbrcIm_eq_cfbrcImClosedRaw (d : ℕ) (X Θ : ℝ) :
    cfbrcIm d X Θ = cfbrcImClosedRaw d X Θ := by
  rw [cfbrcIm, cfbrcR_eq_cfbrcClosed, cfbrcClosed, cfbrcImClosedRaw, Complex.im_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hXRe : Complex.re ((X : ℂ) ^ (k + 1)) = X ^ (k + 1) := by
    simpa using ofReal_pow_re (d := k + 1) X
  have hXIm : Complex.im ((X : ℂ) ^ (k + 1)) = 0 := by
    simpa using ofReal_pow_im (d := k + 1) X
  calc
    Complex.im ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k) *
        (Nat.choose d (k + 1) : ℂ))
      = Complex.im ((X : ℂ) ^ (k + 1) * (Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_im]
          simp
    _ = (X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k))) *
          (Nat.choose d (k + 1) : ℝ) := by
          rw [Complex.mul_im]
          rw [hXRe, hXIm]
          ring
    _ = X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k)) *
          (Nat.choose d (k + 1) : ℝ) := by
          ring

/--
`cfbrcReClosedRaw` の添字を反転し、
純位相の指数を `j` として読む形に直した補助補題。
-/
private lemma cfbrcReClosedRaw_reindex (d : ℕ) (X Θ : ℝ) :
    cfbrcReClosedRaw d X Θ =
      ∑ j ∈ Finset.range d,
        X ^ (d - j) * Complex.re ((Complex.I * Θ) ^ j) * (Nat.choose d j : ℝ) := by
  unfold cfbrcReClosedRaw
  let f : ℕ → ℝ := fun k =>
    X ^ (k + 1) * Complex.re ((Complex.I * Θ) ^ (d - 1 - k)) * (Nat.choose d (k + 1) : ℝ)
  calc
    ∑ k ∈ Finset.range d, f k
        = ∑ j ∈ Finset.range d, f (d - 1 - j) := by
            simpa using (Finset.sum_range_reflect f d).symm
    _ = ∑ j ∈ Finset.range d,
          X ^ (d - j) * Complex.re ((Complex.I * Θ) ^ j) * (Nat.choose d j : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj_lt : j < d := Finset.mem_range.1 hj
          have h1 : d - 1 - j + 1 = d - j := by omega
          have h2 : d - 1 - (d - 1 - j) = j := by omega
          have h3 : Nat.choose d (d - j) = Nat.choose d j := by
            exact Nat.choose_symm (Nat.le_of_lt hj_lt)
          dsimp [f]
          rw [h1, h2, h3]

/--
`cfbrcImClosedRaw` の添字を反転し、
純位相の指数を `j` として読む形に直した補助補題。
-/
private lemma cfbrcImClosedRaw_reindex (d : ℕ) (X Θ : ℝ) :
    cfbrcImClosedRaw d X Θ =
      ∑ j ∈ Finset.range d,
        X ^ (d - j) * Complex.im ((Complex.I * Θ) ^ j) * (Nat.choose d j : ℝ) := by
  unfold cfbrcImClosedRaw
  let f : ℕ → ℝ := fun k =>
    X ^ (k + 1) * Complex.im ((Complex.I * Θ) ^ (d - 1 - k)) * (Nat.choose d (k + 1) : ℝ)
  calc
    ∑ k ∈ Finset.range d, f k
        = ∑ j ∈ Finset.range d, f (d - 1 - j) := by
            simpa using (Finset.sum_range_reflect f d).symm
    _ = ∑ j ∈ Finset.range d,
          X ^ (d - j) * Complex.im ((Complex.I * Θ) ^ j) * (Nat.choose d j : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hj_lt : j < d := Finset.mem_range.1 hj
          have h1 : d - 1 - j + 1 = d - j := by omega
          have h2 : d - 1 - (d - 1 - j) = j := by omega
          have h3 : Nat.choose d (d - j) = Nat.choose d j := by
            exact Nat.choose_symm (Nat.le_of_lt hj_lt)
          dsimp [f]
          rw [h1, h2, h3]

/--
純位相項の実部を偶奇で分解した式。
-/
private lemma re_phase_if (j : ℕ) (Θ : ℝ) :
    Complex.re ((Complex.I * Θ) ^ j) =
      if Even j then (-1 : ℝ) ^ (j / 2) * Θ ^ j else 0 := by
  rcases Nat.even_or_odd j with hjEven | hjOdd
  · rcases hjEven with ⟨m, hm⟩
    subst hm
    have hm2 : m + m = 2 * m := by omega
    have hdiv : (m + m) / 2 = m := by omega
    calc
      Complex.re ((Complex.I * Θ) ^ (m + m))
          = (-1 : ℝ) ^ m * Θ ^ (2 * m) := by
            simpa [hm2] using pure_phase_pow_even_re m Θ
      _ = (-1 : ℝ) ^ ((m + m) / 2) * Θ ^ (m + m) := by
            rw [hdiv, hm2]
      _ = if Even (m + m) then (-1 : ℝ) ^ ((m + m) / 2) * Θ ^ (m + m) else 0 := by
            simp
  · rcases hjOdd with ⟨m, hm⟩
    subst hm
    calc
      Complex.re ((Complex.I * Θ) ^ (2 * m + 1)) = 0 := by
            simpa using pure_phase_pow_odd_re m Θ
      _ = if Even (2 * m + 1) then (-1 : ℝ) ^ ((2 * m + 1) / 2) * Θ ^ (2 * m + 1) else 0 := by
            simp

/--
純位相項の虚部を偶奇で分解した式。
-/
private lemma im_phase_if (j : ℕ) (Θ : ℝ) :
    Complex.im ((Complex.I * Θ) ^ j) =
      if Odd j then (-1 : ℝ) ^ (j / 2) * Θ ^ j else 0 := by
  rcases Nat.even_or_odd j with hjEven | hjOdd
  · rcases hjEven with ⟨m, hm⟩
    subst hm
    have hm2 : m + m = 2 * m := by omega
    calc
      Complex.im ((Complex.I * Θ) ^ (m + m)) = 0 := by
            simpa [hm2] using pure_phase_pow_even_im m Θ
      _ = if Odd (m + m) then (-1 : ℝ) ^ ((m + m) / 2) * Θ ^ (m + m) else 0 := by
            simp
  · rcases hjOdd with ⟨m, hm⟩
    subst hm
    have hdiv : (2 * m + 1) / 2 = m := by omega
    calc
      Complex.im ((Complex.I * Θ) ^ (2 * m + 1))
          = (-1 : ℝ) ^ m * Θ ^ (2 * m + 1) := by
            simpa using pure_phase_pow_odd_im m Θ
      _ = (-1 : ℝ) ^ ((2 * m + 1) / 2) * Θ ^ (2 * m + 1) := by
            rw [hdiv]
      _ = if Odd (2 * m + 1) then (-1 : ℝ) ^ ((2 * m + 1) / 2) * Θ ^ (2 * m + 1) else 0 := by
            simp

/--
`if Even j then F (j/2) else 0` 形の和を
`range ((d+1)/2)` の和へ圧縮する補助補題。
-/
private lemma sum_even_if_eq {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    ∀ d : ℕ,
      (∑ j ∈ Finset.range d, if Even j then F (j / 2) else 0)
        = ∑ m ∈ Finset.range ((d + 1) / 2), F m := by
  intro d
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rcases Nat.even_or_odd d with hdEven | hdOdd
      · rcases hdEven with ⟨n, hn⟩
        subst hn
        have hdiv : (n + n) / 2 = n := by omega
        have hleft : ((n + n + 1) / 2) = n := by omega
        have hright : ((n + n + 1 + 1) / 2) = n + 1 := by omega
        rw [hleft, hright, hdiv, Finset.sum_range_succ]
        simp
      · rcases hdOdd with ⟨n, hn⟩
        subst hn
        have hleft : ((2 * n + 1 + 1) / 2) = n + 1 := by omega
        have hright : ((2 * n + 1 + 1 + 1) / 2) = n + 1 := by omega
        rw [hleft, hright]
        simp

/--
`if Odd j then F (j/2) else 0` 形の和を
`range (d/2)` の和へ圧縮する補助補題。
-/
private lemma sum_odd_if_eq {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    ∀ d : ℕ,
      (∑ j ∈ Finset.range d, if Odd j then F (j / 2) else 0)
        = ∑ m ∈ Finset.range (d / 2), F m := by
  intro d
  induction d with
  | zero =>
      simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rcases Nat.even_or_odd d with hdEven | hdOdd
      · rcases hdEven with ⟨n, hn⟩
        subst hn
        have hdiv : (n + n) / 2 = n := by omega
        have hright : ((n + n + 1) / 2) = n := by omega
        have hnotOdd : ¬ Odd (n + n) := by simp
        rw [hdiv, hright]
        simp [hnotOdd]
      · rcases hdOdd with ⟨n, hn⟩
        subst hn
        have hdiv : (2 * n + 1) / 2 = n := by omega
        have hright : ((2 * n + 1 + 1) / 2) = n + 1 := by omega
        rw [hdiv, hright, Finset.sum_range_succ]
        simp

/--
`cfbrcRe` の `Nat.choose` 閉形式（偶数位相項のみ抽出）。
-/
def cfbrcReClosed (d : ℕ) (X Θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.range ((d + 1) / 2),
    X ^ (d - 2 * m) * ((-1 : ℝ) ^ m * Θ ^ (2 * m)) * (Nat.choose d (2 * m) : ℝ)

/--
`cfbrcIm` の `Nat.choose` 閉形式（奇数位相項のみ抽出）。
-/
def cfbrcImClosed (d : ℕ) (X Θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (d / 2),
    X ^ (d - (2 * m + 1)) * ((-1 : ℝ) ^ m * Θ ^ (2 * m + 1)) *
      (Nat.choose d (2 * m + 1) : ℝ)

/--
`cfbrcReClosedRaw` は偶数位相だけを残した閉形式 `cfbrcReClosed` と一致する。
-/
lemma cfbrcReClosedRaw_eq_cfbrcReClosed (d : ℕ) (X Θ : ℝ) :
    cfbrcReClosedRaw d X Θ = cfbrcReClosed d X Θ := by
  rw [cfbrcReClosedRaw_reindex]
  have hphase :
      (∑ j ∈ Finset.range d,
          X ^ (d - j) * Complex.re ((Complex.I * Θ) ^ j) * (Nat.choose d j : ℝ))
        =
      (∑ j ∈ Finset.range d,
          X ^ (d - j) *
              (if Even j then (-1 : ℝ) ^ (j / 2) * Θ ^ j else 0) *
              (Nat.choose d j : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [re_phase_if]
  rw [hphase]
  let F : ℕ → ℝ := fun m =>
    X ^ (d - 2 * m) * ((-1 : ℝ) ^ m * Θ ^ (2 * m)) * (Nat.choose d (2 * m) : ℝ)
  have hif :
      (∑ j ∈ Finset.range d,
          X ^ (d - j) *
              (if Even j then (-1 : ℝ) ^ (j / 2) * Θ ^ j else 0) *
              (Nat.choose d j : ℝ))
        =
      (∑ j ∈ Finset.range d, if Even j then F (j / 2) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hEven : Even j
    · have htwo : 2 * (j / 2) = j := Nat.two_mul_div_two_of_even hEven
      simp [hEven, F, htwo]
    · simp [hEven, F]
  rw [hif, sum_even_if_eq F d]
  simp [cfbrcReClosed, F]

/--
`cfbrcImClosedRaw` は奇数位相だけを残した閉形式 `cfbrcImClosed` と一致する。
-/
lemma cfbrcImClosedRaw_eq_cfbrcImClosed (d : ℕ) (X Θ : ℝ) :
    cfbrcImClosedRaw d X Θ = cfbrcImClosed d X Θ := by
  rw [cfbrcImClosedRaw_reindex]
  have hphase :
      (∑ j ∈ Finset.range d,
          X ^ (d - j) * Complex.im ((Complex.I * Θ) ^ j) * (Nat.choose d j : ℝ))
        =
      (∑ j ∈ Finset.range d,
          X ^ (d - j) *
              (if Odd j then (-1 : ℝ) ^ (j / 2) * Θ ^ j else 0) *
              (Nat.choose d j : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [im_phase_if]
  rw [hphase]
  let F : ℕ → ℝ := fun m =>
    X ^ (d - (2 * m + 1)) * ((-1 : ℝ) ^ m * Θ ^ (2 * m + 1)) *
      (Nat.choose d (2 * m + 1) : ℝ)
  have hif :
      (∑ j ∈ Finset.range d,
          X ^ (d - j) *
              (if Odd j then (-1 : ℝ) ^ (j / 2) * Θ ^ j else 0) *
              (Nat.choose d j : ℝ))
        =
      (∑ j ∈ Finset.range d, if Odd j then F (j / 2) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hOdd : Odd j
    · have htwo : 2 * (j / 2) + 1 = j := Nat.two_mul_div_two_add_one_of_odd hOdd
      simp [hOdd, F, htwo]
    · simp [hOdd, F]
  rw [hif, sum_odd_if_eq F d]
  simp [cfbrcImClosed, F]

/--
`cfbrcRe` は偶数位相抽出版の閉形式 `cfbrcReClosed` に一致する。
-/
lemma cfbrcRe_eq_cfbrcReClosed (d : ℕ) (X Θ : ℝ) :
    cfbrcRe d X Θ = cfbrcReClosed d X Θ := by
  rw [cfbrcRe_eq_cfbrcReClosedRaw, cfbrcReClosedRaw_eq_cfbrcReClosed]

/--
`cfbrcIm` は奇数位相抽出版の閉形式 `cfbrcImClosed` に一致する。
-/
lemma cfbrcIm_eq_cfbrcImClosed (d : ℕ) (X Θ : ℝ) :
    cfbrcIm d X Θ = cfbrcImClosed d X Θ := by
  rw [cfbrcIm_eq_cfbrcImClosedRaw, cfbrcImClosedRaw_eq_cfbrcImClosed]

/--
`cfbrcClosed` の実部は、偶数位相抽出版 `cfbrcReClosed` に一致する。
-/
lemma cfbrcClosed_re_eq_cfbrcReClosed (d : ℕ) (X Θ : ℝ) :
    Complex.re (cfbrcClosed d X Θ) = cfbrcReClosed d X Θ := by
  calc
    Complex.re (cfbrcClosed d X Θ) = cfbrcRe d X Θ := by
      rw [← cfbrcR_eq_cfbrcClosed]
      rfl
    _ = cfbrcReClosed d X Θ := by
      exact cfbrcRe_eq_cfbrcReClosed d X Θ

/--
`cfbrcClosed` の虚部は、奇数位相抽出版 `cfbrcImClosed` に一致する。
-/
lemma cfbrcClosed_im_eq_cfbrcImClosed (d : ℕ) (X Θ : ℝ) :
    Complex.im (cfbrcClosed d X Θ) = cfbrcImClosed d X Θ := by
  calc
    Complex.im (cfbrcClosed d X Θ) = cfbrcIm d X Θ := by
      rw [← cfbrcR_eq_cfbrcClosed]
      rfl
    _ = cfbrcImClosed d X Θ := by
      exact cfbrcIm_eq_cfbrcImClosed d X Θ

end

end DkMath.CFBRC.TrigBridge

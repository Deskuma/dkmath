/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

-- import Mathlib
import DkMath.Algebra.DiffPow

namespace DkMath.NumberTheory.GcdDiffPow

open scoped BigOperators
open Finset
open DkMath.Algebra.DiffPow

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- gcd に関する補題群 ---------------------------------------------------------

✅ **補助補題について**
この補題は「全ての素因子 p が d を割るなら n ∣ d」という基本的な数論的事実で：
- 前提：n の全ての素因子が d を割る
- 結論：n ∣ d
- 依存する Mathlib の性質：`Nat.gcd_eq_left_iff_dvd` (gcd n d = n ⟺ n ∣ d)

⚠️ **残る `so#rry`**
最後の `so#rry` は、以下の複雑な部分の形式化が必要：
```
gcd n d = n を示す
├─ n の最小素因子による分解 (n = minFac(n) * m)
├─ minFac(n) | d は h から直接得られる
├─ m < n で m の全ての素因子も d を割る（帰納的）
└─ gcd(minFac(n) * m, d) = minFac(n) * m を導く
```
-/

-- here additional lemmas about gcd may be placed

-- **補題1：全き素数冪版**
/-- 補助補題：全ての素数冪 p^k が d を割るなら n | d

    リファレンス実装：n の全ての素数冪因子が d を割る場合、n ∣ d が成立する。
    これは Mathlib の `Nat.factorization` や `padicValNat` を使って証明される。

    重要：この版は「素因子」ではなく「素因子の冪」を扱うため、
    入射性（重複度の保存）を正しく捉えられる。
-/
lemma nat_dvd_of_all_prime_powers_dvd {n d : ℕ}
    (h : ∀ p k : ℕ, Nat.Prime p → p^k ∣ n → p^k ∣ d) (hn : 0 < n) : n ∣ d := by
  -- Strategy: use factorization_prime_le_iff_dvd
  by_cases hd : d = 0
  · simp [hd]
  · -- d ≠ 0 case: use factorization
    have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    rw [← Nat.factorization_prime_le_iff_dvd hn_ne hd]
    intro p hp
    -- For each prime p, show n.factorization p ≤ d.factorization p
    -- Strategy: p^(n.factorization p) ∣ n, so by h, p^(n.factorization p) ∣ d
    have hpow_n : p ^ n.factorization p ∣ n := by
      rw [hp.pow_dvd_iff_le_factorization hn_ne]
    have hpow_d : p ^ n.factorization p ∣ d := h p (n.factorization p) hp hpow_n
    -- Convert to factorization inequality
    exact (hp.pow_dvd_iff_le_factorization hd).mp hpow_d

-- **補題2：prime power 版（素数冪レベル）**
/-- 補助補題：p^k が gcd を割るなら p^k が d を割る（Integer variant）

    リファレンス実装：既存の prime_dividing_gcd_divides_d (素数版) を
    prime power へ拡張したもの。

    GcdDiffPow.lean の素数版の証明を参考に：
    - (p:ℤ)^k ∣ Int.gcd(a-b, S)
    - → (p:ℤ)^k ∣ (a-b) and (p:ℤ)^k ∣ S
    - → (p:ℤ)^k ∣ d * b^(d-1)（素数版と同じロジック）
    - → (p:ℤ)^k ∣ d（(p:ℤ)^k ∤ b を使う）
-/
lemma prime_pow_dividing_gcd_divides_d_pow {p k : ℕ} (hp : Nat.Prime p)
    {a b : ℤ} {d : ℕ}
    (hab : Int.gcd a b = 1)
    (hpkdiv : (p : ℤ) ^ k ∣ Int.gcd (a - b) (diffPowSum a b d)) :
    (p : ℤ) ^ k ∣ (d : ℤ) := by
  -- k=0 の場合は p^0 = 1 なので自明
  by_cases hk : k = 0
  · subst hk; simp
  · -- k > 0 の場合の証明
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk

    -- Step 1: Extract divisibility from gcd
    have hpk_ab : (p : ℤ) ^ k ∣ (a - b) := dvd_trans hpkdiv (Int.gcd_dvd_left _ _)
    have hpk_S : (p : ℤ) ^ k ∣ diffPowSum a b d := dvd_trans hpkdiv (Int.gcd_dvd_right _ _)

    -- Step 2: Show (a-b) ∣ (S - d*b^(d-1))
    have S_minus_eq : diffPowSum a b d - (d : ℤ) * b ^ (d - 1)
      = ∑ i ∈ range d, (a ^ (d - 1 - i) * b ^ i - b ^ (d - 1)) := by
      exact diffPowSum_sub_const_mul a b d

    have ab_div_S_minus : (a - b) ∣ (diffPowSum a b d - (d : ℤ) * b ^ (d - 1)) := by
      rw [S_minus_eq]
      apply Finset.dvd_sum
      intro i hi
      have hi_lt : i < d := Finset.mem_range.mp hi
      have heq : a ^ (d - 1 - i) * b ^ i - b ^ (d - 1) = b ^ i * (a ^ (d - 1 - i) - b ^ (d - 1 - i)) := by
        have : b ^ (d - 1) = b ^ (d - 1 - i) * b ^ i := by
          have : d - 1 = (d - 1 - i) + i := by omega
          calc b ^ (d - 1) = b ^ ((d - 1 - i) + i) := by congr 1
            _ = b ^ (d - 1 - i) * b ^ i := by rw [pow_add]
        rw [this]; ring
      rw [heq]
      apply dvd_mul_of_dvd_right
      exact pow_sub_pow_factor a b (d - 1 - i) ▸ dvd_mul_right (a - b) _

    -- Step 3: p^k ∣ (S - d*b^(d-1))
    have hpk_S_minus : (p : ℤ) ^ k ∣ (diffPowSum a b d - (d : ℤ) * b ^ (d - 1)) :=
      dvd_trans hpk_ab ab_div_S_minus

    -- Step 4: p^k ∣ d*b^(d-1) (by subtraction)
    have hpk_db : (p : ℤ) ^ k ∣ (d : ℤ) * b ^ (d - 1) := by
      have : (d : ℤ) * b ^ (d - 1) = diffPowSum a b d - (diffPowSum a b d - (d : ℤ) * b ^ (d - 1)) := by ring
      rw [this]
      exact dvd_sub hpk_S hpk_S_minus
    -- Step 5: Show p ∤ b (from gcd(a,b)=1 and p|(a-b))
    have hp_not_b : ¬((p : ℤ) ∣ b) := by
      intro hp_b
      have hp_1 : (p : ℤ) ∣ (a - b) := by
        calc (p : ℤ) = (p : ℤ) ^ 1 := by rw [pow_one]
          _ ∣ (p : ℤ) ^ k := pow_dvd_pow (p : ℤ) hk_pos
          _ ∣ (a - b) := hpk_ab
      have hp_a : (p : ℤ) ∣ a := by
        have : a = (a - b) + b := by ring
        rw [this]
        exact Int.dvd_add hp_1 hp_b
      -- But then gcd(a,b) ≥ p > 1, contradicting gcd(a,b)=1
      have : (p : ℤ) ∣ (Int.gcd a b : ℤ) := by
        rw [Int.gcd_eq_natAbs]
        -- p|a and p|b in ℤ, so p|(gcd a.natAbs b.natAbs) in ℕ
        have hp_a_nat : (p : ℕ) ∣ a.natAbs := by
          exact Int.natCast_dvd.mp hp_a
        have hp_b_nat : (p : ℕ) ∣ b.natAbs := by
          exact Int.natCast_dvd.mp hp_b
        have : (p : ℕ) ∣ a.natAbs.gcd b.natAbs := Nat.dvd_gcd hp_a_nat hp_b_nat
        exact Int.natCast_dvd_natCast.mpr this
      rw [hab] at this
      simp only [Nat.cast_one] at this
      have : (p : ℤ) ≤ 1 := Int.le_of_dvd zero_lt_one this
      have hp_ge_2 : 2 ≤ (p : ℤ) := by
        have := hp.two_le
        omega
      omega
    -- Step 6: p^k ∣ d (coprime argument)
    by_cases hd : d = 0
    · simp [hd]
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      -- Convert Int divisibility to Nat
      have hpk_nat_db : (p ^ k : ℕ) ∣ (d * b.natAbs ^ (d - 1)) := by
        -- hpk_db: (p:ℤ)^k ∣ (d:ℤ) * b^(d-1)
        -- Key: b^(d-1) in ℤ has natAbs = b.natAbs^(d-1)
        have hb_pow : (b ^ (d - 1)).natAbs = b.natAbs ^ (d - 1) := Int.natAbs_pow b (d - 1)
        have : ((d : ℤ) * b ^ (d - 1)).natAbs = d * b.natAbs ^ (d - 1) := by
          simp only [Int.natAbs_mul, Int.natAbs_natCast, hb_pow]
        rw [← this]
        exact Int.natCast_dvd.mp hpk_db
      -- Show coprime: p^k and b.natAbs are coprime
      have hcoprime : Nat.Coprime (p ^ k) b.natAbs := by
        -- Use hp_not_b: ¬((p:ℤ) ∣ b)
        have hp_not_b_nat : ¬(p ∣ b.natAbs) := by
          intro h
          apply hp_not_b
          exact Int.natCast_dvd.mpr h
        -- gcd(p, b.natAbs) = 1 because p is prime and doesn't divide b.natAbs
        have hgcd_p : Nat.Coprime p b.natAbs := by
          exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hp_not_b_nat
        -- Lift to p^k: if gcd(p, b) = 1 then gcd(p^k, b) = 1
        exact hgcd_p.pow_left k
      -- Use coprimality to extract p^k ∣ d from p^k ∣ d * b.natAbs^(d-1)
      have : (p ^ k : ℕ) ∣ d := by
        -- Use Nat.Coprime.dvd_of_dvd_mul_right or similar
        have hcoprime_pow : Nat.Coprime (p ^ k) (b.natAbs ^ (d - 1)) := by
          exact Nat.Coprime.pow_right (d - 1) hcoprime
        exact Nat.Coprime.dvd_of_dvd_mul_right hcoprime_pow hpk_nat_db
      exact Int.natCast_dvd_natCast.mpr this

-- **補題3：gcd 全体が d を割る（最強版）**
--
-- 注：既に GdcDivD.lean で Integer版 `gcd_divides_d` が定義されているため、
-- Nat版の補題はここでは不要。GcdNatAbsDivD で Integer版を使用する。

-- ----------------------------------------------------------------------------

/- ⚠️ 注意：以下の補題は **偽** です。反例：n=4, d=2

    素因子だけでは重複度（指数）が欠落するため、n ∣ d を導けません。
    代わりに `nat_dvd_of_all_prime_powers_dvd` (素数冪版) を使用してください。

    反例の説明：
    - n = 4 = 2² の素因子は {2} のみ
    - d = 2 の素因子も {2}
    - ∀ p prime, p ∣ 4 → p ∣ 2 は成立 (p=2 のみ)
    - しかし 4 ∤ 2

    この補題は参考用にコメントアウトして保存します。
-/
/-
lemma nat_dvd_of_all_prime_factors_dvd {n d : ℕ}
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ d) (d_pos : 0 < d) : n ∣ d := by
  so#rry
-/


end DkMath.NumberTheory.GcdDiffPow

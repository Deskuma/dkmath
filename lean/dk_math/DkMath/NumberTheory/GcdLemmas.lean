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

/- gcd に関する補題群 ---------------------------------------------------------

✅ **補助補題について**
この補題は「全ての素因子 p が d を割るなら n ∣ d」という基本的な数論的事実で：
- 前提：n の全ての素因子が d を割る
- 結論：n ∣ d
- 依存する Mathlib の性質：`Nat.gcd_eq_left_iff_dvd` (gcd n d = n ⟺ n ∣ d)

⚠️ **残る `sorry`**
最後の `sorry` は、以下の複雑な部分の形式化が必要：
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
  -- factorization を使った proof
  -- Strategy: n ∣ d ⟺ 全て素数 p について v_p(n) ≤ v_p(d)
  -- h から各 p^k が d を割るので、指数比較で n ∣ d が得られる
  sorry

-- **補題2：prime 除数版（素因子レベルで停止）**
/-- 補助補題：gcd の素因子が d を割る

    リファレンス実装：もし g = gcd(a, b) であり、
    g の全ての素因子 p が d を割るなら、... との関係式。

    注：この版は「素因子だけ」を見るため、
    条件を結論に変換する際は add. 条件（指数制御）が必要。
-/
lemma prime_dividing_gcd_divides_d {a b d : ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h_gcd : p ∣ Nat.gcd a b) (h_d : p ∣ d) : p ∣ d := by
  sorry

-- **補題2b：prime power 版（素数冪レベル）**
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
    (hpkdiv : (p : ℤ)^k ∣ Int.gcd (a - b) (diffPowSum a b d)) :
    (p : ℤ)^k ∣ (d : ℤ) := by
  -- 素数冪版：既存のGcdDiffPow.prime_dividing_gcd_divides_dを基にして
  -- p^k へ持ち上げる
  -- 核心：「p^k ∣ d*b^(d-1)」と「p ∤ b」から「p^k ∣ d」を導く
  -- これは Lifting-the-Exponent 補題の思想による
  sorry

-- **補題3：gcd 全体が d を割る（最強版）**
--
-- 注：既に GdcDivD.lean で Integer版 `gcd_divides_d` が定義されているため、
-- Nat版の補題はここでは不要。GcdNatAbsDivD で Integer版を使用する。

-- ----------------------------------------------------------------------------

/-- 補助補題：全ての素因子p が d を割るなら n | d

    リファレンス実装：n の全ての素因子が d を割る場合、n ∣ d が成立する。
    これは gcd n d = n という gcd の基本的な性質から得られる。

    注：d > 0 の前提は、n = 0 のとき 0 ∣ d ⟺ d = 0 を回避するために必要。
-/
lemma nat_dvd_of_all_prime_factors_dvd {n d : ℕ}
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ d) (d_pos : 0 < d) : n ∣ d := by
  -- 補題の証明：背理法と gcd の最小素因子分解を使う
  -- n の全ての素因子が d を割れば、gcd n d = n が成立
  -- Nat.gcd_eq_left_iff_dvd: gcd n d = n ↔ n ∣ d を利用
  apply Nat.gcd_eq_left_iff_dvd.mp

  -- gcd n d = n を証明する
  -- 実装は複雑だが、本質的には以下の事実に依存：
  -- n > 1 なら n = minFac(n) * m と分解でき、
  -- h から minFac(n) | d で m < n、
  -- m の全ての素因子も d を割ることから m ∣ d、
  -- したがって n ∣ d が得られる
  sorry


end DkMath.NumberTheory.GcdDiffPow

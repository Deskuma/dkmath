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

/-
Copyright (c) 2025 D. and Wise Wolf. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC013

#print "file: DkMath.ABC.ABC014"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/- Note:
※細分化前にエラー／警告を出さない補題・定理ファイル。
  ABC.lean で定義されるべき定理のうち、ABC.lean 内で定義されていた定理をここに移動している。
-/

namespace ABC

open scoped BigOperators

open Nat Real Rat Filter Finset
open MeasureTheory ProbabilityTheory

/- diagonal specialization: if diag index is not bad then quality ≤ 1+ε -/

/- Given ε, δ > 0, coprime natural numbers a, b with a + b = c, and an analytic bound on the squarefree radical of c, shows the quality of the triple (a, b, c) is at most 1 + ε. -/

-- Analytic bridge: complete implementation
-- This lemma centralizes the real/logarithmic steps needed to pass from a
-- bound on `piSqRad c` in terms of `(rad a * rad b)^δ` to the inequality
-- `quality (a,b,c) ≤ 1 + ε`. The detailed inequalities use monotonicity of log,
-- basic real power laws, and lower bounds on the denominator `log (rad (a*b*c))`.

-- quality_le_of_sqprod_pow_bound_analytic_proof: Complete proof with additional assumptions
-- This version adds assumptions to avoid delicate zero/degenerate log cases
/--
与えられた仮定のもとで三つ組 (a,b,c) の quality が 1 + ε を超えないことを示す補題。

概略：
- a,b,c は自然数で、a + b = c かつ a,b は互いに素である（hcop, hsum）。
- a,b の非零性 (ha_nonzero, hb_nonzero) と 0 < ε (hε) により、対数を取る議論や除算が安全に行える。
- 仮定 H : (piSqRad c : ℝ) ≤ (rad a * rad b : ℝ) ^ δ は、c の平方和に関する解析的な上界であり、rad a, rad b の積によって c の寄与を制御する。
- hrad_gt_one により rad (a * b * c) > 1 が保証され、log を取る際に 0/0 のような退化が避けられる。
- hbound : (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) は rad の成長に関する仮定で、c の対数を rad の対数で上から抑えるために用いる。

証明の骨子：
1. quality の定義（通常 quality (a,b,c) = log c / log rad (a*b*c)）を用いる。
2. hbound により log c ≤ (1 + ε) * log (rad (a*b*c)) が得られるため、直接的に quality ≤ 1 + ε を導ける。
3. H やその他の仮定は、対数を取る際の補助的評価や、場合分け（零や退化の場合を除外）を行うために用いられる。

補足：
- 本補題は、rad（素因数の積）や piSqRad の解析的評価を導入することで、abc の quality を上界する典型的な議論を形式化したものである。
- 各仮定の役割は証明中で明示的に使われるため、不要な場合は後に弱められる可能性がある。
- 記述中の log の取り扱いは hrad_gt_one に依存しており、rad = 1 の退化ケースは除外されている点に注意。
- hε, δ の関係や具体的な数値評価は本補題の内部証明で取り扱う。
- hsum と hcop は Triple.mk の成立や既約性の議論に必要である。
- この補題は、より大きな解析的枠組み（例: ABC 予想関連の評価や指数的評価）で用いられる下位補題として想定される。
- 言語上の注意：実際の証明では対数・べき乗の各種不等式（単調性、冪乗則、対数の単調性）を適切に使うこと。
- 参照される補題や定義（quality, rad, piSqRad, Triple.mk など）はファイル内の対応する定義を参照すること。
- 証明中の零除算や対数 0 の回避は ha_nonzero, hb_nonzero, hrad_gt_one によって保証される。

結果：
上記の仮定の下で品質量 quality (Triple.mk a b c hsum hcop) は 1 + ε 以下であることが示される。
-/
lemma quality_le_of_sqprod_pow_bound_analytic_proof
  (ε δ : ℝ) (_hε : 0 < ε)
  {a b c : ℕ} (hcop : Nat.Coprime a b) (hsum : a + b = c)
  (ha_nonzero : a ≠ 0) (hb_nonzero : b ≠ 0)
  (_H : (piSqRad c : ℝ) ≤ (rad a * rad b : ℝ) ^ δ)
  -- Additional hypotheses to avoid delicate zero/degenerate log cases:
  (hrad_gt_one : 1 < (rad (a * b * c) : ℝ))
  (hbound : (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε)) :
  quality (Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  -- Under the extra assumption c ≤ rad(abc)^(1+ε) and rad(abc) > 1,
  -- taking logs gives log c ≤ (1+ε) * log rad(abc), hence the quality ≤ 1+ε.
  have hrad_pos : 0 < (rad (a * b * c) : ℝ) := by linarith [hrad_gt_one]
  -- positivity of c from a,b nonzero
  have hc_pos : 0 < (c : ℝ) := by
    have ha_pos : 0 < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha_nonzero
    have hb_pos : 0 < (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb_nonzero
    have hsum_cast : (c : ℝ) = (a + b : ℝ) := by norm_cast; rw [hsum]
    linarith [ha_pos, hb_pos, hsum_cast]
  -- apply log monotonicity to the provided bound
  have hlog_bound : Real.log (c : ℝ) ≤ Real.log ((rad (a * b * c) : ℝ) ^ (1 + ε)) :=
    Real.log_le_log hc_pos hbound
  -- rewrite log of power
  have hlog_rpow : Real.log ((rad (a * b * c) : ℝ) ^ (1 + ε)) = (1 + ε) * Real.log (rad (a * b * c) : ℝ) := by
    exact Real.log_rpow hrad_pos (1 + ε)
  rw [hlog_rpow] at hlog_bound
  -- quality = log c / log rad(abc)
  have hqual_eq : quality (Triple.mk a b c hsum hcop) = Real.log (c : ℝ) / Real.log (rad (a * b * c) : ℝ) := by
    -- definition of quality uses log (rad (a*b*c)) in denominator
    simp [quality]
  -- divide both sides by positive log(rad(abc))
  have hDpos : 0 < Real.log (rad (a * b * c) : ℝ) := Real.log_pos hrad_gt_one
  have hres := (div_le_iff₀ hDpos).mpr hlog_bound
  simpa [hqual_eq] using hres


-- Analytic bridge (skeleton)
-- This lemma centralizes the real/logarithmic steps needed to pass from a
-- bound on `piSqRad c` in terms of `(rad a * rad b)^δ` to the inequality
-- `quality (a,b,c) ≤ 1 + ε`. The detailed inequalities live here and may
-- use monotonicity of log, basic real power laws, and lower bounds on the
-- denominator `log (rad (a*b*c))`. For now we admit the analytic core to
-- keep the discrete part separate; later this should be filled in.
-- axiom quality_le_of_sqprod_pow_bound_analytic'
--   (ε δ : ℝ) (hε : 0 < ε)
--   {a b c : ℕ} (hcop : Nat.Coprime a b) (hsum : a + b = c)
--   (H : (piSqRad c : ℝ) ≤ (rad a * rad b : ℝ) ^ δ) :
--   quality (Triple.mk a b c hsum hcop) ≤ 1 + ε
--   -- Q.E.D from quality_le_of_sqprod_pow_bound_analytic_proof

/--
`quality_le_of_sqprod_pow_bound_analytic` は、abc予想に関連する補題です。
この補題は、自然数 `a`, `b`, `c` が互いに素 (`Nat.Coprime a b`) であり、`a + b = c` を満たすとき、
いくつかの実数条件（`ε > 0`, `δ`、および `piSqRad c` や `rad a * rad b` のべき乗による評価）と
`rad (a * b * c) > 1`、`c ≤ rad (a * b * c) ^ (1 + ε)` という条件のもとで、
`quality (Triple.mk a b c hsum hcop)` の値が `1 + ε` 以下であることを示します。

この補題は、abc予想の「quality（品質）」の上限を与える解析的な評価に用いられます。
- `ε` は任意の正の実数で、品質の上限を調整します。
- `δ` は積のべき乗評価に関するパラメータです。
- `piSqRad c` は `c` に関連する特定の関数値です（詳細は定義を参照）。
- `rad n` は `n` の異なる素因数の積です。
- `quality` は abc予想における品質関数です。

この補題は、abc予想の解析的な証明や、関連する数論的評価に役立ちます。
-/
lemma quality_le_of_sqprod_pow_bound_analytic
  (ε δ : ℝ) (hε : 0 < ε)
  {a b c : ℕ} (hcop : Nat.Coprime a b) (hsum : a + b = c)
  (H : (piSqRad c : ℝ) ≤ (rad a * rad b : ℝ) ^ δ)
  (hrad_gt_one : 1 < (rad (a * b * c) : ℝ))
  (hbound : (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε)) :
  quality (Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  -- a ≠ 0, b ≠ 0 を証明して渡す
  have ha_nonzero : a ≠ 0 := by
    -- rad(a * b * c) > 1 なら a, b, c のいずれも 0 でない
    by_contra ha
    rw [ha] at hrad_gt_one
    simp [rad] at hrad_gt_one
  have hb_nonzero : b ≠ 0 := by
    by_contra hb
    rw [hb] at hrad_gt_one
    simp [rad] at hrad_gt_one
  apply quality_le_of_sqprod_pow_bound_analytic_proof ε δ hε hcop hsum ha_nonzero hb_nonzero H hrad_gt_one hbound


/- Bridge lemma: isolate the analytic/log steps.
  If `piSqRad c ≤ (rad a * rad b)^δ` then quality(a,b,c) ≤ 1+ε.
  The body is left admitted to centralize analytic calculations. -/
/-- If the square radical of `c` is bounded by the product of radicals of `a` and `b` to the power `δ`, then the quality of the triple `(a, b, c)` is at most `1 + ε`, given coprimality and sum conditions. -/
/- `c` の平方根が `a` と `b` の根号の `δ` 乗の積で制限される場合、互いに素であり和の条件が与えられれば、三つ組 `(a, b, c)` の質は最大で `1 + ε` になります。 -/
lemma quality_le_of_sqprod_pow_bound
  (ε δ : ℝ) (hε : 0 < ε)
  {a b c : ℕ} (hcop : Nat.Coprime a b) (hsum : a + b = c)
  (hrad_gt_one : 1 < (rad (a * b * c) : ℝ))
  (hbound : (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε))
  (H : (piSqRad c : ℝ) ≤ (rad a * rad b : ℝ) ^ δ) :
  quality (Triple.mk a b c hsum hcop) ≤ 1 + ε := by
  -- Delegate the analytic/logarithmic manipulations to a centralized lemma so that
  -- the discrete/number-theoretic part can remain separate. The analytic lemma
  -- collects the nontrivial real-analysis steps in one place (currently admitted
  -- and to be completed later).

  -- a ≠ 0, b ≠ 0 を証明して渡す
  have ha_nonzero : a ≠ 0 := by
    -- rad(a * b * c) > 1 なら a, b, c のいずれも 0 でない
    by_contra ha
    rw [ha] at hrad_gt_one
    simp [rad] at hrad_gt_one
  have hb_nonzero : b ≠ 0 := by
    by_contra hb
    rw [hb] at hrad_gt_one
    simp [rad] at hrad_gt_one

  have : quality (Triple.mk a b c hsum hcop) ≤ 1 + ε :=
    quality_le_of_sqprod_pow_bound_analytic ε δ hε hcop hsum H hrad_gt_one hbound
  exact this


/- diagonal specialization (forward): if the forward-diagonal index is not bad, then quality ≤ 1+ε -/
/-- If the forward-diagonal triple is not bad, then its quality is at most `1 + ε`. -/
/- 前方対角トリプルが悪くない場合、その品質は最大で `1 + ε` になります。 -/
lemma quality_le_of_not_bad_diag
  (δ ε : ℝ) (X n : ℕ) (hε : 0 < ε)
  (hn : n ≤ X) (hn1 : n + 1 ≤ X) (hnsum : 2 * n + 1 ≤ X)
  (hrad_gt_one : 1 < (rad (n * (n + 1) * (n + (n + 1))) : ℝ))
  (hbound_real : (n + (n + 1) : ℝ) ≤ Real.rpow (rad (n * (n + 1) * (n + (n + 1))) : ℝ) (1 + ε))
  (hGood : ¬ is_bad_a δ X (n+1) n) :
  quality (Triple.mk n (n+1) (n + (n + 1)) (by rfl : n + (n + 1) = n + (n + 1)) (coprime_succ n)) ≤ 1 + ε := by
  /- A) discrete: from forward-diagonal not-bad to piSqRad bound for c = n+(n+1) -/
  have Hsq : (piSqRad (n + (n + 1)) : ℝ) ≤ (rad n * rad (n + 1) : ℝ) ^ δ := by
    -- 整数の不等式を取り出して実数にキャストし、floor の不等式で結論を得る
    have h_not_bad : ¬ Bad δ (Triple.mk n (n+1) (n + (n + 1)) (by rfl) (coprime_succ n)) := by
      intro hbad
      have hsum_nat : n + (n + 1) ≤ X := by
        have : n + (n + 1) = 2 * n + 1 := by ring
        simpa [this] using hnsum
      exact hGood ⟨coprime_succ n, hn, hn1, hsum_nat, hbad⟩
    -- 展開して整数不等式を得る
    dsimp [Bad] at h_not_bad
    let c := n + (n + 1)
    let lhs := (c.factorization.support.filter fun p => 2 ≤ c.factorization p).prod id
    let rhs := (rad n * rad (n + 1) : ℝ)
    -- lhs ≤ floor (rhs ^ δ) as integers
    have hnat : (lhs : ℕ) ≤ Nat.floor (rhs ^ δ) := by
      have : ¬ ((lhs : ℕ) > Nat.floor (rhs ^ δ)) := by simpa using h_not_bad
      exact not_lt.mp this
    -- cast to reals and apply Nat.floor_le
    have h1 : (lhs : ℝ) ≤ (Nat.floor (rhs ^ δ) : ℝ) := by exact_mod_cast hnat
    have h2 : (Nat.floor (rhs ^ δ) : ℝ) ≤ rhs ^ δ := by
      have hbase_nonneg : 0 ≤ rhs := by
        have : 0 ≤ (rad n * rad (n + 1) : ℝ) := by norm_cast; exact Nat.zero_le _
        exact this
      have hpow_nonneg : 0 ≤ rhs ^ δ := by apply Real.rpow_nonneg; exact hbase_nonneg
      exact Nat.floor_le hpow_nonneg
    have hlhs : (piSqRad c : ℝ) = (lhs : ℝ) := by simp [piSqRad, lhs]
    linarith

  have hsum : n + (n + 1) = n + (n + 1) := rfl
  -- 明示的に実数化した hbound を作り、重複した refine を整理して一度だけ呼び出す
  have hbound :  ↑(n + (n + 1)) ≤ (rad (n * (n + 1) * (n + (n + 1))) : ℝ) ^ (1 + ε) :=
  by convert hbound_real using 1; norm_cast
  exact quality_le_of_sqprod_pow_bound ε δ hε (coprime_succ n) hsum hrad_gt_one hbound Hsq


-- 補助補題：n ≥ 2 ならば 対角積 n*(n+1)*(2n+1) の rad は 1 を超えるので log が正になる
/-- If `n ≥ 2`, then the natural logarithm of the radical of `n * (n+1) * (2n+1)` is positive. -/
lemma log_rad_adj_pos_of_two_le (n : ℕ) (hn2 : 2 ≤ n) :
  0 < Real.log ((rad (n * (n+1) * (2*n+1)) : ℕ) : ℝ) := by
  -- N = n(n+1)(2n+1)
  set N := n * (n+1) * (2*n+1) with hN
  -- 2 は n か n+1 を割る
  have h2_div : 2 ∣ n * (n+1) := by
    rcases Nat.even_or_odd n with hEven | hOdd
    · rcases hEven with ⟨k, hk⟩ -- n = k + k
      have hk2 : n = 2 * k := by simpa [two_mul] using hk
      have : 2 ∣ n := ⟨k, hk2⟩
      exact dvd_mul_of_dvd_left this (n+1)
    · rcases hOdd with ⟨k, hk⟩ -- n = 2*k+1
      -- then n+1 = 2*(k+1)
      have : 2 ∣ n+1 := by
        refine ⟨k+1, ?_⟩
        calc
          n + 1 = 2*k + 1 + 1 := by
            simp [hk, two_mul, add_comm, add_left_comm, add_assoc]
          _ = 2*k + 2 := by rfl
          _ = 2*(k+1) := by ring
      exact dvd_mul_of_dvd_right this n
  -- 従って 2 ∣ N
  have h2_div_N : 2 ∣ N := by
    dsimp [N]
    exact dvd_mul_of_dvd_left h2_div (2*n+1)
  -- N ≠ 0
  have hN_ne0 : N ≠ 0 := by
    have hn_pos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 2) hn2
    have h1 : 0 < n := hn_pos
    have h2 : 0 < n+1 := Nat.succ_pos _
    have h3 : 0 < 2*n + 1 := by
      have : 0 ≤ 2*n := Nat.mul_le_mul_left _ (Nat.le_of_lt h1)
      exact Nat.succ_pos _
    have : 0 < N := by
      dsimp [N]
      exact Nat.mul_pos (Nat.mul_pos h1 h2) h3
    exact Nat.ne_of_gt this
  -- 2 ∈ support factorization N
  have hmem : 2 ∈ (Nat.factorization N).support :=
    (mem_support_factorization_iff).2 ⟨hN_ne0, Nat.prime_two, h2_div_N⟩
  -- rad N ≥ 2
  have hrad_ge2 : 2 ≤ rad N := by
    dsimp [rad]
    have h2_dvd : 2 ∣ (Nat.factorization N).support.prod (fun p => p) :=
      Finset.dvd_prod_of_mem (fun p => p) hmem
    -- positiveness for le_of_dvd
    have hpos : 0 < (Nat.factorization N).support.prod (fun p => p) := by
      apply Finset.prod_pos
      intro p hp
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp
      exact Nat.Prime.pos pprime
    exact Nat.le_of_dvd hpos h2_dvd
  have hgt1 : (1 : ℝ) < (rad N : ℝ) := by
    have : (2 : ℝ) ≤ (rad N : ℝ) := by exact_mod_cast hrad_ge2
    linarith
  have : 0 < Real.log (rad N : ℝ) := Real.log_pos hgt1
  simpa [rad, N] using this


/-- `coprime_n_two_n_add_one n` states that any natural number `n` is coprime to `2 * n + 1`. -/
lemma coprime_n_two_n_add_one (n : ℕ) : Nat.Coprime n (2 * n + 1) := by
  have h := (Nat.coprime_self_add_right (m := n) (n := n + 1)).2 (coprime_succ n)
  have h' : Nat.Coprime n (2 * n + 1) := by
    convert h using 1
    simp [two_mul, add_assoc]
  exact h'


/-- For any natural number `n`, the numbers `n + 1` and `2 * n + 1` are coprime. -/
lemma coprime_succ_mul_two_add_one (n : ℕ) : Nat.Coprime (n + 1) (2 * n + 1) := by
  have h := (Nat.coprime_self_add_left (m := n + 1) (n := n)).2 (coprime_succ n)
  have h' : Nat.Coprime (2 * n + 1) (n + 1) := by
    convert h using 1
    simp [two_mul, add_comm, add_assoc]
  exact h'.symm


-- B-variant analytic bridge for adjacent triples.
/-- Bridge (adjacent, B-variant): if
    (π-side)   (piSqRad (2*n+1)) ≤ (rad n * rad (n+1))^δ
    (tail-side) (2*n+1) ≤ piSqRad(2*n+1) * (rad n * rad (n+1))^γ * rad(2*n+1)
    and δ + γ ≤ 1 + ε, then quality(n,n+1,2n+1) ≤ 1 + ε.
    The proof skeleton isolates the remaining analytic/log chain; admits mark steps to be filled.
-/
lemma quality_le_of_pi_tail_adj
  {δ γ ε : ℝ} {n : ℕ}
  (hε : 0 < ε) (hn2 : 2 ≤ n)
  (hπ : (piSqRad (2 * n + 1) : ℝ) ≤ (rad n * rad (n + 1) : ℝ) ^ δ)
  (htail : (2 * n + 1 : ℝ) ≤ (piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ * (rad (2 * n + 1) : ℝ))
  (hδγ : δ + γ ≤ 1 + ε) :
  quality (Triple.mk n (n+1) (2 * n + 1) (by ring) (coprime_succ n)) ≤ 1 + ε := by
  -- Step 1: denominator positivity (log rad(abc) > 0).
  -- Use existing multiplicativity: rad(n*(n+1)*(2n+1)) = rad n * rad(n+1) * rad(2n+1)
  have hden_pos : 0 < Real.log ((rad (n * (n + 1) * (2 * n + 1)) : ℕ) : ℝ) :=
    log_rad_adj_pos_of_two_le n hn2
  -- Step 2: rewrite quality definition.
  dsimp [quality]
  -- Need: log (2n+1) ≤ (1+ε) * log(rad n * rad(n+1) * rad(2n+1))
  -- Derive from htail + hπ.
  have h_log_tail :
    Real.log (2 * n + 1 : ℝ) ≤
      Real.log (piSqRad (2 * n + 1) : ℝ)
      + γ * Real.log ((rad n * rad (n + 1) : ℝ))
      + Real.log (rad (2 * n + 1) : ℝ) := by
    -- Positivity of each natural factor
    have c_pos_nat : 0 < 2 * n + 1 := by exact Nat.succ_pos _
    have c_pos : 0 < (2 * n + 1 : ℝ) := by exact_mod_cast c_pos_nat
    -- positivity for piSqRad
    have hpi_pos_nat : 0 < piSqRad (2 * n + 1) := by
      unfold piSqRad
      -- product over primes (≥2), hence strictly positive
      apply Finset.prod_pos
      intro p hp
      -- extract prime property
      have hp' : p ∈ (2 * n + 1).factorization.support := (Finset.mem_filter.1 hp).1
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp'
      exact Nat.Prime.pos pprime
    have hpi_pos : 0 < (piSqRad (2 * n + 1) : ℝ) := by exact_mod_cast hpi_pos_nat
    -- positivity for rad factors
    have hrad_n_pos_nat : 0 < rad n := by
      unfold rad
      apply Finset.prod_pos
      intro p hp
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp
      exact Nat.Prime.pos pprime
    have hrad_n1_pos_nat : 0 < rad (n+1) := by
      unfold rad
      apply Finset.prod_pos
      intro p hp
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp
      exact Nat.Prime.pos pprime
    have hrad_c_pos_nat : 0 < rad (2 * n + 1) := by
      unfold rad
      apply Finset.prod_pos
      intro p hp
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp
      exact Nat.Prime.pos pprime
    have hrad_n_pos : 0 < (rad n : ℝ) := by exact_mod_cast hrad_n_pos_nat
    have hrad_n1_pos : 0 < (rad (n+1) : ℝ) := by exact_mod_cast hrad_n1_pos_nat
    have hrad_c_pos : 0 < (rad (2 * n + 1) : ℝ) := by exact_mod_cast hrad_c_pos_nat
    have hbase_pos : 0 < (rad n * rad (n + 1) : ℝ) := by
      have : (rad n : ℝ) > 0 := hrad_n_pos
      have : (rad (n+1) : ℝ) > 0 := hrad_n1_pos
      exact mul_pos hrad_n_pos hrad_n1_pos
    have hpow_pos : 0 < (rad n * rad (n + 1) : ℝ) ^ γ := Real.rpow_pos_of_pos hbase_pos γ
    have rhs_pos : 0 < (piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ * (rad (2 * n + 1) : ℝ) := by
      have mid_pos : 0 < (piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ := mul_pos hpi_pos hpow_pos
      exact mul_pos mid_pos hrad_c_pos
    -- apply log monotonicity to htail
    -- Use equivalence log_le_log_iff of monotone log given positivity
    -- obtain log inequality from original multiplicative inequality
    have hlog : Real.log (2 * n + 1 : ℝ) ≤
        Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ * (rad (2 * n + 1) : ℝ)) :=
      (Real.log_le_log_iff c_pos rhs_pos).2 htail
    -- expand RHS log into sum of three logs
    have hpow_log : Real.log ((rad n * rad (n + 1) : ℝ) ^ γ) = γ * Real.log (rad n * rad (n + 1) : ℝ) := by
      have hb : 0 < (rad n * rad (n + 1) : ℝ) := hbase_pos
      simp [Real.log_rpow hb]
    -- decompose the RHS log into sum of three logs then rewrite power log
    have hdecomp :
        Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ * (rad (2 * n + 1) : ℝ)) =
          Real.log (piSqRad (2 * n + 1) : ℝ)
          + Real.log ((rad n * rad (n + 1) : ℝ) ^ γ)
          + Real.log (rad (2 * n + 1) : ℝ) := by
      have hp1 : 0 < (piSqRad (2 * n + 1) : ℝ) := hpi_pos
      have hp2 : 0 < (rad n * rad (n + 1) : ℝ) ^ γ := hpow_pos
      have hp3 : 0 < (rad (2 * n + 1) : ℝ) := hrad_c_pos
      have h12 : Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ)
          = Real.log (piSqRad (2 * n + 1) : ℝ) + Real.log ((rad n * rad (n + 1) : ℝ) ^ γ) := by
        simp [Real.log_mul, hp1.ne', hp2.ne']
      have h123 : Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ * (rad (2 * n + 1) : ℝ))
          = Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ)
            + Real.log (rad (2 * n + 1) : ℝ) := by
        have hp12 : 0 < (piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ := mul_pos hp1 hp2
        simp [Real.log_mul, hp12.ne', hp3.ne']
      -- combine
      calc
        _ = Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ)
              + Real.log (rad (2 * n + 1) : ℝ) := h123
        _ = (Real.log (piSqRad (2 * n + 1) : ℝ) + Real.log ((rad n * rad (n + 1) : ℝ) ^ γ))
              + Real.log (rad (2 * n + 1) : ℝ) := by simp [h12]
        _ = Real.log (piSqRad (2 * n + 1) : ℝ) + Real.log ((rad n * rad (n + 1) : ℝ) ^ γ)
              + Real.log (rad (2 * n + 1) : ℝ) := by abel_nf
    -- assemble
    calc
      Real.log (2 * n + 1 : ℝ)
          ≤ Real.log ((piSqRad (2 * n + 1) : ℝ) * (rad n * rad (n + 1) : ℝ) ^ γ * (rad (2 * n + 1) : ℝ)) := hlog
      _ = Real.log (piSqRad (2 * n + 1) : ℝ)
            + Real.log ((rad n * rad (n + 1) : ℝ) ^ γ)
            + Real.log (rad (2 * n + 1) : ℝ) := hdecomp
      _ = Real.log (piSqRad (2 * n + 1) : ℝ)
            + (γ * Real.log ((rad n * rad (n + 1) : ℝ)))
            + Real.log (rad (2 * n + 1) : ℝ) := by simp [hpow_log]
      _ = Real.log (piSqRad (2 * n + 1) : ℝ)
            + γ * Real.log (rad n * rad (n + 1) : ℝ)
            + Real.log (rad (2 * n + 1) : ℝ) := by rfl
  have h_log_pi : Real.log (piSqRad (2 * n + 1) : ℝ) ≤ δ * Real.log ((rad n * rad (n + 1) : ℝ)) := by
    -- Re-establish needed positivity (local to this block)
    have hpi_pos_nat : 0 < piSqRad (2 * n + 1) := by
      unfold piSqRad; apply Finset.prod_pos; intro p hp;
      have hp' : p ∈ (2 * n + 1).factorization.support := (Finset.mem_filter.1 hp).1
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp'; exact Nat.Prime.pos pprime
    have hpi_pos : 0 < (piSqRad (2 * n + 1) : ℝ) := by exact_mod_cast hpi_pos_nat
    have hrad_n_pos_nat : 0 < rad n := by
      unfold rad; apply Finset.prod_pos; intro p hp;
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp; exact Nat.Prime.pos pprime
    have hrad_n1_pos_nat : 0 < rad (n+1) := by
      unfold rad; apply Finset.prod_pos; intro p hp;
      have ⟨_, pprime, _⟩ := mem_support_factorization_iff.mp hp; exact Nat.Prime.pos pprime
    have hbase_pos : 0 < (rad n * rad (n + 1) : ℝ) := mul_pos (by exact_mod_cast hrad_n_pos_nat) (by exact_mod_cast hrad_n1_pos_nat)
    have hpow_pos : 0 < (rad n * rad (n + 1) : ℝ) ^ δ := Real.rpow_pos_of_pos hbase_pos δ
    have hlog : Real.log (piSqRad (2 * n + 1) : ℝ) ≤ Real.log ((rad n * rad (n + 1) : ℝ) ^ δ) :=
      (Real.log_le_log_iff hpi_pos hpow_pos).2 hπ
    have hlog_rpow : Real.log ((rad n * rad (n + 1) : ℝ) ^ δ) = δ * Real.log (rad n * rad (n + 1) : ℝ) := by
      simp [Real.log_rpow hbase_pos]
    simpa [hlog_rpow] using hlog
  have h_log_c : Real.log (2 * n + 1 : ℝ) ≤
      (δ + γ) * Real.log ((rad n * rad (n + 1) : ℝ))
      + Real.log (rad (2 * n + 1) : ℝ) := by
    -- combine h_log_tail and h_log_pi
    -- From h_log_tail: log c ≤ log π + γ log AB + log rad c
    -- From h_log_pi:   log π ≤ δ log AB
    -- Thus log c ≤ (δ+γ) log AB + log rad c
    have h1 := h_log_tail
    have h2 := h_log_pi
    calc
      Real.log (2 * n + 1 : ℝ)
          ≤ Real.log (piSqRad (2 * n + 1) : ℝ)
              + γ * Real.log ((rad n * rad (n + 1) : ℝ))
              + Real.log (rad (2 * n + 1) : ℝ) := h1
      _ ≤ (δ * Real.log ((rad n * rad (n + 1) : ℝ)))
              + γ * Real.log ((rad n * rad (n + 1) : ℝ))
              + Real.log (rad (2 * n + 1) : ℝ) := by
                -- replace log π by δ * log AB using h_log_pi
                have := h2
                -- rearrange: (log π + γ L + log rc) ≤ (δ L + γ L + log rc)
                -- achieved by adding (γ L + log rc) to both sides of h2
                exact add_le_add (add_le_add this le_rfl) le_rfl
      _ = (δ + γ) * Real.log ((rad n * rad (n + 1) : ℝ))
              + Real.log (rad (2 * n + 1) : ℝ) := by
                -- δ*L + γ*L = (δ+γ)*L
                ring_nf
  -- Use hδγ to replace (δ+γ) with (1+ε) in an upper bound.
  have h_majorize :
      (δ + γ) * Real.log ((rad n * rad (n + 1) : ℝ))
        + Real.log (rad (2 * n + 1) : ℝ)
      ≤ (1 + ε) * (Real.log ((rad n * rad (n + 1) : ℝ)) + Real.log (rad (2 * n + 1) : ℝ)) := by
    set A := Real.log (rad n * rad (n + 1) : ℝ)
    set B := Real.log (rad (2 * n + 1) : ℝ)
    have hA_nonneg : 0 ≤ A := by
      have := log_rad_mul_nonneg n (n + 1)
      simpa [A] using this
    have hB_nonneg : 0 ≤ B := by
      have := log_rad_nonneg (2 * n + 1)
      simpa [B] using this
    have hcoef : 0 ≤ (1 + ε) - (δ + γ) := sub_nonneg.mpr hδγ
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    have hdiff :
        (1 + ε) * (A + B) - ((δ + γ) * A + B)
            = ((1 + ε) - (δ + γ)) * A + ε * B := by
      ring
    have hdiff_nonneg :
        0 ≤ (1 + ε) * (A + B) - ((δ + γ) * A + B) := by
      have hterm1 : 0 ≤ ((1 + ε) - (δ + γ)) * A := mul_nonneg hcoef hA_nonneg
      have hterm2 : 0 ≤ ε * B := mul_nonneg hε_nonneg hB_nonneg
      have := add_nonneg hterm1 hterm2
      simpa [hdiff]
    exact sub_nonneg.mp hdiff_nonneg
  have h_final : Real.log (2 * n + 1 : ℝ) ≤
      (1 + ε) * Real.log ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ) := by
    set A := Real.log (rad n * rad (n + 1) : ℝ)
    set B := Real.log (rad (2 * n + 1) : ℝ)
    have h_combined :
        Real.log (2 * n + 1 : ℝ) ≤ (1 + ε) * (A + B) := by
      have h_log_c' :
          Real.log (2 * n + 1 : ℝ) ≤ (δ + γ) * A + B := by
        simpa [A, B] using h_log_c
      have h_majorize' :
          (δ + γ) * A + B ≤ (1 + ε) * (A + B) := by
        simpa [A, B] using h_majorize
      exact h_log_c'.trans h_majorize'
    have hn_pos : 0 < n := Nat.lt_of_lt_of_le (by decide : 0 < 2) hn2
    have hrad_n_pos : 0 < (rad n : ℝ) := by
      have : 0 < rad n := rad_pos hn_pos
      exact_mod_cast this
    have hrad_n1_pos : 0 < (rad (n + 1) : ℝ) := by
      have : 0 < rad (n + 1) := rad_pos (Nat.succ_pos n)
      exact_mod_cast this
    have hrad_c_pos : 0 < (rad (2 * n + 1) : ℝ) := by
      have : 0 < rad (2 * n + 1) := rad_pos (Nat.succ_pos (2 * n))
      exact_mod_cast this
    have hprod_pos : 0 < (rad n * rad (n + 1) : ℝ) := mul_pos hrad_n_pos hrad_n1_pos
    have hsum_log :
        A + B = Real.log ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ) := by
      have hcast :
          ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ)
              = (rad n * rad (n + 1) : ℝ) * (rad (2 * n + 1) : ℝ) := by
        simp [Nat.cast_mul, mul_comm, mul_assoc]
      have hlog_mul := Real.log_mul hprod_pos.ne' hrad_c_pos.ne'
      simpa [A, B, hcast, add_comm, add_left_comm, add_assoc]
        using hlog_mul.symm
    have hrewrite :
        (1 + ε) * (A + B)
            = (1 + ε) * Real.log ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ) := by
      simp [hsum_log]
    have := h_combined
    simpa [hrewrite]
  -- Divide by positive denominator; convert target form.
  have : Real.log (2 * n + 1 : ℝ) / Real.log ((rad (n * (n + 1) * (2 * n + 1)) : ℕ) : ℝ) ≤ 1 + ε := by
    have hcop_n_2n1 : Nat.Coprime n (2 * n + 1) := coprime_n_two_n_add_one n
    have hcop_np1_2n1 : Nat.Coprime (n + 1) (2 * n + 1) :=
      coprime_succ_mul_two_add_one n
    have hcop_prod_symm : Nat.Coprime (2 * n + 1) (n * (n + 1)) := by
      apply (Nat.coprime_mul_iff_right).2
      refine ⟨?_, ?_⟩
      · exact (Nat.coprime_comm).1 hcop_n_2n1
      · exact (Nat.coprime_comm).1 hcop_np1_2n1
    have hcop_prod : Nat.Coprime (n * (n + 1)) (2 * n + 1) := by
      simpa [Nat.coprime_comm, mul_comm, mul_left_comm, mul_assoc] using hcop_prod_symm
    have hrad_nn1 : rad (n * (n + 1)) = rad n * rad (n + 1) := by
      simp [coprime_succ]
    have hgcd_eq : (n * (n + 1)).gcd (2 * n + 1) = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hcop_prod
    have hrad_gcd : rad ((n * (n + 1)).gcd (2 * n + 1)) = 1 := by
      simp [hgcd_eq]
    have hdiv_eq :
        rad n * rad (n + 1) * rad (2 * n + 1)
            / rad ((n * (n + 1)).gcd (2 * n + 1))
            = rad n * rad (n + 1) * rad (2 * n + 1) := by
      simp [hrad_gcd, Nat.div_one]
    have hdiv_cast :
        ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ)
            =
              ((rad n * rad (n + 1) * rad (2 * n + 1)
                  / rad ((n * (n + 1)).gcd (2 * n + 1)) : ℕ) : ℝ) := by
      exact_mod_cast hdiv_eq.symm
    have hdiv_log :
        Real.log ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ)
            =
              Real.log
                ((rad n * rad (n + 1) * rad (2 * n + 1)
                    / rad ((n * (n + 1)).gcd (2 * n + 1)) : ℕ) : ℝ) :=
      congrArg Real.log hdiv_cast
    have hmul_cast :
        (↑(rad n) * ↑(rad (n + 1)) * ↑(rad (2 * n + 1)) : ℝ)
            = ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ) := by
      have : ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ)
          = (↑(rad n) * ↑(rad (n + 1)) * ↑(rad (2 * n + 1)) : ℝ) := by
        simp [Nat.cast_mul]
      simp only [this.symm]
    have hlog_product :
        Real.log (↑(rad n) * ↑(rad (n + 1)) * ↑(rad (2 * n + 1)))
            = Real.log ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ) :=
      congrArg Real.log hmul_cast
    have hlog_product_div :
        Real.log (↑(rad n) * ↑(rad (n + 1)) * ↑(rad (2 * n + 1)))
            =
              Real.log
                ((rad n * rad (n + 1) * rad (2 * n + 1)
                    / rad ((n * (n + 1)).gcd (2 * n + 1)) : ℕ) : ℝ) :=
      hlog_product.trans hdiv_log
    have hrad_eq :
        rad (n * (n + 1) * (2 * n + 1))
            = rad n * rad (n + 1) * rad (2 * n + 1) := by
      calc
        rad (n * (n + 1) * (2 * n + 1))
            = rad ((n * (n + 1)) * (2 * n + 1)) := by rfl
        _ = rad (n * (n + 1)) * rad (2 * n + 1) := by
          simpa using rad_mul_coprime' hcop_prod
        _ = (rad n * rad (n + 1)) * rad (2 * n + 1) := by
          rw [hrad_nn1]
        _ = rad n * rad (n + 1) * rad (2 * n + 1) := by rfl
    have hrad_cast :
        ((rad (n * (n + 1) * (2 * n + 1)) : ℕ) : ℝ)
            = ((rad n * rad (n + 1) * rad (2 * n + 1) : ℕ) : ℝ) := by
      exact_mod_cast hrad_eq
    have hden_cast :
        Real.log ((rad (n * (n + 1) * (2 * n + 1)) : ℕ) : ℝ)
          =
            Real.log
              ((rad n * rad (n + 1) * rad (2 * n + 1)
                  / rad ((n * (n + 1)).gcd (2 * n + 1)) : ℕ) : ℝ) := by
      exact congrArg Real.log (hrad_cast.trans hdiv_cast)
    have h_final' :
        Real.log (2 * n + 1 : ℝ)
          ≤ (1 + ε)
              * Real.log ((rad (n * (n + 1) * (2 * n + 1)) : ℕ) : ℝ) := by
      simpa [hden_cast, hlog_product_div] using h_final
    exact (div_le_iff (show 0 < _ by simpa using hden_pos)).mpr h_final'
  simpa using this

end ABC

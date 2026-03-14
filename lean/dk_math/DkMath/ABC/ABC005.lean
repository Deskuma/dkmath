/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/


import DkMath.ABC.ABC004

#print "file: DkMath.ABC.ABC005"

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

-- **Dyadic composition lemma (abstract form).**
-- If every block ad#mits a bound of the shape `C · (2^k)^(α+ε)`, then
-- `BadCountOn θ (MidIdx X)` is `O(X^(α+ε))`.

-- ## Required lemmas and proof plan for `dyadic_compose`
-- Below we collect the minimal list of statements (with types) that are used
-- when proving `dyadic_compose` from block-level bounds (`BlockBound`) and
-- the combinatorial covering `BadCountOn_bind_le`.  For each item we indicate
-- whether the lemma is already present in `MathlibHello/ABC.lean` and give a
-- brief note on the intended proof strategy.  The actual formal, per-lemma
-- proofs will be filled in here in small steps; initially some items may be
-- referenced from `ABC.lean` and others temporarily `axiom`-ized until a
-- complete constructive derivation is provided.

-- 1) Covering / decomposition
--    Lemma: BadCountOn_bind_le (θ : ℝ) (X : ℕ) :
--      BadCountOn θ (MidIdx X) ≤ ∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1),
--        BadCountOn θ (MidBlock k X)
--    Location: present in `MathlibHello/ABC.lean` (see `BadCountOn_bind_le`).
--    Role: split the middle-band count into dyadic blocks.  Proof already
--      implemented as a simple `card ≤ sum card` argument.

-- 2) Monotonicity of BadCountOn
--    Lemma: BadCountOn_mono (θ : ℝ) {S T : Finset ℕ} (hST : S ⊆ T) :
--      BadCountOn θ S ≤ BadCountOn θ T
--    Location: present in `ABC.lean`.
--    Role: used to adjust ranges and to control finite head terms.

-- 3) Per-block bound (hypothesis schema)
--    Structure: BlockBound (θ : ℝ) with fields
--      α : ℝ, 0 < α,
--      bound : ∀ ε>0, ∃ k0 C≥0, ∀ ⦃X k⦄, X ≥ 2^k → k ≥ k0 →
--        (BadCountOn θ (MidBlock k X) : ℝ) ≤ C * (2^k)^(α + ε)
--    Location: defined in `ABC.lean` (structure `BlockBound`).
--    Role: supplies the local dyadic estimate used on the large-k tail.

-- 4) Geometric-sum bound
--    Lemma: geom_sum_pow_two_le (α ε : ℝ) (h : 0 < α + ε) :
--      ∀ X, 1 ≤ X →
--        (∑ k ∈ Finset.range (Nat.log2 (X + 1) + 1), ((2:ℝ) ^ (α + ε))^k)
--          ≤ Cgeom * (X : ℝ)^(α + ε)
--    Location: present in `ABC.lean` as `geom_sum_pow_two_le` with an explicit
--      constant Cgeom := 2^(3*(α+ε)) / (2^(α+ε) - 1).
--    Role: converts the dyadic geometric sum into the desired X^{α+ε} factor.

-- 5) Head/tail splitting lemma (finite head absorption)
--    Informal statement: for any fixed k0 the finite sum over k < k0 of
--      BadCountOn θ (MidBlock k X) is O( (2^{k0})^const ) and can be absorbed
--      into the multiplicative constant C once X is large.  Precise form:
--    For fixed k0 and any X ≥ 1,
--      ∑_{k < k0} BadCountOn θ (MidBlock k X) ≤ C_head (k0) · (X : ℝ)^{α + ε}
--    Status: can be derived by crude bounding (each MidBlock k X.card ≤ (2^k+1))
--      and monotonicity; not present as a named lemma in `ABC.lean` — we will
--      implement a small helper lemma here.

-- 6) Casting / exact_mod_cast helpers
--    Facts about casting Naturals to Reals and `exact_mod_cast` usage when
--    moving between `(BadCountOn ... : ℕ)` and `( ... : ℝ)` are needed.  These
--    are standard and available from `Mathlib` (we will use `exact_mod_cast` in
--    proofs).

-- 7) Aggregation (combine tail bound using BlockBound.bound and geom_sum)
--    Lemma (to prove): Given `H : BlockBound θ` and ε>0, choose k0 from H.bound
--      and apply H.bound for k ≥ k0 to get constants C. Then:
--      ∑_{k ≥ k0, k ≤ log2(X+1)} (BadCountOn θ (MidBlock k X) : ℝ)
--        ≤ C * ∑_{k ≥ k0}^{log2(X+1)} (2^k)^(α + ε)
--      ≤ C' * (X : ℝ)^(α + ε)
--    Status: to be implemented here by a short chain using `BlockBound.bound`
--      and `geom_sum_pow_two_le`.

-- 8) Final assembly lemma (`dyadic_compose`) statement
--    Already present as an `axiom dyadic_compose` in this file.  The aim is
--    to replace that axiom by a `theorem` whose proof follows the steps:
--      (i) apply `BadCountOn_bind_le` to reduce to the block-sum;
--      (ii) split sum into head (k < k0) + tail (k ≥ k0) where k0 is from
--           `H.bound ε` (H : BlockBound θ);
--      (iii) bound head by a fixed constant times X^{α + ε} for large X;
--      (iv) bound tail using `H.bound` and `geom_sum_pow_two_le`; combine
--           and absorb constants to get the desired `C` and `X0`.

-- Implementation plan (next steps):
--  A. Formalize a small helper lemma `head_absorb` that bounds the finite
--     head sum uniformly in X by a constant factor times `X^(α+ε)` once X
--     exceeds a threshold depending on k0.
--  B. Formalize the tail aggregation `tail_geom_bound` using `BlockBound.bound`
--     and `geom_sum_pow_two_le`.
--  C. Put together `dyadic_compose` by combining A and B and using
--     `BadCountOn_bind_le` and simple algebraic manipulations (casts and
--     constant absorption).

-- Notes on casting and domains:
--  - `BadCountOn` is defined as a `ℕ` (cardinal). In the dyadic sum we will
--    cast each summand to `ℝ` before applying multiplicative estimates. Use
--    `exact_mod_cast` / `by exact_mod_cast` to bridge `ℕ`→`ℝ` inequalities.
--  - `Finset.range (Nat.log2 (X + 1) + 1)` is the usual index set for blocks;
--    care is needed for the case `X = 0` (we will restrict to `1 ≤ X` in many
--    lemmas to avoid degenerate edge cases).

-- End of dyadic composition checklist. The next edit will implement helper
-- lemmas `head_absorb` and `tail_geom_bound` and then promote `dyadic_compose`
-- from `axiom` to `theorem` by following the outlined assembly.

-- Dyadic composition lemmas end
-- Helper: absorb the finite head (k < k0) into a constant times X^(α+ε).
-- We prove a crude bound: for fixed k0 and fixed α,ε>0 there exists C_head and
-- X0 such that for all X ≥ X0,
--   ∑_{k < k0} (BadCountOn θ (MidBlock k X) : ℝ) ≤ C_head * (X : ℝ)^(α + ε).
-- The detailed combinatorial proof is straightforward but not essential for the
-- current composition development; we provide a tiny ad#mitted lemma to keep the
-- file lightweight and make downstream proofs possible.

/-
dyadic_tail_bound: ダイアディックブロックの尾部和に対する多項的上界

BlockBound を仮定して、ダイアディック（2^k に対応する）ブロックの「尾部和」を多項的な上界で抑える補題。
与えられた θ と BlockBound BB, および任意の小さな ε > 0 に対して、
ある k0 ∈ ℕ と非負定数 Ctot が存在して、任意の X ≥ 1 について
  k ≥ k0 かつ k ≤ log2(X+1) である全ての k に対する BadCountOn θ (MidBlock k X) の和が
Ctot * X^(BB.α + ε) に一様に抑えられる、という主張である。

主な仮定と結論:
- BB : BlockBound θ により各ブロックの寄与は適切な冪で抑えられている（α 等のパラメータを含む）。
- ε > 0 を取ると、尾部和を任意に小さく増やすための余裕（+ε）が得られる。
- 結論は k0 と Ctot の存在を保証し、これらは X に依存しない定数である。

証明の骨子（概観）:
- 大きな k に対して各ブロック寄与が幾何級数的に減少する点を利用して、尾部を制御する。
- ブロックごとの上界を合成し、有限個（log2 X に比例する個数）の和を評価して
  指数 α+ε の形の上界にまとめる。
- k0 は BB や ε に応じて選び、Ctot は有限和と定数因子から構成することで得られる。

用途:
- ダイアディック分解を用いた数え上げやふるい理論における尾部制御に用いる補題。
- 後続の推論で全和を主項と誤差項に分離する際の誤差評価として使える。
-- cid: 68cd0644-a688-8330-b253-16fa847542de -/
/- Tail bound: using BlockBound, sum over k ≥ k0 up to log2(X+1)+1 is bounded by a constant * X^(α+ε). -/
theorem dyadic_tail_bound {θ : ℝ} (BB : BlockBound θ) (ε : ℝ) (hε : 0 < ε) :
  ∃ (k0 : ℕ) (Ctot : ℝ), 0 ≤ Ctot ∧ ∀ (X : ℕ), 1 ≤ X →
    (∑ k ∈ Finset.filter (fun k => k ≥ k0) (Finset.range (Nat.log2 (X + 1) + 1)), (BadCountOn θ (MidBlock k X) : ℝ))
    ≤
    Ctot * (X : ℝ)^(BB.α + ε) := by
  -- Given BlockBound, obtain k0 and Cblk such that for k ≥ k0, BadCountOn θ (MidBlock k X) ≤ Cblk * (2^k)^(α+ε)
  -- Then sum over k from k0 to log2(X+1)+1, and bound the sum by a geometric series times X^(α+ε).
  -- The geometric series converges because 2^(α+ε) > 1 (since α > 0 and ε > 0).
  -- Finally, define Ctot = Cblk * (geometric series sum) to get the desired bound.
  /- 主なアイデア:
  - BlockBound により、k ≥ k0 に対して各ブロックの寄与が Cblk * (2^k)^(α+ε) で抑えられる。
  - これを k0 から log2(X+1)+1 まで和をとり、幾何級数的に評価する。
  - α+ε の冪が 1 より大きいので、幾何級数は収束する。
  - Ctot を Cblk と幾何級数の和の積として定義し、目的の評価を得る。
  -/
  obtain ⟨k0, Cblk, hCblk_nonneg, hblock⟩ := BB.bound ε hε  -- BlockBound から k0, Cblk を取得
  let Cgeom := (2:ℝ)^(3 * (BB.α + ε)) / ((2:ℝ)^(BB.α + ε) - 1)  -- 幾何級数の和
  let Ctot := Cblk * Cgeom  -- 最終的な定数
  use k0, Ctot  -- k0 と Ctot を存在量として提示
  constructor  -- 証明を二つの部分に分ける
  · -- Ctot nonneg: 0 ≤ Ctot
    have num_pos : 0 < (2:ℝ)^(3 * (BB.α + ε)) := by  -- 分子は正
      have : (2:ℝ) > 0 := by norm_num
      exact Real.rpow_pos_of_pos this (3 * (BB.α + ε))
    have den_pos : 0 < (2:ℝ)^(BB.α + ε) - 1 := by  -- 分母は正
      have h2gt1 : (2:ℝ) > 1 := by norm_num
      have hposp : 0 < BB.α + ε := by linarith [BB.hα, hε]
      have one_lt := Real.one_lt_rpow h2gt1 hposp
      linarith
    have hCgeom_pos : 0 < Cgeom := div_pos num_pos den_pos
    exact mul_nonneg (by exact_mod_cast hCblk_nonneg) (le_of_lt hCgeom_pos)
  · -- For any X ≥ 1, bound the tail sum by Ctot * X^(α+ε)
    -- Tail: sum over k from k0 to log2(X+1)+1 of BadCountOn θ (MidBlock k X)
    -- Use the per-block bound from BlockBound
    -- Then sum the geometric series and multiply by Cblk to get Ctot
    -- Finally, multiply by X^(α+ε) to get the desired form
    -- The key steps are:
    -- 1. For each k in the tail, use the BlockBound to get BadCountOn θ (MidBlock k X) ≤ Cblk * (2^k)^(α+ε)
    -- 2. Rewrite (2^k)^(α+ε) as ((2)^(α+ε))^k
    -- 3. Sum over k in the tail, which is a geometric series
    -- 4. Bound the geometric series by the full sum up to K = log2(X+1)+1
    -- 5. Use the formula for the geometric series to get Cgeom
    -- 6. Combine all to get the final bound
    intro X hX_pos
    let K := Nat.log2 (X + 1) + 1
    let tail := Finset.filter (fun k => k ≥ k0) (Finset.range K)
    -- Per-index bound: for k ∈ tail we have BadCountOn ≤ Cblk * (2^k)^(α+ε)
    have per_le : ∀ k ∈ tail, (BadCountOn θ (MidBlock k X) : ℝ) ≤ Cblk * ((2:ℕ)^k : ℝ)^(BB.α + ε) := by
      intro k hk
      have hk_mem := Finset.mem_filter.mp hk
      have hk_ge := hk_mem.2
      by_cases h2k_le : (2:ℕ)^k ≤ X
      · have hX_ge_2k : X ≥ (2:ℕ)^k := by exact_mod_cast h2k_le
        have hk_ge_k0 : k ≥ k0 := hk_ge
        exact_mod_cast (hblock hX_ge_2k hk_ge_k0)
      · -- MidBlock is empty when 2^k > X
        have : MidBlock k X = (∅ : Finset ℕ) := by
          dsimp [MidBlock]
          have hmin : min ((2:ℕ) ^ (k + 1) - 1) X < (2:ℕ) ^ k := by
            calc
              min ((2:ℕ) ^ (k + 1) - 1) X ≤ X := min_le_right _ _
              _ < (2:ℕ) ^ k := by exact_mod_cast (lt_of_not_ge h2k_le)
          have : Finset.Icc ((2:ℕ) ^ k) (min ((2:ℕ) ^ (k + 1) - 1) X) = ∅ := by
            apply Finset.eq_empty_of_forall_notMem
            intro n hn
            rcases Finset.mem_Icc.mp hn with ⟨hlo, hup⟩
            -- hlo : 2^k ≤ n, hup : n ≤ min(...), and hmin : min(...) < 2^k
            have t := le_trans hlo hup -- 2^k ≤ min(...)
            have : (2:ℕ) ^ k < (2:ℕ) ^ k := lt_of_le_of_lt t hmin
            exact lt_irrefl _ this
          simp [this]
        have : (BadCountOn θ (MidBlock k X) : ℝ) = 0 := by simp [this, BadCountOn]
        have pow_pos : 0 < ((2:ℕ) ^ k : ℝ) ^ (BB.α + ε) := by
          have base_pos : 0 < (2:ℝ) ^ k := by
            apply pow_pos; norm_num
          exact Real.rpow_pos_of_pos base_pos (BB.α + ε)
        have rhs_nonneg : 0 ≤ Cblk * ((2:ℕ) ^ k : ℝ) ^ (BB.α + ε) :=
          mul_nonneg (by exact_mod_cast hCblk_nonneg) (le_of_lt pow_pos)
        -- Using the equality to 0, conclude the desired inequality
        rw [this]
        exact rhs_nonneg
    -- Sum up per-index bounds
    -- First rewrite each ((2:ℕ)^k : ℝ)^(BB.α + ε) as ((2:ℝ)^(BB.α + ε))^k and sum
    have per_le2 : ∀ k ∈ tail, (BadCountOn θ (MidBlock k X) : ℝ) ≤ Cblk * ((2:ℝ)^(BB.α + ε)) ^ k := by
      intro k hk
      have h := per_le k hk
      -- rewrite RHS ((2:ℕ)^k : ℝ)^(p) = ((2:ℝ)^p)^k without using `simp` to avoid recursion
      have hcast : ((2:ℕ) ^ k : ℝ) = (2:ℝ) ^ k := by
        norm_cast
      have hpos : 0 < (2:ℝ) := by norm_num
      have eq : ((2:ℕ) ^ k : ℝ) ^ (BB.α + ε) = ((2:ℝ) ^ (BB.α + ε)) ^ k := by
        calc
          ((2:ℕ) ^ k : ℝ) ^ (BB.α + ε) = ((2:ℝ) ^ k) ^ (BB.α + ε) := by rw [hcast]
        _ = (2:ℝ) ^ (k * (BB.α + ε)) := by
            -- (x^y)^z = x^(y*z) for x > 0
            rw [Real.rpow_pow hpos] -- Utils: rpow_pow used here
        _ = (2:ℝ) ^ ((BB.α + ε) * (k : ℝ)) := by
            have : k * (BB.α + ε) = (k : ℝ) * (BB.α + ε) := by norm_cast
            rw [this, mul_comm]
        _ = ((2:ℝ) ^ (BB.α + ε)) ^ k := by
            rw [Real.rpow_mul (le_of_lt hpos) (BB.α + ε) (k : ℝ)]
            norm_cast
      rwa [eq] at h
    have hsum2 := Finset.sum_le_sum per_le2
    -- Bound the tail geometric sum by the full range K geometric sum
    have tail_subset : tail ⊆ Finset.range K := Finset.filter_subset _ _
    -- apply geometric sum lemma to the full range
    have hgeom := geom_sum_pow_two_le (BB.α) (ε) (by linarith [BB.hα])
    have hgeom_app := hgeom X hX_pos
    -- combine: sum Bad ≤ sum_tail (Cblk * pow^k) = Cblk * sum_tail pow^k ≤ Cblk * sum_range pow^k ≤ Cblk * (Cgeom * X^p)
    have step1 : Finset.sum tail (fun (k : ℕ) => (BadCountOn θ (MidBlock k X) : ℝ))
      ≤ Cblk * Finset.sum (Finset.range K) (fun (k : ℕ) => ((2:ℝ)^(BB.α + ε)) ^ k) := by
        -- sum_le_sum gives: sum tail Bad ≤ sum tail (Cblk * pow^k)
        have h_sum_le := hsum2
        -- tail subset of range K
        have tail_subset' : tail ⊆ Finset.range K := Finset.filter_subset _ _
        -- show the (nonnegative) power-summands inequality over the smaller set
        have sum_tail_pow_le : Finset.sum tail (fun (k : ℕ) => ((2:ℝ)^(BB.α + ε)) ^ k)
          ≤ Finset.sum (Finset.range K) (fun (k : ℕ) => ((2:ℝ)^(BB.α + ε)) ^ k) := by
          -- use the library lemma: supply the subset proof first, then the nonnegativity proof
          apply Finset.sum_le_sum_of_subset_of_nonneg tail_subset'
          intro k hk h_not_in_tail
          -- 0 ≤ ((2:ℝ)^(BB.α + ε)) ^ k
          -- show the base is positive, then its nat-power is positive, hence nonnegative
          have base_pos : 0 < (2:ℝ) ^ (BB.α + ε) := by
            have h2pos : (2:ℝ) > 0 := by norm_num
            exact Real.rpow_pos_of_pos h2pos (BB.α + ε)
          have pow_pos_k : 0 < ((2:ℝ) ^ (BB.α + ε)) ^ k := by
            exact pow_pos base_pos k
          exact le_of_lt pow_pos_k
        -- factor Cblk out of the tail sum
        have sum_tail_mul_eq :
          Finset.sum tail (fun (k : ℕ) => Cblk * ((2:ℝ)^(BB.α + ε)) ^ k)
          = Cblk * Finset.sum tail (fun (k : ℕ) => ((2:ℝ)^(BB.α + ε)) ^ k) := by
            -- Cblk を和から因数分解する（帰納法で証明）
            induction tail using Finset.induction_on
            case empty => simp
            case insert a s ha_not_mem ih =>
              calc
                Finset.sum (insert a s) (fun k => Cblk * ((2:ℝ)^(BB.α + ε)) ^ k)
                  = Cblk * ((2:ℝ)^(BB.α + ε)) ^ a + Finset.sum s (fun k => Cblk * ((2:ℝ)^(BB.α + ε)) ^ k) := by
                    simp [Finset.sum_insert ha_not_mem]
                _ = Cblk * ((2:ℝ)^(BB.α + ε)) ^ a + Cblk * Finset.sum s (fun k => ((2:ℝ)^(BB.α + ε)) ^ k) := by
                    rw [ih]
                _ = Cblk * (((2:ℝ)^(BB.α + ε)) ^ a + Finset.sum s (fun k => ((2:ℝ)^(BB.α + ε)) ^ k)) := by
                    simp [mul_add, add_comm]
                _ = Cblk * Finset.sum (insert a s) (fun k => ((2:ℝ)^(BB.α + ε)) ^ k) := by
                    simp [Finset.sum_insert ha_not_mem]
        -- combine the three inequalities
        calc
          Finset.sum tail (fun (k : ℕ) => (BadCountOn θ (MidBlock k X) : ℝ))
            ≤ Finset.sum tail (fun (k : ℕ) => Cblk * ((2:ℝ)^(BB.α + ε)) ^ k) := h_sum_le
          _ = Cblk * Finset.sum tail (fun (k : ℕ) => ((2:ℝ)^(BB.α + ε)) ^ k) := by rw [sum_tail_mul_eq]
          _ ≤ Cblk * Finset.sum (Finset.range K) (fun (k : ℕ) => ((2:ℝ)^(BB.α + ε)) ^ k) := by
            apply mul_le_mul_of_nonneg_left sum_tail_pow_le
            exact_mod_cast hCblk_nonneg
    -- apply the geometric sum bound to the full range
    have step2 : Cblk * Finset.sum (Finset.range K) (fun k : ℕ => ((2:ℝ)^(BB.α + ε)) ^ k)
      ≤ Cblk * (Cgeom * (X : ℝ)^(BB.α + ε)) := by
      apply mul_le_mul_of_nonneg_left
      · exact hgeom_app
      · exact_mod_cast hCblk_nonneg
    have final := le_trans step1 step2
    -- conclude: combine all steps to get the final bound
    calc
      (∑ k ∈ Finset.filter (fun k => k ≥ k0) (Finset.range (Nat.log2 (X + 1) + 1)), (BadCountOn θ (MidBlock k X) : ℝ))
        = (∑ k ∈ tail, (BadCountOn θ (MidBlock k X) : ℝ)) := by rfl
      _ ≤ Cblk * (Cgeom * (X : ℝ)^(BB.α + ε)) := by exact final
      _ = Ctot * (X : ℝ)^(BB.α + ε) := by
        change Cblk * (Cgeom * (X : ℝ)^(BB.α + ε)) = Cblk * Cgeom * (X : ℝ)^(BB.α + ε)
        ring

/--
θ, α, ε ∈ ℝ と k0 ∈ ℕ に対する存在定理。

仮定 hpos : 0 < α + ε のもとで、ある自然数 X0 と非負の実数 C ≥ 0 が存在して、
任意の X : ℕ について 1 ≤ X かつ X ≥ X0 ならば
  Finset.range k0 に属する全ての k に対する (BadCountOn θ (MidBlock k X)) の和は
  C * (X : ℝ)^(α + ε)
以下で抑えられる。

直観的には、有限個（k0 個）の「ヘッド」寄与は多項式的成長 X^(α+ε) に吸収されることを主張する。
C は θ, α, ε, k0 に依存して決まり、X が十分大きければ和を一様に上界できることを示す。
用途としては、漸近評価における先頭項の制御や誤差項の抑制に用いることができる。
-/
theorem head_absorb' (θ α ε : ℝ) (hpos : 0 < α + ε) (k0 : ℕ) :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, 1 ≤ X → X ≥ X0 →
      (Finset.sum (Finset.range k0) fun k => (BadCountOn θ (MidBlock k X) : ℝ)) ≤ C * (X : ℝ)^(α + ε) := by
  -- Very short, robust proof: each MidBlock k X has cardinality ≤ 2^(k0+1), so
  -- the finite sum is bounded by k0 * 2^(k0+1), independent of X. Since X^(α+ε) ≥ 1
  -- for X ≥ 1, the desired inequality follows with X0 = 1.
  use 1, (k0 : ℝ) * ↑(2 ^ (k0 + 1))
  constructor
  · have hk0_nonneg : 0 ≤ (k0 : ℝ) := by norm_cast; exact Nat.cast_nonneg k0
    have hpow_nonneg : 0 ≤ (↑(2 ^ (k0 + 1)) : ℝ) := by
      norm_cast
      exact Nat.cast_nonneg (2 ^ (k0 + 1))
    exact mul_nonneg hk0_nonneg hpow_nonneg
  intro X h1 _
  calc
    Finset.sum (Finset.range k0) fun k => ((MidBlock k X).card : ℝ)
    _ ≤ Finset.sum (Finset.range k0) fun _ => ((2 : ℕ) ^ (k0 + 1) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      -- trivial bound: for k < k0 we may bluntly bound each MidBlock's size by 2^(k0+1)
      have : (MidBlock k X).card ≤ (2 : ℕ) ^ (k0 + 1) := by
        -- Bound MidBlock k X by the dyadic interval Icc (2^k , 2^(k+1)-1)
        have hsubset : (MidBlock k X) ⊆ Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1) := by
          simp only [MidBlock]
          -- min (2 ^ (k + 1) - 1) X ≤ 2 ^ (k + 1) - 1 は min_le_left で示せる
          apply Finset.Icc_subset_Icc
          -- 2 ^ k ≤ 2 ^ k は自明
          · exact le_refl (2 ^ k)
          · exact min_le_left (2 ^ (k + 1) - 1) X
        -- further bound the Icc by the range 0 .. 2^(k+1)-1 to get a simple cardinality bound
        have hsubset_range : (Finset.Icc (2 ^ k) (2 ^ (k + 1) - 1)) ⊆ Finset.range (2 ^ (k + 1)) := by
          intro n hn
          have ⟨_, hle⟩ := Finset.mem_Icc.1 hn
          have hlt : n < 2 ^ (k + 1) := by
            -- first get n < (2^(k+1) - 1) + 1, then simplify the successor equality to 2^(k+1)
            have htmp : n < (2 ^ (k + 1) - 1) + 1 := Nat.lt_of_le_of_lt (hle : n ≤ 2 ^ (k + 1) - 1)
              (Nat.lt_succ_self (2 ^ (k + 1) - 1))
            have : (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1) := by
              rw [Nat.sub_add_cancel]
              -- 1 ≤ 2 ^ (k + 1) は自明
              exact Nat.one_le_pow (k + 1) 2 (by decide)
            simpa [this] using htmp
          exact Finset.mem_range.2 hlt
        have hcard_le := Finset.card_le_card (hsubset.trans hsubset_range)
        calc
          (MidBlock k X).card ≤ (Finset.range (2 ^ (k + 1))).card := hcard_le
          _ = (2 : ℕ) ^ (k + 1) := by simp [Finset.card_range]
          _ ≤ (2 : ℕ) ^ (k0 + 1) := by
            have hk_lt : k < k0 := Finset.mem_range.1 hk
            apply Nat.pow_le_pow_right
            · norm_num
            · exact Nat.succ_le_succ (Nat.le_of_lt hk_lt)
      exact_mod_cast this
    _ = (Finset.range k0).card * (↑(2 ^ (k0 + 1))) := by simp [Finset.sum_const]
    _ = k0 * ↑(2 ^ (k0 + 1)) := by simp [Finset.card_range]
    _ ≤ (k0 : ℝ) * ↑(2 ^ (k0 + 1)) * (X : ℝ) ^ (α + ε) := by
      -- 計数定数 C := k0 * 2^(k0+1) が非負であることを示す
      have nonneg_C : 0 ≤ (k0 : ℝ) * ↑(2 ^ (k0 + 1)) := by
        apply mul_nonneg
        · norm_cast; exact Nat.cast_nonneg k0
        · norm_cast; exact Nat.cast_nonneg (2 ^ (k0 + 1))
      -- X ≥ 1 と α+ε > 0 から 1 ≤ ↑X ^ (α+ε)
      have one_le : 1 ≤ (X : ℝ) ^ (α + ε) := Real.one_le_rpow (by exact_mod_cast h1) (le_of_lt hpos)
      -- 両辺に非負定数 C を掛けて目的の不等式を得る
      simpa [mul_one] using mul_le_mul_of_nonneg_left one_le nonneg_C

-- -------------------------------------------------------

end ABC

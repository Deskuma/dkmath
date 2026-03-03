/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.ABC.Core

#print "file: DkMath.ABC.Triple"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace ABC

/-
  ABC/FormalBridge.lean
  中帯強化と squarefull 決定論強化を「外部結果」として受ける受け皿。
  以降の代数合成は Lean 内で厳密化する。
-/

/-- “悪い三つ組”の述語： a+b=c, coprime, かつ要石に違反（∏p^2|c > (rad a rad b)^δ） -/
structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  hsum  : a + b = c
  hcop  : Nat.Coprime a b

/-- “悪い三つ組”の述語 -/
def Bad (δ : ℝ) (T : Triple) : Prop :=
  let lhs := (T.c.factorization.support.filter (fun p => 2 ≤ T.c.factorization p)).prod id
  let rhs := (rad T.a * rad T.b : ℕ)
  (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ)

/-- “X 以下”の悪い組の個数 -/
noncomputable def BadCount (δ : ℝ) (X : ℕ) : ℕ :=
  -- enumerate all numeric triples (a,b,c) with components ≤ X, then filter by the predicate
  let ranges := ((Finset.range (X+1)).product (Finset.range (X+1))).product (Finset.range (X+1))
  -- predicate on a triple encoded as ((a, b), c)
  let P := fun t : (ℕ × ℕ) × ℕ =>
    let a := t.1.1
    let b := t.1.2
    let c := t.2
    a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ a + b = c ∧ Nat.Coprime a b ∧
      let lhs := (c.factorization.support.filter fun p => 2 ≤ c.factorization p).prod id
      let rhs := (rad a * rad b : ℕ)
      (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ)
  (@Finset.filter ((ℕ × ℕ) × ℕ) P (fun t => Classical.propDecidable (P t)) ranges).card

/-- squarefull 決定論の外部結果（強化版） -/
/- NOTE: Axiomatic assumption (placeholder).
   This squarefull determinism strong bound is currently taken as an
   external input. In future work it should be replaced by a proved
   statement or a citation-filled lemma. It is left as an `axiom` to
   keep the algebraic parts of the formalization modular and readable.
  -/
axiom Squarefull_determinism_strong
  (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 1) :
  ∃ (X0 : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ ⦃X : ℕ⦄, X ≥ X0 →
      -- 記号上は別カウントだが、結論は 1.75 へ吸い込むための“第二の蓋”
      BadCount (0.435) X ≤ ⌈C * ((X : ℝ) ^ (1.75 : ℝ) + (X : ℝ) ^ ((2 : ℝ) - κ/2))⌉₊

/-- 固定 b, 上界 X のスライス上で Bad な a の本数 -/
-- Top-level predicate for 'a is bad for fixed δ,X,b'.
def is_bad_a (δ : ℝ) (X b a : ℕ) : Prop :=
  ∃ (h : Nat.Coprime a b), a ≤ X ∧ b ≤ X ∧ a + b ≤ X ∧ Bad δ ⟨a, b, a + b, rfl, h⟩

noncomputable instance decidable_is_bad_a (δ : ℝ) (X b a : ℕ) : Decidable (is_bad_a δ X b a) :=
  Classical.propDecidable _

/-/ 固定 b, 上界 X のスライス上で Bad な a の本数 -/
noncomputable def sliceBadCount (δ : ℝ) (X b : ℕ) : ℕ :=
  ((Finset.range (X+1)).filter (fun a => is_bad_a δ X b a)).card

/-- 自明のスライス上界：どの b に対してもスライス内の a の個数は高々 X+1 である -/
@[simp]
lemma sliceBadCount_le_trivial (δ : ℝ) (X b : ℕ) :
  sliceBadCount δ X b ≤ X + 1 := by
  dsimp [sliceBadCount]
  have : ((Finset.range (X+1)).filter fun a => is_bad_a δ X b a).card ≤ (Finset.range (X+1)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  exact Nat.le_trans this (by simp)

/-
より良い下位 bound を得る場合、例えば a+b ≤ X の制約を使うとスライスごとの a の取り得る範囲は 0..(X-b) で長さは X-b+1 になる。
以下の補題はその形の自明 bound を与える（b ≤ X の場合のみ）。
-/
@[simp]
lemma sliceBadCount_le_X_sub_b (δ : ℝ) {X b : ℕ} (hb : b ≤ X) :
  sliceBadCount δ X b ≤ (X - b) + 1 := by
  dsimp [sliceBadCount]
  -- filter 範囲を Finset.range (X - b + 1) に狭める写像を作る
  have hsub : ((Finset.range (X+1)).filter fun a => is_bad_a δ X b a) ⊆ (Finset.range (X - b + 1)) := by
    intro a ha
    rcases Finset.mem_filter.1 ha with ⟨ha_range, ha_bad⟩
    -- ha_range : a ∈ Finset.range (X+1) ⇒ a ≤ X
    have ha_le : a ≤ X := Nat.le_of_lt_succ (Finset.mem_range.mp ha_range)
    -- from is_bad_a we have a + b ≤ X
    rcases ha_bad with ⟨_hcop, hleft⟩
    rcases hleft with ⟨ha_le', hb_le', hab_le, _⟩
    -- hab_le : a + b ≤ X gives a ≤ X - b (use Nat.le_sub_iff_add_le with b ≤ X)
    have : a ≤ X - b := (Nat.le_sub_iff_add_le hb).mpr hab_le
    -- now a ∈ range (X - b + 1)
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le this
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_range] at hcard
  exact hcard

/-
より精密な補題（保守的な combinatorial bound）の追加：
`Bad δ ⟨a,b,c,...⟩` が成り立つとき、c の平方因子由来の積 lhs が大きいことにより
rad a * rad b が比較的小さい（または逆）である関係を利用して a の可能性を制限する。
ここではまず、lhs ≥ 1 かつ lhs divides c などの自明観察から出発する単純補題を入れる。
-/

/-- 保守的補題：もし `Bad δ ⟨a,b,c,...⟩` ならば、
   c に寄与する平方因子の積 (lhs) は 1 以上で、lhs ≤ c かつ lhs ≤ (rad a * rad b) ^? のような関係を扱うための基本補題。 -/
lemma bad_implies_squarefactor_bounds {_ : ℝ} {T : Triple} :
  1 ≤ (T.c.factorization.support.filter fun p => 2 ≤ T.c.factorization p).prod id := by
  -- lhs は積なので自然に 1 以上（空積 = 1）
  let lhs := (T.c.factorization.support.filter fun p => 2 ≤ T.c.factorization p).prod id
  have : 0 < (lhs : ℕ) := by
    -- 集合上の素数は正なので積は正
    have hpos : ∀ q ∈ T.c.factorization.support.filter fun p => 2 ≤ T.c.factorization p, 0 < q := by
      intro q hq
      -- q が support に含まれるなら q は素数で 0 ではない
      have hsup := (Finset.mem_filter.1 hq).1
      rcases mem_support_factorization_iff.mp hsup with ⟨_nz, hp, _⟩
      exact Nat.pos_of_ne_zero (Nat.Prime.ne_zero hp)
    exact Finset.prod_pos hpos
  exact Nat.one_le_of_lt (by exact_mod_cast this)

/-- If `Bad δ T` holds then the square-factor product (as a real) is bounded below
   by (rad a * rad b)^δ - 1. This extracts a convenient real inequality from the
   `Bad` predicate which mentions `Nat.floor`. -/
lemma bad_implies_lhs_gt_pow_sub_one {δ : ℝ} {T : Triple} (h : Bad δ T) :
  ((T.c.factorization.support.filter fun p => 2 ≤ T.c.factorization p).prod fun p => (p : ℝ))
    > ((rad T.a * rad T.b : ℕ) : ℝ) ^ δ - 1 := by
  -- Unfold Bad to get the integer inequality involving Nat.floor
  dsimp [Bad] at h
  let lhs := (T.c.factorization.support.filter fun p => 2 ≤ T.c.factorization p).prod id
  let rhs := (rad T.a * rad T.b : ℕ)
  -- h : (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ)
  have hnat : (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ) := h
  -- cast to reals
  have hreal : ((lhs : ℕ) : ℝ) > (Nat.floor ((rhs : ℝ) ^ δ) : ℝ) := by exact_mod_cast hnat
  let y := (rhs : ℝ) ^ δ
  -- from hnat : (lhs : ℕ) > Nat.floor y we obtain Nat.floor y + 1 ≤ lhs
  have hsucc_le : (Nat.floor y) + 1 ≤ lhs := Nat.succ_le_of_lt (by exact hnat)
  -- y is nonnegative because rhs is a nat cast, so we can use Nat.lt_floor_add_one
  have hy_nonneg : 0 ≤ y := by apply Real.rpow_nonneg; exact_mod_cast Nat.zero_le rhs
  have hlt := Nat.lt_floor_add_one y
  -- coerce the integer inequality to reals
  have hcoerc : ((Nat.floor y) + 1 : ℝ) ≤ (lhs : ℝ) := by exact_mod_cast hsucc_le
  -- combine y < ... ≤ lhs to get y < (lhs : ℝ)
  have hy_lt_lhs : y < (lhs : ℝ) := lt_of_lt_of_le hlt hcoerc
  -- express (lhs : ℝ) as the product and rewrite the goal to use (lhs : ℝ)
  have hprod_real_eq : ((lhs : ℕ) : ℝ) = (T.c.factorization.support.filter fun p => 2 ≤ T.c.factorization p).prod fun p => (p : ℝ) := by simp [lhs]
  rw [←hprod_real_eq]
  -- now the goal is (lhs : ℝ) > y - 1 and follows since lhs > y > y - 1
  linarith [hy_lt_lhs]


/--
任意の実数 δ と自然数 X に対して、

  ∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℕ) ≤ BadCount δ X

が成り立つことを表す補題の説明コメント。

内容（直感）:
各 `sliceBadCount δ X b` はスライス `b` に属する「悪い」要素の個数を表しており、
`BadCount δ X` は全体としての悪い要素の個数を表すと想定している。各悪い要素は定義に
従って少なくとも一つのスライスに属するため、スライスごとの個数を総和したものは全体の
個数を超えない、という直感に基づく不等式である。

前提:
この補題は `sliceBadCount` と `BadCount` の定義に依存する。特に各要素がどのように
スライスに割り当てられるか、`sliceBadCount` がどの型で定義されているか（ここでは
自然数へ coercion されている点）を前提としている。

証明方針の概略:
各「悪い」要素を対応するスライスへ写し、その写像によりスライスごとの和が全体の
個数に対応付けられることを示す。必要に応じて coercion の単調性や Finset の和に関する
基本的な不等式を利用する。

用途:
スライス単位で得た上界（局所的な悪さの合計）を全体の上界（グローバルな BadCount）に
変換する際に使う標準的な補題。
-/
@[simp]
lemma slice_sum_le_badcount (δ : ℝ) (X : ℕ) :
  (∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℕ)) ≤ BadCount δ X := by
  -- build the sigma S so the sum of slice counts equals S.card
  let S : Finset (Σ b, ℕ) := Finset.sigma (Finset.range (X+1)) fun b => (Finset.range (X+1)).filter (fun a => is_bad_a δ X b a)
  have hsum_card : (∑ b ∈ Finset.range (X+1), (sliceBadCount δ X b : ℕ)) = S.card := by
    dsimp [sliceBadCount]
    rw [Finset.card_sigma]

  -- ranges and predicate P mirror the definition used in BadCount (see ABCFinal)
  let ranges := ((Finset.range (X+1)).product (Finset.range (X+1))).product (Finset.range (X+1))
  let P := fun t : (ℕ × ℕ) × ℕ =>
    let a := t.1.1; let b := t.1.2; let c := t.2
    a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ a + b = c ∧ Nat.Coprime a b ∧
      let lhs := (c.factorization.support.filter fun p => 2 ≤ c.factorization p).prod id
      let rhs := (rad a * rad b : ℕ)
      (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ)

  let f : (Σ b, ℕ) → ((ℕ × ℕ) × ℕ) := fun ⟨b, a⟩ => ((a, b), a + b)
  let img := S.image f

  -- every element of img satisfies the ranges.filter P predicate
  have h_subset : img ⊆ ranges.filter P := by
    intro y hy
    -- unpack y ∈ img as y = f p with p ∈ S
    obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hbR, ha_mem⟩ := Finset.mem_sigma.1 hpS
    rcases Finset.mem_filter.1 ha_mem with ⟨haR, haP⟩
    -- haP : is_bad_a δ X p.fst p.snd, so unpack its witness
    rcases haP with ⟨hcop, rest⟩
    rcases rest with ⟨ha_le, rest₂⟩
    rcases rest₂ with ⟨hb_le, rest₃⟩
    rcases rest₃ with ⟨hab_le, hbad⟩
    -- build membership in the product and ranges
    have hpair : (p.snd, p.fst) ∈ (Finset.range (X+1)).product (Finset.range (X+1)) :=
      Finset.mem_product.2 ⟨haR, hbR⟩
    have hsum : p.snd + p.fst ∈ Finset.range (X+1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (show p.snd + p.fst ≤ X from hab_le))
    have h_in_ranges : f p ∈ ranges := Finset.mem_product.2 ⟨hpair, hsum⟩
    -- predicate P holds for f p
    have hP : P (f p) := by dsimp [P, f]; exact ⟨ha_le, hb_le, hab_le, rfl, hcop, hbad⟩
    -- conclude membership in the filtered finset
    exact Finset.mem_filter.2 ⟨h_in_ranges, hP⟩

  -- f is injective on S (in fact globally), so |img| = |S|
  have finj : Function.Injective f := by
    intro x y h
    rcases x with ⟨b1, a1⟩; rcases y with ⟨b2, a2⟩
    dsimp [f] at h
    injection h with hpair hsum
    injection hpair with ha hb
    subst ha; subst hb
    rfl

  -- let B be the concrete Finset produced by unfolding BadCount; we'll show
  -- img ⊆ B so |S| = |img| ≤ |B| = BadCount δ X.
  -- define B with the same Decidable witness as in `BadCount` so it unfolds definitionally
  let B := (@Finset.filter ((ℕ × ℕ) × ℕ)
    (fun t =>
      let a := t.1.1; let b := t.1.2; let c := t.2;
      a ≤ X ∧ b ≤ X ∧ c ≤ X ∧ a + b = c ∧ Nat.Coprime a b ∧
        let lhs := (c.factorization.support.filter fun p => 2 ≤ c.factorization p).prod id;
        let rhs := (rad a * rad b : ℕ);
        (lhs : ℕ) > Nat.floor ((rhs : ℝ) ^ δ))
    (fun t => Classical.propDecidable (P t)) ranges)

  have B_eq_ranges_filter : B = ranges.filter P := by
    ext t
    -- show membership in both filters is equivalent after unfolding
    dsimp [B, P]
    simp

  have img_sub_B : img ⊆ B := by
    intro y hy
    -- from img ⊆ ranges.filter P we get membership in the filter; rewrite to B
    have hyR : y ∈ ranges.filter P := h_subset hy
    rwa [← B_eq_ranges_filter] at hyR

  -- now card(img) ≤ card(B); and img.card = S.card by injectivity
  have img_card_le_B : img.card ≤ B.card := Finset.card_le_card img_sub_B
  have img_eq_S : img.card = S.card := by dsimp [img]; exact Finset.card_image_of_injective S finj
  have S_card_le_B : S.card ≤ B.card := by rw [← img_eq_S]; exact img_card_le_B


  -- rewrite S.card ≤ B.card to S.card ≤ (ranges.filter P).card using the equality
  have S_card_le_ranges : S.card ≤ (ranges.filter P).card := by
    rw [← B_eq_ranges_filter]
    exact S_card_le_B

  -- finish: rewrite the sum as S.card and turn B into BadCount δ X, then apply S_card_le_B.
  rw [hsum_card]
  -- show B.card = BadCount δ X by unfolding BadCount and using B_eq_ranges_filter
  have hB_eq_BadCount : B.card = BadCount δ X := by
    -- BadCount is defined with the same explicit Decidable witness, so unfolding matches definitionally
    dsimp [BadCount]
    rfl

  have final_le : S.card ≤ BadCount δ X := by
    calc
      S.card ≤ (ranges.filter P).card := S_card_le_ranges
      _ = B.card := by rw [B_eq_ranges_filter]
      _ = BadCount δ X := hB_eq_BadCount

  exact final_le

-- 「悪い組の割合 → 0」を形式化：与えられた外部上界（O(X^(1.75+ε))) から直接に従う。
-- 元の強い版は Conjecture として保持。

/--
この補題は、`BadCount` 関数の比率の上限を多項式の上限に基づいて確立します。

具体的には、`β` が 2 未満で非負であり、`C` が非負の定数である場合に、`BadCount 0.435 X` と `X^2` の比率が、十分大きな `X` に対して `(C + 1) / (X ^ (2 - β))` で上に制約されることを示します。

## パラメータ
- `β`: 0 ≤ β < 2 を満たす実数。
- `hβ0`: `β` が非負であることの証明。
- `C`: 非負の実数定数。
- `X`: 1 以上の自然数。
- `hC`: `C` が非負であることの証明。
- `hX1`: `X` が 1 以上であることの証明。
- `hUx`: `BadCount 0.435 X` を `C` と `X^β` に関連付ける仮定。

## 結論
この補題は、`BadCount 0.435 X` と `X^2` の比率が `(C + 1) / (X ^ (2 - β))` で制約されることを結論付けます。
-/
lemma ratio_bound_of_poly_upper {β : ℝ} (_ : β < 2) (hβ0 : 0 ≤ β) {C : ℝ} {X : ℕ}
  (hC : 0 ≤ C) (hX1 : 1 ≤ X) (hUx : ↑(BadCount 0.435 X) ≤ C * (X : ℝ) ^ β + 1) :
  ↑(BadCount 0.435 X) / (X : ℝ) ^ 2 ≤ (C + 1) / (X : ℝ) ^ (2 - β) := by
  -- prepare positivity facts
  have hpos : 0 < (X : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hX1)))
  have hXpow_pos : 0 < (X : ℝ) ^ β := Real.rpow_pos_of_pos hpos β
  have hXpow_ne : (X : ℝ) ^ β ≠ 0 := ne_of_gt hXpow_pos
  have hXexp_pos : 0 < (X : ℝ) ^ (2 - β) := Real.rpow_pos_of_pos hpos (2 - β)
  -- divide the upper bound by X^β (>0) to get (BadCount)/X^β ≤ C + 1/X^β
  have h1 : 0 ≤ (1 : ℝ) / (X : ℝ) ^ β := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hXpow_pos)
  have h_div : (BadCount (0.435) X : ℝ) / (X : ℝ) ^ β ≤ C + 1 / (X : ℝ) ^ β := by
    -- from hUx: BadCount ≤ C * X^β + 1, multiplying both sides by (X^β)⁻¹ ≥ 0 gives
    -- BadCount * (X^β)⁻¹ ≤ (C * X^β + 1) * (X^β)⁻¹, and the RHS simplifies to C + (X^β)⁻¹
    have htmp := mul_le_mul_of_nonneg_right hUx h1
    -- simplify (C * X^β + 1) * (X^β)⁻¹ = C + (X^β)⁻¹ using field_simp (X^β ≠ 0)
    have hrhs_eq : (C * (X : ℝ) ^ β + 1) * (1 / (X : ℝ) ^ β) = C + 1 / (X : ℝ) ^ β := by
      field_simp [hXpow_ne]
    -- turn the equality into a usable inequality, then finish
    have hrhs_le : (C * (X : ℝ) ^ β + 1) * (1 / (X : ℝ) ^ β) ≤ C + 1 / (X : ℝ) ^ β :=
      le_of_eq hrhs_eq
    simpa [div_eq_mul_inv] using le_trans htmp hrhs_le
  -- since X ≥ 1 and β ≥ 0 we have 1 / X^β ≤ 1, so (BadCount)/X^β ≤ C + 1
  have inv_le_one : 1 / (X : ℝ) ^ β ≤ 1 := by
    have one_le_X : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
    -- from 1 ≤ X and β ≥ 0 we get 1 ≤ X^β
    have one_le_pow : (1 : ℝ) ≤ (X : ℝ) ^ β := by
      simpa [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le one_le_X hβ0
    -- multiply both sides by (1 / X^β) > 0 to obtain 1 / X^β ≤ 1
    have hpos_inv : 0 < (1 : ℝ) / (X : ℝ) ^ β := div_pos (by norm_num : (0 : ℝ) < 1) hXpow_pos
    calc
      1 / (X : ℝ) ^ β = 1 * (1 / (X : ℝ) ^ β) := by simp
      _ ≤ (X : ℝ) ^ β * (1 / (X : ℝ) ^ β) := mul_le_mul_of_nonneg_right one_le_pow (le_of_lt hpos_inv)
      _ = 1 := by field_simp [ne_of_gt hXpow_pos]
  have h_upper : (BadCount (0.435) X : ℝ) / (X : ℝ) ^ β ≤ C + 1 := by
    -- use h_div and the simple inequality 1 / X^β ≤ 1 to bound the right hand side
    calc
      (BadCount (0.435) X : ℝ) / (X : ℝ) ^ β
          ≤ C + 1 / (X : ℝ) ^ β := h_div
      _ ≤ C + 1 := by
        -- from inv_le_one we get (1 / X^β) + C ≤ 1 + C
        have htmp : (1 / (X : ℝ) ^ β) + C ≤ 1 + C := add_le_add_left inv_le_one C
        -- rearrange using commutativity to the desired order
        simpa [add_comm, add_left_comm, add_assoc] using htmp
  -- multiply both sides by 1 / X^(2-β) (nonneg) to finish
  have inv_nonneg_exp : 0 ≤ (1 : ℝ) / (X : ℝ) ^ (2 - β) := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt hXexp_pos)
  have final_le := mul_le_mul_of_nonneg_right h_upper inv_nonneg_exp
  -- massage `final_le` so its LHS becomes `BadCount * (X^2)⁻¹` by reassociating and
  -- collapsing the product of inverses, then simplify to the desired inequality.
  have hXexp_ne : (X : ℝ) ^ (2 - β) ≠ 0 := ne_of_gt hXexp_pos
  have hassoc : (BadCount (0.435) X : ℝ) / (X : ℝ) ^ β * (1 / (X : ℝ) ^ (2 - β))
    = (BadCount (0.435) X : ℝ) * ((1 / (X : ℝ) ^ β) * (1 / (X : ℝ) ^ (2 - β))) := by
    simp [div_eq_mul_inv, mul_assoc]
  rw [hassoc] at final_le
  have inv_prod : (1 / (X : ℝ) ^ β) * (1 / (X : ℝ) ^ (2 - β)) = 1 / ((X : ℝ) ^ β * (X : ℝ) ^ (2 - β)) := by
    field_simp [hXpow_ne, hXexp_ne]
  rw [inv_prod] at final_le
  have prod_rpow : (X : ℝ) ^ β * (X : ℝ) ^ (2 - β) = (X : ℝ) ^ 2 := by
    simp [←Real.rpow_add hpos β (2 - β)]
  rw [prod_rpow] at final_le
  simpa [div_eq_mul_inv] using final_le

end ABC

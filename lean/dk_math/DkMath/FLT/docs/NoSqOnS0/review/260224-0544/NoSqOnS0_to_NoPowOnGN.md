# 1. 追加する「入力仕様」：NoPowOnGN（Body の深刺し禁止）

> `NoSqOnS0` の一般化版。
> “原始素因子が Body（GN）に刺さったとき、\(q^p\) までは刺さってはいけない” を仕様化する。

```lean
namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/-- Body（GN）に対する “深刺し禁止” 入力仕様。
`q ∣ GN p x u` なら `¬ q^p ∣ GN p x u` を要求する。 -/
def NoPowOnGN (p x u : ℕ) : Prop :=
  ∀ {q : ℕ}, Nat.Prime q → q ∣ GN p x u → ¬ q ^ p ∣ GN p x u

end DkMath.FLT
```

---

## 2. 汎用補助：`¬ q^p ∣ N` から `padicValNat ≤ p-1` を作る

`d=3` の `padicValNat_le_one_of_not_sq_dvd` を **完全に一般化** する。

```lean
namespace DkMath.FLT

open DkMath.ABC

/-- `¬ q^p ∣ N` なら `padicValNat q N ≤ p-1`（p>0） -/
lemma padicValNat_le_pred_of_not_pow_dvd {q N p : ℕ}
    (hp_pos : 0 < p) (hq : Nat.Prime q)
    (hnot : ¬ q ^ p ∣ N) :
    padicValNat q N ≤ p - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- 0 の場合は q^p | 0 が常に成り立つので、hnot から N≠0 が出る
  have hN_ne : N ≠ 0 := by
    intro h0
    have : q ^ p ∣ N := by simpa [h0] using (dvd_zero (q ^ p))
    exact hnot this

  -- もし padicValNat ≥ p なら q^p | N、により矛盾
  by_contra hle
  have hp_le : p ≤ padicValNat q N := by
    -- `¬(v ≤ p-1)` から `p ≤ v` を出す
    have : p - 1 < padicValNat q N := Nat.lt_of_not_ge hle
    -- p>0 なので p-1 < v なら p ≤ v
    exact Nat.succ_le_of_lt (by simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_of_lt hp_pos)] using this)

  -- `p ≤ padicValNat` から `q^p ∣ N`
  have hpow : q ^ p ∣ N := by
    -- DkMath.ABC の補題（既にある）：k ≤ v_p(n) ↔ p^k ∣ n
    -- ※あなたの `padicValNat_le_iff_dvd` を使う
    have := (DkMath.ABC.padicValNat_le_iff_dvd (p := q) (n := N) hq hN_ne p).1 hp_le
    simpa using this

  exact hnot hpow

end DkMath.FLT
```

> ※ `Nat.succ_le_of_lt` 周りは、環境によって書き換えが必要になることがある。
> その場合は素直に `omega` で片付く形に整えればOKじゃ（本質ではない）。

---

## 3. 汎用補助：`q ∣ a` から `p ≤ padicValNat q (a^p)`（下界）

`padicValNat_lower_bound_of_dvd_d3` を一般化。

```lean
namespace DkMath.FLT

open DkMath.ABC

/-- `q ∣ a` なら `p ≤ padicValNat q (a^p)`（p>0） -/
lemma padicValNat_lower_bound_of_dvd_pow {a q p : ℕ}
    (hp_pos : 0 < p) (ha_pos : 0 < a)
    (hq : Nat.Prime q) (hq_dvd_a : q ∣ a) :
    p ≤ padicValNat q (a ^ p) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have ha_ne : a ≠ 0 := Nat.ne_of_gt ha_pos

  -- v_q(a) ≥ 1
  have h_val_a_ge1 : 1 ≤ padicValNat q a := by
    -- q|a なら v_q(a)≠0、よって ≥1
    have hne0 : padicValNat q a ≠ 0 := by
      intro h0
      have : ¬ q ∣ a := by
        -- padicValNat=0 なら q∤a（Mathlib の eq_zero_iff）
        exact (padicValNat.eq_zero_iff).1 h0 |>.2 |>.2
      exact this hq_dvd_a
    exact Nat.one_le_iff_ne_zero.2 hne0

  -- v_q(a^p) = p * v_q(a)
  have hpow : padicValNat q (a ^ p) = p * padicValNat q a :=
    padicValNat.pow (n := p) ha_ne

  -- p*1 ≤ p*v_q(a) ≤ v_q(a^p)
  -- ここは `omega` が通りやすい
  rw [hpow]
  have : p ≤ p * padicValNat q a := by
    have hp1 : 1 ≤ padicValNat q a := h_val_a_ge1
    exact Nat.mul_le_mul_left p hp1
  simpa [Nat.mul_one] using this

end DkMath.FLT
```

---

## 4. 本体テンプレ：`FLT_dp_by_padicValNat`（“差し替え可能”版）

ここで `d=3` の Main を **ほぼ置換** する。

- 原始素因子は `GcdNext.exists_primitive_prime_factor_prime` を使用（条件 `¬ p ∣ c-b` が要る）
- 上界は **NoPowOnGN** を仮定して作る（供給理論は後で差し替え）

```lean
namespace DkMath.FLT

open scoped BigOperators
open DkMath.ABC
open DkMath.CosmicFormulaBinom
open DkMath.NumberTheory.GcdNext

/-- `a^p + b^p = c^p` から `c^p - b^p = a^p` -/
lemma pow_sub_eq_of_add_eq {a b c p : ℕ} (h : a ^ p + b ^ p = c ^ p) :
    c ^ p - b ^ p = a ^ p := by
  -- (a^p + b^p) - b^p = a^p
  simpa [h] using (Nat.add_sub_cancel_left (a ^ p) (b ^ p))

/-- `gcd(a,b)=1` かつ `a^p+b^p=c^p` なら `gcd(c,b)=1`（p>0） -/
lemma coprime_cb_of_eq_pow {a b c p : ℕ}
    (hp_pos : 0 < p)
    (hab : Nat.Coprime a b) (h : a ^ p + b ^ p = c ^ p) :
    Nat.Coprime c b := by
  -- d=3 の `coprime_cb_of_eq` の完全一般化
  by_contra hnot
  have hgcd_ne : Nat.gcd c b ≠ 1 := by
    intro hg; apply hnot
    exact (Nat.coprime_iff_gcd_eq_one).2 hg
  obtain ⟨r, hr, hr_dvd_g⟩ := Nat.exists_prime_and_dvd hgcd_ne
  have hr_dvd_c : r ∣ c := dvd_trans hr_dvd_g (Nat.gcd_dvd_left c b)
  have hr_dvd_b : r ∣ b := dvd_trans hr_dvd_g (Nat.gcd_dvd_right c b)
  have hr_dvd_cp : r ∣ c ^ p := dvd_trans hr_dvd_c (dvd_pow_self c (Nat.ne_of_gt hp_pos))
  have hr_dvd_bp : r ∣ b ^ p := dvd_trans hr_dvd_b (dvd_pow_self b (Nat.ne_of_gt hp_pos))

  have hsub : c ^ p - b ^ p = a ^ p := pow_sub_eq_of_add_eq h
  have hr_dvd_sub : r ∣ c ^ p - b ^ p := Nat.dvd_sub hr_dvd_cp hr_dvd_bp
  have hr_dvd_ap : r ∣ a ^ p := by simpa [hsub] using hr_dvd_sub
  have hr_dvd_a : r ∣ a := hr.dvd_of_dvd_pow hr_dvd_ap

  have : r ∣ 1 := by
    have : r ∣ Nat.gcd a b := Nat.dvd_gcd hr_dvd_a hr_dvd_b
    simpa [hab.gcd_eq_one] using this
  exact hr.not_dvd_one this

/-- Main の一般化（素数指数 p≥3、NoPowOnGN を入力として要求） -/
theorem FLT_dp_by_padicValNat
    {p a b c : ℕ}
    (hp : Nat.Prime p) (hp_ge3 : 3 ≤ p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : Nat.Coprime a b)
    (hpnd : ¬ p ∣ c - b)                         -- まずは “良い位相” を先に閉じる
    (hNoPow : NoPowOnGN p (c - b) b) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro h_eq

  -- b < c を d=3 と同じ背理法で作る（pow_le_pow_left だけで済む）
  have hbc : b < c := by
    by_contra hbc_not
    have hcb : c ≤ b := Nat.not_lt.mp hbc_not
    have hcp_le : c ^ p ≤ b ^ p := Nat.pow_le_pow_left hcb p
    have hsum_le : a ^ p + b ^ p ≤ b ^ p := by simpa [h_eq] using hcp_le
    have hap_pos : 0 < a ^ p := by positivity
    omega

  have hcop_cb : Nat.Coprime c b := coprime_cb_of_eq_pow (hp_pos := Nat.lt_of_lt_of_le (by decide : 0 < 3) hp_ge3) hab h_eq

  -- 層A：原始素因子 q を取る（Zsigmondy層A：存在）
  obtain ⟨q, hq_prime, hq_dvd_diff, hq_ndvd_diff⟩ :=
    DkMath.NumberTheory.GcdNext.exists_primitive_prime_factor_prime
      hp hp_ge3 hbc hb hcop_cb hpnd

  -- 差分の同一視：c^p - b^p = a^p
  have hsub : c ^ p - b ^ p = a ^ p := pow_sub_eq_of_add_eq h_eq

  -- q | a^p なので q | a
  have hq_dvd_ap : q ∣ a ^ p := by simpa [hsub] using hq_dvd_diff
  have hq_dvd_a : q ∣ a := hq_prime.dvd_of_dvd_pow hq_dvd_ap

  -- 下界：p ≤ v_q(a^p) = v_q(c^p-b^p)
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 3) hp_ge3
  have h_lower_ap : p ≤ padicValNat q (a ^ p) :=
    padicValNat_lower_bound_of_dvd_pow (p := p) hp_pos ha hq_prime hq_dvd_a
  have h_lower : p ≤ padicValNat q (c ^ p - b ^ p) := by
    simpa [hsub] using h_lower_ap

  -- 上界：因数分解 c^p - b^p = (c-b) * GN p (c-b) b に帰着し、
  --       q ∤ (c-b) と NoPow で v_q ≤ p-1 を作る
  have hfactor : c ^ p - b ^ p = (c - b) * GN p (c - b) b :=
    pow_sub_pow_factor_cosmic_N (a := c) (b := b) (d := p) hp_pos hbc

  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hcb_ne : c - b ≠ 0 := Nat.sub_ne_zero_of_lt hbc

  -- まず q | GN p (c-b) b（原始素因子が Body に刺さる）
  have hq_dvd_body : q ∣ GN p (c - b) b := by
    have hprod : q ∣ (c - b) * GN p (c - b) b := by
      simpa [hfactor] using hq_dvd_diff
    exact (hq_prime.dvd_mul.mp hprod).resolve_left hq_ndvd_diff

  -- NoPow により ¬ q^p | Body
  have hnot_pow : ¬ q ^ p ∣ GN p (c - b) b :=
    hNoPow hq_prime hq_dvd_body

  -- Body の付値上界：v_q(Body) ≤ p-1
  have h_body_upper : padicValNat q (GN p (c - b) b) ≤ p - 1 :=
    padicValNat_le_pred_of_not_pow_dvd (q := q) (N := GN p (c - b) b) (p := p)
      hp_pos hq_prime hnot_pow

  -- v_q(c^p-b^p) = v_q(c-b) + v_q(Body) = 0 + v_q(Body)
  have h_val_diff0 : padicValNat q (c - b) = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_ndvd_diff

  -- Body ≠ 0（hnot_pow からも出るが、mul のために明示しとく）
  have h_body_ne : GN p (c - b) b ≠ 0 := by
    intro h0
    have : q ^ p ∣ GN p (c - b) b := by simpa [h0] using (dvd_zero (q ^ p))
    exact hnot_pow this

  have h_val_mult :
      padicValNat q (c ^ p - b ^ p)
        = padicValNat q (c - b) + padicValNat q (GN p (c - b) b) := by
    -- padicValNat.mul 用
    rw [hfactor]
    exact padicValNat.mul hcb_ne h_body_ne

  have h_upper : padicValNat q (c ^ p - b ^ p) ≤ p - 1 := by
    -- 0 + v_q(Body) ≤ p-1
    simpa [h_val_mult, h_val_diff0] using h_body_upper

  -- 矛盾：p ≤ v ≤ p-1
  have : (p : ℕ) ≤ p - 1 := le_trans h_lower h_upper
  omega

end DkMath.FLT
```

---

## 5. これで「黒子が主役だった」が露呈するポイント

このテンプレは、**\(d=3\)** の Main と同じ勝ち筋を **そのまま \(d=p\)** へ持ち上げている：

- Big：\(c^p\)
- Gap：\(c^p-b^p\)
- Body：\((c^p-b^p)/(c-b)=GN(p,c-b,b)\)
- 格子判定：\(v_q(a^p)\equiv 0 \pmod p\) になれない（上界が \( < p\)）

あとは **供給するだけ**じゃ：

1. 原始素因子 \(q\)（層A）
2. NoPowOnGN（層B：NoLift / harmonic / phase / cyclotomic どれでもよい）

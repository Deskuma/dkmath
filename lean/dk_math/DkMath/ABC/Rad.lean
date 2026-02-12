import DkMath.Basic

#print "file: DkMath.ABC.Rad"

namespace DkMath.ABC.Rad

/- ============================================================================
     2. rad: definition + basic facts
   ============================================================================ -/

/-- rad(n) := 素因数分解の support 上に現れる素数の積 -/
def rad (n : ℕ) : ℕ :=
  n.factorization.support.prod (fun p => p)

/-- rad(n) の定義を n ≥ 1 に制限したバージョン -/
def rad' (n : ℕ) (hn : n ≥ 1) : ℕ :=
  match n with
  | 0 => 1 -- In the case n = 0: we define rad(0) = 1 for convenience (technically undefined)
  | _ =>   -- For n ≥ 1: rad(n) ≥ 1
    n.factorization.support.prod (fun p => p)

/-- rad(1) = 1 であること -/
lemma rad_one' : rad 1 = 1 := by
  simp only [rad, Nat.factorization_one, Finsupp.support_zero, Finset.prod_empty]

/-- rad(0) = 1 であること -/
lemma rad_zero' : rad 0 = 1 := by
  simp only [rad, Nat.factorization_zero, Finsupp.support_zero, Finset.prod_empty]

/-- rad(0) = 1 であること -/
@[simp] lemma rad_zero : rad 0 = 1 := by rw [rad_zero']
/-- rad(1) = 1 であること -/
@[simp] lemma rad_one : rad 1 = 1 := by rw [rad_one']

/- 小さな補題群の整理：rad に関する再利用可能補題 -/

/-`rad n ∣ n` を切り出しておくと再利用が楽になる（n ≠ 0 の場合）。-/
/--
`rad_dvd_nonzero` は、任意の自然数 `n` が 0 でないとき、その数の radical（`rad n`、すなわち `n` の素因数の積）が `n` を割り切ることを示す補題です。

radical `rad n` は、`n` の素因数全体の積として定義されます。
この補題の証明では、まず `n` の素因数分解を利用して `n = ∏_{p∈s} p^(f p)` という形に書き換えます。
（ここで `s` は `n` の素因数の集合、`f p` は素因数 `p` の指数）
各素因数 `p` について、`p` は `p^(f p)` を割り切ることから、素因数全体の積（radical）は `n` を割り切ることが分かります。

この補題は、整数論において radical の基本的な性質を述べており、例えば square-free な数や、radical を用いた他の性質の証明の基礎となります。
-/
lemma rad_dvd_nonzero (n : ℕ) (hn : n ≠ 0) : rad n ∣ n := by
  classical
  unfold rad
  let f := n.factorization
  let s := f.support
  -- n = ∏_{p∈s} p^(f p)
  have hfac : n = s.prod (fun p => p ^ f p) := Eq.symm (Nat.factorization_prod_pow_eq_self hn)
  -- 各 p ∈ s について p ∣ p^(f p)
  have hpt : ∀ p ∈ s, p ∣ p ^ f p := by
    intro p hp
    -- support 上の要素なので指数は非零
    rw [Finsupp.mem_support_iff] at hp
    have hf : f p ≠ 0 := hp
    exact dvd_pow_self p hf
  have hdiv : s.prod (fun p => p) ∣ s.prod (fun p => p ^ f p) :=
    Finset.prod_dvd_prod_of_dvd (fun p => p) (fun p => p ^ f p) fun p hp => hpt p hp
  rw [Eq.symm hfac] at hdiv
  exact hdiv

-- Quick sanity checks (equivalent to the original #eval tests)
-- #eval rad 0 -- 1 (by definition)
-- #eval rad 1 -- 1 (by definition)
-- #eval rad 2 -- 2
-- #eval rad 3 -- 3
-- #eval rad 4 -- 2
-- #eval rad 6 -- 6 = 2 * 3
-- #eval rad 7 -- 7
-- #eval rad 8 -- 2
-- #eval rad 9 -- 3
-- #eval rad 12 -- 6 = 2 * 3
-- #eval rad 123 -- 123 = 3 * 41
-- #eval rad 456 -- 114 = 2 * 3 * 19
-- #eval rad 840 -- 210 = 2 * 3 * 5 * 7
-- #eval rad 1000 -- 10 = 2 * 5

end DkMath.ABC.Rad

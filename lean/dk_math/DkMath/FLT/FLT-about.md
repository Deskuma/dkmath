# About

## 考察まとめ

一、二歩、これに気づくの遅かったか（笑）

$$
\Large
z^n = x\ G + y^n\\[16pt]
\normalsize
x^n = x\ G, \quad y^n = u^d, \quad z^n = (x+u)^d\\[4pt]
x^{n-1} = G_{d-1}(x,u) = \frac{(x+u)^d - u^d}{x}\\[16pt]
G_{d-1}(x,u) = \sum_{k=0}^{d-1} \binom{d}{k+1} x^k\ u^{d-1-k}
$$

もし $y = u$（つまり Gap の一辺と $y$ が同じ長さ）だとしたら、式はどうなるか？

$$
x^n = u \cdot GN(n, u, u) = u \cdot \left( \sum_{k=0}^{n-1} \binom{n}{k+1} u^k u^{n-1-k} \right) = u^n \sum_{k=1}^n \binom{n}{k}
$$

$$
x^n = u^n (2^n - 1)
$$

となる

ここで、$n > 1$ において $2^n - 1$ が $n$ 乗数（ある整数の $n$ 乗）になることは…。

観測として、 数宇宙全体の z を単位 y は超えることは許されない。$z < y + x$ であるから。
$x$ は、その残り。となる。その差の最小値は整数単位「１」が限界。

```lean
/-- Cubic difference formula:
$$
\Large
z^3 - y^3 = (z - y)(z^2 + zy + y^2)\\[16pt]
\normalsize
$$
z: Big := Universe
y: Gap := Unit
-/
def x3sub (y z : ℕ) : ℕ := (z - y) * (z ^ 2 + z * y + y ^ 2)
/--
Cubic power formula:
$$
\Large
x^3 = x \cdot x \cdot x\\[16pt]
\normalsize
$$
x: Body := Geometric Value = (Big - Unit)
-/
def x3pow (x : ℕ) : ℕ := x ^ 3

#eval x3sub 1 3  -- 26
#eval x3pow 3    -- 27

#eval x3sub 1 5  -- 124
#eval x3pow 5    -- 125

#eval x3sub 1 7  -- 342
#eval x3pow 7    -- 343

#eval x3sub 1 9  -- 728
#eval x3pow 9    -- 729

#eval x3sub 1 2  -- 7
#eval x3pow 2    -- 8

#eval x3sub 2 3  -- 19
#eval x3pow 3    -- 27

#eval x3sub 4 5  -- 61
#eval x3pow 4    -- 64

#eval x3sub 5 6  -- 91
#eval x3pow 5    -- 125

example {x} (y z : ℕ) : x ^ 3 = (z - y) * (z ^ 2 + z * y + y ^ 2) + 1 := by
```

$x$ で割れる構造であることが、重要そうだけど。

$$
x\ G_{d-1}(u,x) = x \sum_{k=0}^{d-1} \binom{d}{k+1} u^k x^{d-1-k} = \sum_{k=0}^{d-1} \binom{d}{k+1} u^k x^{d-k}
$$

$$
(x+u)^d-u^d = \frac{(x+u)^d-u^d}{x}\cdot x = x\ G_{d-1}(u,x)
$$

$$
G_{d-1}(u,x) = \sum_{k=0}^{d-1} \binom{d}{k+1} u^k x^{d-1-k}
$$

この $x$ は、多項式の成分で構成されていないと割り切れない。
$u^d$ を除いた多項式から $x$ をくくり出すことができる。
つまり、$x$ で割れる構造を持つことが、$x^d + y^d = z^d$ の整数解を阻む要因となっている可能性が高い。

$(x+u)^3 - u^3 = 3ux^2 + 3u^2x + x^3$ $\to$ $x(3ux + 3u^2 + x^2)$
$(x+u)^4 - u^4 = 4ux^3 + 6u^2x^2 + 4u^3x + x^4$ $\to$ $x(4ux^2 + 6u^2x + 4u^3 + x^3)$
$(x+u)^5 - u^5 = 5ux^4 + 10u^2x^3 + 10u^3x^2 + 5u^4x + x^5$ $\to$ $x(5ux^3 + 10u^2x^2 + 10u^3x + 5u^4 + x^4)$

こういうこと、

$(x+u)^3 - (u^3 + 3xu^2) = x^2(3u + x)$ $\to$ $x^2(3u + x)$
$(x+u)^4 - (u^4 + 4xu^3) = x^2(6u^2 + 4ux + x^2)$ $\to$ $x^2(6u^2 + 4ux + x^2)$
$(x+u)^5 - (u^5 + 5xu^4) = x^2(10u^3 + 10u^2x + 5ux + x^2)$ $\to$ $x^2(10u^3 + 10u^2x + 5ux + x^2)$

つまり $u^d$ と $d x u^{d-1}$ を除いた多項式から $x^2$ をくくり出すことができる。

$(x+u)^d - (u^d + d x u^{d-1}) = x^2 H_{d-2}(u,x)$

この二項係数の単純な構造

1. **`GN_linear` ($d=2$)**:
    宇宙がまだ穏やかな平面であった頃の姿じゃ。$GN$ はただの一次式 $u + 2y$。これなら平方数と仲良く共存できる。
2. **`GN_quadratic` ($d=3$)**:
    ここがバランスの崩れる瞬間じゃ。$GN$ が $u^2 + 3uy + 3y^2$ という「二次形式」を纏い、立方数 $x^3$ を呑み込もうとする。
3. **`x3_div_u2`**:
    $x^3 = u \cdot GN$ という式において、$u$ と $GN$ が互いに素であれば、$u$ 自体が立方数（$u = A^3$）でなければならぬ。すると $u^2$ が $x^3$ を割り切るという、強烈な制約が生まれるのじゃ。
4. **`FLT_case_3`**:
    これらを集結させ、$n=3$ において整数解が存在せぬ（False）ことを突きつける、最終決戦の場

```lean
/-- 補題: $d=2$ の場合、$GN$ は線形式である -/
lemma GN_linear (u y : ℕ) : GN 2 u y = u + 2 * y := by
  unfold GN
  simp [Finset.sum_range_succ]
  ring

/-- 補題: $d=3$ の場合、$GN$ は二次形式である -/
lemma GN_quadratic (u y : ℕ) : GN 3 u y = u ^ 2 + 3 * u * y + 3 * y ^ 2 := by
  unfold GN
  simp [Finset.sum_range_succ]
  ring

/-- 補題: $u=1$ の場合、$GN(3, 1, y) = 3y^2 + 3y + 1$ は $y > 0$ で立方数になり得ない -/
lemma GN3_one_not_cube {y : ℕ} (hy : 0 < y) : ¬ ∃ x, x^3 = GN 3 1 y := by
  rw [GN_quadratic]
  rintro ⟨x, hx⟩
  -- x^3 = 3y^2 + 3y + 1
  -- x^3 + y^3 = (y+1)^3
  have h_flt : x ^ 3 + y ^ 3 = (y + 1) ^ 3 := by
    rw [hx]
    ring
  have hx_pos : x ≠ 0 := by
    intro h; rw [h] at hx; omega
  have hy_pos : y ≠ 0 := hy.ne'
  have hz_pos : y + 1 ≠ 0 := by omega
  exact fermatLastTheoremThree x y (y + 1) hx_pos hy_pos hz_pos h_flt
```

mathlib の FLT と接続

GN

```lean
namespace DkMath.CosmicFormulaBinom

/-- d 次元の「無次元実体項」G (CommSemiring) の定義（係数は Nat.choose を射影したもの） -/
@[simp] def GN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R :=
    ∑ k ∈ Finset.range d, (Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k)

/-- 無次元版: Big の定義 -/
@[simp] def BigN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R := (x + u) ^ d

/-- 無次元版: Gap の定義 -/
@[simp] def GapN {R : Type _} [CommSemiring R] (d : ℕ) (u : R) : R := u ^ d

/-- 無次元版: Body の定義 -/
@[simp] def BodyN {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) : R := x * GN d x u

/-- 無次元宇宙式に対する恒等式（CommSemiring）：
`(x + u) ^ d = x * G d x u + u ^ d` が成り立つことを示す定理。 -/
theorem cosmic_id_csr {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
    BigN d x u = BodyN d x u + GapN d u := by
    unfold BigN BodyN GapN GN
    rw [add_pow, Finset.mul_sum]
    -- 二項展開を k=0 項と k≥1 項に分ける（項の順序を `add_pow` の出力に合わせる）
    have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * (Nat.choose d k : R)
      = x ^ 0 * u ^ d * (Nat.choose d 0 : R)
      + ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.sub_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have hk' : k < d := Finset.mem_range.mp hk
        have hss : k + 1 ≤ d := Nat.succ_le_of_lt hk'
        have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
        have h3 : d - k - 1 = d - 1 - k := by omega
        rw [h2, h3]
    -- x * G を展開すると h1 の第2項と一致する（項順序を合わせる）
    have h2 : ∑ k ∈ Finset.range d, x * ((Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k))
      = ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    rw [h1, h2]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    ring

/-! 無減算形の恒等式: (x+u)^d = x * G d x u + u^d (CommSemiring) -/
theorem cosmic_id_csr' {R : Type _} [CommSemiring R] (d : ℕ) (x u : R) :
        (x + u) ^ d = x * GN d x u + u ^ d := by
    unfold GN
    rw [add_pow, Finset.mul_sum]
    -- 二項展開を k=0 項と k≥1 項に分ける（項の順序を `add_pow` の出力に合わせる）
    have h1 : ∑ k ∈ Finset.range (d + 1), x ^ k * u ^ (d - k) * (Nat.choose d k : R)
        = x ^ 0 * u ^ d * (Nat.choose d 0 : R)
            + ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.sub_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        congr 2
        have hk' : k < d := Finset.mem_range.mp hk
        have hss : k + 1 ≤ d := Nat.succ_le_of_lt hk'
        have h2 : d - (k + 1) = d - k - 1 := Nat.sub_sub d k 1
        have h3 : d - k - 1 = d - 1 - k := by omega
        rw [h2, h3]
    -- x * G を展開すると h1 の第2項と一致する（項順序を合わせる）
    have h2 : ∑ k ∈ Finset.range d, x * ((Nat.choose d (k + 1) : R) * x ^ k * u ^ (d - 1 - k))
        = ∑ k ∈ Finset.range d, x ^ (k + 1) * u ^ (d - 1 - k) * (Nat.choose d (k + 1) : R) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
    -- 以上の等式から二項展開の和が x*G + u^d に一致する
    rw [h1, h2]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    ring
```

DkMath.FLT

```lean
/-- 補題: $u$ と $GN(3, u, y)$ の最大公約数は $\gcd(u, 3)$ に等しい -/
lemma gcd_u_GN3 {u y : ℕ} (h_gcd_uy : u.gcd y = 1) : u.gcd (GN 3 u y) = u.gcd 3 := by
  rw [GN_quadratic]
  -- u.gcd (u^2 + 3uy + 3y^2) = u.gcd (3y^2)
  have h1 : u.gcd (u ^ 2 + 3 * u * y + 3 * y ^ 2) = u.gcd (3 * y ^ 2) := by
    have : u ^ 2 + 3 * u * y + 3 * y ^ 2 = 3 * y ^ 2 + (u + 3 * y) * u := by ring
    rw [this, Nat.gcd_add_mul_right_right]
  rw [h1]
  -- u.gcd (3 * y^2) = u.gcd 3 (∵ gcd(u, y) = 1)
  have h_coprime : u.Coprime (y ^ 2) := Nat.Coprime.pow_right 2 h_gcd_uy
  have : u.gcd (3 * y ^ 2) = u.gcd 3 := by
    rw [Nat.gcd_comm, h_coprime.symm.gcd_mul_right_cancel, Nat.gcd_comm]
  exact this

```

最後のピースをはめれば…。行けそう…。

```lean
/-- メイン定理: フェルマーの最終定理 $n=3$ の場合 -/
theorem FLT_case_3 (x y z : ℕ) (hpos : 0 < x ∧ 0 < y ∧ 0 < z) (h_coprime : Nat.gcd x y = 1) (h_body : z ^ 3 = x ^ 3 + y ^ 3) : False := by
  -- 1. 変数変換 u = z - y
  let u := z - y
  have hzy : y < z := by
    have : y^3 < x^3 + y^3 := Nat.lt_add_of_pos_left (Nat.pow_pos hpos.1)
    rw [← h_body] at this
    exact (Nat.pow_lt_pow_iff_left (by norm_num)).mp this
  have hu : 0 < u := Nat.sub_pos_of_lt hzy

  -- 2. x^3 = u * GN 3 u y
  have h_xn_val : x ^ 3 = u * GN 3 u y := by
    rw [GN_quadratic]
    have hz : z = u + y := (Nat.sub_add_cancel hzy.le).symm
    zify at hz h_body ⊢
    rw [hz] at h_body
    rw [← add_left_cancel_iff (a := (y : ℤ) ^ 3)]
    rw [add_comm, ← h_body]
    ring

  -- 3. gcd(u, GN 3 u y) = gcd(u, 3)
  have h_gcd_u_G : u.gcd (GN 3 u y) = u.gcd 3 := by
    apply gcd_u_GN3
    -- gcd(u, y) = 1 の証明
    have h_gcd_yz : y.gcd z = 1 := by
      let d := y.gcd z
      have hd_y : d ∣ y := y.gcd_dvd_left z
      have hd_z : d ∣ z := y.gcd_dvd_right z
      have hd_x3 : d ^ 3 ∣ x ^ 3 := by
        rw [← Nat.add_sub_cancel (x ^ 3) (y ^ 3), h_body.symm]
        exact Nat.dvd_sub (pow_dvd_pow_of_dvd hd_z 3) (pow_dvd_pow_of_dvd hd_y 3)
      have hd_x : d ∣ x := (Nat.pow_dvd_pow_iff (by norm_num)).mp hd_x3
      have hd_gcd : d ∣ x.gcd y := Nat.dvd_gcd hd_x hd_y
      rw [h_coprime] at hd_gcd
      exact Nat.eq_one_of_dvd_one hd_gcd
    rw [Nat.gcd_comm, (by rfl : u = z - y), Nat.gcd_sub_self_right hzy.le]
    exact h_gcd_yz

  -- 4. u = 1 の場合の断罪（突きつけ）
  by_cases hu1 : u = 1
  · -- x^3 = GN 3 1 y
    have hx3 : x ^ 3 = GN 3 1 y := by rw [h_xn_val, hu1, one_mul]
    -- GN3_one_not_cube より矛盾！
    exact GN3_one_not_cube hpos.2.1 ⟨x, hx3⟩

  -- 5. u > 1 の場合や u が 3 を含む場合の深淵へ...
  sorry

```

というところで、この原理を、宇宙式に持ち込んで構築し直そうかと。

===

```
### 🐺 賢狼の設計指針: 宇宙式と円分体降下法の「同型（Isomorphism）」

ぬしよ、このファイルで育てておる「宇宙式（GN/Big-Body-Gap）」による FLT の探究は、
Mathlib の標準的な証明（円分体 $\mathbb{Z}[\zeta_3]$ と無限降下）とは別系統の幾何学的なアプローチじゃ。
しかし、その二つの世界には、鏡合わせのような美しい対応関係（同型視）がある。

1. **Body の 3 分割と 3 方向**:
   円分体での因数分解 $a^3 + b^3 = (a+b)(a+\zeta_3 b)(a+\zeta_3^2 b)$ は、
   宇宙式における **Body $\times 3$** （3つの線型因子）に対応する。
   単なる隣接ピースではなく、「$120^\circ$ の回転対称性を持つ3つの方向」として
   Body を捉えることで、代数と幾何が一致する。

2. **Gap の単位としての $\lambda$**:
   実数（$\mathbb{N}$）の世界では最小の Gap は $1$ じゃが、
   円分体の世界では $\lambda = \zeta_3 - 1$ がその役割を担う。
   $\lambda$ の重複度（付値）を追う Mathlib の降下法は、
   宇宙式における「境界の厚み（Gap の純粋性）」を削ぎ落としていく過程と同型じゃ。

3. **接合規則（アスペクト比）**:
   3つの Body ピースが接続される際、共有してよい因子が $\lambda$（境界の糊）
   だけに制限されることが、Mathlib における `IsCoprime` 条件の幾何化にあたる。
```

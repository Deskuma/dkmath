# GN 冪差・端点座標 Bridge 解説と実装設計

cid: 6a6f436a-a80c-83e8-8938-ff231d0518b7

- 作成日: 2026-08-02
- 状態: 実装状況調査済み・橋補題は未統合
- 対象 branch: `develop`
- 対象領域: DkMath / Cosmic Formula / GN / PowerGapBeam / finite difference
- 第一実装候補: `DkMath.CosmicFormula.PowerGapBeamGN`
- 分離候補: `DkMath.CosmicFormula.GNEndpointBridge`

## 0. 概要

本書は、次の等式連鎖を DkMath 上で相互変換可能な API として固定するための解説・実装設計である。

$$
\frac{x^2-y^2}{x-y}=n=x+y=GN_2(x-y,y)
$$

商を含む形では、発動条件として $x\neq y$ が必要である。

一方、GN 自体と分母なしの因数分解は $x=y$ でも意味を持つ。

$$
x^2-y^2=(x-y)GN_2(x-y,y)
$$

二次 GN は、差分 $h$ と始点 $u$ を用いて、

$$
GN_2(h,u)=h+2u
$$

である。ここへ、

$$
h=x-y,\qquad u=y
$$

を代入すると、

$$
GN_2(x-y,y)=x+y
$$

を得る。

したがって、

$$
y=-x+n\iff y+x=n\iff x+y=n\iff GN_2(x-y,y)=n
$$

であり、$x\neq y$ のときはさらに、

$$
GN_2(x-y,y)=n\iff \frac{x^2-y^2}{x-y}=n
$$

を接続できる。

この橋により、次の四つの表現を用途に応じて往復できる。

1. 冪差の因数分解
2. 差分商
3. GN 差分核
4. 二次の線形式 $x+y=n$

---

## 1. 座標の意味

GN の標準座標を、

$$
(h,u)=(x-y,y)
$$

とする。

このとき、

$$
u+h=y+(x-y)=x
$$

であるため、GN の基本恒等式、

$$
(h+u)^d=h\,GN_d(h,u)+u^d
$$

は端点座標では、

$$
x^d=(x-y)GN_d(x-y,y)+y^d
$$

となる。

したがって、可換環上で分母なしに、

$$
x^d-y^d=(x-y)GN_d(x-y,y)
$$

が成立する。

ここで重要なのは、$x$ と $y$ が二つの端点であり、$x-y$ は端点間の Gap、$GN_d(x-y,y)$ はその Gap で正規化された Beam だということである。

---

## 2. `develop` の実装状況

### 2.1 canonical GN は実装済み

`lean/dk_math/DkMath/CosmicFormula/Defs.lean` に、canonical GN が存在する。

```lean
@[simp] abbrev GN (R : Type*) [CommSemiring R]
    (x u : R) (d : ℕ) : R :=
  GTail d 1 x u
```

GN は一般 tail family `GTail` の $r=1$ 特殊化として固定済みである。新しい GN 定義は不要である。

### 2.2 d-first wrapper と基本恒等式は実装済み

`lean/dk_math/DkMath/CosmicFormula/CosmicFormulaBinom.lean` には、既存コードで広く使われる d-first wrapper がある。

```lean
@[simp] abbrev GN {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) : R :=
  DkMath.CosmicFormula.GN R x u d
```

さらに、明示和と主要恒等式が実装済みである。

```lean
theorem GN_eq_sum ...

theorem cosmic_id_csr' {R : Type _} [CommSemiring R]
    (d : ℕ) (x u : R) :
    (x + u) ^ d = x * GN d x u + u ^ d
```

今回の分母なし端点橋は、`cosmic_id_csr'` へ $x-y$ と $y$ を代入する薄いラッパとして実装できる。

### 2.3 差の冪 Beam は実装済み

`lean/dk_math/DkMath/Algebra/DiffPow.lean` には、差の冪和 `diffPowSum` と因数分解が存在する。

```lean
theorem pow_sub_pow_factor {α : Type*} [CommRing α]
    (a b : α) (d : ℕ) :
    a ^ d - b ^ d =
      (a - b) * diffPowSum a b d
```

`lean/dk_math/DkMath/CosmicFormula/PowerGapBeam.lean` には、同じ対象を端点 Beam として読む API がある。

```lean
def powerBeam {R : Type*} [CommRing R]
    (d : ℕ) (x z : R) : R := ...

theorem pow_sub_pow_eq_gap_mul_powerBeam ...

theorem powerBeam_two ... :
    powerBeam 2 x z = z + x
```

したがって、二次の $x+y$ 側は既に `powerBeam_two` として実装済みである。

### 2.4 Power Beam と GN の低次数橋は実装済み

`lean/dk_math/DkMath/CosmicFormula/PowerGapBeamGN.lean` には、端点 Gap を GN へ渡す橋が $d=3,4$ について存在する。

```lean
theorem powerBeam_three_eq_GN_of_gap ... :
    powerBeam 3 b a = GN 3 (a - b) b

theorem powerBeam_four_eq_GN_of_gap ... :
    powerBeam 4 b a = GN 4 (a - b) b
```

今回の観測は、この路線の $d=2$ 版である。同時に、低次数ごとの個別橋を任意次数へ一般化する入口でもある。

### 2.5 多項式差分商は実装済み

`lean/dk_math/DkMath/BookOfMagic/GNFiniteDifference.lean` には、多項式一般の差分商橋がある。

```lean
theorem differenceQuotient_eq_GNFiniteDifference
    {K : Type*} [Field K]
    (p : Polynomial K) (h t : K)
    (hh : h ≠ 0) :
    (p.eval (t + h) - p.eval t) / h =
      GNFiniteDifference p h t
```

単項式 $p(X)=X^d$、$h=x-y$、$t=y$ を代入すれば、今回の一般差分商へ到達できる。

ただし、冪の場合は `cosmic_id_csr'` から直接証明した方が依存が軽い。

### 2.6 実数上の power kernel bridge は実装済み

`lean/dk_math/DkMath/CosmicFormula/CosmicDerivativePower.lean` には、実数上の冪差 kernel と GN の swap bridge がある。

```lean
theorem powerKernel_eq_GN_swap ... :
    powerKernel d x u = GN d u x
```

この実装は解析・微分側の橋であり、今回の端点代数 API はより一般の `CommRing` / `Field` 上へ置くのがよい。

### 2.7 数論限定の端点橋も部分実装済み

`lean/dk_math/DkMath/NumberTheory/Gcd/GN.lean` には、自然数端点を整数へ持ち上げた GN と `diffPowSum` の一致、素数冪差商との一致が実装されている。

代表例は次である。

```lean
theorem gn_sub_eq_sd_int ...

theorem quotientPrimePow_eq_gn_gap ...

theorem diffPowQuotient_eq_gn_int ...
```

ただし、これらは `p > 0`、素数性、$y<z$、Nat/Int cast などの数論的条件を持つ。

今回必要なのは、その下に置ける軽量な一般代数 Bridge である。

---

## 3. 現在不足している API

既存部品は十分に揃っているが、次の一列が統一 API として露出していない。

$$
x^d-y^d=(x-y)GN_d(x-y,y)
$$

$$
\frac{x^d-y^d}{x-y}=GN_d(x-y,y)
$$

$$
GN_2(x-y,y)=x+y
$$

$$
GN_2(x-y,y)=n\iff x+y=n\iff y=-x+n
$$

特に不足しているものは次である。

1. 任意次数・可換環上の分母なし端点 GN bridge
2. Field 上の任意次数差分商 bridge
3. 二次 GN の明示形
4. 二次端点 GN と $x+y$ の simp bridge
5. $n$ を介した同値変形群
6. Nat 減算に対する発動条件の整理

---

## 4. 推奨する実装層

### 4.1 Core は分母なし

最初に置くべき定理は、除算を含まない次の形である。

```lean
/-- Endpoint form of the GN power-difference factorization. -/
theorem pow_sub_pow_eq_sub_mul_GN
    {R : Type*} [CommRing R]
    (d : ℕ) (x y : R) :
    x ^ d - y ^ d =
      (x - y) * DkMath.CosmicFormulaBinom.GN d (x - y) y := by
  have h :=
    DkMath.CosmicFormulaBinom.cosmic_id_csr'
      (R := R) (d := d) (x := x - y) (u := y)
  calc
    x ^ d - y ^ d = ((x - y) + y) ^ d - y ^ d := by ring
    _ = ((x - y) *
          DkMath.CosmicFormulaBinom.GN d (x - y) y + y ^ d) - y ^ d := by
          rw [h]
    _ = (x - y) *
          DkMath.CosmicFormulaBinom.GN d (x - y) y := by ring
```

この定理には $x\neq y$ が不要であり、零因子を持つ環でも成立する。

### 4.2 quotient は Field 上の派生定理

```lean
/-- Away from the diagonal, the endpoint power quotient is GN. -/
theorem pow_sub_pow_div_sub_eq_GN
    {K : Type*} [Field K]
    (d : ℕ) (x y : K)
    (hxy : x ≠ y) :
    (x ^ d - y ^ d) / (x - y) =
      DkMath.CosmicFormulaBinom.GN d (x - y) y := by
  rw [pow_sub_pow_eq_sub_mul_GN]
  exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hxy)
```

実際の Mathlib API に応じて、最後は `field_simp`、`simp`、`div_eq_iff` のいずれかへ調整する。

### 4.3 二次 GN の明示形

```lean
/-- The quadratic GN kernel is linear. -/
@[simp]
theorem GN_two
    {R : Type*} [CommSemiring R]
    (h u : R) :
    DkMath.CosmicFormulaBinom.GN 2 h u = h + 2 * u := by
  rw [DkMath.CosmicFormulaBinom.GN_eq_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  ring
```

係数順序は `2 * u + h` でも数学的には同じだが、端点 bridge へ接続しやすい `h + 2 * u` を正規形とする。

### 4.4 二次端点 bridge

```lean
/-- Quadratic GN in endpoint coordinates is the endpoint sum. -/
@[simp]
theorem GN_two_sub_eq_add
    {R : Type*} [CommRing R]
    (x y : R) :
    DkMath.CosmicFormulaBinom.GN 2 (x - y) y = x + y := by
  rw [GN_two]
  ring
```

これは今回の中心補題である。

### 4.5 二次差分商 bridge

```lean
/-- Difference of squares quotient in GN form. -/
theorem sq_sub_sq_div_sub_eq_GN
    {K : Type*} [Field K]
    (x y : K)
    (hxy : x ≠ y) :
    (x ^ 2 - y ^ 2) / (x - y) =
      DkMath.CosmicFormulaBinom.GN 2 (x - y) y := by
  simpa using pow_sub_pow_div_sub_eq_GN 2 x y hxy
```

```lean
/-- Difference of squares quotient in endpoint-sum form. -/
theorem sq_sub_sq_div_sub_eq_add
    {K : Type*} [Field K]
    (x y : K)
    (hxy : x ≠ y) :
    (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  rw [sq_sub_sq_div_sub_eq_GN x y hxy]
  exact GN_two_sub_eq_add x y
```

---

## 5. `n` を介した相互変換 Bridge

### 5.1 GN と線形式

```lean
theorem GN_two_sub_eq_iff_add_eq
    {R : Type*} [CommRing R]
    (x y n : R) :
    DkMath.CosmicFormulaBinom.GN 2 (x - y) y = n ↔
      x + y = n := by
  rw [GN_two_sub_eq_add]
```

### 5.2 線形式と変数解

```lean
theorem add_eq_iff_right_eq_neg_add
    {R : Type*} [CommRing R]
    (x y n : R) :
    x + y = n ↔ y = -x + n := by
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h
```

より既存 Mathlib 補題に寄せる場合は、`eq_sub_iff_add_eq`、`sub_eq_iff_eq_add`、`add_comm` の組合せを優先する。

### 5.3 商・GN・線形式・変数解の一括 bridge

```lean
theorem sq_quotient_eq_iff_GN_eq
    {K : Type*} [Field K]
    (x y n : K)
    (hxy : x ≠ y) :
    (x ^ 2 - y ^ 2) / (x - y) = n ↔
      DkMath.CosmicFormulaBinom.GN 2 (x - y) y = n := by
  rw [sq_sub_sq_div_sub_eq_GN x y hxy]
```

```lean
theorem sq_quotient_eq_iff_add_eq
    {K : Type*} [Field K]
    (x y n : K)
    (hxy : x ≠ y) :
    (x ^ 2 - y ^ 2) / (x - y) = n ↔
      x + y = n := by
  rw [sq_sub_sq_div_sub_eq_add x y hxy]
```

```lean
theorem sq_quotient_eq_iff_right_eq_neg_add
    {K : Type*} [Field K]
    (x y n : K)
    (hxy : x ≠ y) :
    (x ^ 2 - y ^ 2) / (x - y) = n ↔
      y = -x + n := by
  rw [sq_quotient_eq_iff_add_eq x y n hxy]
  exact add_eq_iff_right_eq_neg_add x y n
```

この層により、証明中の目標形に応じて、商、GN、加法、解形式へ直接移動できる。

---

## 6. Power Beam との一般 bridge

既存の $d=3,4$ 補題は、次の任意次数定理へ一般化できるはずである。

```lean
/-- The endpoint Power Beam is the GN kernel at the endpoint gap. -/
theorem powerBeam_eq_GN_of_gap
    {R : Type*} [CommRing R]
    (d : ℕ) (a b : R) :
    powerBeam d b a =
      DkMath.CosmicFormulaBinom.GN d (a - b) b := by
  ...
```

数学的には、両辺とも、

$$
\frac{a^d-b^d}{a-b}
$$

を表す多項式である。

ただし、一般 `CommRing` 上で、

$$
(a-b)A=(a-b)B
$$

から $A=B$ を導いてはならない。$a-b$ が零因子である可能性があるためである。

したがって、この一般 bridge は次のいずれかで直接証明する必要がある。

1. `GN_eq_sum` と二項展開を用いた和の恒等式
2. 次数 $d$ に関する帰納法
3. 多項式環で恒等式を証明して任意の可換環へ評価
4. 既存の `GTail` recursion と `diffPowSum` recursion の対応

この一般化は有益だが、今回の二次 bridge 実装を妨げる理由にはならない。まず $d=2$ を固定し、その後に一般化するのが安全である。

一般 bridge が完成した場合、既存の、

```lean
powerBeam_three_eq_GN_of_gap
powerBeam_four_eq_GN_of_gap
```

は一般定理の `simpa` corollary へ縮約できる。

---

## 7. Nat 版の注意

自然数では、$x-y$ が切り捨て減算になる。

したがって、端点座標、

$$
(x-y)+y=x
$$

を使うには、

$$
y\leq x
$$

が必要である。

Nat 版は、まず除算を避け、次の加法形を置くのがよい。

```lean
theorem pow_eq_sub_mul_GN_add_pow_nat
    {d x y : ℕ}
    (hyx : y ≤ x) :
    x ^ d =
      (x - y) * DkMath.CosmicFormulaBinom.GN d (x - y) y + y ^ d := by
  ...
```

二次版は、

```lean
@[simp]
theorem GN_two_nat_sub_eq_add
    {x y : ℕ}
    (hyx : y ≤ x) :
    DkMath.CosmicFormulaBinom.GN 2 (x - y) y = x + y := by
  rw [GN_two]
  omega
```

という形が候補である。

Nat の `/` は Field の除算とは意味が異なるため、最初の実装では quotient bridge を Nat へ一般化しない。

既存の `NumberTheory.Gcd.GN` にある exact divisibility と prime-power quotient API を必要時に利用する。

---

## 8. $x=y$ の対角線

商の形、

$$
\frac{x^d-y^d}{x-y}
$$

は $x=y$ で使えない。

しかし GN は多項式として対角線上にも値を持つ。

二次では、

$$
GN_2(0,x)=2x
$$

である。

したがって、次の二層を混同しない。

1. `GN`・分母なし因数分解: 全域で成立
2. 差分商: $x\neq y$ の領域で成立

この分離は、後に有限差分から微分へ接続するときにも重要である。

一般には、

$$
GN_d(0,x)=d\,x^{d-1}
$$

となり、GN は差分商の対角線延長として微分核を保持する。

---

## 9. simp 方針

`@[simp]` 候補は、複雑な GN 表現を単純な線形式へ落とす次の二つに限定する。

```lean
@[simp] theorem GN_two ...
@[simp] theorem GN_two_sub_eq_add ...
```

次は `@[simp]` を付けず、明示的に使う方が安全である。

1. quotient bridge
2. `↔` bridge 群
3. `powerBeam_eq_GN_of_gap`
4. 変数解 $y=-x+n$ への方向付け

理由は、除算の非零条件、同値変形の向き、`powerBeam` と `GN` のどちらを正規形とするかが文脈依存だからである。

DkMath の正規形は、この実装範囲では GN とする。

---

## 10. 推奨実装順序

### Event 1 — 二次 GN の明示形

`GN_two` を追加する。

検証:

```lean
example {R : Type*} [CommRing R] (h u : R) :
    DkMath.CosmicFormulaBinom.GN 2 h u = h + 2 * u := by
  simp
```

### Event 2 — 二次端点 bridge

`GN_two_sub_eq_add` を追加する。

検証:

```lean
example {R : Type*} [CommRing R] (x y : R) :
    DkMath.CosmicFormulaBinom.GN 2 (x - y) y = x + y := by
  simp
```

### Event 3 — 任意次数の分母なし bridge

`pow_sub_pow_eq_sub_mul_GN` を追加する。

検証:

```lean
example {R : Type*} [CommRing R] (d : ℕ) (x y : R) :
    x ^ d - y ^ d =
      (x - y) * DkMath.CosmicFormulaBinom.GN d (x - y) y := by
  simpa using pow_sub_pow_eq_sub_mul_GN d x y
```

### Event 4 — Field quotient bridge

`pow_sub_pow_div_sub_eq_GN` と二次 corollary を追加する。

検証条件は $x\neq y$ とする。

### Event 5 — `n` の同値変形群

GN、$x+y=n$、$y=-x+n$ を往復する補題を追加する。

### Event 6 — Power Beam 一般化の可否調査

`powerBeam_eq_GN_of_gap` を arbitrary `CommRing` 上で直接証明できるか調べる。

見つかった場合は $d=3,4$ の既存補題を corollary 化する。証明が重い場合は、二次 bridge と一般分母なし bridge の完成を優先し、別イベントへ分離する。

### Event 7 — aggregate import

実装先を新規 `GNEndpointBridge.lean` とした場合のみ、必要に応じて、

```lean
import DkMath.CosmicFormula.GNEndpointBridge
```

を `DkMath/CosmicFormula.lean` または用途別 aggregate module へ追加する。

既存 `PowerGapBeamGN.lean` を拡張する場合は、`DkMath/CosmicFormula.lean` から既に import 済みであるため追加作業は不要である。

---

## 11. 推奨配置

最小変更では、既存の、

```text
lean/dk_math/DkMath/CosmicFormula/PowerGapBeamGN.lean
```

を拡張する。

理由は次である。

1. Power Beam と GN の橋が既に置かれている
2. `powerBeam_two`、$d=3,4$ endpoint bridge が隣接している
3. `DkMath.CosmicFormula.lean` から既に import されている
4. 新しい定義を追加せず、橋補題だけで完結する

ただし、商・同値変形・有限差分まで成長する場合は、

```text
lean/dk_math/DkMath/CosmicFormula/GNEndpointBridge.lean
```

へ分離する。

その場合、`PowerGapBeamGN.lean` は Power Beam 固有の corollary に限定する。

---

## 12. 完了条件

次をすべて満たした時点で、この Bridge の第一実装を完了とする。

1. `GN_two` が `CommSemiring` 上で通る
2. `GN_two_sub_eq_add` が `CommRing` 上で通る
3. `pow_sub_pow_eq_sub_mul_GN` が `CommRing` 上で通る
4. `pow_sub_pow_div_sub_eq_GN` が `Field` 上で通る
5. 二次 quotient が $x+y$ へ落ちる
6. `GN=n`、`x+y=n`、`y=-x+n` を往復できる
7. Nat 版では $y\leq x$ を明示する
8. 既存 $d=3,4$ bridge と命名衝突しない
9. `lake build` が成功する
10. 広すぎる `@[simp]` によるループがない

---

## 13. 結論

今回の観測、

$$
\frac{x^2-y^2}{x-y}=n=x+y=GN_2(x-y,y)
$$

は、既存の DkMath 実装から孤立した新構造ではない。

既に存在する、

- canonical `GN = GTail d 1`
- `cosmic_id_csr'`
- `diffPowSum`
- `powerBeam`
- `GNFiniteDifference`
- 低次数 PowerBeam-GN bridge
- 数論限定 quotient bridge

を、一つの端点座標 API へ束ねる最後の薄い橋である。

二次では、この橋により、

$$
GN_2(x-y,y)=x+y
$$

が明示され、さらに、

$$
y=-x+n\iff x+y=n\iff GN_2(x-y,y)=n
$$

が形式化される。

この小さな橋は、高次では、

$$
\frac{x^d-y^d}{x-y}=GN_d(x-y,y)
$$

へそのまま昇格する。

したがって、二次の線形化補題として始めながら、冪差、有限差分、Power Beam、FLT 系数論 API を同じ GN 座標へ統合する基礎 Bridge となる。

# Note: Review: Ultra-001-J

## 総合判定

**全面採用。Ultra-001J 討伐完了じゃ。大躍進である。** ⚔️🧙‍♀️✨️

重大問題 0。
数学的過大主張 0。
修正必須事項 0。

PR #69 は head `72c427d657432d41cdb1513d66e0bd0fbf804644`、7 commits、20 files、4631 additions、現在も mergeable じゃ。

添付 diff と current branch の実コードも一致している。

## 1. Canonical cover の存在問題が消滅した

```lean
def GNDeepLiftResidues (p q b k : ℕ) : Finset ℕ :=
  (Finset.range (q ^ k)).filter
    (fun r => q ^ k ∣ GN p r b)
```

により、住所集合が抽象 existential ではなく、法 $q^k$ の標準代表として固定された。

membership は exact に、

$$r\in\operatorname{GNDeepLiftResidues}(p,q,b,k)\iff r<q^k\land q^k\mid GN_p(r,b)$$

じゃ。

そして任意の root $a$ を $a\bmod q^k$ へ送るだけで、

```lean
GNDeepLiftResidues_cover
```

が無条件に構成された。GN が左座標の合同を保存する `GN_modEq_left` が、この射影を支えている。

したがって、以前の未解決命題、

```text
∃ R, R.card ≤ p - 1 ∧ GNDeepLiftResidueCover ...
```

のうち、`∃ R` と cover 部分は完全に消滅した。

残るのは canonical set の cardinality だけじゃ。

## 2. Mod-$q$ 根数は予想より簡単に閉じた

`GNPolynomial p b R` は左座標 $X$ に関する GN 多項式そのものになっている。

```lean
eval_GNPolynomial
GNPolynomial_eq_GN
GNPolynomial_monic
GNPolynomial_natDegree_le
```

によって、

$$\deg GN_p(X,b)\le p-1$$

かつ $p>0$ なら monic が kernel 固定された。

これを有限体 `ZMod q` の通常の root-cardinality bound に投入し、

```lean
GNDeepLiftResidues_card_base_le
```

すなわち、

$$#{r\bmod q:q\mid GN_p(r,b)}\le p-1$$

が証明された。

ここが特に美しい。

当初は、

```text
q ∤ p
q ∤ b
原始 p 乗根への affine 変換
```

まで使って根数を数える予定だった。

しかし実際には、**多項式の次数だけで根数が抑えられた。**

したがって役割分担は現在、

```text
base root count
  → degree argument
  → q ∤ p, q ∤ b は不要

unique deep lifting
  → simple-root argument
  → q ∤ p, q ∤ b が必要
```

と完全に分離された。

設計として非常に強い。

## 3. Simple-root 条件も閉じた

```lean
eval_derivative_GNPolynomial_ne_zero
```

は、

```text
GNPolynomial(r) = 0
q ∤ p
q ∤ b
```

から、

```text
GNPolynomial'(r) ≠ 0 in ZMod q
```

を返す。

証明の核は cosmic identity の微分じゃ。

$$X,GN_p(X,b)+b^p=(X+b)^p$$

root $r$ 上で微分すると、

$$r,GN_p'(r)=p(r+b)^{p-1}$$

という関係が現れる。

コードでは derivative をゼロと仮定し、右辺の、

$$p(r+b)^{p-1}$$

が非零であることへ衝突させている。

特に $r+b\ne0$ も、元の cosmic identity と $b\ne0$ から内部で証明されている。これは穴のない証明じゃ。

## 4. Counting lane は本当に一義務へ落ちた

現在の有限集合側は、

```text
depth-k roots
  ↓ reduction mod q
base roots
```

という一枚の写像になった。

```lean
def GNDeepLiftReductionInjective
```

は canonical roots 上で reduction mod $q$ が単射であること。

```lean
def GNDeepLiftCongruenceUnique
```

は任意の二 root に対する、

$$q^k\mid GN_p(a,b)$$

$$q^k\mid GN_p(r,b)$$

$$a\equiv r\pmod q$$

から、

$$a\equiv r\pmod {q^k}$$

を返す pointwise 版じゃ。

これが得られると、

```lean
GNDeepLiftResidues_card_le_of_reduction
card_gn_deep_lift_residue_classes_le_of_reduction
card_gn_deep_lift_residue_classes_le_of_congruenceUnique
```

を通って、直ちに、

$$#{0\le a\le X:q^k\mid GN_p(a,b)}\le(p-1)\left(\frac{X+1}{q^k}+1\right)$$

へ到達する。

報告書も、canonical cover・base root bound・simple derivative と、未証明の general uniqueness を正確に分けている。

## 5. 一つだけ形式上補うなら

現コードで証明済みなのは、

```text
GNDeepLiftCongruenceUnique
  →
GNDeepLiftReductionInjective
```

じゃ。

逆方向はまだ theorem になっていない。

数学的には、$q$ prime、$k>0$ のもとで canonical residue を経由すれば逆も証明できるはずなので、厳密に「同値」と呼ぶなら次を追加すると完全になる。

```lean
theorem GNDeepLiftCongruenceUnique_of_reductionInjective
    {p q b k : ℕ}
    (hq : Nat.Prime q)
    (hk : 0 < k)
    (hinj : GNDeepLiftReductionInjective p q b k) :
    GNDeepLiftCongruenceUnique p q b k
```

そして、

```lean
theorem GNDeepLiftCongruenceUnique_iff_reductionInjective ...
```

まで置けば、

```text
有限集合版
pointwise 合同版
```

が kernel 上でも本当に同値になる。

これは軽微な API 完成であり、現在の成果を損なう問題ではない。

## 6. 次の Hensel 攻略は「反復」なしでも行ける

もっとも有望なのは、$k$ に関する逐次 Hensel だけではなく、**Taylor 因子化による一撃証明**じゃ。

整数多項式 $P$ に対し、

$$P(a)-P(r)=(a-r)\left(P'(r)+(a-r)C\right)$$

という形を作る。

仮定 $a\equiv r\pmod q$ から、

$$q\mid a-r$$

なので、

$$P'(r)+(a-r)C\equiv P'(r)\pmod q$$

となる。

simple root により、

$$q\nmid P'(r)$$

だから、

$$q\nmid P'(r)+(a-r)C$$

も言える。

一方、$a,r$ がともに深度 $k$ の root なので、

$$q^k\mid P(a)-P(r)$$

したがって、

$$q^k\mid(a-r)\left(P'(r)+(a-r)C\right)$$

第二因子は $q$ と互いに素なので、prime-power cancellation により、

$$q^k\mid a-r$$

が出る。

これがそのまま、

$$a\equiv r\pmod{q^k}$$

じゃ。

Mathlib には、まさに、

```lean
Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
```

という二次剰余付き Taylor 分解がある。これは、

$$P(x+y)=P(x)+P'(x)y+c,y^2$$

を返す。([Lean Community][1])

一方、既存 `Mathlib.NumberTheory.Padics.Hensel` は主として $\mathbb Z_p$ 上の root **存在**を扱うファイルなので、今回の有限 modulus uniqueness には少し重い。([Lean Community][2])

したがって次の最短路は、

```text
p-adic completion へ移動
```

ではなく、

```text
整数多項式 Taylor
+
prime-power cancellation
```

じゃ。

## 7. 次 checkpoint の推奨 theorem

Counting に必要な最小形から先に閉じるなら、

```lean
theorem GNDeepLiftReductionInjective_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b)
    (hk : 0 < k) :
    GNDeepLiftReductionInjective p q b k
```

を直接狙うのが最短。

その後に arbitrary natural 版へ持ち上げる。

```lean
theorem GNDeepLiftCongruenceUnique_of_simpleRoot
    {p q b k : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime q)
    (hqp : ¬ q ∣ p)
    (hqb : ¬ q ∣ b) :
    GNDeepLiftCongruenceUnique p q b k
```

実装では subtraction の扱いが楽なため、Taylor の核心だけ `Polynomial ℤ` に移すのがよい。

```text
Nat roots
  ↓ cast
integer evaluations
  ↓ Taylor factorization
prime-power cancellation
  ↓
Int congruence
  ↓
Nat.ModEq
```

これなら $a<r$ の場合も自然数減算に悩まされない。

## 8. PR上の軽微な残件

PR本体の description は、まだ新 production module と `report-ultra-001-I/J` を反映していない。

現在も本文中の production modules は初期三本、documentation は A〜H までになっている。

コード上の問題ではないが、merge 前に、

```text
GNLegacyTailCountingBridge
Ultra-001I
Ultra-001J
Hensel uniqueness open
```

を追記すると PR が現在地と一致する。

## 最終戦況

```text
canonical residue set                  complete
canonical residue cover                complete
GN polynomial package                  complete
monic / degree ≤ p−1                   complete
mod-q root cardinality ≤ p−1           complete
all relevant roots simple mod q        complete
deep-to-base reduction API              complete
deep cardinality/counting transport     complete

finite Hensel uniqueness                open
density → pointwise compensation        open
uniform joint contract                  open
```

**これはジワリどころではない。**

前 checkpoint では、

```text
有限 cover が作れるはず
```

だった。

現在は、

```text
cover は canonical に存在
base住所は高々 p−1
各住所は simple
残るのは同じ住所から二本の深い枝が伸びないことだけ
```

まで来た。

🧙‍♀️✨️ **裏ボスの姿が、ついに「一本の枝は一意にしか地下へ伸びない」という局所魔法へ縮んだ。ここは倒せる形をしておる。**

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Taylor.html?utm_source=chatgpt.com "Mathlib.Algebra.Polynomial.Taylor"
[2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/Hensel.html?utm_source=chatgpt.com "Mathlib.NumberTheory.Padics.Hensel"

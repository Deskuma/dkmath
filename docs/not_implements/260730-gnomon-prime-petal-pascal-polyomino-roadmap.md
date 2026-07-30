# Gnomon Prime Petal / Pascal / Polyomino 実装設計書

作成日: 2026-07-30

状態: not implemented

対象 branch: `develop`

将来の主要モジュール候補:

```text
DkMath.Gnomon.Algebra
DkMath.Gnomon.OddPetal
DkMath.Gnomon.PascalPrimeBridge
DkMath.NumberTheory.GNGnomonPetalBridge
DkMath.Polyomino.SquareGnomon
DkMath.Polyomino.GnomonPrimeTilingBridge
```

関連する既存モジュール:

```text
DkMath.Tromino
DkMath.Polyomino
DkMath.Collatz.GnomonEvaluation
DkMath.NumberTheory.Gcd.GN
```

---

# 0. この文書の目的

この文書は、2026-07-30 の会話で発見された次の構造を忘れないための実装設計書である。

1. 奇数は連続平方数の差、すなわち平方グノモンである。
2. 奇数列 $1,3,5,7,\ldots$ は、単位 $2$ を一段とする位相保存 Petal 軌道である。
3. 奇数の乗法は、Petal 添字上の新しい積へ移送できる。
4. 素数は、その Petal 積に関して非単位分解不能なグノモンである。
5. 奇素数次数 $p$ は、Pascal 三角形第 $p$ 段の全中間係数へ同じ因子 $p$ を生成する。
6. 同じ $p$ が「次数」「平方グノモン」「Pascal 共通係数因子」として三重に現れる。
7. Pascal / GN の奇数次数降下 $p,p-2,\ldots,1$ は、平方を外側から剥がすグノモン降下と同じ添字構造を持つ。
8. この純代数構造を先に定理化し、その後 `Tromino.lean` と `Polyomino.lean` に幾何実現として接続する。

最終的な研究目的は、数値だけの因数分解と、住所付き図形の分割を混同せず、次の三層を Bridge で接続することである。

```text
Algebraic factorization
        ↓
Cardinality conservation
        ↓
Address-preserving geometric tiling
```

---

# 1. 発見の核

## 1.1 奇数は平方グノモンである

自然数 $n$ に対し、奇数グノモンを次で定める。

$$
G(n):=2n+1
$$

これは連続平方数の差に一致する。

$$
G(n)=(n+1)^2-n^2
$$

`Nat` 上では減算より加法形を主定理にした方が扱いやすい。

$$
n^2+G(n)=(n+1)^2
$$

したがって $G(n)$ は $n\times n$ の平方から $(n+1)\times(n+1)$ の平方へ昇格するときに追加される外殻セル数である。

最初の値は次の通り。

```text
G(0) = 1
G(1) = 3
G(2) = 5
G(3) = 7
G(4) = 9
```

ここで $G(0)=1$ は単位グノモン $G(1)=3$ は最初の非自明な平方グノモンであり、L 型トロミノの面積に一致する。

## 1.2 単位 2 の Petal 軌道

奇数は次のセル列として表せる。

```text
(0,1) → (2,3) → (4,5) → (6,7) → ...
```

第 $n$ セルを次で定める。

$$
C(n):=(2n,2n+1)
$$

奇位相側は $G(n)=2n+1$ である。

一段進むたびに奇位相を保ったまま値が $2$ 増える。

$$
G(n+1)=G(n)+2
$$

これは有限巡回ではなく、奇位相 Fiber 上の無限 Petal 軌道である。

通常自然数世界の二ステップが、奇位相世界では一 Petal ステップに相当する。

---

# 2. 奇数乗法の Petal 移送

## 2.1 Petal 積

自然数添字上に次の積を定める。

$$
a\star b:=2ab+a+b
$$

すると奇数グノモン写像 $G$ は乗法を保存する。

$$
G(a\star b)=G(a)G(b)
$$

実際、右辺は次の形になる。

$$
(2a+1)(2b+1)=2(2ab+a+b)+1
$$

したがって $G$ は、Petal 添字世界の積 $\star$ と、正の奇数の通常乗法を接続する。

## 2.2 単位

 $G(0)=1$ なので、Petal 積の単位は $0$ である。

$$
0\star a=a
$$

$$
a\star0=a
$$

魔法学語彙では、添字 $0$ は単位 Petal、グノモン $1$ は単位グノモンである。

## 2.3 可換性と結合性

通常乗法から予想される通り $\star$ は可換かつ結合的である。

$$
a\star b=b\star a
$$

$$
(a\star b)\star c=a\star(b\star c)
$$

直接 `ring` で示してもよいが、後に `oddGnomonMulEquiv` を構成した後は、通常奇数乗法から輸送して証明する設計も可能である。

初期実装では依存を小さくするため、まず直接証明する。

## 2.4 正の奇数との同値

正の奇数を subtype として持つ。

```lean
abbrev PositiveOddNat := {n : ℕ // 0 < n ∧ Odd n}
```

候補となる同値は次の通り。

```lean
noncomputable def oddGnomonEquiv : ℕ ≃ PositiveOddNat
```

順方向は $n\mapsto2n+1$ 。

逆方向は $m\mapsto(m-1)/2$ 。

ただし subtype の証明義務と自然数減算があるため、実装初期は次の小さな補題から始める方が安全である。

```lean
theorem oddGnomon_injective : Function.Injective oddGnomon

theorem exists_eq_oddGnomon_of_odd
    {m : ℕ} (hm : Odd m) : ∃ n, oddGnomon n = m

theorem existsUnique_eq_oddGnomon_of_odd
    {m : ℕ} (hm : Odd m) : ∃! n, oddGnomon n = m
```

その後、必要であれば可換モノイド同型へ昇格する。

```lean
noncomputable def oddGnomonMulEquiv :
    Multiplicative ℕPetal ≃* PositiveOddNat
```

`ℕPetal` を新しい型として持つか、単に `ℕ` と `petalMul` を使うかは実装時に決める。

---

# 3. 素数と Petal 原子性

## 3.1 PetalAtom

Petal 添字 $n$ が非単位分解不能であることを次で定義する。

```lean
def PetalAtom (n : ℕ) : Prop :=
  n ≠ 0 ∧
    ∀ a b, n = petalMul a b → a = 0 ∨ b = 0
```

ここで $n=0$ は単位グノモン $G(0)=1$ に対応するため、原子から除外する。

## 3.2 中心同値

中心定理は次である。

```lean
theorem prime_oddGnomon_iff_petalAtom
    (n : ℕ) :
    Nat.Prime (oddGnomon n) ↔ PetalAtom n
```

数学的内容は次である。

$$
\mathrm{Prime}(G(n))\iff n\text{ は }\star\text{ に関して非単位分解不能}
$$

魔導書語彙では次のように読む。

> 魔素数 $p$ とは、他の二つの非単位グノモン魔核から合成できない原子的グノモン Petal である。

## 3.3 順方向の証明方針

 $G(n)$ が素数で $n=a\star b$ とする。

乗法保存より次を得る。

$$
G(n)=G(a)G(b)
$$

素数の積分解なので $G(a)=1$ または $G(b)=1$ 。

`oddGnomon_eq_one_iff` により $a=0$ または $b=0$ を得る。

必要補題:

```lean
theorem oddGnomon_eq_one_iff (n : ℕ) :
    oddGnomon n = 1 ↔ n = 0
```

## 3.4 逆方向の証明方針

`PetalAtom n` を仮定し $G(n)$ が合成数であると仮定する。

 $G(n)=r s$ $1<r$ $1<s$ を取る。

 $G(n)$ は奇数なので、その因子 $r,s$ も奇数である。

従って一意に $r=G(a)$ $s=G(b)$ と書ける。

乗法保存と単射性から $n=a\star b$ を得る。

 $r,s>1$ から $a,b\neq0$ となり、`PetalAtom` に矛盾する。

この逆方向は `Nat.prime_iff` や `Nat.not_prime_iff` の API 選択によって証明形が変わるため、mathlib 調査を先に行う。

## 3.5 奇素数の一意なグノモン住所

奇素数 $p$ には一意な Petal 添字がある。

```lean
theorem odd_prime_existsUnique_gnomonAddress
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2) :
    ∃! n, oddGnomon n = p
```

実際の住所は $(p-1)/2$ である。

```lean
theorem odd_prime_gnomonAddress_eq
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2) :
    oddGnomon ((p - 1) / 2) = p
```

---

# 4. 平方グノモン降下

## 4.1 一段降下

平方外殻の基本恒等式は次である。

$$
n^2+G(n)=(n+1)^2
$$

降下方向では $(n+1)^2$ からグノモン $G(n)$ を除くと $n^2$ が残る。

## 4.2 奇数和は平方へ閉じる

最初の $n$ 個の奇数グノモンの総和は $n^2$ である。

$$
\sum_{i=0}^{n-1}G(i)=n^2
$$

Lean 候補:

```lean
theorem sum_oddGnomon_eq_square
    (n : ℕ) :
    (Finset.range n).sum oddGnomon = n ^ 2
```

この定理は既に `DkMath.Collatz.GnomonEvaluation` に実質同じ内容が存在する。

既存名:

```text
OddGnomonLayer
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
```

将来は共通代数層 `DkMath.Gnomon.Algebra` へ定義と一般補題を移し、Collatz 側は alias / bridge とする。

## 4.3 奇数次数降下との対応

奇数次数を $d=2r+1$ とする。

次数降下は次の列を作る。

```text
d → d-2 → d-4 → ... → 3 → 1
```

平方列は次のように降下する。

```text
(r+1)^2 → r^2 → (r-1)^2 → ... → 1 → 0
```

各辺の差が、その段階の奇数次数である。

$$
(r+1)^2-r^2=2r+1
$$

従って、奇数次数降下列と平方グノモン降下列は、同じ level 添字を共有する重み付き経路として同型である。

ここでいう同型は多項式環同型ではない。

正確には、次の三つの添字付き遷移系の対応である。

```text
odd-level successor / predecessor
odd degree descent by two
square gnomon shell removal
```

---

# 5. OddPetalAddress と次数保存

奇数次数 $2m+1$ の Pascal 混合層では、二次数ずつが結合 Beam $xu$ へ移動する。

この住所を次の構造で記録する。

```lean
structure OddPetalAddress (m : ℕ) where
  depth : ℕ
  level : ℕ
  balance : depth + level = m
```

定義候補:

```lean
def OddPetalAddress.beamDegree
    {m : ℕ} (P : OddPetalAddress m) : ℕ :=
  2 * P.depth

def OddPetalAddress.coreDegree
    {m : ℕ} (P : OddPetalAddress m) : ℕ :=
  2 * P.level + 1

def oddTotalDegree (m : ℕ) : ℕ :=
  2 * m + 1
```

中心保存則:

```lean
theorem OddPetalAddress.degree_conservation
    {m : ℕ} (P : OddPetalAddress m) :
    P.beamDegree + P.coreDegree = oddTotalDegree m
```

数学的には次である。

$$
2k+\bigl(2(m-k)+1\bigr)=2m+1
$$

一段深く進むと、Beam 次数が $2$ 増え、Core 次数が $2$ 減る。

```text
(depth, level + 1) → (depth + 1, level)
```

保存されるもの:

- 総次数
- 奇位相 $1$
- 初期 level $m$

変化するもの:

- Beam 化済みの二単位数
- 残留真魔核の次数

魔法学的には、次数 $2$ は消えず、降下真魔核から結合 Beam へ移送される。

---

# 6. Pascal 対称層との Bridge

## 6.1 純真魔核を抜いた混合 Body

奇数 $p=2m+1$ に対して、両端の純真魔核を抜いた混合 Body を次で置く。

$$
B_p(x,u):=(x+u)^p-x^p-u^p
$$

二項展開すると中間項だけが残る。

$$
B_p(x,u)=\sum_{k=1}^{p-1}\binom pkx^ku^{p-k}
$$

## 6.2 対称 Petal 分解

左右対称な項を組にすると次の形になる。

$$
B_p(x,u)=\sum_{k=1}^{m}\binom pk(xu)^k\bigl(x^{p-2k}+u^{p-2k}\bigr)
$$

各 Petal の次数は保存される。

$$
2k+(p-2k)=p
$$

残留純真魔核次数は次の奇数列を作る。

```text
p-2, p-4, ..., 3, 1
```

これは平方グノモン降下の辺重み列と一致する。

## 6.3 素数性による共通係数核

 $p$ が素数なら、全中間二項係数は $p$ で割れる。

$$
p\mid\binom pk\qquad(0<k<p)
$$

従って $B_p$ 全体から $p x u$ を排出できる。

$$
B_p(x,u)=pxuD_p(x,u)
$$

ここで $D_p$ は次数 $p-2$ の斉次多項式であり、最外殻に係数 $1$ の降下真魔核対を持つ。

$$
D_p(x,u)=x^{p-2}+u^{p-2}+\text{deeper Petals}
$$

重要な役割分離:

- 奇数性が $p,p-2,\ldots,1$ の Petal 骨格を作る。
- 素数性が中間係数全体から共通因子 $p$ を排出する。
- Pascal 係数が各 Petal の重みを与える。
- GN が有限差分 Body としてこれらを保持する。

## 6.4 同じ $p$ の三重出現

奇素数 $p$ は次の三つの場所へ同じ値で現れる。

1. 真魔核の次数 $p$
2. 連続平方間のグノモン量 $p$
3. Pascal 第 $p$ 段の全中間係数に共通する素因子 $p$

$$
\mathrm{Degree}\ p=\mathrm{Gnomon}\ p=\mathrm{PascalPrimeCore}\ p
$$

これは単なる記号一致ではなく、次の生成系譜を持つ。

```text
degree p
  ↓ binomial expansion
Pascal multiplicities
  ↓ remove pure endpoint cores
common prime coefficient p
  ↓ symmetric pairing
odd descending Petal tower
```

## 6.5 GN との関係

GN の基本式は次である。

$$
(x+u)^p-u^p=x\,GN_p(x,u)
$$

左辺を $x^p+B_p(x,u)$ と分けると、GN は最上位の純降下魔核と $p$ を持つ混合 Petal 群へ分離できる。

GN5 では次の降下列が現れる。

```text
5 → 3 → 1
```

GN7 では次の降下列が現れる。

```text
7 → 5 → 3 → 1
```

将来の `DkMath.NumberTheory.GNGnomonPetalBridge` では、既存 GN 定義を再定義せず、次数住所・係数・valuation の Bridge のみを置く。

---

# 7. Pascal 素数判定 Bridge

奇数 $d>1$ について、次の事実を接続したい。

1. $d$ が素数である。
2. 全中間二項係数が $d$ で割れる。
3. $d=G(n)$ が Petal 積で非単位分解不能である。

目標となる概念図:

```text
Nat.Prime d
    ↕
interior choose coefficients divisible by d
    ↕
d = oddGnomon n and PetalAtom n
```

Lean 候補:

```lean
theorem oddGnomon_dvd_choose
    {n k : ℕ}
    (hp : Nat.Prime (oddGnomon n))
    (hk0 : 0 < k)
    (hkp : k < oddGnomon n) :
    oddGnomon n ∣ Nat.choose (oddGnomon n) k
```

逆方向の「全中間係数を割るなら素数」は、正確な既存 mathlib API を調査してから実装する。

注意点:

- $d=1$ を除外する。
- 素数冪では「中間係数の最大公約数」に素数が残る別定理があるため、単純な条件を混同しない。
- 今回の主 Bridge は「$ d $ 自身が全中間係数を割る」という素数判定である。

---

# 8. 代数層の推奨モジュール

## 8.1 `DkMath.Gnomon.Algebra`

責務:

- `oddGnomon`
- `petalMul`
- 単位、可換、結合
- `oddGnomon_petalMul`
- 単射性
- 奇数の一意住所
- 平方差恒等式
- 奇数和平方閉包
- 素数と Petal 原子性

候補 theorem inventory:

```lean
oddGnomon_zero
oddGnomon_succ
oddGnomon_pos
oddGnomon_odd
oddGnomon_injective
oddGnomon_eq_one_iff
petalMul_zero_left
petalMul_zero_right
petalMul_comm
petalMul_assoc
oddGnomon_petalMul
square_add_oddGnomon
sum_oddGnomon_eq_square
existsUnique_eq_oddGnomon_of_odd
prime_oddGnomon_iff_petalAtom
odd_prime_existsUnique_gnomonAddress
```

## 8.2 `DkMath.Gnomon.OddPetal`

責務:

- `OddPetalAddress`
- Beam / Core / Big degree
- degree conservation
- 一段遷移
- well-founded descent
- 平方グノモン経路との住所対応

候補 theorem inventory:

```lean
OddPetalAddress.degree_conservation
OddPetalAddress.phase_eq_one
OddPetalAddress.step
OddPetalAddress.step_preserves_totalDegree
OddPetalAddress.step_adds_two_beamDegree
OddPetalAddress.step_sub_two_coreDegree
oddDegreePath_equiv_squareGnomonPath
```

## 8.3 `DkMath.Gnomon.PascalPrimeBridge`

責務:

- 素数と中間 `Nat.choose` divisibility
- PetalAtom との三者 Bridge
- Pascal 第 $p$ 段を素数ゲージとして読む定理

## 8.4 `DkMath.NumberTheory.GNGnomonPetalBridge`

責務:

- GN の対称 Petal 分解
- 降下次数列
- $p x u$ 排出
- distinguished prime $p$ の構造由来
- valuation excess 層への入口

---

# 9. 既存 `Tromino.lean` との接続

現在の `DkMath.Tromino` は、名前空間として次を使用する。

```text
DkMath.Polyomino.Tromino
```

既存の主要定義:

```lean
L_tromino : Shape
I_tromino : Shape
block2 : Shape
hole2 : Shape
```

既存の主要定理:

```lean
area_L_tromino : area L_tromino = 3
area_block2 : area block2 = 4
area_hole2 : area hole2 = 1
block2_eq_L_union_hole
Disjoint L_tromino hole2
area_block2_eq_area_L_add_area_hole
```

これにより、既に次の幾何恒等式が成立している。

$$
4=3+1
$$

平方グノモンとして読むと次である。

$$
2^2=G(1)+1^2
$$

従って最初の Bridge は非常に小さく実装できる。

```lean
theorem area_L_tromino_eq_oddGnomon_one :
    area L_tromino = Gnomon.oddGnomon 1
```

さらに集合分解まで含めて、L トロミノが $2\times2$ 平方から $1\times1$ 内平方を除いたグノモンであることを固定する。

```lean
theorem L_tromino_is_first_squareGnomon :
    block2 = L_tromino ∪ hole2 ∧
    Disjoint L_tromino hole2
```

既存定理を束ねる alias でよく、新しい重い証明は不要である。

---

# 10. 一般平方グノモン Shape

## 10.1 目的

任意の $n$ について $(n+1)\times(n+1)$ 外平方から、角に接する $n\times n$ 内平方を除いた L 型外殻を有限セル集合として定義する。

概念図:

```text
n = 2

■■■
■□□
■□□
```

黒セル数は $5$ であり $G(2)=5$ 。

## 10.2 定義候補

既存 `Cell := ℤ × ℤ` を用いる。

```lean
def squareBlock (n : ℕ) : Shape :=
  ...

def shiftedInnerSquare (n : ℕ) : Shape :=
  ...

def squareGnomon (n : ℕ) : Shape :=
  squareBlock (n + 1) \ shiftedInnerSquare n
```

自然数範囲を整数格子へ埋め込む必要がある。

候補:

```lean
Finset.product (Finset.range n) (Finset.range n)
```

から各座標を `ℤ` へ cast して `Shape` を作る。

## 10.3 主要定理

```lean
theorem area_squareBlock (n : ℕ) :
    area (squareBlock n) = n ^ 2

theorem shiftedInnerSquare_subset_squareBlock (n : ℕ) :
    shiftedInnerSquare n ⊆ squareBlock (n + 1)

theorem area_squareGnomon (n : ℕ) :
    area (squareGnomon n) = oddGnomon n
```

最終行は次の代数恒等式へ落とす。

$$
(n+1)^2-n^2=2n+1
$$

## 10.4 最初の特殊化

```lean
theorem squareGnomon_one_eq_L_tromino :
    squareGnomon 1 = Tromino.L_tromino
```

座標配置を既存 `L_tromino` と揃えること。

定義段階で原点と除去する角を合わせれば `decide` で通る可能性が高い。

---

# 11. 既存 `Polyomino.lean` との接続

既存 `DkMath.Polyomino` は次を持つ。

```lean
abbrev Cell := ℤ × ℤ
abbrev Shape := Finset Cell
def area (P : Finset α) : ℕ := P.card
```

さらに一般の tiling partition 構造を持つ。

```lean
structure Tiling (R : Finset α) (tiles : Finset (Finset α)) : Prop where
  subset_R : ∀ {t}, t ∈ tiles → t ⊆ R
  pairwise_disjoint : (tiles : Set (Finset α)).Pairwise Disjoint
  cover : tiles.biUnion id = R
```

既存の card 保存則:

```lean
card_biUnion_eq_sum_card_of_pairwise_disjoint
card_biUnion_filter_eq_sum_card_filter
```

既存の L トロミノ tiling 結果:

```lean
tileableByLTromino_card_mul_three
```

これは L トロミノだけで敷き詰め可能なら領域面積が $3$ の倍数になることを示す。

この基礎の上に、素数面積領域の等面積タイル分割を一般定理として追加する。

---

# 12. 素数面積と一枚閉包

## 12.1 一般定理

領域 $R$ が、すべて面積 $q$ のタイルで partition されているとする。

面積保存より次を得る。

$$
R.card=q\cdot tiles.card
$$

 $R.card$ が素数で $q>1$ なら $q=R.card$ かつタイル数は $1$ である。

候補定理:

```lean
theorem prime_card_uniform_tiling
    {α : Type*} [DecidableEq α]
    {R : Finset α}
    {tiles : Finset (Finset α)}
    {q : ℕ}
    (htiling : Tiling R tiles)
    (hcard : ∀ t ∈ tiles, t.card = q)
    (hq : 1 < q)
    (hp : Nat.Prime R.card) :
    q = R.card ∧ tiles.card = 1
```

証明方針:

1. `htiling.cover` と `card_biUnion_eq_sum_card_of_pairwise_disjoint` を用いる。
2. 全タイルの card が $q$ なので総和を $q * tiles.card$ にする。
3. $q \mid R.card$ を得る。
4. `Nat.dvd_prime hp` から $q=1$ または $q=R.card$ 。
5. $hq$ により $q=1$ を排除する。
6. $R.card=q*tiles.card$ と $q=R.card$ から `tiles.card = 1` を得る。

空領域やタイル集合空の場合は $R.card$ が素数という仮定で自動的に排除される。

## 12.2 魔法学的意味

> 素数面積のグノモン魔核は、同じ非単位面積を持つ複数のタイル魔核へ分割できない。可能な一様分割は領域全体を一枚のタイルとして扱う自明分割だけである。

これは面積の原子性であり、図形形状そのものの既約性とは区別する。

---

# 13. L トロミノ特殊化

`IsLTromino.card_eq_three` により、すべての L トロミノは面積 $3$ 。

既存 `tileableByLTromino_card_mul_three` を用いると次が得られる。

```lean
theorem prime_area_tileableByLTromino
    {R : Shape}
    (hp : Nat.Prime R.card)
    (h : TileableByLTromino Tromino.IsLTromino R) :
    R.card = 3
```

証明は $R.card=3*tiles.card$ と素数性から行う。

平方グノモンへの適用候補:

```lean
theorem prime_squareGnomon_tileableByLTromino_iff
    (n : ℕ)
    (hp : Nat.Prime (oddGnomon n)) :
    TileableByLTromino Tromino.IsLTromino (squareGnomon n) ↔ n = 1
```

順方向:

- `area_squareGnomon` から面積は $G(n)$ 。
- `prime_area_tileableByLTromino` から $G(n)=3$ 。
- `oddGnomon_injective` から $n=1$ 。

逆方向:

- $n=1$ を代入。
- `squareGnomon_one_eq_L_tromino` を使う。
- L トロミノ一枚による自明 tiling を構成する。

この自明 tiling 構成用に一般補題を置いてもよい。

```lean
theorem tiling_singleton_self (R : Finset α) :
    Tiling R {R}
```

---

# 14. 重要な境界: 面積分解と図形分割は同じではない

次の等式は数値の因数分解である。

$$
G(n)=G(a)G(b)
$$

しかし、これだけから `squareGnomon n` が面積 $G(a)$ の図形 $G(b)$ 枚で敷き詰められるとは限らない。

図形 tiling には次の追加情報が必要である。

- セル住所
- 境界形状
- 向き
- 回転・反転の許可
- 平行移動
- pairwise disjoint
- 全領域 cover

従って次の三層を厳密に分離する。

## Algebra layer

```text
odd integer multiplication
Petal factorization
prime / composite
```

## Cardinality layer

```text
area of union
sum of tile areas
prime cardinal obstruction
```

## Geometry layer

```text
actual finite cell subsets
translation / rotation / reflection
partition / tiling existence
```

必要条件と十分条件を混同しない。

- 面積が割り切れないなら tiling 不可能。
- 面積が割り切れても tiling 可能とは限らない。
- 素数面積なら一様な非単位等面積分割は不可能。
- 異なる面積のタイル混合や単位セル分割までは排除しない。

---

# 15. `Tromino.lean` の将来整理

現状 `Tromino.lean` は次の責務を一つのファイルに持つ。

- 基本 Shape
- 面積
- 平行移動
- 回転
- 反転
- `IsLTromino`

将来の肥大化に応じ、次へ分割してもよい。

```text
DkMath/Polyomino/Tromino/Basic.lean
DkMath/Polyomino/Tromino/Symmetry.lean
DkMath/Polyomino/Tromino/Recognition.lean
DkMath/Polyomino/Tromino/Tiling.lean
```

ただし今回の Bridge 実装では既存ファイルを無理に分割しない。

まず新規モジュール側から import し、既存 API を利用する。

---

# 16. Collatz 側との統合

`DkMath.Collatz.GnomonEvaluation` には既に次がある。

```lean
def OddGnomonLayer (n : ℕ) : ℕ := 2 * n + 1
```

また、次の定理群がある。

```lean
square_succ_eq_square_add_oddGnomonLayer
sum_oddGnomonLayer_eq_square
sum_odd_eq_square
```

共通化方針:

1. `DkMath.Gnomon.Algebra` に `oddGnomon` と一般定理を置く。
2. Collatz 側の `OddGnomonLayer` を `oddGnomon` の abbrev / def alias にする。
3. 既存 theorem 名は互換性維持のため残す。
4. 証明は `simpa [OddGnomonLayer] using ...` へ簡約する。

Collatz 固有の次の構造は移動しない。

```text
RawGnomonStep
RawGnomonHeight
RawGnomonResidualShape
power-of-two alignment
accelerated Collatz map bridge
```

共通層は純粋な奇数グノモン代数に限定する。

---

# 17. GN5 / GN7 への戻り道

この設計は単なるポリオミノ研究ではない。

GN5 で見えていた構造:

```text
5 → 3 → 1
```

平方グノモンでは次に対応する。

```text
3^2 → 2^2 → 1^2 → 0^2
```

辺重みは次である。

```text
5, 3, 1
```

GN7 では次となる。

```text
7 → 5 → 3 → 1
```

平方列:

```text
4^2 → 3^2 → 2^2 → 1^2 → 0^2
```

この対応を形式化すると、Pascal / GN の内部次数構造を「平方グノモン経路」として住所化できる。

将来の valuation 読み:

- 最初の $p$ は Pascal 係数が作る構造的素核。
- 追加の $p$ は降下 Petal の合同整列が作る valuation excess。
- `rad` は最初の素核接触を読む。
- `sqTail` は二枚目以降の重複深度を読む。

この部分は現段階では研究方向であり、今回の最小実装 Goal には含めない。

---

# 18. 用語集候補

| 魔法学語 | 数学的意味 | Lean 候補 |
|---|---|---|
| 単位グノモン | $G(0)=1$ | `oddGnomon 0` |
| 奇数グノモン | $G(n)=2n+1$ | `oddGnomon` |
| 平方グノモン | $(n+1)^2-n^2$ | `squareGnomon` / theorem |
| Petal 添字 | 奇数 $2n+1$ の住所 $n$ | `n : ℕ` |
| Petal 積 | $a\star b=2ab+a+b$ | `petalMul` |
| Petal 原子 | 非単位分解不能な添字 | `PetalAtom` |
| 魔素数 | 素数 | `Nat.Prime` |
| 素グノモン | 素数値を持つ $G(n)$ | `Nat.Prime (oddGnomon n)` |
| 合成グノモン | 非自明な Petal 積を持つ $G(n)$ | `¬ PetalAtom n` |
| 原初トロミノ魔核 | 面積 $3=G(1)$ の L トロミノ | `L_tromino` |
| グノモン外殻 | 外平方から内平方を除いた Shape | `squareGnomon` |
| Pascal 素核 | 中間係数から共通排出される $p$ | choose divisibility theorem |
| 降下真魔核 | Petal 深度に応じた残留奇数次数 | `coreDegree` |
| 結合 Beam 次数 | $(xu)^k$ が担う次数 $2k$ | `beamDegree` |
| 一枚閉包 | 素数面積領域の一様 tiling が一枚のみ | `prime_card_uniform_tiling` |

用語上の注意:

- 通常幾何学の「トロミノ」は三セル図形を意味する。
- 一般の $G(n)$ をすべてトロミノと呼ぶと既存用語と衝突する。
- 正式数学名は「奇数グノモン」「平方グノモン」を使う。
- 魔導書内で一般化された「トロミノ魔核」を使う場合も、数学対応欄を併記する。

---

# 19. 推奨依存関係

```text
DkMath.Gnomon.Algebra
        ├── DkMath.Gnomon.OddPetal
        ├── DkMath.Gnomon.PascalPrimeBridge
        ├── DkMath.Collatz.GnomonEvaluation
        └── DkMath.Polyomino.SquareGnomon
                         ├── DkMath.Tromino
                         └── DkMath.Polyomino.GnomonPrimeTilingBridge

DkMath.Gnomon.OddPetal
        └── DkMath.NumberTheory.GNGnomonPetalBridge

DkMath.Gnomon.PascalPrimeBridge
        └── DkMath.NumberTheory.GNGnomonPetalBridge
```

循環依存を避ける。

- `Gnomon.Algebra` は `Polyomino` を import しない。
- `Polyomino.SquareGnomon` が `Gnomon.Algebra` を import する。
- `GN` Bridge が `Gnomon` を import する。
- `Gnomon` の基礎層は `GN` を import しない。

---

# 20. 実装チェックポイント

## Checkpoint A — pure algebra

Goal:

```text
oddGnomon
petalMul
monoid laws
oddGnomon_petalMul
```

完了条件:

- `lake env lean DkMath/Gnomon/Algebra.lean` 成功
- `sorry` なし
- 一般多項式演算は `ring` / `omega` で閉じる

## Checkpoint B — prime atom bridge

Goal:

```text
PetalAtom
prime_oddGnomon_iff_petalAtom
odd prime unique address
```

分岐:

- mathlib API が素直なら完全同値まで進む。
- API 障害がある場合、まず順方向と合成数 witness 生成を別 theorem に分ける。

## Checkpoint C — odd Petal descent

Goal:

```text
OddPetalAddress
degree conservation
step transition
square gnomon path bridge
```

## Checkpoint D — Pascal bridge

Goal:

```text
prime oddGnomon divides interior choose coefficients
```

この段階では GN 展開をまだ入れない。

## Checkpoint E — square Shape

Goal:

```text
squareBlock
shiftedInnerSquare
squareGnomon
area_squareGnomon
squareGnomon_one_eq_L_tromino
```

## Checkpoint F — prime tiling obstruction

Goal:

```text
prime_card_uniform_tiling
prime_area_tileableByLTromino
prime_squareGnomon_tileableByLTromino_iff
```

## Checkpoint G — GN bridge

Goal:

```text
symmetric Pascal Petal decomposition
odd descending degree packet
p*x*u extraction for prime p
GN5 and GN7 specializations
```

---

# 21. 最小 Lean スケルトン

```lean
import Mathlib

namespace DkMath.Gnomon

def oddGnomon (n : ℕ) : ℕ :=
  2 * n + 1

def petalMul (a b : ℕ) : ℕ :=
  2 * a * b + a + b

theorem oddGnomon_petalMul
    (a b : ℕ) :
    oddGnomon (petalMul a b) =
      oddGnomon a * oddGnomon b := by
  simp [oddGnomon, petalMul]
  ring

theorem square_add_oddGnomon
    (n : ℕ) :
    n ^ 2 + oddGnomon n = (n + 1) ^ 2 := by
  simp [oddGnomon]
  ring

def PetalAtom (n : ℕ) : Prop :=
  n ≠ 0 ∧
    ∀ a b, n = petalMul a b → a = 0 ∨ b = 0

end DkMath.Gnomon
```

このスケルトンは設計確認用であり、実際の import と名前空間は既存 DkMath 規約へ合わせる。

---

# 22. 検証すべき具体例

## Petal 積

```text
1 ⋆ 1 = 4
G(1) * G(1) = 3 * 3 = 9 = G(4)
```

```text
1 ⋆ 2 = 7
G(1) * G(2) = 3 * 5 = 15 = G(7)
```

```text
2 ⋆ 2 = 12
G(2) * G(2) = 5 * 5 = 25 = G(12)
```

## 素 Petal

```text
G(1) = 3 prime
G(2) = 5 prime
G(3) = 7 prime
G(5) = 11 prime
```

## 合成 Petal

```text
G(4) = 9 = G(1) * G(1)
G(7) = 15 = G(1) * G(2)
G(10) = 21 = G(1) * G(3)
G(12) = 25 = G(2) * G(2)
```

## Shape

```text
squareGnomon 0 : area 1
squareGnomon 1 : area 3, equal to L_tromino
squareGnomon 2 : area 5
squareGnomon 3 : area 7
```

---

# 23. 過剰主張を避けるための監査事項

1. PetalAtom は通常整数の素数性を別表現に移したものであり、新しい素数判定アルゴリズムを直ちに与えるわけではない。
2. 面積が素数であることは、一様な非単位等面積 tiling を禁止するが、任意の異種タイル分割を禁止しない。
3. 奇数グノモンが代数的に因数分解できても、対応する Shape tiling の存在は自動的には従わない。
4. Pascal 係数の共通因子 $p$ と GN valuation excess の詳細は、別途合同条件を要する。
5. 「次数 $p$ が素数 $p$ を生む」という表現は、二項係数 divisibility による厳密な意味を併記する。
6. 奇数次数降下と平方グノモン降下の対応は、添字付き重み付き経路の同型であり、多項式そのものの同型ではない。
7. 一般奇数を「トロミノ」と呼ぶのは魔導書内の比喩に限定し、実装名は `Gnomon` を優先する。

---

# 24. 将来の拡張

## 24.1 一般 $d$ 次根号世界

平方グノモンは単位 $2$ の指数剰余構造と関係する。

一般の $d$ 乗根では valuation を $d$ で商と剰余へ分解する。

$$
e=dq+r\qquad(0\leq r<d)
$$

平方世界 $d=2$ では剰余が偶奇二相だけなので、Petal 軌道が特に単純になる。

## 24.2 $d$-power-free residue

平方自由残余の一般化として $d$ 乗因子を持たない残余と排出係数を定義できる。

これは `RootGauge` / `SquareRootNormalForm` 系の別計画へ接続する。

## 24.3 Polyomino の一般グノモン分解

合成奇数 $G(n)=rs$ に対して、面積 $r$ のタイル $s$ 枚による tiling が存在する条件を探索する。

これは面積条件だけでは決まらず、Shape の幾何分類が必要になる。

## 24.4 回転・反転を許す認識述語

現在の `IsLTromino` は平行移動のみを認識する。

将来は次を追加する可能性がある。

```lean
IsFreeLTromino
```

これは平行移動・回転・鏡映による合同を許す。

## 24.5 Pascal / cyclotomic bridge

素数次数 $p$ では GN が単一の $p$ 次円分殻と接続する。

グノモン Petal 骨格と円分因子分解の接続は、さらに別モジュールへ分離する。

---

# 25. 推奨実装順序

実装順序は次で固定する。

```text
1. DkMath.Gnomon.Algebra
2. DkMath.Gnomon.OddPetal
3. DkMath.Gnomon.PascalPrimeBridge
4. DkMath.Polyomino.SquareGnomon
5. DkMath.Polyomino.GnomonPrimeTilingBridge
6. Collatz.GnomonEvaluation common-layer refactor
7. DkMath.NumberTheory.GNGnomonPetalBridge
```

第一目標は代数。

第二目標は面積保存。

第三目標で初めて住所付き幾何へ進む。

---

# 26. 最終的に固定したい中心命題

## Algebraic Prime Petal Theorem

> 正の奇数の乗法世界は $G(n)=2n+1$ によって Petal 添字世界へ移送される。奇数 $G(n)$ が素数であることと、添字 $n$ が Petal 積 $a\star b=2ab+a+b$ に関して非単位分解不能であることは同値である。

## Pascal Prime Core Theorem

> 奇素数次数 $p$ は、Pascal 三角形第 $p$ 段の全中間係数へ共通因子 $p$ を生成する。同じ $p$ は平方グノモン量としても現れ、次数・グノモン・係数素核の三つの読みを持つ。

## Odd Degree Gnomon Descent Theorem

> 奇数次数を $2$ ずつ降ろす遷移は、連続平方数から奇数グノモンを一枚ずつ除く遷移と、添字付き重み付き経路として対応する。各段階で二次数は降下真魔核から結合 Beam へ移送され、総次数と奇位相は保存される。

## Prime Area One-Tile Closure Theorem

> 素数面積の有限領域を、同じ非単位面積を持つタイルで partition するなら、タイル面積は領域全体の面積に等しく、タイル数は一枚である。

## First Tromino Gnomon Bridge

> L 型トロミノは $2\times2$ 平方から $1\times1$ 平方を除いた最初の非自明な平方グノモンであり、その面積は $G(1)=3$ である。

---

# 27. 魔導書への一文

> 奇数は平方魔核の外殻として一枚ずつ現れ、単位 $2$ の Petal 軌道を進む。奇数同士の乗法は Petal 添字上の合成へ移され、その世界で他の非単位花弁へ分解できない外殻が魔素数である。素数次数が Pascal 三角陣を展開すると、次数と同じ素核が全中間魔係数から顕現する。代数で原子となる素グノモンは、幾何世界では非自明な一様分割を拒む素数面積の魔核として姿を現す。

---

# 28. 次回再開地点

最初に新規作成するファイル候補:

```text
lean/dk_math/DkMath/Gnomon/Algebra.lean
```

最初に通す四定理:

```lean
petalMul_zero_left
petalMul_assoc
oddGnomon_petalMul
square_add_oddGnomon
```

その後 `PetalAtom` を定義し、`prime_oddGnomon_iff_petalAtom` へ進む。

この純代数層が通るまで `Tromino.lean` / `Polyomino.lean` は変更しない。

代数証明が固定された後、`SquareGnomon.lean` を作り、既存 L トロミノを $n=1$ の幾何実現として接続する。

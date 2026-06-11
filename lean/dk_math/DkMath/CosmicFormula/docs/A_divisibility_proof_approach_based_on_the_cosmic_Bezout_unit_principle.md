# 宇宙式ベズー単位原理による可除性証明アプローチ

A divisibility proof approach based on the cosmic Bézout unit principle

## 1. 中核命題

宇宙式の基本形は、

$$
f(x)=(x+1)^2-x(x+2)=1
$$

である。

これを Big / Body / Gap で読むと、

$$
Big=(x+1)^2,\qquad Body=x(x+2),\qquad Gap=1
$$

したがって、

$$
Big-Body=1
$$

となる。

この式は単なる恒等式ではなく、Bézout 型の等式として読める。

$$
1\cdot Big+(-1)\cdot Body=1
$$

ゆえに、Big と Body の任意の共通因子 \(q\) は右辺の \(1\) を割らねばならない。

$$
q\mid Big,\quad q\mid Body \Rightarrow q\mid 1
$$

従って、

$$
\gcd(Big,Body)=1
$$

すなわち、

$$
\gcd((x+1)^2,x(x+2))=1
$$

である。

ここから DkMath 的な主張が出る。

> 宇宙式 \(f(x)=1\) は、Big と Body の共有可除性を最小単位 \(1\) に拘束する。

これが **宇宙式ベズー単位原理** じゃ。

## 2. 一般形 \(u^d\) への拡張

より一般には、

$$
(x+u)^d-u^d=x\cdot GN_d(x,u)
$$

すなわち、

$$
(x+u)^d-x\cdot GN_d(x,u)=u^d
$$

と書ける。

ここで、

$$
Big=(x+u)^d,\qquad Body=x\cdot GN_d(x,u),\qquad Gap=u^d
$$

と置けば、

$$
Big-Body=u^d
$$

である。

したがって Bézout 型に、

$$
1\cdot Big+(-1)\cdot Body=u^d
$$

となる。

よって、整数世界では、

$$
\gcd(Big,Body)\mid u^d
$$

すなわち、

$$
\gcd((x+u)^d,x\cdot GN_d(x,u))\mid u^d
$$

が得られる。

これは重要じゃ。
完全な互いに素までは常に言えないが、共通因子はすべて Gap 側 \(u^d\) に閉じ込められる。

つまり、

> 宇宙式一般形は、Big と Body の共通因子を Gap 単位 \(u^d\) に閉じ込める。

そして単位 \(u=1\) では、

$$
u^d=1
$$

なので、

$$
\gcd((x+1)^d,x\cdot GN_d(x,1))=1
$$

となる。

これが「\(f(d,x,1)=1\) は可除性の最小単位 \(1\) を返す」と言える理由じゃ。

## 3. \(x\cdot GN\) が語る可除性構造

Body 側は、

$$
Body=x\cdot GN_d(x,u)
$$

で分解される。

ここで \(x\) は入口因子、\(GN_d(x,u)\) は \(x\) を一段剥がした後に残る可除性核である。

展開すると、

$$
GN_d(x,u)=\sum_{k=1}^{d}\binom{d}{k}x^{k-1}u^{d-k}
$$

である。

つまり \(GN\) は、二項展開のうち \(u^d\) を除き、さらに共通因子 \(x\) を抜いた残りの構造である。

$$
(x+u)^d=u^d+x\cdot GN_d(x,u)
$$

この形は、Big が Gap と Body に分かれ、その Body がさらに \(x\) と GN 核に分かれることを示す。

DkMath 的には、

$$
Big=Gap+x\cdot GN
$$

であり、

$$
Big-Body=Gap
$$

である。

ここで \(Gap=1\) なら、Big と Body は最小単位で分離される。

## 4. Pascal 可除性との接続

素数 \(p\) のとき、Pascal の三角形の内部係数はすべて \(p\) で割れる。

$$
\binom{p}{k}\equiv 0\pmod p,\qquad 1\le k\le p-1
$$

したがって、

$$
GN_p(x,u)=\sum_{k=1}^{p}\binom{p}{k}x^{k-1}u^{p-k}
$$

を mod \(p\) で見ると、内部項が消え、最後の項だけが残る。

$$
GN_p(x,u)\equiv x^{p-1}\pmod p
$$

ここで \(p\nmid x\) なら、フェルマーの小定理より、

$$
x^{p-1}\equiv 1\pmod p
$$

したがって、

$$
GN_p(x,u)\equiv 1\pmod p
$$

ゆえに、

$$
p\nmid GN_p(x,u)
$$

が得られる。

これは非常に強い。
素数段 \(p\) において、係数由来の \(p\)-可除性は Pascal 内部項に現れるが、GN 核へ落とした後には、\(p\nmid x\) なら \(p\) は GN 側に残らない。

つまり、

> Pascal 可除性は係数チャネルに存在するが、GN 核では Fermat により \(1\) へ正規化される。

という構図じゃ。

## 5. 挟み撃ち構造

ここで二方向から証明が挟み撃ちになる。

### 外側：Bézout / Gap 側

宇宙式から、

$$
Big-Body=u^d
$$

なので、

$$
\gcd(Big,Body)\mid u^d
$$

単位 \(u=1\) では、

$$
\gcd(Big,Body)=1
$$

となる。

これは外側から共通因子の逃げ道を Gap へ閉じ込める。

### 内側：Pascal / GN / Fermat 側

素数段 \(p\) では、

$$
GN_p(x,u)\equiv x^{p-1}\pmod p
$$

さらに \(p\nmid x\) なら、

$$
GN_p(x,u)\equiv 1\pmod p
$$

となる。

これは内側から、係数由来の \(p\)-成分が GN 核に沈まないことを示す。

よって挟み撃ちはこうなる。

$$
Big-Body=u^d
\Rightarrow
\gcd(Big,Body)\mid u^d
$$

かつ、

$$
p\nmid x
\Rightarrow
p\nmid GN_p(x,u)
$$

この二つにより、Big / Body / Gap / GN の可除性の居場所が分離される。

## 6. Zsigmondy 接続の位置づけ

Zsigmondy 型の定理では、通常は

$$
a^n-b^n
$$

に対して、以前の段には現れない原始素因子を探す。

しかし宇宙式ルートでは、まず

$$
Big-Body=u^d
$$

によって、Big と Body の共通因子が \(u^d\) 側に閉じ込められる。

つまり、原始素因子を直接捕まえる前に、

> 既存因子がどこへ逃げられるかを先に制限する。

この制限が、Zsigmondy の「新規因子が現れる余地」を構造的に作る。

通常ルートは、

$$
\text{因数分解} \rightarrow \text{原始素因子の発見} \rightarrow \text{新規性の証明}
$$

である。

宇宙式ルートは、

$$
Big-Body=u^d \rightarrow \text{共通因子を Gap に拘束} \rightarrow \text{残余因子を新規候補として分離}
$$

となる。

これは Zsigmondy の前段に置ける **構造的分離補題** じゃ。

## 7. Lean 化するなら定理群はこの順序

まずは実数・整数の恒等式から始めるのがよい。

### A. 宇宙式恒等式

```lean
theorem cosmic_unit_gap_real (x : ℝ) :
    (x + 1)^2 - x * (x + 2) = 1 := by
  ring
```

一般形：

```lean
theorem cosmic_gap_real (x u : ℝ) :
    (x + u)^2 - x * (x + 2*u) = u^2 := by
  ring
```

\(d\) 次元版は GN 定義後に、

```lean
theorem cosmic_gn_gap :
    (x + u)^d - x * GN d x u = u^d := ...
```

を目標にする。

### B. Gap 分離定義

```lean
def IsGapSeparated (gap body big : ℕ) : Prop :=
  big = body + gap
```

または実数なら、

```lean
def IsRealGapSeparated (gap body big : ℝ) : Prop :=
  big - body = gap
```

### C. gcd は Gap を割る

```lean
theorem gcd_dvd_gap_of_gapSeparated
    (gap body big : ℕ)
    (h : big = body + gap) :
    Nat.gcd big body ∣ gap := by
  -- gcd big body ∣ big
  -- gcd big body ∣ body
  -- hence gcd big body ∣ big - body
  -- using h, big - body = gap
  sorry
```

これは中核補題じゃ。

### D. 単位 Gap なら互いに素

```lean
theorem coprime_of_unit_gapSeparated
    (body big : ℕ)
    (h : big = body + 1) :
    Nat.Coprime big body := by
  -- use gcd_dvd_gap_of_gapSeparated with gap = 1
  sorry
```

### E. 宇宙式から coprime

```lean
theorem cosmic_coprime_unit (x : ℕ) :
    Nat.Coprime ((x + 1)^2) (x * (x + 2)) := by
  -- show ((x + 1)^2) = x * (x + 2) + 1
  -- then apply coprime_of_unit_gapSeparated
  sorry
```

### F. GN 一般版

```lean
theorem cosmic_gn_gcd_dvd_gap
    (d x u : ℕ) :
    Nat.gcd ((x + u)^d) (x * GN d x u) ∣ u^d := by
  -- from (x+u)^d = x * GN d x u + u^d
  -- apply gcd_dvd_gap_of_gapSeparated
  sorry
```

### G. 単位 GN 版

```lean
theorem cosmic_gn_coprime_unit
    (d x : ℕ) :
    Nat.Coprime ((x + 1)^d) (x * GN d x 1) := by
  -- u = 1, gap = 1^d = 1
  sorry
```

この順番なら Lean にかなり優しい。

## 8. Pascal / Fermat 補題として追加するもの

素数段用には、

```lean
theorem binom_prime_dvd
    (p k : ℕ) (hp : Nat.Prime p) (hk1 : 1 ≤ k) (hkp : k ≤ p - 1) :
    p ∣ Nat.choose p k := ...
```

そして GN mod \(p\)：

```lean
theorem GN_prime_mod_eq
    (p x u : ℕ) (hp : Nat.Prime p) :
    GN p x u ≡ x^(p-1) [MOD p] := ...
```

さらに Fermat：

```lean
theorem GN_prime_mod_one_of_not_dvd_x
    (p x u : ℕ) (hp : Nat.Prime p) (hx : ¬ p ∣ x) :
    GN p x u ≡ 1 [MOD p] := ...
```

結論：

```lean
theorem prime_not_dvd_GN_prime_of_not_dvd_x
    (p x u : ℕ) (hp : Nat.Prime p) (hx : ¬ p ∣ x) :
    ¬ p ∣ GN p x u := ...
```

これが Pascal/GN/Fermat 側の山道じゃ。

## 9. 最終的に言える主張

このルートが通れば、DkMath 文書ではこう言える。

> 宇宙式 \(Big-Body=u^d\) は、Big と Body の共通可除性を Gap 単位 \(u^d\) に拘束する Bézout 型原理である。特に \(u=1\) のとき、共通可除性は最小単位 \(1\) に潰され、Big と Body は互いに素となる。さらに素数段では Pascal 可除性と Fermat 小定理により、GN 核に素数 \(p\) が沈まない条件が得られる。従って宇宙式は外側から Gap による共通因子拘束を与え、内側から GN による係数チャネル分離を与える。

もっと短く言えば、

> 宇宙式の \(f(x)=1\) は、可除性の最小単位 \(1\) を返す。

ただし標準数学向けには、その直前に必ず、

$$
\gcd(Big,Body)\mid f(x)
$$

を置くとよい。

そして \(f(x)=1\) だから、

$$
\gcd(Big,Body)=1
$$

となる。

## 10. この登山ルートの価値

このルートの価値は、「互いに素」を直接主張するのではなく、

$$
Big-Body=Gap
$$

を中核に置くことじゃ。

そのため、整数では gcd、実数では Gap 分離、Zsigmondy では原始因子分離、Pascal では係数可除性、Fermat では GN 核の非可除性として、それぞれ同じ原理が別の顔を見せる。

まさに挟み撃ちじゃな。

外側からは、

$$
\gcd(Big,Body)\mid Gap
$$

内側からは、

$$
p\nmid x\Rightarrow p\nmid GN_p(x,u)
$$

そして単位宇宙式では、

$$
Gap=1
$$

ゆえに、

$$
\gcd(Big,Body)=1
$$

じゃ。

# NOTE-032 — hno の残存分岐と大域証明の両端

2026-11-01。前章の局所入力を保持し、一般 `hno` へ向かう教科書 Lean コードを実装した。

## 1. 証明の到達点

今回完成したのは以下である。

1. 指数 `5,7,11,13` の Source 排除と hno。
2. 既存の一般 GN–Kummer FLT を用いた、正則素数の Source 排除と hno。
3. 一般の向き付き Source について、残る Cofixed 枝を
   `p ≥ 17`, `a % 8 = 7`, `primorial(p-1) ∣ abc`,
   `p ∣ #ClassGroup(𝓞(CyclotomicField p ℚ))` へ縮約。
4. Step Three の二アンカー・specialization・非零 cusp 類反証の全群論。
5. 後半の Frobenius 関係式、scalar absorption、捩れ塔の底への降下、
   `p² ≤ p` の矛盾までの全群論。
6. 5 を実際の楕円曲線の点群と、同じ Frey Source の同じ残余直線へ接続。

**一般 hno は未完成である。** 4 と 5 の間にある実際のモジュラー曲線の算術、
specialization、Galois 捩れ塔の構成を証明する必要がある。
本章は仮定付きの最終矛盾を一般 hno の完成とは扱わない。

## 2. 小指数・正則素数を除く方向

Lean ソース:

- `DkMath/FLT/FreyHnoSmallIndex.lean`
- `DkMath/FLT/FreyHnoRegularPrime.lean`
- `DkMath/FLT/FreyHnoHardCase.lean`

FLT5 の完成済み終点は正の自然数についての命題だった。非零自然数が正であることを
使って `FermatLastTheoremFor 5` へ接続し、Mathlib の
`fermatLastTheoremFor_iff_int` によって符号付き整数へ移す。
したがって、負の整数の方程式に `natAbs` を無条件に適用するような符号の飛躍はない。

正則素数については既存の
`Kummer.not_int_solution_regular_prime` をそのまま使う。
その入力である非零性、原始性、冪方程式は同じ `Source` のフィールドから供給される。
正則性は明示的に

```lean
Nat.Coprime p (Fintype.card (ClassGroup (𝓞 K)))
```

である。これを仮定した hno は一般 hno と異なる。逆に Source が与えられれば、
標準円分体の類群濃度を `p` が割る。この必要条件は、非正則素数で反例が存在するという
主張ではない。

重要な依存方向は

```text
completed FLT5 / FLT7 / FLT11 / FLT13 / regular-prime FLT
  → no corresponding Source
  → hno for these exponents
```

である。この上位層を、使用した FLT 自身の証明へ戻してはならない。
`evidence/note032-hno-global-core-import-audit.json` は、完成済み FLT と前章の局所終点の
import 閉包に今回の上位層が含まれないこと、および新しい閉包の非循環性を記録する。

向き付け済み反例の入口
`ofCounterexample_hard_case_of_cofixed` は `PrimitiveReduction` と `OrientationTrace` を
結論へ残す。元との共通因子・符号付き置換の証拠を破棄していない。

## 3. Step Three の二アンカー

Lean ソース: `DkMath/Lib/Algebra/MazurStepThreeTwoAnchor.lean`。

実際の Eisenstein 商の有限有理部分群に後で適用できるよう、一般の可換加法群 `G` と
有限部分群 `H` で証明する。周囲の群 `G` の有限性は不要である。

まず specialization `s : G →+ T` が `q` と素な位数の捩れで核自明だとする。
`z ∈ H`, `s z = 0` に対して有限性から `ord z > 0`。位数を

\[
\operatorname{ord}(z)=q^a m,\qquad q\nmid m
\]

と分けると、`q^a • z` は `m` 倍で消え、かつ specialization で消える。
従って prime-to-`q` 単射性から `q^a • z = 0`。
これが `exists_prime_power_nsmul_eq_zero_of_specialization_zero` である。

2進と3進に適用すると

\[
2^a y=0,\qquad 3^b y=0.
\]

元の位数は両方の整数を割る。二冪の gcd は 1 なので位数は 1、すなわち `y=0`。
この二アンカー消滅には `q` 冪捩れ上の単射性はまだ要らない。

最後に別住所の specialization で `s(y+c)=0` とする。`y=0` から `s c=0`。
同じ位数分解によって `c` が `q` 冪で消えることが分かり、今度は `q` 冪捩れ上の
単射性を使って `c=0`。非零 cusp 類 `c ≠ 0` と矛盾する。

この最後の定理は `nonzero_cusp_not_killed_after_two_anchors`。
実際の有限部分群・非零 cusp 類・specialization・二種類の単射性を構成する数学は
仮定として明示されており、ここではまだ Frey 曲線へ適用していない。

## 4. Frobenius と捩れ塔の最後の矛盾

Lean ソース:

- `DkMath/Lib/Algebra/TorsionTowerFrobenius.lean`
- `DkMath/Lib/NumberTheory/EllipticTorsionTowerObstruction.lean`
- `DkMath/FLT/FreyTorsionTowerObstruction.lean`

### 4.1 関係式から scalar absorption へ

`φ` が `G[n]/K` 上で自明に作用すれば、

\[
\varphi y-y\in K,\qquad \varphi^2y-\varphi y\in K.
\]

Cayley–Hamilton 関係

\[
\varphi^2y+\ell y=(\ell+1-N)\varphi y
\]

から

\[
N\varphi y=\ell(\varphi y-y)-(\varphi^2y-\varphi y)\in K.
\]

さらに `N y = N φy - N(φy-y)` なので `N y ∈ K`。
`nsmul_mem_of_frobenius_relation` は、この計算だけに必要な入力を公開する。
`φ` が本当に良還元素数の Frobenius であることは利用側の算術である。

### 4.2 塔から底への降下

`N > 0`, `N=p^t u`, `p ∤ u` と分解する。`p^t ≤ N < p^N` より `t < N`。
任意の `p` 捩れ点 `e` を可除性で `p^t y=e` と持ち上げると、
`p^(t+1)y=0`、従って `p^N y=0`。

scalar absorption から `N y = u e ∈ K`。この点も `p` 捩れなので、塔の降下条件

```lean
∀ x ∈ K, p • x = 0 → x ∈ H
```

によって `u e ∈ H`。`gcd(u,p)=1` の Bézout 係数で `u` を約分して `e ∈ H` を得る。
これを `prime_torsion_mem_of_scalar_absorbs` として証明した。

### 4.3 濃度の矛盾と実点群への接続

全ての `p` 捩れが `H` に入るので、点をそのまま保つ単射 `G[p] → H` ができる。
`#G[p]=p²`, `#H=p` なら `p²≤p`、素数 `p≥2` と矛盾する。
`Nat.card` の無限型での零値を利用せず、非零濃度から有限性を確保している。

楕円曲線では二つの一般群仮定を既存の幾何学で埋めた。

- `card_torsion_sq` が `#E[p]=p²` を供給。
- `multiplication_surjective` が `p^t` 倍による持ち上げを供給。

Frey 固有の終点では底も任意の群ではなく、同じ Source の
`pointSubgroup S.rationalCurve p L`。一次元性から既存 `card_pointSubgroup` が
その濃度 `p` を供給する。作用も既存 `pointAction S.rationalCurve σ` そのものである。

従って残る仮定は、実際の上段 `K`、その `p` 捩れの底への包含、商上の固定性、
実際の Frobenius 関係式である。これらの同時成立を排除する定理は完成したが、
Cofixed からそのデータを構成する大域証明は未実装である。

## 5. 次に埋める数学

```text
Cofixed on the remaining irregular, large, seven branch
  → fixed geometric p-torsion and all 2/3 local inputs              [existing]
  → finite rational Eisenstein quotient, cusp, specialization      [open]
  → two-anchor group-theoretic contradiction pattern               [implemented]
  → exclusion at the other bad primes                             [open application]
  → compatible stable p-power subgroups / extension vanishing      [open]
  → inertia absorption and trivial global quotient action          [open]
  → actual good-prime Frobenius Cayley–Hamilton relation            [open]
  → scalar absorption / p²≤p contradiction on actual Frey points   [implemented]
```

現在の局所情報から、ここにある open の数学を省略する新しい不変量や矛盾は得ていない。
primorial 支持、非正則性、二進分解群外への脱出条件の言い換えを、排除の証明とは扱わない。

## 6. 検証

実行結果、公理依存、禁止構文走査、import 依存の範囲は
`evidence/validation-note032-hno-global-core.txt` と
`evidence/note032-hno-global-core-import-audit.json` に保存する。
回帰では同じ素数を二回使っても非零捩れが消える例を確認し、二アンカーの
互いに素性を落とせないことも明示した。

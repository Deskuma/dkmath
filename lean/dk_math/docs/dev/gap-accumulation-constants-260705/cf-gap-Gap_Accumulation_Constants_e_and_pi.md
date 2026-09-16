# DkMath Design Note: Gap Accumulation Constants e and π

作成日: 2026-07-05
対象: DkMath / Cosmic Formula / Wallis-Cosmic-Petal Bridge
状態: Concept note / implementation-aligned draft

## 0. 目的

本ノートは、DkMath におけるネイピア数 `e` と円周率 `π` を、どちらも

```text
宇宙式 Gap の相対サイズを積み上げた極限定数
```

として比較するための設計メモである。

ただし、本ノートでは過大主張を避ける。

```text
π 側:
  現在の Wallis-Cosmic-Petal Bridge 実装事実に基づく。

e 側:
  既存の宇宙式 Gap 累積の見方を比較軸として置く。
  必要なら別ファイルで Lean 実装状況を確認し、後で補強する。
```

本ノートの主張は、次の形である。

```text
e:
  非対称・直進・自己増殖型 Gap の累積定数

π:
  対称・mirror・閉路型 Gap の累積定数
```

## 1. 背景

通常、`π` は円周率として導入される。

しかし DkMath の現在の研究線では、`π` を円から直接出す前に、次のような順序が見えている。

```text
有限代数構造
  -> 左右対称性
  -> mirror product
  -> Wallis product
  -> π/2
  -> 境界スケール 2
  -> π
```

このルートでは、円は最初の入力ではない。

円は、後から標準幾何へ接続したときに現れるモデルである。

したがって本ノートでは、次の慎重な表現を採用する。

```text
π は円からしか来ない定数ではない。
DkMath の Wallis-Cosmic 実装では、
π はまず対称 Gap 比率の閉包定数として現れる。
```

## 2. 宇宙式 Gap の基本語彙

DkMath の宇宙式では、構造を次の三つに分けて読む。

```text
Big:
  全体の平方・冪・保存される大域量

Body:
  Gap を除いた本体

Gap:
  Big と Body の差として残る単位・補正・保存核
```

典型形は次である。

```text
Big = Body + Gap
```

平方の場合は、

```text
(x+u)^2 = x(x+2u) + u^2
```

ここで `u^2` が Gap である。

Wallis-Cosmic 側では、奇数境界に特化した単位 Gap が現れる。

```text
(P+1)^2 = P(P+2) + 1
```

ここでは、

```text
Big  = (P+1)^2
Body = P(P+2)
Gap  = 1
```

である。

## 3. π 側: 対称 Gap 比率の累積

Wallis-Cosmic-Petal Bridge の局所核は、奇数 `P` と次の奇数 `P+2` の中央に、偶数 `P+1` があることである。

```text
P      = 2j - 1
P + 1  = 2j
P + 2  = 2j + 1
```

このとき、

```text
(P+1)^2 = P(P+2) + 1
```

したがって Wallis 因子は、

```text
(2j)^2 / ((2j-1)(2j+1))
  = (P+1)^2 / (P(P+2))
  = (P(P+2)+1) / (P(P+2))
  = 1 + 1 / (P(P+2))
```

と読める。

つまり Wallis 積は、

```text
Π_j (1 + 1 / ((2j-1)(2j+1)))
```

という形の、単位 Gap 比率の積である。

ここで重要なのは、Gap がただ直進的に積まれているのではなく、

```text
左奇数境界
中央偶数平方
右奇数境界
```

という左右対称構造の中に現れることである。

## 4. mirror product の意味

現在の Wallis bridge では、逆中央二項比を `C_m`、mirror product を `M_m`、有限 Wallis 積を `W_m` と見る。

```text
C_m = 4^m / choose(2m, m)

M_m = Π_{j=1..m} 2j / (2j+1)

W_m = Π_{j=1..m} (2j)^2 / ((2j-1)(2j+1))
```

実装上の中心事実は次である。

```text
C_m * M_m = W_m
```

これは、

```text
片側成長 * mirror 補正 = 閉じた Wallis 積
```

と読める。

さらに、

```text
C_m / M_m = 2m + 1
```

が成り立つ。

これは、片側成長と mirror 側の非対称性が、最後の奇数境界 `2m+1` として残ることを意味する。

この二つを合わせると、

```text
C_m^2 = (2m+1) * W_m
```

を得る。

DkMath 的には、これは次のように読める。

```text
片側 Petal 成長の平方
  = 境界スケール * 対称 Gap 積
```

## 5. π が現れる場所

Wallis 極限は、

```text
W_m -> π / 2
```

である。

有限恒等式

```text
C_m^2 = (2m+1) * W_m
```

を `m` で割ると、

```text
C_m^2 / m = ((2m+1) / m) * W_m
```

ここで、

```text
(2m+1) / m -> 2
W_m -> π / 2
```

なので、

```text
C_m^2 / m -> 2 * (π / 2) = π
```

したがって、現在の Wallis-Cosmic 実装から見た `π` の発生原理は次である。

```text
π/2:
  対称 Gap 比率の Wallis 閉包

2:
  mirror 非対称性として残る線形境界スケール

π:
  境界スケール 2 と Wallis 閉包 π/2 の合成
```

一言で言えば、

```text
π = 境界スケール 2 × 対称 Gap 積閉包 π/2
```

である。

## 6. e 側: 直進 Gap 比率の累積

一方、ネイピア数 `e` は、DkMath 的には次の型として読む。

```text
同じ向きへ進む相対 Gap を、直進的に積み上げた極限
```

標準的な形は、

```text
(1 + 1/n)^n -> e
```

である。

ここで各因子は、

```text
1 + relative_gap
```

という形を持つ。

Wallis-Cosmic 側の `π` と違って、`e` 側では mirror 補正や左右境界の閉じは主役ではない。

主役は、

```text
同じ向き
同じ型
自己増殖
直進的累積
```

である。

したがって、比較軸としては次のように置ける。

```text
e:
  Gap の相対サイズを一方向に積む。

π:
  Gap の相対サイズを左右対称な比率として積む。
```

## 7. 統一原理

本ノートの中心命題は次である。

```text
e と π は、どちらも Gap の相対累積定数である。
違いは Gap の積み上げ形状にある。
```

分類すると、

```text
e:
  非対称
  直進
  自己増殖
  one-sided accumulation
  open growth

π:
  対称
  mirror
  境界補正
  two-sided accumulation
  closed growth
```

より DkMath 的には、

```text
e = 直進 Gap 累積の閉包定数
π = 対称 Gap 累積の閉包定数
```

と表現できる。

## 8. 円との関係

本ノートは「π は円ではない」と断言するものではない。

より正確には、次の立場を取る。

```text
標準数学:
  π は円周率として定義されることが多い。

DkMath / Wallis-Cosmic route:
  π は対称 Gap 積の閉包から先に現れる。

幾何的解釈:
  円は、その対称性構造が連続幾何へ写った姿である。
```

したがって、研究上の安全な表現は次である。

```text
π は円からしか来ない定数ではない。
少なくとも Wallis-Cosmic route では、
π は円を前提にせず、対称 Gap 比率の閉包として現れる。
```

## 9. Lean 実装との対応

現在の Wallis-Cosmic-Petal Bridge では、少なくとも次の対応がある。

```text
cosmic_square_odd_bridge_Q:
  (P+1)^2 = P(P+2) + 1 の局所核

wallisFactorQ_eq_cosmicFactorQ:
  Wallis 因子が Cosmic Gap 比率であること

wallisFactorQ_eq_one_add_inv_body:
  factor = 1 + 1 / Body

centralRatioQ_mul_mirror_eq_wallisPartialQ:
  片側成長 * mirror = Wallis 部分積

centralRatioQ_mul_mirror_eq_cosmicPartialQ:
  片側成長 * mirror = Cosmic Gap 部分積

centralRatioQ_div_mirrorOddRatioPartialQ_eq_two_mul_add_one:
  mirror 非対称性が 2m+1 として残ること

centralRatioQ_sq_eq_odd_mul_wallisPartialQ:
  C_m^2 = (2m+1) W_m

centralRatioQ_sq_eq_odd_mul_cosmicPartialQ:
  C_m^2 = (2m+1) cosmicPartialQ(m)

tendsto_cosmicPartialQ_pi_div_two:
  Cosmic Gap 部分積が π/2 へ収束すること

tendsto_real_centralRatioQ_sq_div_nat_pi:
  C_m^2 / m が π へ収束すること
```

## 10. 過大主張を避けるための注意

本ノートでは、次を主張しない。

```text
DkMath が Real.pi を完全に独立構成した。
Wallis 極限そのものを DkMath 内部から証明した。
円周率の標準幾何的意味を置き換えた。
e 側の全定理が Wallis-Cosmic 側と同じ実装水準で完成している。
```

現時点で言えるのは次である。

```text
Wallis-Cosmic-Petal Bridge では、
π が円ではなく対称 Gap 積の側から現れる構造が実装上確認できる。

この構造は、e を直進 Gap 累積として読む見方と並べることで、
Gap accumulation constants という統一語彙を与える。
```

## 11. 今後の実装候補

### 11.1. GapAccumulationConstants ノート

候補ファイル:

```text
docs/dev/gap-accumulation-constants/e-pi-unification-note-260705.md
```

目的:

```text
e と π を Gap 累積定数として比較する。
π 側は Wallis-Cosmic 実装事実に基づく。
e 側は既存議論・今後の実装候補として整理する。
```

### 11.2. e 側の実装確認

候補調査:

```text
DkMath.Analysis
DkMath.Exp
DkMath.Cosmic
DkMath.GN
DkMath.DkReal
```

確認したい theorem:

```text
(1 + 1/n)^n 型の極限
Gap 比率積としての定式化
直進型 Gap accumulation の命名
```

### 11.3. π 側の presentation theorem

候補 alias:

```text
tendsto_cosmicGapProduct_pi_div_two
tendsto_symmetricGapProduct_pi_div_two
tendsto_centralRatioQ_sq_div_nat_pi_via_symmetric_gap
```

### 11.4. 将来の統一定義

将来的には、次のような抽象語彙を検討できる。

```text
GapFactor:
  1 + gap / body 型の因子

GapProduct:
  GapFactor の有限積

GapAccumulation:
  GapProduct の極限

StraightGapAccumulation:
  one-sided / direct / exponential 型

MirrorGapAccumulation:
  two-sided / symmetric / Wallis 型
```

この抽象化により、

```text
StraightGapAccumulation -> e
MirrorGapAccumulation   -> π
```

という橋定理を目標にできる。

## 12. 短い標語

```text
e は、まっすぐ積まれた Gap の定数。
π は、対称に閉じた Gap の定数。
```

または、

```text
e:
  open growth constant

π:
  closed symmetry constant
```

DkMath 語彙では、

```text
e:
  直進 Gap 累積定数

π:
  mirror Gap 閉包定数
```

## 13. 現時点の結論

DkMath の現在の視界では、`e` と `π` は別種の神秘定数ではなく、どちらも

```text
Gap の相対サイズをどう積み上げるか
```

によって現れる極限定数として並べられる。

違いは、値そのものではなく、積み上げ形状である。

```text
e:
  一方向に開いていく Gap の累積

π:
  左右対称に閉じていく Gap の累積
```

この比較により、`π` は円の影としてだけでなく、

```text
対称性が閉じたときに残る定数
```

として扱える。

これは、DkMath における pre-geometric π program と Wallis-Cosmic-Petal Bridge をつなぐ、中核的な設計原理である。

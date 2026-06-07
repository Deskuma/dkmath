# DHNT から DAS/Sequence への再解釈メモ

## 目的

このメモは、`dynamic_arithmetic_sequence` を Lean で単に移植するのではなく、
`DkMath.Sequence` / `DkMath.KUS` / `DkMath.PowerSwap` へ分解して再構築した理由を残す。

実装メモではなく、設計の入口を説明する文書である。

## 発端: DHNT の異単位調和演算

発端は DHNT、すなわち「動的調和数論」という視点にある。

DHNT では、数量を単なる実数として扱うのではなく、

```text
係数 x
単位 u
実体値 x * u
```

のように、係数と単位を分けて見る。

このとき異なる単位を持つ数量は、そのままでは足せない。まず共通単位へ換算し、
その上で演算する必要がある。Lean 側では、この考え方が
`DkMath.DHNT.Qty.convert` や `DkMath.DHNT.Qty.addVia` に現れている。

```text
(u, x) --convert--> (w, x * u / w)
```

ここで重要なのは、演算の前に「単位を揃える」という点である。

## 指数対数法則と単位の分岐

DHNT の背景には、指数・対数法則によって異なる単位を束ねる、という見方がある。

オイラーの等式

```text
e^{iπ} = -1
```

は、指数関数を通じて実軸と複素方向の情報が接続される典型例である。
この視点では、単位は一つに固定されたものではなく、指数・対数を通じて分岐し、
複素数の世界で束ね直される対象になる。

この発想は、宇宙式の基本恒等式ともつながる。

```text
f(x) = (x + 1)^2 - x * (x + 2) = 1
```

これは単なる展開公式ではなく、二次元的な幾何構造から差分 `1` が取り出される形である。
単位付きにすると、

```text
(x + u)^2 - x * (x + 2u) = u^2
```

となり、差分は単位 `u` の二乗として閉じる。

つまり、DHNT の「異単位を揃えて演算する」という考え方と、
宇宙式の「多次元構造から単位差分を取り出す」という考え方は、
どちらも「見えている数値の背後に単位・構造・変換がある」と読む点でつながっている。

## DAS の最初の形

Python 側の DAS は、もともと次の形だった。

```text
a_i = a + ln(e^k) * i * d
```

しかし数学的には、

```text
ln(e^k) = k
```

なので、Lean ではこれを指数・対数で直接書かず、

```text
a_i = a + i * (d * k)
```

として正規化した。

ここで `d * k` は「公差 d をスケール k によって変形したもの」と読む。
この段階では `d` と `k` は同じ係数宇宙 `C` に属しており、
Lean では `Mul C` によって抽象化されている。

## なぜ Sequence へ切り出したか

DAS を数値リストとして見ると、

```text
1, 3, 5, 7, ...
```

のような表示列に見える。

しかし Lean で扱いたい本体は、表示された数値ではなく、

```text
origin
step
term i = origin + i * step
```

という生成原理である。

このため、DAS を `DkMath.DHNT` の局所的なデモに閉じ込めず、
`DkMath.Sequence` へ切り出した。

現在の実装では、次の層を持つ。

```text
DkMath.Sequence.Closed
  term : ℕ → A

DkMath.Sequence.AdditiveGenerator
  origin : C
  step   : C
  term i = origin + i * step

DkMath.Sequence.Recurrence
  seed : A
  next : ℕ → A → A

DkMath.Sequence.StateRecurrence
  hidden state
  observe
```

DAS はその中の `AdditiveGenerator` の特殊化である。

```text
dynamicGenerator a d k
  origin = a
  step   = d * k
```

これにより、DAS は「特殊な数列」ではなく、
「生成器の一例」として扱える。

## KUS への持ち上げ

KUS では、係数と support/blueprint を分離する。

```text
GKUS C U Blueprint
  coeff
  unit
  blueprint
```

DAS を KUS に持ち上げると、

```text
support は固定
coeff だけが DAS の規則で進む
```

という軌道になる。

つまり、数列は単なる値の列ではなく、

```text
構造を持った状態が、同じ support 上で係数だけを変化させる orbit
```

として読める。

この設計により、係数が 0 になっても support は消えない。
これは KUS の zero tracking と相性が良い。

## PowerSwap との関係

PowerSwap は、現時点では主に

```text
a^b = b^a
```

および

```text
A = a^t → A^m = a^(t*m)
```

を扱う。

ここには「別の宇宙へ正規化する」という見方がある。

例えば、ある積構造

```text
x * y
```

を、一度

```text
z^n
```

という冪正規形へ送る。

これは「積の宇宙」から「冪の宇宙」への変換である。
このため `DkMath.PowerSwap.NormalForm` では、

```text
PowNormalForm
  base
  exponent
  eval = base ^ exponent
```

という小さな正規形を導入した。

将来的には、正規化された `exponent` 側を `Sequence` の軸として動かすことで、

```text
積を作る
冪正規形へ送る
指数軸上で並べる
必要なら KUS support を保持する
```

という道が開く。

## 現時点での境界

この文書は、次の方針を明確にするためのものでもある。

現時点で実装済み:

- `DkMath.Sequence`: 数列生成原理の抽象核
- `DkMath.DHNT.DynamicArithmeticSequence`: DHNT 側の薄い DAS bridge
- `DkMath.KUS.DynamicArithmeticSequence`: support を固定した GKUS 版 DAS
- `DkMath.PowerSwap.NormalForm`: 冪正規形の最小核

まだ入れないもの:

- `SMul` による外部スケール一般化
- 環・群・体としての sequence 演算体系
- PowerSwap と Sequence の本格統合
- 複素単位分岐の完全形式化

これらは必要になった段階で載せる。
いまは、DAS から見えた「数列とは生成原理である」という核を、
Lean 上で壊れにくい形に切り出すことを優先する。

## 実装対応表

| 概念 | Lean module |
|---|---|
| 異単位数量と換算 | `DkMath.DHNT.DHNT_Base` |
| DAS の DHNT 入口 | `DkMath.DHNT.DynamicArithmeticSequence` |
| 数列生成器 | `DkMath.Sequence.Generator` |
| DAS / 可変公差列 | `DkMath.Sequence.Arithmetic` |
| Fibonacci 型の状態再帰 | `DkMath.Sequence.Fibonacci` |
| support 保持付き DAS | `DkMath.KUS.DynamicArithmeticSequence` |
| KUS/DHNT bridge | `DkMath.KUS.Bridge` |
| PowerSwap 交換則 | `DkMath.PowerSwap.Exchange` |
| 冪正規形 | `DkMath.PowerSwap.NormalForm` |


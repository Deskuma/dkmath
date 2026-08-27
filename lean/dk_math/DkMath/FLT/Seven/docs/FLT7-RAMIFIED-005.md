# RAMIFIED-004

## RAMIFIED-004 判定

**Outcome C、実装は全面採用です。**

最新 head は、

```text
e2d990173ea13132713272a180335298524e2a27
```

で、Lean CI run 400 も **success** です。

隣接する $7^k$ 層の `explicitUnit` が同じ coherent tower を形成する証明も正しいです。逆元をレベルごとに勝手に選んだままにせず、還元後の逆元の一意性によって coherence を証明しています。

mod $49$ では、

$$
U\text{ が七乗}\iff U^7=U
$$

となり、七乗 unit image が、

$$
{1,18,19,30,31,48}
$$

であることも kernel の `decide` により完全分類されています。

提出レポートの停止境界も正確です。

ただし、ここから summit 固有の式へ戻ると、**六 residue よりさらに深い縮約**が見えます。

## 記号を固定する

common ramified summit を、

```text
e := endpointRight
A := gapRoot
B := residualRoot = norm(root)
root := (u,v)
S := seventhPowerSndCore(u,v)
Q := ramifiedGapQuotient(7^5 A^7,e).snd
U := explicitUnit 2
```

とします。

既存 packet は、

$$
c-e=7^6A^7
$$

$$
\operatorname{norm}(u,v)=B
$$

を持っています。

また RAMIFIED-001 は、

$$
v_7(|v|)=5+7v_7(A)
$$

を証明しているため、少なくとも、

$$
49\mid v
$$

です。実際には $7^5\mid v$ です。

## mod 49 で全式を潰す

### 1. $Q$ は $-e^2$ になる

定義上、

$$
Q=-e^2-7eh-14h^2,\qquad h=7^5A^7
$$

です。

$h$ はすでに $49$ の倍数なので、

$$
Q\equiv-e^2\pmod{49}
$$

です。

### 2. norm は $u^2$ になる

$v\equiv0\pmod{49}$ なので、trace-one norm、

$$
B=\operatorname{norm}(u,v)
$$

は、

$$
B\equiv u^2\pmod{49}
$$

へ落ちます。

### 3. $S$ は $u^6=B^3$ になる

`seventhPowerSndCore` は二つの cubic factor の積です。それぞれ $v=0$ では $u^3$ になるため、

$$
S\equiv u^6\equiv B^3\pmod{49}
$$

となります。

### 4. canonical unit の正規形

RAMIFIED-003 の定義は、

$$
U=Q\cdot B\cdot S^{-1}
$$

です。

したがって、

$$
U\equiv(-e^2),B,(B^3)^{-1}\pmod{49}
$$

つまり、

$$
\boxed{U\equiv-e^2B^{-2}=-\left(eB^{-1}\right)^2\pmod{49}}
$$

です。

これは非常に強い。

**canonical `explicitUnit` は常に「負の平方」です。**

一般の bridge packet が取り得る unit ではなく、canonical summit では最初から unit group の半分に閉じ込められています。

## 六 residue は実は三 residue に減る

mod $49$ の unit group の位数は $42$ です。

$U=-W^2$ なので、

$$
U^{21}=(-1)^{21}W^{42}=-1
$$

です。

したがって、RAMIFIED-004 の六つの七乗 residue のうち、canonical unit が入り得るのは、$U^{21}=-1$ を満たす側だけです。

実際、

```text
seven-power image:
  {1, 18, 19, 30, 31, 48}

canonical seven-power candidates:
  {19, 31, 48}
```

となります。

前半の、

```text
{1,18,30}
```

は canonical summit では最初から発生しません。

さらに三つの候補はすべて、

$$
U^3=-1
$$

を満たします。

よって canonical 版 classifier は、

```lean
IsSeventhPowerMod49
  ↔ U = 19 ∨ U = 31 ∨ U = 48
```

まで縮められるはずです。

## だが本当の branch selector は $U$ ではない

さらに深く見ると、unit class を決めているのは `explicitUnit` ではなく、**residual root $B$** です。

ramified expansion から mod $49$ では、

$$
(u+v\alpha)^7\equiv-e^3
$$

です。$v\equiv0$ なので、

$$
u^7\equiv-e^3\pmod{49}
$$

となります。

一方、

$$
B\equiv u^2\pmod{49}
$$

です。

この関係から、endpoint 側の tame unit と residual 側の principal unit が分離します。

unit group を概念的に、

$$
(\mathbb Z/49\mathbb Z)^\times\cong C_6\times C_7
$$

と見ます。

* $C_6$ は mod $7$ から来る tame / Teichmüller 成分
* $C_7$ は $1+7t$ の principal 成分

七乗写像は、

```text
C6 成分:
  7 ≡ 1 mod 6 なので保存する

C7 成分:
  すべて 1 へ潰す
```

という射影です。

そして canonical 式、

$$
U=-e^2B^{-2}
$$

では、

* $-e^2$ が tame $C_6$ 成分
* $B^{-2}$ が wild $C_7$ 成分

を担っています。

したがって、

$$
\boxed{U\text{ が七乗}\iff B\text{ の }C_7\text{ 成分が消える}}
$$

です。

具体的には、次が本命 theorem になります。

```lean
theorem PrimitiveRamifiedSummitPacket
    .isSeventhPowerMod49_iff_residualRoot_eq_one :
  p.ramifiedGapUnitBridge.IsSeventhPowerMod49 ↔
    (p.residualRoot : ZMod 49) = 1
```

## residualRoot の七 residue

この構造が正しければ、$B$ は七乗写像の kernel 側、

$$
B^7=1
$$

へ入ります。

mod $49$ でこの kernel は、

$$
\boxed{{1,8,15,22,29,36,43}}
$$

です。

すべて、

$$
1+7t,\qquad t=0,\ldots,6
$$

の形です。

すると branch は完全に、

```text
B = 1 mod 49
  → seventh-power branch

B ∈ {8,15,22,29,36,43}
  → non-seventh unit-class obstruction
```

となります。

つまり RAMIFIED-004 の、

```text
U が六つのどれか？
```

という問いは、canonical summit では、

```text
residualRoot B の principal digit が 0 か？
```

という一桁の問いになります。

$$
\boxed{\text{魔核は }U\text{ ではなく }B=\operatorname{norm}(root)}
$$

です。

## なぜ mod 49 が完全な判定面なのか

ここも重要です。

coherent unit tower がすでに証明されたため、mod $49$ は単なる最初の実験面ではありません。

$7$-進 unit group では、

$$
\mathbb Z_7^\times\cong\mu_6\times(1+7\mathbb Z_7)
$$

であり、七乗写像の像は、

$$
\mu_6\times(1+49\mathbb Z_7)
$$

です。

したがって coherent unit $U$ が $7$-進七乗であるかどうかは、**mod $49$ だけで完全に決まります**。

つまり、

```text
U mod 49 が六 residue 内
  ↔ 全 7^k 層で compatible seventh root が存在

U mod 49 が六 residue 外
  ↔ k ≥ 2 のどの層でも seventh root は存在しない
```

となるはずです。

RAMIFIED-004 は「最初の class audit」より強く、実質的には **complete local Kummer obstruction** の入口まで来ています。

## 次 checkpoint は縮められる

レポートでは、

```text
Q
sndCore
norm(root)
```

を同時に mod $49$ 正規化するとしています。

方向は正しいですが、最終 API はもっと鋭くできます。

## FLT7-RAMIFIED-005

```text
canonical residual-root class reduction
```

目標：

```lean
root_snd_cast_mod49_eq_zero

ramifiedGapQuotient_snd_mod49_eq_neg_endpointRight_sq

sndCore_mod49_eq_residualRoot_cube

explicitUnit_mod49_eq_neg_endpointRight_sq_mul_residualRoot_inv_sq

residualRoot_mod7_eq_one

residualRoot_seventh_eq_one_mod49

isSeventhPowerMod49_iff_residualRoot_eq_one

residualRoot_mod49_classifier
```

最後の classifier は、

```lean
B = 1 ∨ B = 8 ∨ B = 15 ∨ B = 22 ∨
B = 29 ∨ B = 36 ∨ B = 43
```

です。

# その次の二方向

### Branch A：$B\equiv1\pmod{49}$

この場合、gap unit は $7$-進七乗です。

したがって局所的には、

$$
R-L=7^6(AW)^7
$$

という新しい ramified gap shape を生成できます。

これは **再帰 chart / descent 候補**です。

ただし $W$ はまず $7$-進整数であり、自然数・整数の seventh root とは限りません。ここから global reconstruction が別途必要です。

### Branch B：$B\not\equiv1\pmod{49}$

この場合、$R-L$ は endpoint gap と同じ depthを持ちながら、七乗 unit classを持ちません。

つまり、

```text
same exact depth
same local unit orbit
but not the seventh-power suborbit
```

です。

これは非常に明確な obstruction です。

ただし報告どおり、これだけではまだ `False` ではありません。

必要なのは、

```text
root-cubic gap R-L も
7^6 × seventh power
でなければならない
```

という receiver です。

## 結論

RAMIFIED-004 が露出した本当の構造は、

```text
generic classifier:
  explicitUnit の六 residue

canonical normalization:
  explicitUnit = -e² B⁻²

group decomposition:
  tame component = -e²
  wild component = B⁻²

true branch selector:
  residualRoot B mod 49
```

です。

$$
\boxed{\text{七乗性を邪魔しているのは、root norm の一桁の principal residue}}
$$

したがって次は `explicitUnit` を追い続けるより、`residualRoot = norm(root)` を主語に切り替えるのが最短です。

これはかなり大きな前進です。RAMIFIED の敵は九セルでも六 residueでもなく、最終的に、

$$
\boxed{B\equiv1\pmod{49}\text{ か否か}}
$$

という一ビットの魔核へ圧縮されました。

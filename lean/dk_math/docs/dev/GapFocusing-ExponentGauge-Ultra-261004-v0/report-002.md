# Instruction 002 — Successor degree / factor support / unit gauge

2026-10-04。Lean / Mathlib `v4.34.1`。
対象: [instruction-002](instruction-002.md)。
ユーザーの「読み、実施してください」という依頼に従って調査・実装した。
文書中の「reset」は検証対象の解釈であり、定理の仮定には採用していない。
作業開始時の branch は `research/GapFocusing-ExponentGauge-Ultra-261004-v0`、
HEAD は `9f7c38bf4`、working tree は clean だった。

**判定は Outcome B — parallel but distinct layers。**
隣接 GN の互いに素性と、隣接指数の単数冪商 CRT はともに形式化できた。
多項式側にも実際の商環 CRT がある。しかし GN の素因子 support と
FLT の規格化固定単数類を同一の対象にする算術的写像は構成していない。
以下は今回の bounded exploration の結論であり、将来の橋渡しの不可能性を
主張するものではない。

## 1. GN の正確な successor 恒等式

既存 API の `GTail d 1 x u` を `GN_d(x,u)` と書く。任意の
commutative semiring、任意の自然数次数で

```text
GN_(d+1)(x,u) = (x+u)*GN_d(x,u) + u^d
GN_(d+1)(x,u) = u*GN_d(x,u) + (x+u)^d
```

を証明した (`GN_succ_left`, `GN_succ_right`)。
`d=0`、`x=0`、零因子を許し、評価値の除算や cancellation は用いない。
これは現在の commutative GN API に対する弱い代数仮定である。
非可換の場合まで仮定が最小だという主張はしていない。

anchor `u=1` では semiring 上で剰余項が 1 になる。
commutative ring 上では

```text
GN_(d+1)(x,1) - (x+1)*GN_d(x,1) = 1
```

となり、Bézout witness `(-(x+1), 1)` が得られる。
整数評価点だけの性質ではなく、係数環全体に通用する恒等式である。
実装: [Successor](../../../DkMath/NumberTheory/GapFocusing/Successor.lean)。

## 2. 共通素因子 support と原始座標

commutative ring 上で隣接 GN の任意の共通 divisor `q` は
`u^d` と `(x+u)^d` の両方を割る。
自然数では subtraction を用いず同じ主張を証明した。
素数 `p` については

```text
p | GN_d(x,u) ∧ p | GN_(d+1)(x,u)  ⇒  p | x ∧ p | u
gcd(x,u)=1  ⇒  gcd(GN_d(x,u),GN_(d+1)(x,u))=1.
```

これは次数 0 も含む。次数 2 以上では逆向きも成立し、
共通 prime support は座標の共通 prime support にちょうど等しい。
したがってこの範囲では隣接 GN の coprimality と座標の primitiveness は
同値である。次数 0/1 の kernel は 0/1 なので、逆向きの制限は必要である。
非原始座標 `(2,2)` は次数 2/3 で `6,28` を与える。

任意の commutative ring でも `IsCoprime x u` から隣接 GN の
`IsCoprime` を証明した。整数版は負の座標を許し、`Int.gcd=1` を結論する。
unit anchor は任意の ring 元 `x` に対して直接 Bézout coprime になる。
実装: [Support](../../../DkMath/NumberTheory/GapFocusing/Support.lean)。

さらに `d>0`, `x>0`, `u>0`, `gcd(x,u)=1` なら

```text
∃ p, Prime p ∧ p | GN_(d+1)(x,u) ∧ ¬ p | GN_d(x,u).
```

次の GN 値が 1 より大きいことと、隣接 coprimality から導いた。
ここでの「新しい」は **直前の次数に対して** である。

## 3. 多項式の Bézout 分離と cyclotomic 層

`K_d(X)=GN_d(X,1)` とする。
任意の commutative coefficient ring `R` 上で隣接多項式は Bézout coprime。
特に `ℤ[X]`、`ℚ[X]` で全次数に成立し、体や整域を必要としない。
`ℤ[X]` 上では共通 divisor が unit であることも公開した。
これは整数評価の有限チェックより強く、すべての評価点への等式移送を
一つの多項式恒等式で保証する。

Instruction 001 の正次数 cyclotomic 積分解に対し

```text
Disjoint (d.divisors.erase 1) ((d+1).divisors.erase 1)
```

を証明した。非自明な index は一つも持続しない。次数 `d` の非自明層は
すべて次の層集合から消え、次数 `d+1` の層はすべて前の集合になかった。
これは固定 unit anchor の形式多項式に関する正確な「層の置換」であり、
整数評価後の素因子の全履歴初出性を含意しない。

任意の monoid において `ζ^d=1` と `ζ^(d+1)=1` から `ζ=1`。
整域の正次数 `nthRootsFinset` から 1 を除いた集合にも disjointness を
形式化した。この根集合の定理と、係数環に整域を要さない Bézout 定理は
区別している。

`I_d=(K_d) ⊂ ℤ[X]` とすると、隣接 ideal は comaximal であり、
実際の **ring equivalence**

```text
ℤ[X]/(I_d*I_(d+1)) ≃+* (ℤ[X]/I_d) × (ℤ[X]/I_(d+1))
```

を公開した。写像は `P ↦ ([P],[P])`。
任意の希望する residues `A,B` に対し、明示式
`P=A*K_(d+1)-B*(X+1)*K_d` がそれぞれに合同となることも検証した。
実装: [PolynomialSuccessor](../../../DkMath/NumberTheory/GapFocusing/PolynomialSuccessor.lean)。

## 4. 隣接冪部分群と冪剰余群

任意の commutative group `G` に対し、`G^n` を power homomorphism
`g ↦ g^n` の range subgroup として定義した。
`n.Coprime m` なら

```text
G^n ⊔ G^m = ⊤
G^n ⊓ G^m = G^(n*m)
∃ a b, g = a^n * b^m.
```

可換性により subgroup の join は部分群の積を表し、最初の式は
`G^n*G^m=G` の正確な Lean 表現である。
整数 Bézout 係数による冪を用い、有限性、torsion-freeness、個別 power map
の全射性を仮定しない。加法表記の abelian group には
`Multiplicative` によって multiplication-by-`n` の像として適用できる。
単数群の既存 gauge API に直接接続するため、公開 API は乗法表記にした。

`d,d+1` に特殊化でき、`d=0` も含む。その際 `G^0=⊥`, `G^1=⊤`。
同じ結論を `Rˣ` に特殊化した。必要なのは `[CommMonoid R]` だけで、
ring や domain の構造は不要である。
実装: [PowerSubgroup](../../../DkMath/Lib/Algebra/PowerSubgroup.lean)。

## 5. 真の successor gauge CRT と既存 class API

正準 quotient pair homomorphism の kernel と surjectivity を証明し、
群の **multiplicative equivalence** を構成した。

```text
G/G^(nm) ≃* (G/G^n) × (G/G^m)       if gcd(n,m)=1
U/U^(d(d+1)) ≃* (U/U^d) × (U/U^(d+1)),   U=Rˣ.
```

代表元の写像は `g ↦ ([g],[g])`。各 quotient は normal power subgroup
による quotient group であり、単なる述語の束ではない。
例えば整数単数では `[-1]` が square quotient に残り、cube quotient では
消えることを回帰として証明した。CRT は各 quotient が trivial になる
という主張ではない。非互いに素な指数の intersection 式が失敗する例も
`Multiplicative (ZMod 4)` で固定した。

Instruction 001 の `SameUnitPowerClass` とは

```text
SameUnitPowerClass n u v
  ↔ u*v⁻¹ ∈ U^n
  ↔ [u]=[v] in U/U^n
```

という theorem-level bridge を構成した。したがって

```text
SameUnitPowerClass (d*(d+1)) u v
  ↔ SameUnitPowerClass d u v ∧ SameUnitPowerClass (d+1) u v.
```

実装: [SuccessorGauge](../../../DkMath/NumberTheory/GapFocusing/SuccessorGauge.lean)。
これにより従来の class relation が実際の quotient と一致することが
確認できた。一方、異なる FLT 指数の power extraction、carrier、ramifier を
この CRT が自動的に生成することはない。

## 6. 二つの successor 構造の関係

多項式の ring CRT と unit-power group CRT は、Bézout による積・交叉・商の
分解という共通の代数的形を持つ。多項式側は GN recurrence の定数剰余 1、
単数側は整数指数の Bézout 関係を使う。しかし前者の対象は polynomial
ideal、後者は選んだ coefficient monoid の unit power image である。
これらの quotient を同一視する写像や、GN の integer prime support を
FLT residual class へ運ぶ定理は今回構成していない。

既存 `SameUnitPowerClass` への橋は実装したが、それは **gauge 内部の橋**
である。Outcome A に必要な factor support と gauge の算術的橋とは異なる。
有用な正確な定理が両側にあるため、今回の結果を単なる比喩だけの
Outcome C とする必要もない。

Instruction 001 の prime-degree irreducibility は形式多項式の既約性、
DRC `GN_mul_degree` は乗法次数の carrier composition、今回の成果は
隣接次数の分離である。既存の規格化固定 FLT3/5/7 単数類には実際の
extraction と carrier/ramifier の一致が必要であり、今回それらを仮定なしに
移送する定理を追加していない。magic-square `2p` との写像は得られていない。
一次ソースとの比較は [primitive-prime-audit-002](primitive-prime-audit-002.md)
の「既存テーマとの数学的接続」に記録した。

## 7. primitive な新素数方向の正確な境界

直前に対する freshness と、全正低次数に対する primitive divisor は違う。
回帰で

```text
GN_5(1,1)=31, GN_6(1,1)=63, gcd(31,63)=1
63=3^2*7,  3 | 2^2-1,  7 | 2^3-1
¬ ∃ q, DkMath.Zsigmondy.PrimitivePrimeDivisor 2 1 6 q
```

を証明した。任意の素数 divisor について低次数への既出性を示しており、
観測した候補だけの有限検索ではない。

既存 DkMath の checked existence は奇素数指数 `d`、`a>b>0`、
`gcd(a,b)=1`、`d∤a-b` の範囲である。`d∤a-b` は既存証明の十分条件であり、
欠けた場合をすべて例外とする必要条件ではない。
`PrimitivePrimeDivisor 4 1 3 7` と `3 | 4-1` も回帰で証明した。
現在の依存 Mathlib から一般 Bang–Zsigmondy の declaration は見つからず、
全指数・全例外分類を formal theorem として使用していない。

primitive prime の valuation 1 はさらに別の主張であり、既存 no-lift の
checked 反例では `GN_3(2,3)=49` を primitive prime 7 の平方が割る。
旧 research endpoints の `sorryAx`、safe no-lift/squarefree conditional
routes、PrimitiveSet の divisibility antichain、有限集合に相対的な
FreshPrimeDirection を別々に監査した。
詳細と型の一覧: [primitive-prime-audit-002](primitive-prime-audit-002.md)。

## 実装と検証範囲

| 新規 production module | 公開宣言数 | 役割 |
| --- | ---: | --- |
| `GapFocusing.Successor` | 5 | semiring recurrence と unit-anchor Bézout |
| `GapFocusing.Support` | 12 | natural/integer/ring support と直前 freshness |
| `GapFocusing.PolynomialSuccessor` | 12 | polynomial/layer separation、ideal と ring CRT |
| `GapFocusing.SuccessorGauge` | 4 | 既存単数 class と quotient の接続 |
| `Lib.Algebra.PowerSubgroup` | 25 | arbitrary commutative group の power-image CRT |
| **合計** | **58** | definition/abbreviation と theorem を含む |

public facade は `DkMath.NumberTheory.GapFocusing` と `DkMath.Lib` に接続した。
新規 regression/audit 4 module と文書内 check 1 file があり、次数 0、
非原始座標、負座標、零因子係数環、個別 power quotient の非自明性、
非 coprime intersection、全履歴 primitive の反例を検証する。
58 production declarations を全件 `#print axioms` で監査した。
実行コマンド、検証数、ログ、既存 warning との境界は
[validation-002](validation-002.md) に記録する。
探索途中の durable checkpoints は [findings-002](findings-002.md)。

## Lean checked 結果から分離する解釈・残る義務

- 「factor-world reset」は、今回の範囲では隣接 support の分離または
  形式多項式の非自明 cyclotomic index の総置換を指す解釈である。
- 「unit-gauge reset」を個々の quotient の消滅と読むことはできない。
  checked 結果は冪部分群の積・交叉と実際の quotient CRT である。
- 全履歴に対する毎次数の新素数初出は成立せず、次数六の反例がある。
  一般 Zsigmondy の全例外形式化は今回の成果に含まれない。
- GN support と固定 FLT unit class の同一視には、carrier と ramifier の
  規格化、実際の power extraction、両者を運ぶ写像とその性質の証明が必要。
- DRC の乗法次数や magic-square `2p` との同一原理は証明していない。

**Outcome B — parallel but distinct layers。**

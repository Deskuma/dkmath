# GN-LIB-003b — 平方完成・有限帯の中立核

2026-10-23。ブランチ：`lib/FLT-GN-Completion-261023-v0`。

[Lib.Algebra.SquareCompletion](../../../../DkMath/Lib/Algebra/SquareCompletion.lean) に
一般可換半環の7定理を固定した。
`Gnomon.Algebra` と `Primitive.SquareBody` の旧7定理は、従来の型・全修飾名・carrierを保持し、
Libの式を特殊化するwrapperにした。
新一般核と旧wrapperの双方に `[DkMath.Lib]` と昇格説明を付けた。

今回の検証はユーザー指定に従い、影響する本体モジュールに限定した。
フルビルド、`DkMathTest` のビルド、`lake test` は実行していない。

## 1. 平方完成と帯の合成

任意の可換半環Rとx,u,v∈Rで、一般核は

\[
x^2+u(2x+u)=(x+u)^2,
\]

\[
(u+v)(2x+u+v)=u(2x+u)+v(2(x+u)+v)
\]

を与える。後半の帯の基点はx+uである。
同じ基点xへ帯を二つ置いた式へ、合成則を置き換えない。
減算・約分・整域性・正性は不要であり、負座標を持つ環や正標数の環も含む。

単位厚さでは

\[
x^2+(2x+1)=(x+1)^2=(x^2+2x)+1.
\]

左側は旧Gnomonの「平方＋単位帯」、右側は旧Primitiveの「squareBody＋Gap=1」である。
同じ完成を異なる括り方で読む一般式を供給し、旧carrierの意味は旧モジュールに残す。

## 2. 有限帯と自然数の層数

n∈ℕに対し、係数環Rへ自然数をcastして

\[
n(2x+n)=\sum_{i<n}(2(x+i)+1)
\]

を証明した。帰納法の後続は、移動した基点x+nへ単位帯を一つ加える操作である。
n=0は空和を表す。
係数環の任意の元uを層数として列挙するのではなく、層数と有限和の添字は自然数のまま保持する。
正標数ではcastが単射とは限らないが、恒等式には単射性は不要である。

この式と平方完成から

\[
x^2+\sum_{i<n}(2(x+i)+1)=(x+n)^2,
\quad\sum_{i<n}(2i+1)=n^2
\]

も一般可換半環で得られる。
「奇数」という自然数上の性質や順序、素数性はこの一般式に含めない。

## 3. 新規APIと旧API

一般核のnamespaceは `DkMath.Lib.Algebra`。

| 新規API | 役割・旧接続 |
|---|---|
| `square_add_band` | A20の平方帯を任意の可換半環へ一般化 |
| `square_add_unit_layer` | `Gnomon.square_add_oddGnomon` の一般式 |
| `band_add_thickness` | `Gnomon.squareGnomonBand_add` の合成則 |
| `band_eq_sum_unit_layers` | A21の有限帯を係数環へ一般化。層数はNat |
| `square_add_sum_unit_layers` | 有限帯の和を保った平方完成 |
| `sum_unit_layers_eq_square` | 旧 `sum_oddGnomon_eq_square` と `sum_odd_eq_square` の一般核 |
| `square_body_add_one` | A23のunit squareBodyの端点恒等式 |

```lean
import DkMath.Lib.Algebra.SquareCompletion

example (x u : ℕ) : x ^ 2 + u * (2 * x + u) = (x + u) ^ 2 :=
  DkMath.Lib.Algebra.square_add_band x u
```

旧 `oddGnomon`、`squareGnomonBand`、`squareBody` は移動・改名していない。
旧carrierを参照する素数支持・有限世界の定理はそのまま残した。
`Gnomon.CosmicBridge` も変更せず再ビルドし、
`GTail 2 1 u x = 2*x+u` という既存の座標の向きと接続が保たれることを確認した。

`DkMath.Lib.lean` には新所有者のimportを一度追加した。
この公開登録は静的に確認しており、公開集約モジュール自体のフルビルドはユーザー側の検証範囲である。

## 4. 確認範囲

以下の4本体モジュールをまとめてビルドし、3,115ジョブで成功した。

- `DkMath.Lib.Algebra.SquareCompletion`
- `DkMath.Gnomon.Algebra`
- `DkMath.Gnomon.CosmicBridge`
- `DkMath.NumberTheory.Primitive.SquareBody`

新所有者には零厚さ・零基点・空和・有限帯・負整数など8個の小さな教科書例を含む。
テストライブラリは追加・変更していない。
新所有者の直接依存はMathlibの3モジュールだけで、Gnomon・Primitive・FLTなどの旧carrierをimportしない。
型と公理の確認結果は [validation-gn-lib-003b.txt](evidence/validation-gn-lib-003b.txt)、
一般核・wrapperの対応と保持した型は [gn-lib-003b.json](evidence/gn-lib-003b.json) に記録する。

平方恒等式は完成根や帯の素数性を主張しない。
Legendreの素数存在、hno、一般FLTへの接続は今回追加していない。
次はGN-LIB-003cの二項係数付値の中立化である。

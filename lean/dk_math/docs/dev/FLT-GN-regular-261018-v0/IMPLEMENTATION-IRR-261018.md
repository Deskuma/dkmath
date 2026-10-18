# IRR-001〜005 教科書実装：37次 GN と二種類の冪障害

2026-10-18。NOTE-003 と、ユーザー指定の37次・二方向GN・小冪合成を対象とする。
既存の `RegularDescent.Conditions`、State、FLT11/13 の証明は変更しない。

## 何を比較するか

37次でも任意の可換環で

\[
(x+u)^{37}-u^{37}=x\,GN_{37}(x,u),\qquad
(x+u)^{37}-x^{37}=u\,GN_{37}(u,x)
\]

が成立する。零の座標も許し、x や u による割算は使わない。
`GNPrime37.lean` は既存の `CoreNested`・`GTail` と名前を固定した `GN` を合成する。

大きな冪の演算は

```lean
pow_thirtySeven_small x : x^37 = (((x^2)^2)^3)^3 * x
pow_seven_small x       : x^7 = x^4 * x^2 * x
```

で扱う。`36=2*2*3*3`、最後に x を掛けて37となる。任意の Monoid で有効である。
GN の恒等式を巨大な37次展開で再証明するのではなく、既存の一般恒等式を特殊化した。

## 二項係数にはどの差が現れるか

素数 p、`0<k<p` について、次を**全ての素数に共通の定理**として証明した。

\[
p\mid\binom pk,\qquad p^2\nmid\binom pk.
\]

`k*C(p,k)=p*C(p-1,k-1)` と、pより小さい行の係数の p 互いに素性を用いる。
したがって、11・13・37 の間で、この p 可除性の階数に正則性による差は出ない。
既存の係数内容 API を使い、内部全係数の gcd がそれぞれ11・13・37であることも確認する。

37次の先頭内部係数は`37`、`666=37*18`、`7770=37*210`。
また素数 p に対して有限体では

\[
GN_p(x,u)=x^{p-1}\quad\text{in }\mathbf F_p
\]

となる。局所的な正確可除性 `37∣x,37∤u ⇒ 37∣GN₃₇(x,u),37²∤GN₃₇(x,u)` も証明した。
いずれも類数や正則性の仮定を使わない。
これは「二項係数から作る全ての合成量が正則性を区別できない」という主張ではない。
Bernoulli の再帰のような合成量では、次の違いが現れる。

## Bernoulli 比較：有限計算と類群の判定を区別する

`BernoulliPrime37.lean` は Mathlib の `bernoulli'` の再帰式から0〜34を順に検査する。
生成に用いた有理数候補を公理として採用せず、それぞれを前段の証明から検算する。
二項係数は階乗による式で計算し、Bernoulli 再帰や Pascal 再帰の重複展開を避けた。

証明した結果は次の通り。

- `bernoulli 32 = -7709321041217 / 510`。
- 分子は37で割れ、分母は37で割れない。
- pが素数、`2≤n≤p-3`、nが偶数、pが `bernoulli n` の分子を割る、という有限条件を `BernoulliIrregularPair p n` と定義。
- p=37 では、この条件を満たす n は32だけ。
- p=11、13 では、この条件を満たす n はない。

非正則対の数値的定義・計算の背景は [NIST DLMF 24.19(ii)](https://dlmf.nist.gov/24.19#ii) を参照。
DLMF の対の並びは `(2n,p)`、本実装では `(p,n)` としている。
Bernoulli 数の分子・分母の算術は [DLMF 24.10](https://dlmf.nist.gov/24.10) も参照。

**形式化の境界：** Bernoulli の非正則対と円分体類群の非自明 p-torsion を結ぶ Kummer 判定は追加していない。
37次円分体の類群の37-torsionの証人も、特定の GN 位相が非自明類に属すことも、この有限計算からは導かない。
11・13の類障害の実消滅は、既存の証明済み PID／類数1 provider を使う別の回帰検査で確認した。

## IRR-001：イデアル冪障害

`IdealPowerObstruction R p Q` は

```lean
root     : (Ideal R)⁰
equation : Ideal.span {Q} = (root : Ideal R)^p
```

を保持する。零イデアルを許さないため、実際の類 `ω=ClassGroup.mk0 root` を取れる。
`ω^p=1` は正則性なしに証明できる。
`ω=1` は、同じ root が主イデアルであることと同値。
p≠0 なら、これは `Q=u*b^p` という単元倍の元の冪表示の存在とも同値である。

ここでは二つの冪写像の違いが重要となる。

- **イデアルのモノイド**では、正の冪写像は単射。したがって同じ Q,p のイデアル根とその類は一意。
- **類群**では、非自明 p-torsion があれば冪写像は単射でない。`[I]^p=1` だけから `[I]=1` は言えない。

`HasClassGroupPTorsion R p ↔ ¬ classGroupPTorsionFreeAt R p` も証明した。
類群全体に非自明類があることと、今回の根の類が非自明であることを区別する。

## IRR-002：位相類 packet

`PhaseClassPacket R p ι` は各位相の値と、その値の同じ非零イデアル根を保持する。
位相障害は任意に付けるラベルではなく、その根から計算する。

全位相の類が1であることを局所的に証明できれば、各因子の単元倍 p 乗表示を復元できる。
そのために類群**全体**の p-torsion-free 性を仮定する必要はない。
正則な場合の一律消滅は、この個別判定に対する十分条件として別の補題に置いた。

## IRR-003：実際に証明した輸送と保存則

- 単元倍では同じイデアル根を使え、類障害は変わらない。
- 因子の積は根の積となり、類障害も乗法的に移る。
- 添字の置換・再索引は、同じ位相障害の再索引となる。
- 全因子の積が単元倍 p 乗なら、全障害の積は1になる。

特に仮想 State から生じる GN 剥離商は

\[
\prod_i Q_i=\varepsilon(\lambda^m z)^p
\quad\Longrightarrow\quad\prod_i\omega_i=1
\]

を満たす。この結論に大域的な正則性は不要である。
ただし ωとω⁻¹はともに非自明でも積が1となる。
回帰検査では37-torsionを持つ抽象群でこの相殺を確認するが、円分類群の実際のイデアル類の構成とは主張しない。

GN の三項**加法**関係を、イデアル類の加法関係へ読み替える定理は作っていない。
State 側の `three_term` は元の値の等式として保持し、類への影響には別の橋を要求する。

## IRR-004：必要な単元比の障害

`UnitObstructionPacket` は Q=u*b^p の u と b を保持し、実際の商群
`Rˣ / (Rˣ)^p` に単元障害を記録する。

- 同じ単元 u の類が1であることと、u自身の p 乗根の存在は同値。
- その場合に初めて、Q自身の p 乗根を得る。
- 必要な二つの係数についてだけ、比 u/v の剰余類を観測できる。
- p≠0、Q≠0、整閉性のもとで、根の取り方を変えても残った単元の剰余類は不変。

イデアル障害消滅から unit packet を取り出す補題も、同じ root の生成元であることを保存する。
二つの障害を統一する完全な Selmer 群・完全列は、この実装の対象外である。

## IRR-005：障害を残して止まり、消えたところだけ進む

`ObstructedState P m` は元の `State P (m+1)` と全剥離商の `PhaseClassPacket` を保持する。
`ofState` は類群条件・単元 criterion を要求せず、既存のイデアル冪抽出から実際の根を選ぶ。
元の State の方程式・`IsCoprime x y`・λ非分岐 guard を変更しない。

次の二つの出口を区別する。

1. この族の全イデアル障害が消えた場合、同じ族の元の根とGN三項関係から、深度mの `WeightedObstructedState` を**実際に構成**する。
   分岐深度を取り出す証明は、大域的 torsion-free 性による根抽出を経由しない。
2. その重み付き状態の係数比 u/v の単元障害も消えた場合、既存の `normalize_weighted` に具体的な根を渡し、
   同じ y,z と原始性を保持した `State P m` を得る。

非自明な類を残したままの新しい厳密降下は、今回証明していない。
障害が残る場合には元の State・イデアル根・保存則を観測可能な形で残す。
局所消滅を自動的に仮定した無条件の FLT37 や `no_state` は追加していない。
深度0の State の不存在も主張しない。

`IrregularPrime37` は実際の `CyclotomicField 37 ℚ`・整数環・原始根・分岐剰余体でこの構成を特殊化する。
別途37-torsionの証人が供給された場合には、既存 `Conditions` の類群欄と両立しないことを証明する。
その証人を Bernoulli 計算だけから生成するものではない。

## ファイルと検証

| 段階             | ファイル                                                 |
| ---------------- | -------------------------------------------------------- |
| IRR-001          | `DkMath/Lib/NumberTheory/IdealPowerObstruction.lean`     |
| IRR-002          | `DkMath/Lib/NumberTheory/PhaseClassPacket.lean`          |
| IRR-003          | `DkMath/Lib/NumberTheory/PhaseObstructionTransport.lean` |
| IRR-004          | `DkMath/Lib/NumberTheory/UnitObstructionPacket.lean`     |
| IRR-005          | `DkMath/FLT/Kummer/ObstructedState.lean`                 |
| 37次 GN・Pascal  | `DkMath/Lib/Cosmic/GNPrime37.lean`                       |
| Bernoulli 証明書 | `DkMath/Lib/NumberTheory/BernoulliPrime37.lean`          |
| 37次の実円分体   | `DkMath/FLT/Kummer/IrregularPrime37.lean`                |

`DkMath.Lib` と `DkMath.FLT.Kummer`、ルート `DkMath` から公開する。
回帰検査は `IrregularObstruction`、公理・実証明経路の検査は `IrregularObstructionDependencyAudit` に置く。
後者は72の公開宣言を検査し、主要な実証明グラフでは private な Bernoulli 計算証明も追跡する。
局所根抽出・重み付き輸送のグラフから、既存の大域的な根抽出・Conditions・Kummer criterion・旧降下・完成済みFLTを拒否する。

最終検証結果は [evidence/validation-irr.txt](evidence/validation-irr.txt) に記録した。

統合ビルドは11,482 jobsで成功。ルート import と `DkMathTest.lean` の直接検査も成功した。
72公開宣言と実証明経路の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
8個の追加本体と新規検査に警告はなく、既存の正則契約・State・11/13終点は HEAD とバイト単位で一致する。

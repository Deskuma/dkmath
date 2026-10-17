# FLT7 第一段：GN 一次単元を実三次ノルムへ運ぶ

> 後続の [第二段](SEVEN-CONJUGATE-PHASE.md) で、共役比の解析と単元自身の七乗性を実装した。以下は第一段の範囲を記録する。

2026-10-16。FLT3・FLT5 の GN 接続に続き、FLT7 を段階的に構成する章。
添付の FLT5 検証結果は研究上の提案として読み、一般 FLT の外部証明は導入しない。
今回の終点は **GN 保存パケットの一次単元の相対ノルムが七乗であること**。
FLT7 の矛盾・無限降下・六次単元そのものの七乗性は、今回の結論ではない。

## 1. 二次拡大として六次環を読む

既存の具体的環は

```text
R = SevenRealCubicInt
C = QuadraticAlgebra R (-1) (alpha - 1)
zeta² = (alpha - 1)*zeta - 1
```

である。`alpha` は実三次環の生成元で、`1+zeta+zeta⁻¹` に対応する。
`x = A+B*zeta` の二次ノルムは

\[
N(x)=A^2+(\alpha-1)AB+B^2,
\qquad \operatorname{ofReal}(N(x))=x\,\operatorname{star}(x).
\]

ここで共役は二次代数の `star`。この章ではこれを CM 共役として同定する証明は追加していない。
`relativeNorm` は Mathlib の `QuadraticAlgebra.norm` という乗法的写像である。

## 2. 合同をノルムへ移すと整数は二乗になる

`x=n+7w` を代入して直接展開すると、

\[
N(x)=n^2+7\{n(2\operatorname{re}(w)+(\alpha-1)\operatorname{im}(w))+7N(w)\}.
\]

従って `7 | x-n` から `7 | N(x)-n²` を得る。
合同先を `n` と書かないことが重要である。
`relativeNorm_congruent_integer` は括弧内を割り算の証人として与える有限恒等式の証明。

## 3. 実三次の二成分対数が七乗根を与える

既存の `SevenRealCubicUnitClass` には、実三次単元に対する

\[
\operatorname{projectiveLog}:R^\times\longrightarrow\mathbb F_7^2,
\quad v\in(R^\times)^7\iff\operatorname{projectiveLog}(v)=0
\]

がある。今回、前章の比較テストにあった二命題を production に移した。
`v≡m mod 7` なら非定数の二座標はともに 7 の倍数となり、対数の両成分が零になる。
既存の判定へ入力することで `v=w^7` を得る。追加の単元分類仮定はない。

六次単元 `u` のノルムは単元であり、前節から整数と合同なので、

\[
\boxed{u\equiv n\pmod7\quad\Longrightarrow\quad N(u)=v^7\quad(v\in R^\times)}.
\]

さらに二次代数の恒等式を使い、元の環で

\[
\boxed{u\,\operatorname{star}(u)=\operatorname{ofReal}(v)^7}
\]

を保持する。`relativeNorm_primary_unit_seventh` と `primary_unit_mul_conjugate` が対応する。
これは単元の rank が2であることを障害と呼ぶ段階から、実際に既存の分類を消費する段階への前進である。

## 4. GN の同じ一次単元に適用する

`SevenPrimaryNormBridge` は、既存の整数冪基底写像の単射・全射を

```text
integralEquiv : O(CyclotomicField 7 Q) ≃+* C
```

に束ねる。写像は既存の選ばれた円分生成元を具体的 `zeta` に送る。
`integralEquiv_generator` がその向きを証明する。
ノルムだけで別の元を同一視せず、元そのものをこの同型で運んでからノルムを取る。

`integralRelativeNorm` はこの同型と `relativeNorm` の合成。
`GN_primary_unit_relativeNorm_seventh` は、既存の **同じ**
`RamifiedPrincipalPowerPacket Q` の `Q.primaryUnit hi` を受け取る。
正規化 `ramifiedReduction (Q.generator i)=1` から、既存の
`primaryUnit_congruent_integer` が

\[
7\mid\delta_i-(-u),\qquad \delta_i=Q.\mathrm{primaryUnit}(i)
\]

を供給する。その合同へ新しい定理を適用し、`N(delta_i)=v_i^7` を得る。
FLT 座標の `u=-b` なら合同先は `b`、ノルムの合同先は `b²` となる。
この定理はパケットとその正規化を入力にする。今回それらの無条件な存在定理や一般 Case II の正規化を新たに証明したわけではない。

GN の規約は既存ソースの

\[
(x+u)^p-u^p=x\,GN_p(x,u)
\]

を維持する。引数を交換した別の規約で添付文書の末尾を読むと、整数合同の符号も変わってしまう。

## 5. 何が残ったかを、ノルムの核で見る

テストでは `N(zeta)=N(1)=1` かつ `zeta≠1` を確認した。
ノルムは単射でないため、`N(delta)=v^7` だけで `delta=kappa^7` とは言えない。
また `zeta` は整数と mod 7 で合同ではないことも第二座標から検証した。
合同条件は任意の単元に自動的に成立する条件ではない。

次の段階は以下の順序で進められる。

1. この同型を通した二次共役と円分体の CM 共役を同定し、共役比の有限位数と整数合同を解析する。
2. 共役比が1となる条件を証明する。そうすれば上の積等式が `delta²=eta^7` になる。
3. `delta²=eta^7` から `delta=(delta*eta⁻³)^7` として七乗根を構成する。
4. GN の因子と、現在の `currentLinearCarrier`・固定した分岐因子・単元の対応を、元の等式で示す。
5. 次の内部パケットを構成し、同じ不変条件の保存と反復可能な厳密減少を示す。

1〜5 は今回の定理の結論に含めない。とくに既存の付値 `5→4` は一段の減少であり、反復するパケットの構成を代替しない。
GN の一次単元と現在の carrier の未解析単元も、同じ六次環に属するだけでは同一とは言えない。

## 6. FLT11・FLT13 を見ながら設計する

次表は実装順序を考えるための構造比較である。

| p | 円分次数 p−1 | 実部分の次数 (p−1)/2 | 期待する実単元の独立成分数 (p−3)/2 |
|---|---:|---:|---:|
| 3 | 2 | 1 | 0 |
| 5 | 4 | 2 | 1 |
| 7 | 6 | 3 | 2 |
| 11 | 10 | 5 | 4 |
| 13 | 12 | 6 | 5 |

テストでは `Nat.totient` と右二列の自然数計算を確認した。
**今回 p=11,13 の数体の構成・単元 rank 定理・単元生成系・類群条件を新たに形式化したわけではない。**
右端の列はそれらの指数で単元解析を組み立てる際の見通しであり、
七次の二成分対数を単純に四成分・五成分に増やせば証明が完了するという主張ではない。

再利用できる設計は「整数合同→二次相対ノルムの整数二乗合同→実単元判定→共役比→元の冪」である。
p=11,13 でも相対次数は2なので最初の二次展開と最後の奇数冪の操作は共通化の候補となる。
一方、実部分の単元判定、類群、実際の GN 因子と降下パケットの対応は各段階で証明が必要になる。
まず七次で、ノルムと位相の両方を保存した実例を完成させる。

## 7. 実装と検証

- `DkMath/FLT/Kummer/SevenPrimaryNorm.lean`: 実三次判定の昇格、二次ノルムの合同、単元ノルムの七乗根、共役との積。
- `DkMath/FLT/Kummer/SevenPrimaryNormBridge.lean`: 円分整数環との同型、合同の輸送、同じ GN 一次単元への適用。
- `DkMathTest/FLT/Kummer/SevenPrimaryNorm.lean`: ノルムの核、合同条件の必要性、定理の消費、次数計算、公理 whitelist。
- `DkMathTest/FLT/Kummer/FiveSevenComparison.lean`: production に移した実三次判定の回帰検証。

入口は `DkMath.FLT.Kummer`。実行した検証の範囲と結果は
[evidence/validation-seven-primary-norm.txt](evidence/validation-seven-primary-norm.txt) に記録する。

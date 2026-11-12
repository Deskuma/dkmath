# NOTE-019: 短完全列から全指数のねじれ点位数へ

日付: 2026-10-21。NOTE-019の最初の目標である、全ての正整数指数の無条件な位数公式を実装した。
標数0の体K上の楕円曲線Eについて、代数閉包上の同じ実際の点群で

\[
\boxed{n\ne0\implies |E[n]|=n^2}
\]

を証明した。素数性・互いに素性・外部の位数公式・Weil対を追加入力にしていない。
基礎となるのは、NOTE-018の倍写像全射性と、一般可換群の短完全列

\[
0\longrightarrow G[n]\longrightarrow G[mn]\xrightarrow{[n]}G[m]\longrightarrow0
\]

である。包含と制限倍写像は、既存の点へのガロア作用とも可換する。

## 1. 実装と公開入口

| モジュール | 役割 |
| --- | --- |
| `DkMath.Lib.Algebra.TorsionMultiplication` | 一般可換群の包含・制限倍写像・核と商の同型・短完全列・濃度の乗法性 |
| `DkMath.Lib.NumberTheory.EllipticTorsionAllCard` | 実際の点群への接続、ガロア同変性、全正指数・自然数冪・標準torsionByの位数 |
| `DkMath.FLT.FreyTorsionAllCard` | 同じFrey Sourceの全指数位数、有限短完全列、既存の有限レベルとの接続 |

本体3モジュール285行、教科書docstringを含む。名前付き公開宣言29個。
全新規Leanファイルでimport後に `#print "file: モジュール名"` を置き、
`DkMath.Lib`・`DkMath.FLT`・ルート `DkMath` と、回帰・監査の `DkMathTest` へ配線した。

## 2. 核を保つ二つの実際の写像

一般の可換加法群Gに対して、`Kernel G n` をn倍写像の核として定義する。
`inclusion G m n` はxを同じxのままG[mn]に入れる。
nx=0ならmnx=m(nx)=0なので、この写像は定義でき、点の値を保つため単射である。

`multiply G m n` はG[mn]の点xをnxに送る。
m(nx)=mnx=0なので像はG[m]に入る。この写像の核にはnx=0という条件が記録されるため、
同じxをG[n]へ戻せる。`kernelEquiv` はこの対応を加法同型として固定する。

従って包含の像は制限倍写像の核に一致する。
`exact_pair` はこれをMathlibの `Function.Exact` として公開する。
この単射・核の同定・完全性には、有限性や非零指数の仮定さえ必要ない。

## 3. 全射性と商・核の位数公式

G上のn倍写像が全射であると仮定する。
任意のy∈G[m]を取り、G上でnx=yとなるxを選ぶと、mnx=my=0である。
従ってこのxはG[mn]に入り、制限写像も全射になる。
`short_exact` は単射・完全性・全射性を同じ二つの写像のまままとめる。
ここでG全体のn可除性は十分条件として使っており、一般の群について自動的には仮定していない。

全射な制限写像について第一同型定理から

\[
G[mn]/\ker[n]\simeq G[m]
\]

を得る。核は `kernelEquiv` によりG[n]と同型である。
Mathlibの商と部分群の濃度公式に代入すると

\[
\operatorname{Nat.card}G[mn]
=\operatorname{Nat.card}G[m]\cdot\operatorname{Nat.card}G[n]
\]

が従う。一般の `Nat.card` の等式としては有限性を要求しない。
ただし無限型のNat.cardは0なので、通常の有限群の位数として利用する場合は有限性を確認する。

楕円曲線では、n≠0に対してNOTE-018の `multiplication_surjective` を供給する。
m,nがともに非零ならNOTE-012の `finite_torsion_of_ne_zero` により全て有限であり、
`torsion_finite_short_exact` として中央群の有限性も含めて公開する。
`card_torsion_mul` は右因子n≠0だけを要求する一般のNat.card公式であり、m=0での有限性は主張しない。

## 4. 素数の公式から全ての正整数へ

NOTE-016の `card_torsion_prime_sq` は、正則ファイバーからの下界と既存の上界によって、
全ての素数pについて実際の|E[p]|=p²を証明している。
これと新しい乗法性を `Nat.recOnMul` に入力する。

1. 指数0は、明示的な仮定n≠0と矛盾するので除く。
2. 指数1では既存の `torsion_one_eq_zero` から位数1を得る。
3. 素数pでは既存の幾何学的な位数p²を使う。
4. 積abが非零ならa,bも非零。乗法性と帰納仮定によりa²b²=(ab)²を得る。

この結果が

```lean
card_torsion_sq (n : ℕ) (hn : n ≠ 0) :
  Nat.card (Torsion E n) = n ^ 2
```

である。個別の素数冪公式や、互いに素な因子だけに限定した位数公式を別々に証明する必要はない。
`card_torsion_pow` は任意の非零底nとk≥0について|E[nᵏ]|=n^{2k}を供給する。
`card_standardTorsion_sq` は同じ点を保持する既存の線形同型を通して、標準torsionBy表示へ運ぶ。

## 5. 同じ曲線・同じガロア作用を保つ

楕円曲線側の `torsionInclusion` と `torsionMultiply` は、一般群の写像を
既存の `Points E` と `Torsion E n` に特殊化したもの。
指数の異なる三つの群を、形式的な別の有限群に置き換えていない。

包含は点を変えず、ガロア作用は点の加法を保つので

\[
\iota(\sigma P)=\sigma\iota(P),\qquad
[n](\sigma P)=\sigma([n]P)
\]

も証明できる。異なる指数のZMod加群の間では、まず加法群の短完全列として扱う。
合成数のZMod nを体と見なした次元の議論は行わない。

Frey側は、同じSourceの `rationalCurve_isElliptic` を供給するだけで接続する。
Sourceの指数pと、調べるtorsionの指数nは別々に量化する。
従って実在するSource 2の曲線のE[37²]やE[36]にも適用できる。
`residual_card_sq` で指数を一致させる場合も、素数性ではなくp≠0だけが必要である。
`curve_torsion_card_finite_level` は新しい正確な位数と既存の同じ表現の有限レベルをまとめる。

## 6. 回帰と依存監査

実在するSource 2の(4,3,5)の曲線について、次を検査した。

- |E[1]|=1、|E[4]|=16、|E[36]|=1296。
- |E[37²]|=1874161、37⁰=1の場合と標準torsionByでの|E[4]|=16。
- 互いに素でない6,6について、有限短完全列E[6]→E[36]→E[6]。
- 制限写像の核と商の位数がともに36、包含と倍写像のガロア同変性。
- 右因子0でも組の完全性自体は成立すること。
- 合成数36の正確な位数と有限レベル、任意のSource 37の全指数入口。

加えて一般群ZMod 2を使うと、制限写像G[4]→G[2]の2倍写像は零となり、
標的の非零元1を像に持たない。完全性だけから右側の全射性は出ない、という反例を証明した。

`Note019DependencyAudit` は公開29宣言・回帰17宣言の公理と、14本の型・opaque本体の依存経路を検査する。
核と商の同型、実際の倍写像全射性、素数位数公式、乗法的帰納法、幾何学的有限性、同じSourceを要求する。
全ての検査経路でWeil対データを禁止し、一般群の経路では数論層の宣言も禁止する。
標準論理公理3種だけを許し、外部未移植定理・FLT終点・旧条件付き位数providerへの迂回も禁止する。

実行結果は [検証記録](evidence/validation-note019.txt)、ルートimportの確認コードは
[RootSmokeNOTE019.lean](evidence/RootSmokeNOTE019.lean) に保存した。

## 7. 数学的な到達点と次の境界

今回の全指数位数公式は、標数0の楕円曲線の実際の幾何学的ねじれ点に対する無条件の結果である。
NOTE-018で明示したWeil対データを入力していない。

一方、|E[pᵏ]|=p^{2k}という位数だけでは、ZMod(pᵏ)上の自由加群構造やTate加群の階数を証明したことにはならない。
逆極限・整合的な基底・自由性などの構造定理は今後の課題である。
Weil対の幾何学的存在、円分行列式の無条件化、Frey表現の既約性、Mazur型理論、Artin導手、FLTの終点も別の境界として保持する。

今回、新しい外部ソースの移植は行わず、既存のDkMathの幾何学的CoreとMathlibの一般群・自然数帰納法のAPIを組み合わせた。

## 8. 実行結果

- `lake build DkMath.Lib.Algebra.TorsionMultiplication`: 成功（1244 jobs）。
- `lake build DkMath.Lib.NumberTheory.EllipticTorsionAllCard`: 成功（2249 jobs）。
- `lake build DkMath.FLT.FreyTorsionAllCard`: 成功（3173 jobs）。
- `lake build DkMathTest.FLT.FreyTorsionAllCard`: 成功（3175 jobs）。
- `lake build DkMathTest.FLT.Note019DependencyAudit`: 成功（3176 jobs、29公開宣言・17回帰宣言・14経路）。
- `lake build DkMath DkMath.FLT DkMath.Lib DkMathTest`: 成功（11588 jobs）。
- ルートsmoke、`lake env lean DkMathTest.lean`、マーカー照合、静的検査、`git diff --check`: 成功。

新規5モジュールには警告・エラーなし。別の既存モジュールの歴史的な警告は残るが、
今回の検査対象の公理はpropext・Classical.choice・Quot.soundだけである。

# GN・Kummer から既存 FLT3 の降下へ

2026-10-16。添付の研究提案を数学的な設計案として読み、実際の接続を構成した。
この章の対象は三次での再形式化実験である。一般の正則素数についての
Kummer 単元補題や無限降下を完成したという意味ではない。

## 1. 何を作り直し、何を再利用するか

新しい終点は `DkMath.FLT.Kummer.fermatThree_no_positive_solution_via_GN`。

```lean
(a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ 3 + b ^ 3 ≠ c ^ 3
```

既存の gcd 正規化、mod 9 による向きの選択、整数の冪配分、
Eisenstein 環の Euclidean 構造、三つの座標因子への冪配分、符号選択、
積測度の減少を再利用する。**同じ剥離商 β の三乗抽出**を
GN・円分イデアル・単元合同の経路で作り直す。

既存の完成済み FLT3 定理を結論として呼ぶ方法ではない。
最終段階の強帰納法も新しい降下を用いる。

## 2. ノルム比較から元の環同型へ

中立な補題は [EisensteinCyclotomic.lean](../../../DkMath/Lib/NumberTheory/EisensteinCyclotomic.lean)
に置いた。FLT の仮定を使わず、任意の三次円分体 K と原始根 ζ について

\[
 e:\operatorname{TraceOneInt}(-1)\simeq_{\rm ring}\mathcal O_K,
 \qquad e(r+s\tau)=r+s(1+\zeta)
\]

を構成する。`τ²=τ−1` と `ζ²+ζ+1=0` から `τ ↦ 1+ζ` が環準同型となる。
逆写像は整数冪基底の `PowerBasis.lift` により `ζ ↦ τ²` と指定する。
両合成が恒等写像であることを、片側は座標、片側は冪基底の生成元で証明する。

したがって `e(τ²)=ζ`。元、三乗、単元群の写像を輸送できる。
ノルムが同じだから元を同一視する、という推論は使わない。

既存 Eisenstein 環は Euclidean なので PID である。環同型の全射性で
`𝓞 K` の PID 性を移し、類群の位数が 1 と証明する。
三次のイデアル主イデアル化に要求されていた類数条件は、ここで解消する。

## 3. 第2位相の二つの符号

[ThreeEisensteinBridge.lean](../../../DkMath/FLT/Kummer/ThreeEisensteinBridge.lean)
で `ζ_E=τ²` と定義すると

\[
 \zeta_E^2=-\tau,\qquad
 -(a+\zeta_E^2b)=-a+\tau b,\qquad
 \zeta_E^2-1=-(1+\tau).
\]

GN・イデアル冪抽出・三次 Kummer 単元補題から得た
`a+ζ²b=(ζ²−1)θ³` を環同型の逆で戻す。両方の符号が消えて

\[
 \operatorname{eisensteinCoord}(-a,b)=(1+\tau)\theta_E^3
\]

となる。これは `ζ−1=1+τ` と取り違えることなく証明される。

## 4. 既存パケットの三つの向きを一つにする

添付提案では最初に `3∣c` の向きを扱う案だった。実装では既存パケットの
フィールドだけから全ての向きを統一できる。

`p : SignedThreeAdicPacket a b c` の `α=r+sτ` に対して、
`carrier=s−r`、`N(α)=residual`、`carrier*residual=distinguished³` がある。
したがって恒等式

\[
 (-r)^3+s^3=(s-r)(r^2+rs+s^2)=\mathrm{distinguished}^3
\]

により、符号付きの新しい入力座標 `(-r,s,distinguished)` を得る。
これは降下による次の解ではなく、同じ α の入力表現を変えたもの。
`distinguished` は正で 3 の倍数であり、元の a,b,c のいずれかという来歴も
`SignedThreeAdicOriginPacket` に保持される。

原始性も追加仮定にしない。r,s の gcd は `gcd(carrier,residual)=3` を割る。
gcd=3 なら 9 が `N(α)` を割り、`residual % 9=3` に反するため gcd=1。

こうして、既存パケットから Kummer 側の入力を実際に供給する。

## 5. 同じ剥離商と同じ算術データ

`exists_cube_eq_stripped_beta hζ q` は指定された
`q : EisensteinRamifierStrippedPacket a b c` に対し

\[
 \exists\theta_E,\quad q.\beta=\theta_E^3
\]

を返す。Kummer 側で得た `α=(1+τ)θ_E³` と、q が保存する
`α=(1+τ)β` を比較し、非零の分岐因子を消去する。β を選び直さない。
従来の根 γ と今回の根 θ_E が等しいと主張する必要もない。

q が元々持つ

\[
 \beta.\mathrm{snd}=3A^3,\quad N(\beta)=B^3,\quad 3\nmid B
\]

をそのまま使う。`θ_E=r'+s'τ` と書けば三乗の第二座標から

\[
 r's'(r'+s')=A^3
\]

を得る。ノルムの乗法性と整数上の三乗写像の単射性から
`r'²+r's'+s'²=B` を得る。これが既存降下の必要な二つの入力である。

## 6. 既存の降下を呼べる入口

[ThreeGNDescent.lean](../../../DkMath/FLT/Kummer/ThreeGNDescent.lean)
では従来の `EisensteinExactCubePacket` をセクター `one`、単元 1、
根 θ_E として直接構成する。既存の `beta_eq_cube` やセクター排除は呼ばない。

`gnEisensteinDescentFactorSource` は元の原始解から origin、同じ packet に属する
split、stripped、GN の根を順に構成する。`splitWithPacket.2` により元の
distinguished との対応を明示的に渡す。

既存 [PrimitiveCubicDescent.lean](../../../DkMath/FLT/Three/PrimitiveCubicDescent.lean)
から因子を受け取る入口 `primitiveCubicStrictDescent_of_factors` を切り出した。
従来の入口も同じ証明を使い続ける。新しい入口は三乗抽出を再実行しない。

これに GN 経由の因子を渡すと、新しい正の原始解と

\[
 x y z < a b c
\]

が得られる。`primitiveCubicPack_false_via_GN` はこの厳密な減少を強帰納法で
閉じる。最後に既存の gcd 正規化を接続し、具体的な `CyclotomicField 3 ℚ`
を供給して、追加仮定のない公開終点を得る。

## 7. 検証と研究上の範囲

回帰例は [ThreeGNDescent.lean](../../../DkMathTest/FLT/Kummer/ThreeGNDescent.lean)。
符号の取り違え、非定数の元と三乗の往復、単元群の往復、同じ β の保存、
降下の実入力、追加仮定のない終点を検査する。

[ThreeGNDependencyAudit.lean](../../../DkMathTest/FLT/Kummer/ThreeGNDependencyAudit.lean)
は終点の型・本体・帰納型の構築子を再帰的に辿り、GN のイデアル冪抽出、
三次単元補題、環同型、新しい降下が実際に依存先に含まれることを要求する。
既存 FLT3 終点、従来の単元倍三乗抽出、従来のセクター排除、`sorryAx`
への依存は失敗にする。全 import がこれらを含まないという意味ではない。

11 個の回帰例と新規公開 26 宣言の公理監査に成功した。終点からの再帰的監査は
74,404 宣言・71,748 本体を検査し、必要な証明経路を確認した。
Kummer・Lib・DkMath の入口と指定回帰テストのビルドは 10,512 jobs、終了コード 0。
`import DkMath` からの smoke も成功した。DkMathTest 全体を実行したという意味ではない。
実行結果は [validation-three-gn.txt](evidence/validation-three-gn.txt) に記録した。
この成果は既存 FLT3 の算術と降下を再利用した、GN・イデアル経由の証明経路の
実験である。一般 p の単元補題・任意の Case II の正規化・一般 p の降下は
別の課題として残る。

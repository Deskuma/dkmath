# NOTE-014: 楕円曲線性から非零ねじれ点と次元下界へ

日付: 2026-10-20。NOTE-014 §4の提案を実装した。
標数0の体K上の楕円曲線Eについて、任意のn>1に対し、代数閉包上の実際の非零n-torsion点が存在する。
素数pではNOTE-012の有限性・NOTE-013の上界と合わせ、

\[
1\le\dim_{\mathbb F_p}E(\overline K)[p]\le2,
\qquad p\le|E(\overline K)[p]|\le p^2
\]

を得た。候補は次元1か2、位数pかp²であり、次元0・位数1を除いた。
同じFrey Sourceの曲線にも、非零点・有限性・位数を追加入力にせず接続した。

## 1. 根から実際の点を作る教科書

`EllipticTorsionNontrivial.lean` では、これまで片方向で使っていた座標拘束を同値へ拡張する。

```lean
torsion_some_iff_coordinate_root (E : WeierstrassCurve K) (n : ℕ)
  (h : (E.toAffine⁄(AlgebraicClosure K)).Nonsingular x y) :
  (nsmulAddMonoidHom n : Points E →+ Points E) (Affine.Point.some x y h) = 0 ↔
    ((E.baseChange (AlgebraicClosure K)).ΨSq (n : ℤ)).IsRoot x
```

KにはFieldとCharZeroを要求する。この同値自体には楕円曲線性は不要だが、点の非特異性hが必要である。
逆向きは、NOTE-012の `evalEval_ψ_sq` により

\[
\psi_n(P)^2=\Psi_n^{\mathrm{Sq}}(x)=0
\]

とし、体での平方零からψₙ(P)=0を得る。既存の
`smul_eq_zero_iff_evalEval_ψ` を逆向きに適用して、座標式を**実際の群の倍写像**へ戻す。
最後に整数倍と自然数倍を `natCast_zsmul` で一致させ、元のn倍写像の核へ入れる。

非零点の構成は次の通りである。

1. n>1、標数0から、ΨSqₙの次数n²−1は正である。
   `natDegree_ΨSq_pos` はMathlibの正確な次数公式 `natDegree_ΨSq` を使う。
2. `IsAlgClosed.exists_root` により、代数閉包上でΨSqₙの根xを一つ取る。
3. `exists_affine_equation_y` で曲線方程式を満たすyを取る。
   xを固定した曲線方程式はyについてモニック二次式なので、係数の評価後も次数2を保つ。
   この手順では楕円曲線性も標数0も使わず、方程式の解だけを与える。
4. Eの楕円曲線性を代数閉包への基底変換に運び、`Affine.equation_iff_nonsingular` で
   この解が非特異点であることを得る。ここで初めて実際の点群の `Point.some` を作れる。
5. 上記の同値でn倍零を証明し、元の `Torsion E n` の元Pを構成する。
6. `Point.some_ne_zero` により有限座標点Pは無限遠点Oではないので、P≠0である。

これは一点の存在証明である。異なる根の総数、根の単純性、全ファイバーの正確な点数は扱わない。
指数37の点の座標を巨大な式で具体的に展開する必要もない。

## 2. 仮定を保持した一般API

主要な存在定理の形は次である。

```lean
exists_nonzero_torsion_of_one_lt
  (E : WeierstrassCurve K) [E.IsElliptic] (n : ℕ) (hn : 1 < n) :
  ∃ P : Torsion E n, P ≠ 0
-- KにはFieldとCharZeroを要求する。
```

素数性はこの存在定理に要求しない。任意の合成数n>1にも同じ構成が適用される。
ここでのn-torsionはn倍で零になる点を指し、合成数の場合に点の位数がちょうどnであるとは主張しない。
n=1は零点だけであり、この条件を落とした主張にはしない。
曲線方程式の解だけでは特異点かもしれないので、楕円曲線性も落とさない。
標数0は幾何学の座標体の条件であり、残余空間の係数体Fₚの標数pとは異なる。

`torsion_nontrivial_of_one_lt` はこの存在をNontrivial命題に変換する。
素数pでは `torsionNontrivial` インスタンスとして公開し、実際のE[p]に自動適用できる。
NOTE-012の有限性によって有限次元となったFₚ空間に `Module.finrank_pos` を適用し、
正の次元を得る。この段階の素数性はZMod pを体として扱うために必要である。

上界と下界から `finrank_torsion_one_or_two` を得て、有限空間の濃度公式で
`card_torsion_prime_or_prime_sq` へ移す。標準torsionBy表示にも、既存の点を保つ線形同型で
`finrank_standardTorsion_pos` を運ぶ。

## 3. Frey接続と公開入口

`FreyResidualNontrivial.lean` は、`Source.rationalCurve_isElliptic` を一般定理へ供給する。
同じSourceの同じ残余空間について、非零点・Nontrivial・正の次元、次元1か2、位数pかp²を公開した。
`residual_nontrivial_profile` は以下をまとめる。

```lean
(1 ≤ Module.finrank (ZMod p) S.ResidualSpace ∧
  Module.finrank (ZMod p) S.ResidualSpace ≤ 2) ∧
  (p ≤ Nat.card S.ResidualSpace ∧ Nat.card S.ResidualSpace ≤ p ^ 2) ∧
  S.ResidualFactorsThroughFiniteLevel
```

素数性とSourceだけが入力であり、非零点・Nontrivial・Finite・位数p²を追加仮定にしていない。
新規本体は2モジュール、教科書コメントを含め214行、名前付き公開宣言は19個。
日本語の教科書docstringを付け、import直後の `#print "file: モジュール名"` を全新規Leanファイルに置いた。
`DkMath.Lib`、`DkMath.FLT`、`DkMathTest` の公開入口へ配線した。

## 4. 回帰・監査

回帰は8個の名前付き補題、尖点曲線の定義1個、4個の例で構成する。

- 実在するSource 2の(4,3,5)の曲線について、**その同じ曲線のE[37]** の非零点、
  次元の上下界、37≤位数≤1369、標準torsionByの正の次元を確認する。
- 同じ曲線で合成数4の非零torsion点も存在する。ZMod 4を体としては扱わない。
- n=1には非零点がないこと、Nontrivialの推論、次元1か2という公開結果も確認する。
- 尖点曲線y²=x³の原点は方程式の解だが特異点であることを確認する。
  これは非特異性のガードの検査であり、尖点・節点・楕円曲線の群の分類定理ではない。
- Source 37を入力する入口でも、同じSourceの次元・個数の上下界と有限レベルを得る。

公理監査は全19公開宣言と全9名前付き回帰宣言を対象とする。
主要12経路は型とopaqueな本体まで辿り、次数の正値性、根の存在、yの構成、非特異性、
実際の倍写像との同値、有限性、次元の正値性への依存を要求する。
条件付きの正確な位数・次元2、FLT終点、外部未移植宣言、類群・Kummer providerへの迂回は禁止する。

## 5. 残る一次元の候補

今回の下界は1である。次元1・位数pの候補は排除していない。
NOTE-014 §5にあるΦₚ−cΨSqₚの平方因子を避ける一般ファイバーの構成と、正確なファイバー計数は未実装である。
その調査結果と参照版は [NOTE-013実装報告](IMPLEMENTATION-NOTE013-261020.md) §3を参照する。

特に、deg ΨSqₚ=p²−1という次数の等式から、相異なる根がp²−1個あるとは結論しない。
重複度・分離性・正確な点数の下界を結ぶ幾何学が次の接続点である。
次元2・位数p²の確定、GL₂実現、Weil対・行列式、既約性、局所慣性・Artin導手、
一般FLT・FLT37の終点は今回の結論に含めない。

検証結果は [validation-note014.txt](evidence/validation-note014.txt)、
公開ルートの検査は [RootSmokeNOTE014.lean](evidence/RootSmokeNOTE014.lean) に記録する。

回帰のfocused buildは3,168 jobs、依存監査のfocused buildは3,169 jobs成功。
新規19公開宣言と9名前付き回帰宣言の公理監査、および12経路の依存監査が通った。
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11,556 jobs成功し、新規4モジュールに警告はない。
ルートsmoke、`lake env lean DkMathTest.lean`、指定のマーカーチェッカー、`git diff --check` も成功した。

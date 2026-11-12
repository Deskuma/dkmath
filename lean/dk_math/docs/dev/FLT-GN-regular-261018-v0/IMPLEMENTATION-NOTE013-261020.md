# NOTE-013: 正確な位数公式に先行する次元上界

日付: 2026-10-20。NOTE-013 §5の提案を、同じ曲線の実際のねじれ点群で証明した。
標数0の体Kと素数pについて、有限性・位数p²の追加仮定なしに

\[
\dim_{\mathbb F_p}E(\overline K)[p]\le2,
\qquad |E(\overline K)[p]|\le p^2
\]

が得られる。後者は、最初の粗い個数上界を次元上界へ変換してから濃度公式へ戻す改善である。
正確な位数p²、次元2への確定は今回の結論に含まない。

## 1. 教科書の証明経路

1. NOTE-012の実際の倍写像の核E[n]の有限性を利用する。n≠0を保持する。
2. 零点以外の点P=(x,y)について、`torsion_some_coordinate_root` によってxを `ΨSq n` の根に拘束する。
3. 異なる根の個数は、多重度込みの根の個数以下、それは多項式の次数以下である。
   `natDegree_ΨSq_le` により次数の**上界** n²−1だけを使う。次数の等式や分離性は不要である。
4. 同じxの上にある点はPと−Pに限られる。高々2点のファイバーの有限和と無限遠点から
   `card_torsion_le_degree_bound`、すなわち |E[n]|≤1+2(n²−1) を得る。
5. 素数pについて、有限Fₚ空間の濃度公式 `Module.natCard_eq_pow_finrank` を同じE[p]に適用する。
   pᵈ≤1+2(p²−1)<p³よりd≤2となる。p=2でも7<8なので、奇素数という条件は要らない。
6. このd≤2を濃度公式に戻し、|E[p]|=pᵈ≤p²を得る。

ファイバーは `xRep = ![x, 1]` で定義する。第一成分だけを使うと、無限遠点の表示[1,0]を
有限ファイバーへ混ぜてしまう場合がある。P=−Pの場合は1点なので「常に2点」とは数えない。
根がすべてねじれ点を生むとも、根がすべて単根であるとも仮定しない。

Kの標数0という仮定は、実際の点と除法多項式を結ぶNOTE-012から引き継ぐ。
係数体Fₚの標数pとは区別する。今回の一般定理は非特異点群について成立し、
追加の `E.IsElliptic` 仮定は要求しない。Freyの場合は既存の楕円曲線性も保たれている。

## 2. 公開APIとFrey接続

| モジュール | 主な公開結果 |
| --- | --- |
| `DkMath.Lib.NumberTheory.EllipticTorsionCardBound` | 有限xファイバーの定義・有限性・高々2点、非零nの個数上界 |
| `DkMath.Lib.NumberTheory.EllipticTorsionDimensionBound` | 次元≤2、位数≤p²、次元0/1/2・位数1/p/p²の候補、標準torsionByへの輸送 |
| `DkMath.FLT.FreyResidualDimensionBound` | 同じSourceの残余空間の上界・候補、上界と有限レベルをまとめた定理 |

本体は3モジュール、教科書コメントを含め246行、名前付き公開宣言16個。
日本語の教科書docstringで仮定と推論を説明する。
全新規Leanファイルはimport後に `#print "file: モジュール名"` を持つ。
`DkMath.Lib`、`DkMath.FLT`、`DkMathTest` の公開入口へ接続した。

`Source.residual_bounded_profile` は

```lean
Module.finrank (ZMod p) S.ResidualSpace ≤ 2 ∧
  Nat.card S.ResidualSpace ≤ p ^ 2 ∧ S.ResidualFactorsThroughFiniteLevel
```

を、素数pと同じSourceだけから供給する。有限性・位数・次元2を追加入力にしない。
標準 `torsionBy` 側の次元上界も、既存の点を保つ線形同型で運ぶ。

## 3. 奇素数の正確なファイバー計数の調査

参照実装の
[S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
を再取得して調べた。調査版は1,336行、blob SHAは
`865709609f50e0e2ef445df7c01d01768ca731c5`。
今回は外部コードの移植を追加せず、Mathlibの次数上界とNOTE-012の基盤から上界を組み立てた。

正確な位数へ進む経路で残る主な入力は以下である。

- `finite_not_squarefree_fiber`: Φₙ−cΨSqₙが平方因子を持つ例外的なcは有限。
- `exists_double_fiber_card`: 例外と2-torsion由来の像を避けて一般のQを選び、
  [n]P=Q または [n]P=−Qとなる点を正確に2n²個数える。
- `card_smul_fiber` と `card_nTorsion_odd_fibers`: 非空の倍写像ファイバーを核の平行移動として比較し、
  Qと−Qの重複を処理して核の正確な個数n²へ戻す。

これは今回の「根の数は次数以下」「各xの上は高々2点」という片側の評価より強い幾何学である。
とくに一般ファイバーの平方因子除去と正確な2n²個の計算は未実装であり、
既存の有限性を再証明する代わりに、次の下界の供給点として保持する。
今回のprime用の上界があれば、正確な二重ファイバーを得た後に自己反転Qの候補を
核の個数と比較して除く道も検討できるが、その接続は今回の証明には含めない。

## 4. 回帰・監査と到達範囲

回帰は名前付き6補題と4例である。
実在するSource 2の(4,3,5)に付随する**同じ有理曲線のE[37]**について、次元≤2・位数≤1369を確認する。
同じ曲線のE[2]は既知の非零点から0<次元≤2であることも確認した。
x=0のファイバーは自己反転する(0,0)の1点だけになる。指数1の個数上界とp=2の算術境界も検査する。
Source 37を仮定する入口では、次元・個数上界と有限レベルを同じSourceからまとめて得る。

依存監査では全16公開宣言と6回帰補題の公理、および11の主要経路で型とopaqueな本体を調べる。
条件付きの正確な位数・次元2の定理、FLT終点、外部未移植宣言、類群・Kummer providerへの迂回を禁止し、
実際の倍写像の座標拘束・有限性・ファイバー・次数上界と濃度公式への経路を要求する。

次元の候補は0・1・2、位数は1・p・p²である。一般に0と1を除外する下界は供給していない。
基底を持つFₚ²への同型・GL₂表現、Weil対・行列式、既約性、局所慣性・Artin導手、
一般FLT・FLT37の終点はいずれも今回の結論からは導かない。

検証結果は [validation-note013.txt](evidence/validation-note013.txt)、
公開ルートからの検査は [RootSmokeNOTE013.lean](evidence/RootSmokeNOTE013.lean) に記録する。

回帰のfocused buildは3,166 jobs成功。依存監査は16公開宣言・6回帰補題と11経路が通り、
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみだった。
`lake build DkMath DkMath.FLT DkMath.Lib DkMathTest` は11,552 jobs成功し、新規5モジュールの警告はない。
ルートsmoke、`lake env lean DkMathTest.lean`、指定のマーカーチェッカー、`git diff --check` も成功した。

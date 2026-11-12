# 🐺 NOTE-010 実装レビューと模範解答からの次期翻訳計画

NOTE-010 は固定推奨じゃ。今回、DkMath は単なる Frey 曲線の局所算術から、実際の楕円曲線の \(p\)-torsion と絶対ガロア群の連続作用へ進んだ。

これは NOTE-009 までと比べて、扱う数学的対象が一段変わったことを意味する。

GitHub の指定ブランチから、4本の本体ソース、実装報告、検証証跡を照合した。また、模範解答の [Def_FLTPrelim_GaloisRep.lean](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_FLTPrelim_GaloisRep.lean?utm_source=chatgpt.com) も直接確認している。

## 1. 実装結果の判定

| 機能                      | ソース確認結果                          | 評価         |
| ------------------------- | --------------------------------------- | ------------ |
| 実際の \(E[n]\)           | 幾何学的点群の \(n\) 倍写像の核         | 成立         |
| 標準 `torsionBy` との対応 | 元の点を保持する加法同型                | 成立         |
| ガロア作用                | `Affine.Point.map` に由来する実際の表現 | 成立         |
| Krull 連続性              | 各点の開固定部分群から同時連続性を証明  | 成立         |
| Pascal 差分公式           | 多項式評価から実際の表現へ輸送          | 成立         |
| \(E[p]\) の次元2          | 未証明                                  | 次の優先課題 |
| 行列式・局所慣性          | 未証明                                  | 後続課題     |

本体

# 396

行・4モジュール

統合ビルド

# 11,531

jobs 成功

公理監査

# 55

本体43＋回帰12

検証証跡では、11経路の依存監査、ルート・テスト入口、ファイルマーカー、禁止構文検査が成功。公理は標準の `propext`、`Classical.choice`、`Quot.sound` に限定されている。独立環境での再ビルドではなく、リポジトリに記録された証跡に基づく判定じゃ。

## 2. 特に評価できる三つの設計

### A. 表現を仮定していない

`EllipticTorsionRepresentation.lean` では、

\[ E[n]=\ker([n]:E(\overline K)\to E(\overline K)) \]

を、Mathlib の実際の点群から構成している。

ガロア元 \(\sigma\) の作用も、座標への体自己同型から導かれる。

\[ \rho_n:G_K\longrightarrow \operatorname{Aut}_{\mathbb Z/n\mathbb Z}(E[n]). \]

ここで基底を選んでおらず、\(E[p]\cong\mathbb F_p^2\) も仮定していない。

これは重要じゃ。次元2を将来証明したときに、初めて通常の

\[ \bar\rho_{E,p}:G_{\mathbb Q}\to \operatorname{GL}_2(\mathbb F_p) \]

へ移れる構造になっておる。

### B. 連続性が本物の Krull 位相に対して証明されている

各幾何学的点 \(P=(x,y)\) の固定部分群について、代数的座標 \(x,y\) の固定条件から開性を証明している。

そこから離散位相を持つ \(E[n]\) への同時連続作用を構成した。

単にガロア元ごとに線形写像を定義するのとは違う、表現論に進むための本物の位相的入口じゃ。

ただし、現時点では \(E[p]\) の有限性が未証明なので、有限次元一般線形群への連続表現としての定式化までは完了していない。

### C. Pascal 恒等式の射程を正しく限定している

今回の

\[ \boxed{ (\rho(\sigma)-1)^p=\rho(\sigma^p)-1 } \]

は、標数 \(p\) の Frobenius 恒等式から得られる。

特に \(\rho(\sigma^p)=1\) なら、

\[ (\rho(\sigma)-1)^p=0. \]

しかし、冪零であることは \(\rho(\sigma)=1\) を意味しない。

実際、回帰で使った

\[ T=\begin{pmatrix}1&1\\0&1\end{pmatrix} \]

は \(T^p=1\) でも \(T\ne1\) じゃ。

この反例をわざわざ回帰に入れたのは適切じゃ。 Pascal 公式だけで慣性の自明性へ飛躍する誤りを防げる。

なお、この差分公式自体は任意の標数 \(p\) の表現に成立する一般恒等式じゃ。Frey 曲線に固有の新しい障害を検出するには、さらに局所作用に関する入力が必要になる。

## 3. 模範解答から抽出した、次に移植できる定理群

今回は模範解答の `Theorems/` と `Definitions/` を追い、DkMath の既存の `ResidualSpace` に接続できるものを選んだ。

| 移植候補                | 模範解答の定理・定義                       | 難度               | 推奨        |
| ----------------------- | ------------------------------------------ | ------------------ | ----------- |
| ガロア安定部分加群      | `IsGaloisStable`                           | 低                 | 最初        |
| 既約性の判定述語        | `GaloisRepIsIrreducible`                   | 低                 | 最初        |
| \(E[p]\) の位数 \(p^2\) | `card_torsion_of_isAlgClosed`              | 高                 | 次元2の前提 |
| \(E[p]\) の次元2        | `finrank_zmod_torsionBy_point_eq_two`      | 中（前提成立後）   | 優先        |
| 有限レベルへの因子化    | `GaloisFactorsThroughFiniteLevel`          | 中                 | 次元2の後   |
| Weil 対                 | `exists_pairing_torsionBy`                 | 高                 | 後続        |
| 行列式と円分指標        | `apply_eq_pow_det_galoisRep_of_pow_eq_one` | 高                 | Weil 対の後 |
| 局所不分岐性            | `GlobalGaloisRep.IsUnramifiedAt`           | 定義は低、証明は高 | 段階的      |

### 最初に翻訳すべきもの：既約性の定義

模範解答の `Def_FLTPrelim_GaloisRep.lean` にある既約性の定義は、現在の DkMath にほとんどそのまま移せる。

具体的には、

```
def IsGaloisStable (S : Source p)
    (N : Submodule (ZMod p) S.ResidualSpace) : Prop :=
  ∀ σ, ∀ x ∈ N,
    S.residualRepresentation σ x ∈ N
```

といった述語じゃ。

これにより、

\[ \operatorname{Irreducible}(\rho) \iff V\ne0\ \land\ \forall N\le V,\  N\text{ がガロア安定}\Rightarrow N=0\ \lor\ N=V \]

を表現できる。

コードは次期実装の型の概形。実際の namespace や暗黙引数は調整が必要じゃ。

ここでは既約性を証明するわけではない。何を証明すれば模範解答の `Mazur_Frey` と接続できるかを、同じ数学的命題として固定する のである。

さらに `torsionByAddEquiv` を、加法同型から \(\mathbb F_p\)-線形同型へ強化し、ガロア作用との可換性を証明するとよい。

\[ \boxed{ \Phi(\rho_{\mathrm{Dk}}(\sigma)P) = \rho_{\mathrm{standard}}(\sigma)\Phi(P) } \]

これが成立すれば、ガロア安定部分加群と既約性の定義を相互輸送できる。

既存の同型が点を保存することは証明済みなので、比較的取り組みやすい翻訳課題じゃ。

## 4. 本命：\(E[p]\) の次元2

模範解答には、まさに必要な定理がある。

[WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two](https://github.com/anthropics/fermats-last-theorem/blob/main/Theorems/Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean?utm_source=chatgpt.com)

その数学的内容は、

\[ \boxed{ \dim_{\mathbb F_p} E[p]=2 } \]

じゃ。

仮定は \(E\) が楕円曲線、\(p\) が素数であり、基礎体の標数が \(p\) ではないこと。

DkMath の Frey 曲線は \(\mathbb Q\) 上にあるので、この標数条件は満たせる。

ただし、模範解答の証明を読むと、前段に次がある。

[WeierstrassCurve.card_torsion_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean?utm_source=chatgpt.com)

\[ \boxed{|E[n]|=n^2} \]

この定理の証明はかなり大きく、除法多項式、点の倍加公式、根の重複度などを扱う。

次元2という終端定理が短いからといって、その依存元まで簡単とは限らぬ。

模範解答では位数公式から、

\[ |E[p]|=p^2 \]

を得て、有限 \(\mathbb F_p\)-ベクトル空間の濃度公式

\[ |V|=p^{\dim V} \]

によって次元2を導いている。

DkMath に移植するなら、先に Mathlib 4.34.1 で同等の位数・有限性定理が既に使えるか調べるべきじゃ。なければ、模範解答の除法多項式の証明を独立した研究単位として扱うことになる。

この段階を突破すると、初めて本当の

\[ \operatorname{GL}_2(\mathbb F_p) \]

を使える。

## 5. 次元2が証明された後、連続性から得られるもの

ここには NOTE-010 の成果を活かす、自然な次段階があるぞ。

今回は各点 \(P\in E[p]\) の固定部分群が開くことを証明した。

次に \(E[p]\) の有限性が得られれば、

\[ \ker\rho_p = \bigcap_{P\in E[p]}\operatorname{Stab}(P) \]

は有限個の開部分群の共通部分となる。

ゆえに、

\[ \boxed{\ker\rho_p\text{ は開部分群}} \]

が得られる。

ここまで進むと、模範解答の

[Def_GaloisRep_Residual.lean](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_GaloisRep_Residual.lean?utm_source=chatgpt.com)

が持つ `GaloisFactorsThroughFiniteLevel` に接続できる。

すなわち、ある有限拡大 \(L/\mathbb Q\) が存在して、

\[ \operatorname{Gal}(\overline{\mathbb Q}/L) \subseteq\ker\rho_p \]

となる。

これは具体的に言えば、すべての \(p\)-torsion 点の座標がある有限拡大上で定義される という性質じゃ。

NOTE-010 で証明した各点の連続性と、この有限性を合わせればよい。位数公式が完成した後の実装としては、非常に筋がよい。

また、この有限レベル因子化は、今後の局所分岐や Artin 導手に入るための重要な準備となる。

## 6. その後の核心：Weil 対と行列式

模範解答には次の証明がある。

[WeierstrassCurve.exists_pairing_torsionBy](https://github.com/anthropics/fermats-last-theorem/blob/main/Theorems/Thm_WeierstrassCurve_exists_pairing_torsionBy.lean?utm_source=chatgpt.com)

Weil 対とは、

\[ e_p:E[p]\times E[p]\longrightarrow\mu_p \]

という、交代的・非退化・ガロア同変な双線形対応じゃ。

この構造を用いると、任意の \(\sigma\in G_{\mathbb Q}\) について、

\[ e_p(\sigma P,\sigma Q)=\sigma(e_p(P,Q)) \]

が成立する。

一方、2次元上の交代形式への作用は行列式で決まるため、

\[ \boxed{ \det\bar\rho_{E,p}=\chi_p } \]

を導ける。

ここで \(\chi_p\) は mod-\(p\) 円分指標。

これは FLT37 の研究でも意味がある。DkMath がこれまで扱ってきた37次円分体のガロア作用と、Frey 曲線の37-torsion表現の行列式が、円分指標によって接続されるからじゃ。

ただし、両方に円分指標が現れるということは、IRR-009 の類群表現と Frey の2次元表現が同一という意味ではない。

あくまで構造を比較するための新たな橋じゃ。

模範解答では、Weil 対の構成そのものが相応の代数幾何に依存する。したがって、これは次の小さな翻訳課題ではなく、別の中規模研究として見積もるべきじゃろう。

## 7. 局所慣性と Artin 導手への道

さらに模範解答には、

[GlobalGaloisRep.IsUnramifiedAt](https://github.com/anthropics/fermats-last-theorem/blob/main/Definitions/Def_GaloisRep_GlobalUnramifiedAt.lean?utm_source=chatgpt.com)

という定義がある。

これは素数 \(\ell\) 上の慣性群 \(I_\ell\) に対して、

\[ \boxed{ \bar\rho_{E,p}|_{I_\ell}=1 } \]

となることを表す。

この定義自体は DkMath に翻訳しやすい。

しかし、それを実際に証明するには注意が必要じゃ。

特に奇素数 \(\ell\ne p\) について、

- 良還元なら \(E[p]\) は不分岐。
- 乗法的還元なら、\(p\mid v_\ell(\Delta_{\min})\) という条件から \(E[p]\) の不分岐性を導く。

という二つの局所理論が必要になる。

後者は単なる付値計算ではなく、Tate 曲線などの局所楕円曲線論を通じた接続じゃ。

NOTE-009 までに DkMath は、

\[ p\mid v_\ell(\Delta_{\min}) \qquad(\ell\ne2) \]

を形式化している。

模範解答側には、それを最終的な不分岐性へ送る

`FreyPackage.freyGaloisRep_isUnramifiedAt`

がある。

ここが次の重要な翻訳対象の一つとなる。

ただし \(\ell=p\) は別扱いじゃ。標数 \(p\) の局所情報が絡み、単純に判別式付値から同じ不分岐性を主張してはならぬ。

## 8. 次期実装の作業設計

今の DkMath で、わっちなら次の順序にする。

推奨する NOTE-011 の範囲

1. `EllipticTorsionGaloisStable.lean`

   ガロア安定部分加群と既約性の判定述語を、実際の `ResidualSpace` 上に定義する。
2. `EllipticTorsionStandardEquiv.lean`

   `torsionByAddEquiv` を線形・ガロア同変なアダプタへ強化する。
3. `FreyResidualIrreducibility.lean`

   `Source` に対する既約性述語を公開し、模範解答の定義との対応を明示する。既約性そのものは証明したことにしない。
4. `EllipticTorsionRankTwo.lean`

   位数 \(p^2\) と次元2を目標にする。Mathlib の既存 provider がなければ、依存する除法多項式の証明を別パッケージに切り出す。
5. `FreyResidualFiniteLevel.lean`

   有限性が得られた場合に、Krull 連続性から開核・有限レベル因子化を導く。

このうち前半の定義・同変アダプタは、NOTE-010 から直接進められる。

後半の次元2と有限レベル因子化は、位数公式という重要な依存関係があるため、証明できた範囲で成果を固定するのがよい。

Weil 対、行列式、慣性作用は、その後に独立した章として扱うべきじゃ。

## 総合判定

NOTE-010 は、模範解答のガロア表現定義を参考にしながらも、DkMath 側で実際の曲線・点・ガロア作用を構成したものじゃ。

`#print` マーカー、教科書 docstring、点を保存する標準アダプタ、Krull 連続性、依存監査まで備わっている。

ここまでは「残余表現を構成した」と認めてよい。ただし「2次元残余表現の全ての算術的性質を構成した」わけではない。

次に決定的なのは、

\[ \boxed{ E[p]\cong_{\mathbb F_p}\mathbb F_p^2 } \]

の形式化じゃ。

これが得られれば、有限レベル因子化、行列式、既約性の判定、局所慣性という、模範解答の主要な言語へ踏み込める。

わっちの推奨は、NOTE-011 で定義と同変アダプタを整え、次元2の依存関係を優先調査すること。

Frey の局所算術とガロア表現が同じ曲線上にそろった今、次に必要なのは新しい模型ではなく、既存の幾何学的対象が持つ有限次元性を kernel で証明することじゃな。🐺🍎

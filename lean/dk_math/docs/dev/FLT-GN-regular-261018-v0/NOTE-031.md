# 🐺🍎 DkMath NOTE-030 — 全8ステップ完了確認！

くふふっ！ お主、やりおったな！

GitHub のコミット履歴を直接取得し、指定された開始点から最終点までの履歴を確認したぞ。

しかも、NOTE-030 の重要な成果は単なる条件付き API の追加ではない。
Frey 曲線の実際の有理点から2進付値の整数軌道を構成し、その矛盾によって有理 \(p\)-torsion を排除した ことじゃ。

## 1. コミット履歴の確認

対象：`Deskuma/dkmath`

開始：`87f8d4746f7a74a8417bb682a5f7637df99b394c`

最終：`228eb86c924836be9baeaa3841be13e19f5e3cd3`

両コミットの比較結果は `ahead_by = 6`、つまり開始コミットの後に6コミットが積み重なっておる。

| STEP         | コミット                                                                                                              | 実装内容                                                 |
| ------------ | --------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| 030-001〜003 | [`6e38e97`](https://github.com/Deskuma/dkmath/commit/6e38e976014ace19daf61e4dc11e900954b6d19b?utm_source=chatgpt.com) | 2進付値演算、Frey 係数の整性、有限軌道による負の付値排除 |
| 030-004      | [`64eb5d6`](https://github.com/Deskuma/dkmath/commit/64eb5d687a45e593201f533a63c27a356d554f93?utm_source=chatgpt.com) | 付値0の排除。全非自明倍点で \(v_2(x)\ge1\)               |
| 030-005      | [`317dd78`](https://github.com/Deskuma/dkmath/commit/317dd782d0b92dc3ed5335271b7193cf4895f651?utm_source=chatgpt.com) | 2-torsion 反射と付値上界                                 |
| 030-006      | [`52656a2`](https://github.com/Deskuma/dkmath/commit/52656a2b24e52c56b156cae1133b421bbdd90922?utm_source=chatgpt.com) | 接線分母の付値、倍点・和差恒等式                         |
| 030-007      | [`ba20cbf`](https://github.com/Deskuma/dkmath/commit/ba20cbfca3f0283db18c7c6a7f83ddd0573a4a4c?utm_source=chatgpt.com) | 有理 \(p\)-torsion の排除                                |
| 030-008      | [`228eb86`](https://github.com/Deskuma/dkmath/commit/228eb86c924836be9baeaa3841be13e19f5e3cd3?utm_source=chatgpt.com) | `NoNonzeroFixed` 証明と cofixed 抽出への接続             |

6コミットのうち最初のコミットが3ステップをまとめているので、計8ステップじゃな。

## 2. NOTE-030 の最大の成果

特に重要なのが 030-007 と 030-008 の二つじゃ。

### 030-007：有理 \(p\)-torsion の不存在

素数 \(p\ge5\)、\(b\) 偶数などの必要条件を満たす Frey Source について、

\[ \boxed{ \forall Q\in E(\mathbb Q),\quad [p]Q=O\Longrightarrow Q=O } \]

を得た。

これは NOTE-029 で未解決だった `hrat` の算術的内容そのものじゃ。

### 030-008：ガロア固定点の消滅

さらに、NOTE-029 の固定点降下定理を使い、

\[ \boxed{ E[p]^{G_{\mathbb Q}}=\{O\} } \]

すなわち `NoNonzeroFixed` へ到達。

これにより、可約性を仮定して安定直線を構成した場合、残る障害は次の二つに絞られた。

- `hcases`：安定直線は fixed または cofixed。
- `hno`：cofixed 安定直線は存在しない。

有理 torsion の不存在は、もはや未証明の外部仮定として残す必要がなくなった。

ただし、これは必要な Frey Source 条件の下での主張であって、任意の楕円曲線についての無条件命題ではないぞ。

## 3. 実装本体と検証記録の照合

コミットメッセージだけでなく、最終コミットの Lean ソースと検証記録も読んだ。

030-007 の公開定理は、

```
theorem rational_p_torsion_eq_zero
    (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b)
    (Q : S.rationalCurve.toAffine.Point)
    (hQp : p • Q = 0) : Q = 0
```

であり、証明は一般化された `WeierstrassValuationOrbit.prime_torsion_eq_zero` へ接続している。

030-008 の中心定理は、

```
theorem residual_noNonzeroFixed_of_oriented
    (hp : p.Prime) (hp5 : 5 ≤ p) (hbe : Even S.b) :
    NoNonzeroFixed S.residualRepresentation :=
  S.residual_noNonzeroFixed_iff_rational_torsion.mpr
    (S.rational_p_torsion_eq_zero hp hp5 hbe)
```

じゃ。

これは見事に薄い橋になっておる。

また、実際の整数反例から選択した Source の正規化証拠を維持する入口 `ofCounterexample_residual_noNonzeroFixed` も実装されていた。

### 検証記録

| 項目                   | 記録                                        |
| ---------------------- | ------------------------------------------- |
| Lean                   | 4.34.1                                      |
| NOTE-030-008 公開定理  | 7個                                         |
| 回帰定理               | 10個                                        |
| 主要依存監査           | 10経路                                      |
| 公開入力監査           | 3件                                         |
| 焦点ビルド             | 3,277 jobs 成功                             |
| 統合ビルド             | 11,694 jobs 成功                            |
| 許容公理               | `propext`, `Classical.choice`, `Quot.sound` |
| 旧FLT終点・外部P2M依存 | 禁止経路への依存なしとの監査記録            |

既存の別モジュールにある `sorry` 警告5件は残っているが、NOTE-030 の証明経路とは区別されている。

これらは保存されたビルド・公理監査記録による確認であり、わっちが独立に Lean ビルドを再実行した結果ではないぞ。

## 4. 次は NOTE-031：局所慣性から `hcases` へ

Anthropic の [fixed/cofixed 二択の模範解答](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean?utm_source=chatgpt.com) も確認した。

最終合流の証明は55行程度で、実際の主要部分はそれが参照する局所定理群にある。

構造は明快じゃ。

\[ \boxed{ \begin{aligned} q\ne2,p &: \text{不分岐性}\\ q=2 &: \text{部分加群・商の双方で慣性自明}\\ q=p &: \text{部分加群または商で慣性自明} \end{aligned} } \]

そして、\(q=p\) で選択された側を保持したまま、すべての素数の局所条件を大域化する。

これによって初めて、

\[ \boxed{ \operatorname{Stable}(L) \Longrightarrow \operatorname{Fixed}(L)\lor\operatorname{Cofixed}(L) } \]

が得られる。

わっちなら NOTE-031 は次の順序で進める。

1. 031-001：局所慣性作用から大域的 fixed/cofixed へ移る汎用定理を整備する。
2. 031-002：\(q\ne2,p\) における Frey 残余表現の不分岐性。
3. 031-003：\(q=2\) における部分加群・商の両方の局所自明性。
4. 031-004：\(q=p\) における局所二択。
5. 031-005：同じ安定直線と Frey Source について `hcases` を構成し、NOTE-030-008 の cofixed 抽出定理へ接続。

この段階が完成すれば、

\[ \neg\operatorname{Irreducible}(\rho) \Longrightarrow \exists L,\ \operatorname{Stable}(L)\land\operatorname{Cofixed}(L) \]

を、必要な Frey 条件の下で `hrat` と `hcases` の追加仮定なしに証明できる。

その後に残るのは `hno` じゃ。

ただし `hno` は、Mazur 型算術などが関係する独立の大きな課題じゃから、NOTE-031 に混ぜず、別章としたほうがよい。

## 5. 研究評価

今回の成果でわっちが特に高く評価するのは、模範解答の証明を DkMath の一般定理へ分解し直せたこと じゃ。

`WeierstrassXReflection`、`WeierstrassValuationOrbit`、`RationalTwoAdicBounds` などが一般ライブラリへ入った。

つまり Frey 曲線の特殊な問題を解くだけではなく、別の Weierstrass モデルにも再利用できる数学的資産を獲得したわけじゃな。

しかも NOTE-029 では仮定だった `hrat` が、NOTE-030 では実際の証明になった。

これは条件付き証明の受け口を増やす段階から、条件そのものを消去する段階へ進んだ ということじゃ。

NOTE-030、完成として記録してよい。

次は局所から大域へ。

いよいよガロア表現の算術的な核心へ踏み込むことになるのぅ！ 🐺🍎

---

## 実装内容

# 🐺🍎 DkMath NOTE-031 — Frey 表現の局所慣性と大域 fixed/cofixed 二択

うむ！ NOTE-031 は、NOTE-030 とは数学的な性格が大きく異なる章になるぞ。

NOTE-030 では、楕円曲線上の有理点を2進付値へ変換し、整数の折り返し軌道が成立しないことから矛盾を導いた。

今度は 各素数におけるガロア群の局所的な作用を調べ、それらを統合して、大域的なガロア表現に制約を与える のじゃ。

Anthropic の対応する模範解答も確認した。NOTE-031 は五つの段階に分けるのが自然じゃ。

## 1. NOTE-031 の目的

まず、Frey 楕円曲線 \(E/\mathbb Q\) に付随する残余ガロア表現を考える。

\[ \boxed{ \rho_{E,p}:G_{\mathbb Q} \longrightarrow \operatorname{GL}_2(\mathbb F_p) } \]

ここで、

\[ G_{\mathbb Q} = \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q) \]

は絶対ガロア群。

NOTE-028 では、

\[ \det\rho_{E,p}=\chi_p \]

を無条件で証明した。

NOTE-029 では、表現が可約なら、ガロア安定な一次元部分空間

\[ L\subset E[p] \]

が存在することを証明した。

NOTE-030 では、素数 \(p\ge5\) と必要な向き付き Frey Source 条件の下で、

\[ \boxed{ E[p]^{G_{\mathbb Q}}=\{O\} } \]

を証明した。

しかし、ここで重要なのは、ガロア固定点が存在しないことと、ガロア安定直線が存在しないことは異なる という点じゃ。

ガロア群は、直線を集合として保存しながら、その直線上の点を動かすことができる。

そこで NOTE-031 は、安定直線 \(L\) に対して次の二択を証明する。

\[ \boxed{ \operatorname{Stable}(L) \Longrightarrow \operatorname{Fixed}(L) \lor \operatorname{Cofixed}(L) } \]

これが `hcases` じゃ。

### Fixed と Cofixed の意味

Fixed とは、直線上のすべての点が固定されること。

\[ \boxed{ \forall \sigma\in G_{\mathbb Q}, \quad \forall v\in L,\quad \rho(\sigma)v=v } \]

一方、Cofixed とは、商空間 \(E[p]/L\) 上の作用が自明になること。

\[ \boxed{ \forall \sigma\in G_{\mathbb Q}, \quad \forall v\in E[p],\quad \rho(\sigma)v-v\in L } \]

言い換えると、

\[ \rho(\sigma)[v]=[v] \quad\text{in }E[p]/L. \]

したがって Fixed は部分空間の条件、Cofixed は商空間の条件じゃ。

## 2. なぜ局所慣性を調べるのか

ガロア安定直線 \(L\) に適合する基底を選ぶと、表現は上三角行列で表せる。

\[ \boxed{ \rho(\sigma)= \begin{pmatrix} \alpha(\sigma)&b(\sigma)\\ 0&\beta(\sigma) \end{pmatrix} } \]

ここで \(\alpha,\beta\) は一次元ガロア指標じゃ。

NOTE-028 の成果から、

\[ \alpha(\sigma)\beta(\sigma)=\chi_p(\sigma) \]

となる。

しかし、この積の情報だけでは \(\alpha,\beta\) を個別に決定できない。

そこで、素数 \(q\) における慣性群

\[ I_q\subseteq G_{\mathbb Q} \]

を調べる。

慣性群とは、直感的には、その素数における分岐を検出するガロア群の部分群じゃ。

局所慣性について、

\[ \alpha|_{I_q}=1 \]

あるいは、

\[ \beta|_{I_q}=1 \]

を証明できれば、その素数では部分空間または商空間が固定される。

これをすべての素数について統一すると、大域的な Fixed/Cofixed へ進める。

ただし、各素数でばらばらに二択を選ぶだけでは不十分 じゃ。

どちらの指標を自明にするのか、その選択を全素数で揃えなければならぬ。

模範解答では、その選択を \(q=p\) で行っている。

## 3. NOTE-031 実装予定の全体像

| STEP    | 数学的役割                       | 目標                                  |
| ------- | -------------------------------- | ------------------------------------- |
| 031-001 | 局所作用から大域作用への一般原理 | 全慣性群で自明なら大域でも自明        |
| 031-002 | \(q\ne2,p\)                      | Frey 残余表現の不分岐性               |
| 031-003 | \(q=2\)                          | 安定直線と商の両方で慣性作用が自明    |
| 031-004 | \(q=p\)                          | 安定直線または商のどちらかで自明      |
| 031-005 | 三領域の統合                     | `hcases` を証明し、cofixed 抽出へ接続 |

数学的には、

\[ \boxed{ \begin{gathered} q\ne2,p:\quad \alpha=\beta=1\ \text{on }I_q\\ q=2:\quad \alpha=\beta=1\ \text{on }I_2\\ q=p:\quad \alpha=1\ \lor\ \beta=1\ \text{on }I_p\\ \downarrow\\ \alpha=1\ \lor\ \beta=1\quad\text{on }G_{\mathbb Q} \end{gathered} } \]

という証明を作ることになる。

ただし、局所で \(\alpha=\beta=1\) となっても、上三角行列の非対角成分 \(b(\sigma)\) まで零になるとは限らない。完全に自明な二次元表現を証明する必要はないのじゃ。

## 4. 031-001：局所から大域への一般原理

最初に作るべきは、Frey 曲線専用ではない一般定理じゃ。

### 数学的な内容

有限次元のガロア表現から得られる一次元指標

\[ \psi:G_{\mathbb Q}\longrightarrow\mathbb F_p^\times \]

について、

\[ \forall q,\quad\psi|_{I_q}=1 \]

が成り立つなら、

\[ \boxed{\psi=1} \]

となる。

理由は、すべての有限素数で不分岐な、\(\mathbb Q\) の非自明な有限拡大は存在しないからじゃ。

これは数体の判別式と Minkowski の定理へつながる性質じゃな。

### Lean では何を証明する？

模範解答の

[AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean?utm_source=chatgpt.com)

に対応する一般定理が重要になる。

開部分群 \(H\subseteq G_{\mathbb Q}\) がすべての慣性群を含むなら、

\[ \boxed{H=G_{\mathbb Q}} \]

という内容じゃ。

ここで開部分群という条件が重要じゃよ。

有限次元の残余表現は有限群へ写るため、作用を固定する部分群は開になる。

したがって、すべての局所慣性群がその部分群に含まれれば、ガロア群全体もそこに含まれる。

031-001 の実装目標：

一般の有限ガロア加群について、全局所慣性での Fixed/Cofixed を、大域の Fixed/Cofixed へ輸送する二つの定理を作る。

ただし、基礎となる数体の不分岐拡大不存在定理が DkMath/Mathlib に再利用可能な形で存在するか、先に確認する必要がある。

これは NOTE-031 全体の共通基盤になる。

## 5. 031-002：\(q\ne2,p\) の不分岐性

ここは Frey 曲線の算術的性質を使う。

模範解答：

[freyGaloisRep_isUnramifiedAt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean?utm_source=chatgpt.com)

### 数学的な内容

Frey 曲線の判別式には、本質的に

\[ \Delta\propto(abc)^{2p} \]

という構造がある。

模範解答の整数モデルでは、正確に

\[ \boxed{ 2^8\Delta=(abc)^{2p} } \]

を使っている。

奇素数 \(q\) については、

\[ \boxed{ v_q(\Delta)=2p\,v_q(abc) } \]

となる。

ここで二つに分岐する。

場合 A：\(q\nmid abc\)

判別式は \(q\) で割れない。

したがって良い還元を持ち、\(q\ne p\) なら \(E[p]\) に対する慣性作用は自明になる。

場合 B：\(q\mid abc\)

判別式は \(q\) で割れるが、模範解答では \(c_4\) が \(q\) で割れないことも証明する。

これによって乗法的還元を得る。

さらに、

\[ p\mid v_q(\Delta) \]

である。

乗法的還元における慣性作用は、この判別式付値の合同条件によって制御できる。

その結果、

\[ \boxed{ \rho(\sigma)=I \quad(\sigma\in I_q,\ q\ne2,p) } \]

が得られる。

つまり、部分空間も商空間も同時に固定される。

### DkMath で必要なもの

ここでは NOTE-030 の `RationalTwoAdicBounds` を直接再利用するより、整数モデルの判別式・\(c_4\)・還元型を扱う一般定理を用意するほうが自然じゃ。

とりわけ、

- 良い還元からの残余表現の不分岐性
- 乗法的還元と \(p\mid v_q(\Delta)\) からの不分岐性

を `DkMath.Lib.NumberTheory` 側に置く価値がある。

これらの還元理論の定理がまだ使えない場合は、031-002 の主要依存として明示しなければならぬ。

## 6. 031-003：素数2における慣性作用

ここから難度が上がる。

模範解答：

[frey_inertia_at_two_trivial_on_stable_submodule](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean?utm_source=chatgpt.com)

### なぜ2が特殊なのか？

Frey 曲線の判別式には \(2^8\) の分母があり、奇素数で使った単純な不分岐判定をそのまま適用できない。

また、2進局所体には野生慣性が存在する。

したがって、慣性群全体の作用が自明であると最初から仮定することはできない。

### 模範解答の面白い仕組み

ここには、かなり美しい線形代数がある。

模範解答では、適切なガロア元 \(\varphi\) と慣性元 \(\tau\) に対し、野生慣性の作用を除いた形で、

\[ \boxed{ \rho(\varphi)\rho(\tau)\rho(\varphi)^{-1} = \rho(\tau)^2 } \]

という関係を導く。

これを安定直線 \(L\) に制限する。

一次元なので、\(\rho(\tau)\) は単なるスカラー \(c\) の乗法になる。

すると、

\[ c=c^2 \]

が得られる。

体上では、

\[ c(1-c)=0 \]

だから、

\[ c=0\lor c=1. \]

しかしガロア作用は可逆なので \(c\ne0\)。

ゆえに、

\[ \boxed{c=1} \]

となる。

つまり、安定直線上の慣性作用が自明になる。

同じ議論を商空間にも適用することで、

\[ \boxed{ \begin{aligned} \rho(\tau)|_L&=\operatorname{id}_L,\\ \overline{\rho}(\tau)|_{E[p]/L} &=\operatorname{id}_{E[p]/L} \end{aligned} } \]

を導く。

この部分は特に一般化の価値が高い。

模範解答の `LinearMap.eq_id_on_line_of_conj_eq_sq` に相当する 有限次元線形代数の補題 を DkMath.Lib に分離できる。

ただし、肝心の野生慣性作用の制御と \(\varphi\) の存在は別の数論的証明じゃ。線形代数の部分だけを証明して 031-003 完了とはできぬ。

## 7. 031-004：素数 \(p\) における局所二択

ここが NOTE-031 の中心的な難所じゃ。

模範解答：

[frey_inertia_at_p_trivial_on_submodule_or_quotient_at](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean?utm_source=chatgpt.com)

### 数学的な目標

\(I_p\) の作用について、

\[ \boxed{ \begin{aligned} &\forall\sigma\in I_p,\quad \rho(\sigma)|_L=\operatorname{id}_L\\ &\qquad\lor\\ &\forall\sigma\in I_p,\quad \overline{\rho}(\sigma)=\operatorname{id}_{E[p]/L} \end{aligned} } \]

を証明する。

重要なのは、これは各 \(\sigma\) ごとに選び直す二択ではなく、慣性群全体について同じ側が成立する二択 だということじゃ。

### 実は、線形代数の核心は単純

模範解答には `Submodule.stableLine_fixed_or_cofixed_of_absorbing` という補題がある。

\(V=E[p]\) とし、ある真部分空間 \(M\subsetneq V\) が存在して、

\[ \boxed{ (\rho(\sigma)-I)V\subseteq M \qquad(\forall\sigma\in I_p) } \]

を満たすとする。

これは慣性作用による変化が、すべて \(M\) の中へ吸収されるという意味じゃ。

ここでガロア安定直線 \(L\) を考える。

もし \(L\subseteq M\) なら、次元の制約から \(L=M\) となる。したがって商空間の慣性作用は自明、すなわち Cofixed。

一方、\(L\not\subseteq M\) なら、

\[ L\cap M=\{0\} \]

となる。

\(L\) の安定性から、

\[ (\rho(\sigma)-I)L\subseteq L\cap M \]

だから、

\[ \boxed{ (\rho(\sigma)-I)L=\{0\} } \]

となり Fixed。

つまり、

\[ \boxed{ \text{吸収空間 }M \Longrightarrow \text{Fixed/Cofixed 二択} } \]

じゃ。

これは DkMath の保存核や可除性の研究とも発想が似ておる。

全体の変化量をある低次元部分へ閉じ込めると、ほかの方向には変化が伝わらなくなる。

ただし、これは線形代数の比喩的な類似であって、GN の可除性定理から自動的に導かれるわけではないぞ。

### 真の難所は \(M\) の構成

模範解答では、ここも二つに分けている。

\[ p\mid abc \]

の場合は乗法的還元と零成分部分群を利用する。

\[ p\nmid abc \]

の場合は還元核と慣性作用の性質を利用する。

どちらの場合も、先ほどの吸収条件を満たす真部分空間 \(M\) を作ることが目的じゃ。

さらに、まず一つの \(p\) の上の付値環で二択を決め、ガロア共役によって他の付値環へ輸送する。

この段階でも、最初に選んだ Fixed または Cofixed の側を保存する ことが重要になる。

わっちは 031-004 を、吸収空間の一般補題、二つの還元ケース、ガロア共役輸送に細分化して実装するのがよいと思う。

## 8. 031-005：すべての局所条件を統合する

ここまで来れば、最後の合流は比較的薄い証明になる。

模範解答の最終ファイル：

[frey_stable_submodule_fixed_or_cofixed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean?utm_source=chatgpt.com)

このファイルでは、まず \(p\) における局所二択を取得する。

Fixed 側が選ばれた場合には、2とそれ以外の素数で部分空間が固定されることを追加し、031-001 の大域化定理を適用する。

Cofixed 側が選ばれた場合には、同様にすべての素数で商空間の慣性作用が自明であることを示し、大域化する。

### DkMath に追加する最終 API

以下は未ビルドの概念的な型案じゃ。

```
theorem residual_stable_line_fixed_or_cofixed
    [Fact p.Prime]
    (S : Frey.Source p)
    (hp5 : 5 ≤ p)
    (hbe : Even S.b)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : Module.finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) :
    IsFixedOn S.residualRepresentation L ∨
      IsCofixedOn S.residualRepresentation L
```

これはまさに、NOTE-030-008 で未解決として残した `hcases` の証明じゃ。

そして既存の、

`residual_exists_cofixed_line_of_oriented`

へ渡す。

その結果、

\[ \boxed{ \neg\operatorname{Irreducible}(\rho_{E,p}) \Longrightarrow \exists L,\quad \operatorname{Stable}(L) \land \operatorname{Cofixed}(L) } \]

を導ける。

ここまで完成すれば、既約性へ至る障害は `hno` 一つになる。

## 9. 実装上の重要な判断

今回の模範解答を読んで、わっちが特に注意したいのは実装コストの分布じゃ。

| 段階    | 数学的難度の見立て | 特に注意する依存                        |
| ------- | ------------------ | --------------------------------------- |
| 031-001 | 高                 | 数体の不分岐拡大、慣性群、大域化        |
| 031-002 | 中〜高             | 楕円曲線の還元理論、判別式、\(c_4\)     |
| 031-003 | 非常に高           | 野生慣性、Frobenius 共役、局所作用      |
| 031-004 | 非常に高           | \(p\) での還元、零成分、局所 filtration |
| 031-005 | 低〜中             | 既存定理の接続、同じ Source の保持      |

これは実際の Lean ビルド工数を測定したものではなく、模範解答の依存関係からの見立てじゃ。

特に 031-003 と 031-004 は、模範解答の最終定理だけを見ると短く見えるが、その下に深い局所数論が存在している。

したがって、各ステップは次の三層に分けることを勧める。

1. 数学的な一般核：線形代数、慣性群、付値環の補題。`DkMath.Lib.*` に置く。
2. Frey 専用の算術：判別式、還元、向き付け、局所作用。`DkMath.FLT.Frey*` に置く。
3. 公開接続：NOTE-030 の固定点消滅と統合して `hcases` を供給する。

NOTE-030 と同様、条件付き定理の存在と、その算術的条件の実証を厳密に区別することも重要じゃ。

## 10. NOTE-031 完成後の研究位置

最後に全体を整理しよう。

\[ \boxed{ \begin{gathered} \text{NOTE-028：幾何学的 Weil 対}\\ \downarrow\\ \det\rho=\chi_p\\ \downarrow\\ \text{NOTE-029：可約なら安定直線が存在}\\ \downarrow\\ \text{NOTE-030：非零ガロア固定点が存在しない}\\ \downarrow\\ \text{NOTE-031：安定直線は Fixed または Cofixed}\\ \downarrow\\ \text{可約なら Cofixed 直線が存在}\\ \downarrow\\ \boxed{\text{残る課題：Cofixed 直線の不存在}} \end{gathered} } \]

ただし、この研究経路は元の FLT 反例から構成された Frey Source に対するものであり、すべての楕円曲線の残余表現が既約であるという主張ではない。

### 賢狼が最も注目する核心

NOTE-030 では、点の座標に現れる数値的な付値を利用した。

NOTE-031 では、その同じ曲線に対するガロア作用を、局所慣性という別の方法で観測する。

つまり、

\[ \text{楕円曲線の座標算術} \quad\longleftrightarrow\quad \text{楕円曲線のガロア表現} \]

という二つの世界を調べることになる。

そして、

\[ \text{局所での変化の制限} \Longrightarrow \text{大域での作用の制限} \]

という原理は、今後の DkMath でも大きな汎用性を持つはずじゃ。

NOTE-031 の成果は、FLT 専用の `hcases` を埋めることだけではなく、局所算術から大域ガロア表現への輸送原理を DkMath.Lib に獲得すること。

わっちは、ここを研究の中心に据えたいのぅ。🐺🍎

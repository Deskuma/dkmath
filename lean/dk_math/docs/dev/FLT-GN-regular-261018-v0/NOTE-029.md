# 🐺🍎 NOTE-028 — 幾何学的 Weil 対、ついに完成！

うむ、ぬしよ。これは大きな到達点じゃ。

NOTE-018 で条件付きの定理として固定した円分行列式が、NOTE-028 で実際の楕円曲線の幾何学から無条件に供給される定理へ変わった。

[NOTE-028 実装報告](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE028-261021.md?utm_source=chatgpt.com)、主要な Lean 証明、依存監査、保存されたビルド記録を照合した。

判定：A・B・C および円分行列式への接続を、証明済み Core として固定することを推奨する。

## 1. 三つの障害は、確かに別々の証明で閉じている

\(L=\overline K(E)\)、\(\mu=[n]^\ast \)、\(H=E[n]\) の平行移動作用群とする。

| 段階 | 成立した定理                 | 証明の核心                                   |
| ---- | ---------------------------- | -------------------------------------------- |
| A    | \([L:\mu(L)]\le n^2\)        | 除法多項式と反転作用                         |
| B    | \(L^H=\mu(L)\)、次数 \(n^2\) | 忠実な作用、固定体定理、次数比較             |
| C    | Weil 双指標の左右非退化性    | 局所付値降下、主素イデアル、点群と類群の対応 |

特に A の実装が興味深い。

以前懸念した「\(x\) 座標の次数だけでは余分な2が出る」という問題を、`QuadraticInvolutionDegree` で解決しておる。

\[ [L:\mu(L)]\le 2n^2 \]

という粗い評価で止まらず、反転で \(y\) が動くことと、\([n]\) 倍された一般点が非零であることを組み合わせた。

その結果、

\[ \boxed{L=\mu(L)(x)} \]

まで示し、必要な \(n^2\) の上界を得ている。

そして B では、

\[ |H|=|E[n]|=n^2 \]

から

\[ [L:L^H]=n^2 \]

を得て、二つの部分体が等しいことを証明した。

これは NOTE-019 の位数公式が、NOTE-028 で再び決定的な役割を果たしたということじゃな。

## 2. 非退化性は「主イデアルへの帰還」で閉じた

わっちが最も注目したのは C の証明じゃ。

目標は、

\[ \boxed{ \bigl(\forall S\in E[n],\ e_n(S,T)=1\bigr) \Longrightarrow T=O. } \]

仮定により、\(w_{n,T}\) はすべての torsion 平行移動で不変になる。

B の固定体同定から、

\[ w_{n,T}=[n]^\ast h \]

という実際の関数 \(h\) が存在する。

そこから今回は、無限遠点を含む因子全体の引き戻し公式を新たに完成させる道ではなく、有限点の局所付値上界と一重零点の情報を使っている。

その結果、\(T\ne O\) と仮定した場合、点 \(T\) に対応するイデアルが主となることを導く。

\[ \mathfrak m_T=(r). \]

ところが、NOTE-022 までに完成させた点群と類群の対応により、

\[ \mathfrak m_T\text{ が主}\Longrightarrow T=O. \]

これで矛盾が成立する。

つまり、

\[ \boxed{ \text{不変関数} \longrightarrow \text{倍写像からの降下} \longrightarrow \text{主点イデアル} \longrightarrow T=O } \]

という証明が完成した。

NOTE-022 で作った点群と類群の橋が、NOTE-028 で非退化性を証明する最後の鍵になった。

これは非常に美しい構造じゃ。

## 3. ついに `WeilPairingData` の仮定が消えた

実際のソース [`EllipticGeometricWeilPairing.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticGeometricWeilPairing.lean?utm_source=chatgpt.com) を確認した。

そこでは、新しい形式的な対を仮定するのではなく、既存の

```
weilTranslationUnit
```

を使って `geometricRootPairing` を構成している。

そして、

```
geometricWeilPairingData
```

が、次の四性質を実際の証明から受け取る。

- 左右の加法性：NOTE-025・026
- 交代性：NOTE-026
- ガロア同変性：NOTE-027
- 非退化性：NOTE-028

重要なのは、対の値が NOTE-025 から変わっていないことじゃ。

これが形式化の連続性を保証している。

そして、とうとう次の定理が成立した。

```
theorem torsion_determinant_eq_cyclotomic :
    determinantCharacterWithBasis
        (representation E p)
        (torsionBasis E p) =
      cyclotomicCharacter p
```

ここには `WeilPairingData` という追加入力がない。

数学的には、標数0の体 \(K\) 上の楕円曲線 \(E\) と素数 \(p\) に対して、

\[ \boxed{ \det\rho_{E,p}=\chi_p } \]

を証明したことになる。

さらに [`FreyGeometricWeilPairing.lean`](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/FLT/FreyGeometricWeilPairing.lean?utm_source=chatgpt.com) では、

```
theorem residual_determinant_eq_cyclotomic :
    S.residualDeterminantCharacter =
      cyclotomicCharacter p
```

が成立している。

これも、実際の Frey Source の同じ残余表現についての定理じゃ。

## 4. 監査の評価

保存された検証記録から、次を確認した。

| 項目                      | 結果             |
| ------------------------- | ---------------- |
| 本体宣言                  | 66               |
| 回帰宣言                  | 20               |
| 依存監査                  | 21経路成功       |
| 統合ビルド                | 11,658 jobs 成功 |
| 追加コードの公理          | 標準論理公理のみ |
| NOTE-028 内の `sorry`     | なし             |
| ルート import・直接テスト | 成功             |

特に、依存監査の設計が適切じゃ。

幾何学 Core では `WeilPairingData` の借用を禁止し、最後のデータ構成・行列式アダプタでのみ、その構成済みデータを利用できるようにしている。

したがって、少なくとも監査対象では、

「Weil 対を仮定して Weil 対を証明した」

という循環的な構造になっていないことを確認できる。

わっち自身が独立に Lean ビルドしたわけではないが、報告された検証結果と取得したソースには整合性がある。既存の別モジュールの `sorry` 警告5件は引き続き区別する必要がある。

## 5. これで FLT のどこまで到達したか

ここは重要じゃから、境界を明確にしておこう。

現在の Frey 表現について、

\[ \rho_{E,p}:G_{\mathbb Q}\longrightarrow \mathrm{GL}_2(\mathbb F_p) \]

は実際の楕円曲線のねじれ点群から構成されている。

そして今、

\[ \boxed{\det\rho_{E,p}=\chi_p} \]

が無条件で証明された。

しかし、この等式だけでは表現が既約であることは導けない。

例えば上三角表現でも、対角成分の積を円分指標にできる。

\[ \rho(\sigma)= \begin{pmatrix} \alpha(\sigma)&\ast \\ 0&\beta(\sigma) \end{pmatrix}, \qquad \alpha\beta=\chi_p. \]

この表現には不変直線が存在するため、可約じゃ。

したがって、円分行列式と既約性は独立した証明課題として扱う必要がある。

### NOTE-029 の推奨

次は、Frey 残余表現の既約性に向けて、まずその算術的な判定条件を固定することを推奨する。

具体的には、既存の `IsIrreducible` と安定直線の定理を入口にし、

\[ \rho_{E,p}\text{ が可約} \]

と仮定した場合に、どのようなガロア安定部分群、あるいは有理 \(p\)-isogeny が生じるかを定式化する。

そして、その存在を排除するために必要な算術定理を特定する。

ここからは局所慣性、導手、Mazur 型の有理 isogeny 制約などが関係する。FLT に必要な素数範囲を明示し、すべての素数について既約性を主張しないことが大切じゃ。

## 6. NOTE-018 から NOTE-028 までを振り返る

今回で、一つの大きな研究単位が完成したと考えてよい。

\[ \boxed{ \begin{gathered} \text{実際の楕円曲線}\\ \Downarrow\\ E[p]\simeq(\mathbb F_p)^2\\ \Downarrow\\ \text{全指数ねじれ点・倍写像の全射性}\\ \Downarrow\\ \text{関数体・Dedekind 性・平行移動}\\ \Downarrow\\ \text{主イデアルと Weil 関数}\\ \Downarrow\\ \text{付値・平行移動の固有値}\\ \Downarrow\\ \text{交代的双指標}\\ \Downarrow\\ \text{ガロア同変性・非退化性}\\ \Downarrow\\ \boxed{\text{幾何学的 Weil 対}}\\ \Downarrow\\ \boxed{\det\rho_{E,p}=\chi_p} \end{gathered} } \]

ここで目を引くのは、複数の数学分野を横断していることじゃ。

最初は除法多項式だった。

次に有限群と短完全列。

さらに Dedekind 整域、類群、関数体、離散付値、固定体、ガロア表現。

それらを単に並べたのではなく、定理の依存関係として実際に接続している。

そして最終的には、NOTE-018 で用意した条件付きの受け口へ戻ってきた。

入力として必要だったものを、一つずつ実際の数学から供給し終えたわけじゃな。

これは DkMath の Core を先に固定してから分野を横断する研究方針が、実際に機能した具体例と言える。

NOTE-028 完了。幾何学的 Weil 対と円分行列式の無条件化、達成じゃ。 🍎

長い道のりであったが、ここには確かに、一つの完成した数学があるのぅ。

---

## 模範解答例

模範解答（Anthropic の `fermats-last-theorem`）では、Frey 曲線の残余表現の既約性を、独立した大定理 `FreyPackage.Mazur_Frey` として証明しておる。

NOTE-028 で DkMath が完成させた Weil 対・円分行列式の次には、まさにこの定理が対応する。

興味深いのは、模範解答が既約性を行列式から直接導いていないことじゃ。

代わりに、

\[ \boxed{ \text{可約性} \Longrightarrow \text{特定のガロア安定直線の存在} \Longrightarrow \text{算術的な矛盾} } \]

という反証法を採用している。

実際の終点は次の定理じゃ。

```
theorem FreyPackage.Mazur_Frey (P : FreyPackage) :
    GaloisRepIsIrreducible
      (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p
```

参照：[模範解答 ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_Mazur_Frey.lean?utm_source=chatgpt.com)[`Mazur_Frey`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_Mazur_Frey.lean?utm_source=chatgpt.com)

そして、この証明は 指数 \(p\) の大きさと、Frey 曲線の係数 \(a\) の合同条件によって場合分けされている。

## 1. 模範解答の分岐構造

実際の [`S_FreyPackage_Mazur_Frey.lean`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_Mazur_Frey.lean?utm_source=chatgpt.com) の証明部分を抜き出すと、次の構造じゃ。

```
private theorem mazurM3asmB_of_no_cofixed (P : FreyPackage) :
    GaloisRepIsIrreducible
      (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by
  by_contra hred

  have hN : HasGaloisStableCofixedLine
      (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p :=
    FreyPackage.frey_reducible_hasCofixedLine P hred

  rcases mazurM3asmB_exponent_trichotomy
      P.p P.pp P.hp5 with hsmall | h11 | h17

  · exact FreyPackage.frey_no_cofixed_small P hsmall hN
  · exact FreyPackage.frey_no_cofixed_eleven P h11 hN
  · exact FreyPackage.frey_no_cofixed_large P h17 hN
```

最終定理では、これに \(a\equiv3\pmod8\) の特別分岐を加えている。

| 条件               | 模範解答の方法                                     |
| ------------------ | -------------------------------------------------- |
| \(a\equiv3\pmod8\) | 素数2での局所慣性・分岐交換を使う                  |
| \(p=5,7,13\)       | FLT を別途証明済みなので反例パッケージが存在しない |
| \(p=11\)           | 同じく FLT11 の成立から排除                        |
| \(p\ge17\)         | Mazur の Eisenstein ideal とモジュラー曲線の理論   |

驚くべき点は、\(p=7,11,13\) では既約性を直接証明していないことじゃ。

既に FLT を証明しているので、仮定した FreyPackage 自体が矛盾する、という方法を採用している。

### 2. 可約性から cofixed line を得る

重要な中間定理は、

[`frey_reducible_hasCofixedLine`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean?utm_source=chatgpt.com)

じゃ。

可約と仮定すれば、非零かつ真のガロア安定部分加群 \(N\subset E[p]\) が存在する。

模範解答では、局所慣性作用を調べ、次の二択を導く。

\[ \begin{cases} \text{ガロア群が }N\text{ 上で自明に作用する},\\ \text{ガロア群が }E[p]/N\text{ 上で自明に作用する}. \end{cases} \]

一方、Frey 曲線には非零の有理 \(p\)-torsion 点が存在しないことも、独立に証明している。

したがって第一の場合は矛盾。

残るのが第二の場合、すなわち cofixed line じゃ。

\[ \boxed{ \forall \sigma\in G_{\mathbb Q},\ \forall x\in E[p],\ \rho(\sigma)x-x\in N } \]

これは、商 \(E[p]/N\) へのガロア作用が自明であることを表している。

そして、模範解答はこのような \(N\) が存在しないことを証明する。

注目すべきは、この段階に既に局所慣性の情報が入っていることじゃ。単なる二次元線形代数ではない。

### 3. \(p\ge17\) では Mazur の本格的な算術幾何へ進む

ここが最も重い。

[`frey_no_cofixed_large`](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean?utm_source=chatgpt.com)

は約1,450行の証明モジュールじゃ。

その下には模範解答の公式解説によれば、約5,400個の定理が依存しており、うち約2,400個が `ModularCurve` 名前空間に属する。

中心となる数学は、

- 楕円曲線の乗法的還元と局所慣性
- Frobenius とガロア表現の行列式
- \(X_0(N)\) とその Jacobian \(J_0(N)\)
- Néron model と特殊ファイバー
- Eisenstein ideal・Eisenstein quotient
- Mazur の Step 3

という構成じゃ。

中心にある大定理は、

[`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](https://github.com/anthropics/fermats-last-theorem/blob/main/Theorems/Thm_WeierstrassCurve_mazurStepThree_not_inZeroComponentAt.lean?utm_source=chatgpt.com)

になる。

そしてこの大規模な証明には、円分行列式が実際に使われている。

模範解答の `tw_det_eq_cyclo` は、楕円曲線のガロア作用の行列式を円分指標の指数と一致させる補題じゃ。

ここで、DkMath NOTE-028 が完成させた無条件の行列式公式を再利用できる可能性がある。

ただし、模範解答の残りの Mazur 理論まで省略できるわけではない。

## 4. DkMath と模範解答の重要な違い

ここは FLT7 の研究に直結する。

模範解答の \(p=7\) 分岐は、

```
fermatLastTheoremSeven
```

を参照している。

その証明は、正則素数に対する Kummer の定理と、7次円分体の整数環が PID であることから組み立てられている。

つまり依存関係は、

\[ \boxed{ \text{Kummer による FLT7} \Longrightarrow \text{FLT7 反例の不在} \Longrightarrow \text{FreyPackage の既約性} } \]

なのじゃ。

従って、DkMath が FLT7 を証明するためにこの既約性定理を使おうとすると、循環依存になる可能性がある。

模範解答では、FLT7 を別の経路で先に閉じているから問題にならない。

一方、DkMath は GN-Kummer・GTail など、独自の可除性 Core から FLT7 の無条件化を進めてきた。

その経路と、Mazur の大規模なモジュラー曲線の経路は分けておくべきじゃろう。

## 5. 賢狼が考える NOTE-029 の最適な切り方

模範解答を踏まえると、最初から Mazur の巨大な定理群を移植するのは得策ではない。

まず次の三つを固定するのがよい。

| 段階  | Core                                                 | DkMath にある入力       |
| ----- | ---------------------------------------------------- | ----------------------- |
| 029-A | 可約性から安定直線を抽出                             | `IsGaloisStable`、階数2 |
| 029-B | 局所慣性から fixed / cofixed の二択                  | 残余表現、円分行列式    |
| 029-C | 非零有理 \(p\)-torsion の不在と cofixed への絞り込み | Frey 曲線、ガロア作用   |

特に 029-B は、NOTE-028 で獲得した

\[ \det\rho_{E,p}=\chi_p \]

を使う新しい算術的入口になる。

その先で、既約性を直接閉じる方法を検討する。

ただし 029-B 自体には局所還元・慣性群の整備が必要で、行列式だけで fixed/cofixed の二択は出ない点に注意じゃ。

## 結論

模範解答は、Weil 対で行列式を確定した後、Mazur の理論で Frey 表現の既約性を証明するという正統的な経路を採用している。

ただし、

- \(p=5,7,11,13\) については、先に FLT を証明して場合を消している。
- \(p\ge17\) については、モジュラー曲線と Eisenstein ideal を使った非常に大きな証明を構築している。
- \(a\equiv3\pmod8\) については、素数2での局所情報を利用して別経路で排除している。

DkMath にとって最大の参考部分は、`frey_reducible_hasCofixedLine` の前段にある局所慣性と線形代数の結合じゃ。

NOTE-028 で完成した Weil 対は、そこへ供給する幾何学的 Core として十分に重要な役割を持つ。

ただし、FLT7 の直接証明を優先するなら、模範解答の Kummer 経路と GN-Kummer の比較も並行して価値がある。

わっちの見立てでは、次に着手するなら 「可約性 → 安定直線 → fixed/cofixed」までを独立した Core として形式化するのが、最も再利用性の高い一手じゃな。🐺🍎

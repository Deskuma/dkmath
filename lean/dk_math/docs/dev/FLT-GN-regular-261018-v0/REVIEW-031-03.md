# 🐺🍎 DkMath NOTE-031-003 実装レビュー

対象：`Deskuma/dkmath` ブランチ：`dev/FLT-GN-regular-261018-v0` 確認した先頭コミット：[`4258a1c`](https://github.com/Deskuma/dkmath/commit/4258a1c1b8b906e355c7a420e16063d4042ba3a7?utm_source=chatgpt.com)

031-003 は、実装報告書上では完了しており、最終定理の目標も明確に達成されている。 今回は条件付きの線形代数だけで終わらず、Frobenius 元の構成、野生慣性の作用の消去、Frey 残余表現への接続まで実装している。

報告書は [IMPLEMENTATION-NOTE031-003-261023.md](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/IMPLEMENTATION-NOTE031-003-261023.md?utm_source=chatgpt.com)。

## 1. 何が完成したか

最終目標は、奇素数 \(p\) に対する Frey 曲線の残余表現

\[ \rho_{E,p}:G_{\mathbb Q}\longrightarrow\operatorname{GL}(E[p]) \]

と、非零かつ真のガロア安定部分加群

\[ 0\ne N\subsetneq E[p] \]

について、素数2上のすべての慣性元 \(\tau\) が

\[ \boxed{ \begin{aligned} \rho(\tau)x&=x &&(x\in N),\\ \rho(\tau)y-y&\in N &&(y\in E[p]) \end{aligned} } \]

を満たすことじゃ。

すなわち、

\[ \boxed{ \operatorname{FixedOn}(\rho,N,I_2) \land \operatorname{CofixedOn}(\rho,N,I_2) } \]

が成立する。

これは \(E[p]\) 全体への慣性作用が恒等写像であることより弱い。安定直線上と、その商空間上で作用が恒等であればよい。

この違いを実装が保持している点は重要じゃ。

## 2. 確認したコミット

今回の開発は、主に次の3コミットとマージで構成されていた。

| コミット                                                                                                              | 内容                                     |
| --------------------------------------------------------------------------------------------------------------------- | ---------------------------------------- |
| [`bb5dfc1`](https://github.com/Deskuma/dkmath/commit/bb5dfc1d1122e90e860310810e84e3bcc20e3c49?utm_source=chatgpt.com) | 共役二乗関係から安定直線と商の固定を証明 |
| [`1a5c47e`](https://github.com/Deskuma/dkmath/commit/1a5c47e868b9a38f1b2938398c7ef97af57c0d3e?utm_source=chatgpt.com) | 2進慣性の算術を供給し、最終定理へ接続    |
| [`f199106`](https://github.com/Deskuma/dkmath/commit/f19910693bf41e21de8971917ef8675ae5015b2b?utm_source=chatgpt.com) | 回帰、依存監査、完了報告                 |
| [`4258a1c`](https://github.com/Deskuma/dkmath/commit/4258a1c1b8b906e355c7a420e16063d4042ba3a7?utm_source=chatgpt.com) | 指定開発ブランチへ統合                   |

前回の 031-002 が多数の部分段階に分かれたのに対し、031-003 は比較的まとまったコミット履歴じゃ。

しかし数学的に浅いわけではない。最終定理が短くても、その背後の局所ガロア理論はかなり深い。

## 3. 数学的な証明経路の検証

Lean 本体を確認すると、証明は次の順序で接続されていた。

\[ \boxed{ \begin{gathered} \text{素数2上の Frobenius 元 }\varphi\text{ の構成}\\ \downarrow\\ \omega=\varphi\tau\varphi^{-1}(\tau^2)^{-1}\\ \downarrow\\ \omega\text{ が野生慣性型の合同を満たす}\\ \downarrow\\ \omega\text{ は実際の }E[p]\text{ の全点を固定}\\ \downarrow\\ \rho(\varphi)\rho(\tau)\rho(\varphi)^{-1} =\rho(\tau)^2\\ \downarrow\\ N\text{ と }E[p]/N\text{ で }\rho(\tau)=1 \end{gathered} } \]

重要なのは、この経路に `hcases` や `hno` が入り込んでいないことじゃ。

### 3.1 Frobenius 元は実際に構成されている

確認先：

[Frobenius の構成 — ValuationFrobenius.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/ValuationFrobenius.lean?utm_source=chatgpt.com)

`exists_isFrobeniusAt_of_liesOverPrime` は、任意の素数 \(q\) と、その上の付値環 \(A\) について、剰余体上で \(q\) 乗写像として作用するガロア元 \(\varphi\) を構成する。

証明では、代数的整数の剰余環に Frobenius 自己同型を作り、それをガロア元へ持ち上げている。

実際のコードには、

```
Ideal.Quotient.stabilizerHom_surjective_of_profinite
```

が現れる。

つまり Frobenius の存在を外部引数として要求せず、profinite ガロア作用の既存定理から導出している。

また、031-001 で作った分数表示を使って、代数的整数の剰余環から付値環全体の剰余体へ作用を拡張していた。

一般ライブラリとして独立性の高い成果じゃ。

### 3.2 共役二乗関係の「誤差」が消えている

確認先：

[穏分岐指標 — ValuationTameCharacter.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/ValuationTameCharacter.lean?utm_source=chatgpt.com)

ここでは、非零元 \(z\) に対して、慣性元 \(\tau\) の作用比

\[ \frac{\tau(z)}z \]

を剰余体へ写す。

この穏分岐指標に対して、Frobenius 共役が \(q\) 乗として作用することを証明している。

その結果、

\[ \omega=\varphi\tau\varphi^{-1}(\tau^q)^{-1} \]

について、

\[ \boxed{ \frac{\omega(z)}z\equiv1\pmod{\mathfrak m_A} \qquad(z\ne0) } \]

が得られる。

ここで重要なのは、\(\omega\) のガロア作用そのものを恒等と仮定していないことじゃ。

まず剰余体での合同を証明し、その後で楕円曲線の torsion 点への作用を調べている。

この二段階の区別は正しく保持されておる。

### 3.3 野生合同から実際の点の固定まで証明されている

確認先：

[EllipticDyadicWildInertia.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/EllipticDyadicWildInertia.lean?utm_source=chatgpt.com)

今回、最も難しい算術的な部分はここじゃ。

曲線の係数条件

\[ a_1=1,\qquad a_3=a_6=0,\qquad a_4\ne0 \]

の下で、非零の奇数位数 torsion 点 \(P=(x,y)\) に対し、

\[ \boxed{v(a_4)\le v(x)} \]

を証明している。

この評価には、2-torsion 点 \(T=(0,0)\) との加法と、倍点公式が使われている。

さらに、点の座標を二つの場合に分ける。

- \(x\) が単元の場合：座標の剰余合同を利用する。
- \(x\) が非単元の場合：\(y/x\) の整性と、\(x\) の乗法的合同を利用する。

どちらも、野生合同から差点

\[ \sigma P-P \]

が無限遠点であるか、有限なら座標に極を持つことを導く。

ところが差点も同じ奇数位数の torsion 点だから、既存の除法多項式による整性が適用できる。

よって極を持つ有限点の場合は排除され、

\[ \boxed{\sigma P=P} \]

となる。

この最終部分は `fixed_of_wild` の証明本体で確認できた。

野生合同を点の固定と取り違える飛躍は見つからなかった。

## 4. 線形代数側の検証

確認先：

[ConjugateSquare.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/RepresentationTheory/ConjugateSquare.lean?utm_source=chatgpt.com)

ここでは二次元ベクトル空間 \(V\)、非零真部分空間 \(N\)、線形作用素 \(T,M,M'\) に対し、

\[ MM'=I,\qquad MTM'=T^2 \]

から、\(N\) 上と \(V/N\) 上の \(T\) が恒等になることを証明している。

この証明は数論に依存しない。

一次元で \(T\) の作用をスカラー \(c\) とすると、

\[ c=c^2 \]

となり、単射性から \(c=0\) を排除できるので \(c=1\)。

商空間でも同じ議論が成立することを、有限次元の単射・全射関係を使って証明している。

### 回帰が特に良い

\(\mathbb F_3^2\) 上で、

\[ T= \begin{pmatrix} 1&1\\ 0&1 \end{pmatrix}, \qquad M= \begin{pmatrix} 2&0\\ 0&1 \end{pmatrix} \]

を使用している。

これは、

\[ MTM^{-1}=T^2 \]

を満たすが、

\[ T\ne I. \]

それでも水平直線 \(N\) と商 \(V/N\) では作用が恒等となる。

この回帰は重要じゃ。

なぜなら 031-003 の結論を誤って

\[ \rho(\tau)=I\quad\text{on }E[p] \]

に強めることを防いでいるからじゃ。

031-002 と 031-003 の違いが、実際の反例によって検証されている。

## 5. 最終 API の型と依存関係

確認先：

[FreyDyadicInertia.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/FLT/FreyDyadicInertia.lean?utm_source=chatgpt.com)

最終定理は次の通り。

```
theorem residual_fixed_and_cofixed_at_two
    (hp2 : p ≠ 2)
    (N : Submodule (ZMod p) S.ResidualSpace)
    (hN : IsStable S.residualRepresentation N)
    (hbot : N ≠ ⊥)
    (htop : N ≠ ⊤)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : LiesOverPrime A 2) :
    FixedOn S.residualRepresentation N
      (inertiaSubgroupIn A ℚ) ∧
    CofixedOn S.residualRepresentation N
      (inertiaSubgroupIn A ℚ)
```

この型を読む限り、Frobenius 元や野生慣性の消滅、共役二乗関係を外部入力に要求していない。

実際の証明では、

`residual_exists_dyadic_conjugate_square`

から Frobenius 元と関係式を取得し、

`ConjugateSquare.eq_id_on_line_of_conj_eq_sq`

へ渡している。

また、既存の `S.IsGaloisStable N` は表現の `IsStable` と定義上対応していることも確認した。したがって、031-005 で既存の安定直線を受け取る際に、別の安定性概念を導入してしまう問題は見当たらない。

ただし、安定直線 \(N\) の存在は 031-003 の結論ではない。その存在は NOTE-029 の可約性からの抽出が担当する。

## 6. 検証記録の監査

保存された [validation-note031-003.txt](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/evidence/validation-note031-003.txt?utm_source=chatgpt.com) と監査ソースを確認した。

| 項目                        | 記録された結果                              |
| --------------------------- | ------------------------------------------- |
| Lean                        | 4.34.1                                      |
| Mathlib                     | `d13f23b7...`                               |
| 本体の公開宣言              | 82個                                        |
| 回帰の公開宣言              | 6個                                         |
| 型・証明本体の依存監査      | 10経路                                      |
| 公開入力監査                | 4件                                         |
| 集中ビルド                  | 3,230 jobs 成功                             |
| 統合ビルド                  | 11,765 jobs 成功                            |
| 新規コードの警告・エラー    | なしとの記録                                |
| 許容公理                    | `propext`, `Classical.choice`, `Quot.sound` |
| 既存の無関係な `sorry` 警告 | 5件                                         |

依存監査の本体も確認した。

特に、最終定理から `ConjugateSquare`、`residual_finrank_eq_two`、共役二乗関係の定理へ到達することを要求している。

また、野生慣性を消す補題から、除法多項式の整性と実際の座標比較への依存も検査されている。

単なる定理名の存在確認ではなく、型と証明本体を辿る検査じゃ。

もちろん、わっち自身は今回 Lean ビルドを再実行していない。ここでのビルド・公理監査の合格は、保存された検証記録に基づく判断じゃよ。

## 7. 気になった境界と留意点

重大な数学的欠陥は、確認した範囲では見つからなかった。

ただし、次の境界は保持すべきじゃ。

① 野生慣性の議論と慣性群全体の議論は異なる。

今回の構成は、共役二乗関係の誤差元 \(\omega\) が野生慣性型の合同を満たし、その元が \(E[p]\) を固定することを示している。

そこからすべての \(\tau\in I_2\) について共役二乗関係を得て、直線・商の固定を結論する。

すべての慣性元が野生合同を満たすと主張しているわけではない。この区別は適切じゃ。

② \(p\ge5\) や \(b\) 偶数を要求していない。

031-003 は奇素数 \(p\) で成立する。NOTE-030 の有理 torsion 排除とは適用範囲が異なる。

これは不自然な仮定の省略ではなく、必要な係数整性を同じ Source から供給した結果と確認できた。

③ 回帰の指数37は条件付きの特殊化である。

`source37_fixed_cofixed` は任意の `Source 37` を入力に取る。実在する Fermat 反例や Source を構成しているわけではない。

一方、非恒等な線形作用の回帰は実際に構成されているため、線形代数の結論が空虚でないことは確認できる。

## 8. 総合判定

| 評価対象                | 判定     |
| ----------------------- | -------- |
| 031-003 の数学的目標    | 達成     |
| Frobenius 元の構成      | 確認済み |
| 野生合同の証明          | 確認済み |
| 実際の torsion 点の固定 | 確認済み |
| 共役二乗関係            | 確認済み |
| 同じ安定直線・商の固定  | 確認済み |
| 独立した再ビルド        | 未実施   |
| NOTE-031 全体           | 未完成   |

### 賢狼の研究評価

今回の成果は、031-002 ときれいに対になっておる。

\[ \boxed{ \begin{aligned} q\ne2,p:\quad& \rho(\tau)=I &&\text{全残余空間}\\[2mm] q=2:\quad& \rho(\tau)|_N=I,\quad \overline{\rho}(\tau)=I &&\text{直線と商} \end{aligned} } \]

これで、局所大域輸送に必要な素数のうち、\(p\) 自身を除いたすべての素数が処理された。

また、031-003 は `DkMath.Lib` に二つの重要な一般原理を追加した。

一つは、Frobenius と慣性群の共役関係を、付値環上の合同として厳密に表現する原理。

もう一つは、共役によって二乗になる線形作用が、保存する一次元空間とその商で恒等になる原理じゃ。

これらは Frey 曲線に閉じた道具ではない。

結論：NOTE-031-003 は、指定ブランチの現行実装について、ソースレビューおよび保存された検証記録の照合に合格。完了として固定してよい。

次の 031-004 は \(q=p\) の局所二択。ここは Fixed と Cofixed の両方ではなく、どちらか一方を全慣性群について一貫して選ぶ必要がある。今回とは別種の算術的な難所になるのぅ。

031-003、見事に閉じたぞ！ 🐺🍎

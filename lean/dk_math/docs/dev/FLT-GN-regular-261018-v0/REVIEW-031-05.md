# 🐺🍎 DkMath NOTE-031-005 実装レビュー

対象：`Deskuma/dkmath` ブランチ：`dev/FLT-GN-regular-261018-v0` 確認した HEAD：[`19e927dbf2e414af7551c8b02d75484579aa4b03`](https://github.com/Deskuma/dkmath/commit/19e927dbf2e414af7551c8b02d75484579aa4b03?utm_source=chatgpt.com)

## 1. 結論：`hcases` の実装が完成した

指定ブランチへのマージを確認した。前回の 031-004 から 4コミット進み、031-005 の実装が統合されている。

今回の最大の成果は、NOTE-029 以来、外部仮定として残っていた

\[ \boxed{ \operatorname{Stable}(L) \Longrightarrow \operatorname{Fixed}(L)\lor\operatorname{Cofixed}(L) } \]

を、同じ Frey Source の局所算術から導出する定理として実装したことじゃ。

実際に [FreyStableLineLocalGlobal.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/FLT/FreyStableLineLocalGlobal.lean?utm_source=chatgpt.com) を読み、`residual_stable_line_fixed_or_cofixed` の宣言と証明本体を確認した。

```
theorem residual_stable_line_fixed_or_cofixed (hp5 : 5 ≤ p)
    (L : Submodule (ZMod p) S.ResidualSpace)
    (hline : finrank (ZMod p) L = 1)
    (hstable : S.IsGaloisStable L) :
    IsFixedOn S.residualRepresentation L ∨
    IsCofixedOn S.residualRepresentation L
```

暗黙の入力は `[Fact p.Prime]` と同じ `Source p`。`hcases`、局所慣性の固定性、Frobenius、吸収空間などを新たな仮定として要求しない。

しかも、大域二択そのものには `Even S.b` も不要じゃ。

\(p\ge5\) における `hcases` の数学的な穴は、公開定理の水準で埋まっている。

ただし、これは残余表現の既約性そのものの証明ではない。その境界は後ほど厳密に区別する。

## 2. 局所三経路の合流を検証

031-005 の最初の定理は、

`residual_inertia_common_side_of_stable`

じゃ。

Lean 本体の証明は、まず 031-004 の

```
S.residual_common_side_at_p hp5 N hN hbot htop
```

を呼び、そこで得た Fixed/Cofixed の側を一度だけ選択している。

その後、任意の素数 \(q\) と、その上の付値環 \(A\) について場合分けする。

| 場合        | 使用する定理                               | 得られる条件            |
| ----------- | ------------------------------------------ | ----------------------- |
| \(q=p\)     | `residual_common_side_at_p`                | 選択済みの一方          |
| \(q=2\)     | `residual_fixed_and_cofixed_at_two`        | Fixed と Cofixed の両方 |
| \(q\ne2,p\) | `residual_fixed_and_cofixed_away_two_self` | Fixed と Cofixed の両方 |

この構成は正しい。

特に、

\[ \forall q,\quad \bigl(\operatorname{Fixed}_q\lor\operatorname{Cofixed}_q\bigr) \]

という弱い条件を大域化に渡してはいない。

実際に得ているのは、

\[ \boxed{ \left(\forall q,\operatorname{Fixed}_q\right) \lor \left(\forall q,\operatorname{Cofixed}_q\right) } \]

じゃ。

031-001 で問題になっていた量化順序が、今回は確実に守られている。

同じ Source、同じ部分加群 \(N\)、同じ商 \(E[p]/N\) を維持したまま三経路が合流していることも確認した。

## 3. 大域化は本当に算術へ接続されているか

次の定理は、

`residual_stable_submodule_fixed_or_cofixed`

じゃ。

証明は短く、

```
S.residual_fixed_or_cofixed_of_inertia_common_side N
  (S.residual_inertia_common_side_of_stable hp5 N hN hbot htop)
```

となっている。

ここで重要なのは、呼び出した先の内容じゃ。

[AbsoluteInertiaRepresentation.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/AbsoluteInertiaRepresentation.lean?utm_source=chatgpt.com) と [AbsoluteInertiaGeneration.lean](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMath/Lib/NumberTheory/AbsoluteInertiaGeneration.lean?utm_source=chatgpt.com) まで遡って確認した。

大域化では、まず残余表現の核が開部分群であることを利用する。

その上で、

\[ H=\{g\in G_{\mathbb Q}\mid \rho(g)|_N=\operatorname{id}_N\} \]

または対応する Cofixed 部分群を考える。

全有限素点の慣性群が \(H\) に含まれるなら、

\[ \boxed{H=G_{\mathbb Q}} \]

と結論する。

その証明は、開部分群から有限正規拡大の固定部分群を取り出し、有限レベルにおける慣性群の生成性へ帰着するものじゃ。

この有限レベルの生成性に Minkowski の判別式評価が使われる。

したがって、031-005 の大域二択は、単なる線形代数や命題論理だけで成立したものではない。

031-001 の数論的な大域化定理を実際に使用している。

依存監査でも、`AbsoluteInertiaGeneration.subgroup_eq_top_of_inertia_le` と `NumberField.abs_discr_gt_two` への到達が要求されていた。

## 4. `hcases` の消去と NOTE-030 の接続

ここが今回の第二の大きな成果じゃ。

NOTE-030 では、\(p\ge5\)、`Even S.b` の下で、

\[ \boxed{E[p]^{G_{\mathbb Q}}=\{0\}} \]

を証明していた。

一方、031-005 では、任意のガロア安定直線 \(L\) について、

\[ \operatorname{Fixed}(L)\lor\operatorname{Cofixed}(L) \]

を得た。

ここで Fixed 側が成立すると、非零直線 \(L\) の全点がガロア固定になる。

これは NOTE-030 の結論に反する。

したがって、

\[ \boxed{ \operatorname{Stable}(L) \Longrightarrow \operatorname{Cofixed}(L) } \]

が成立する。

その定理が、

`residual_stable_line_cofixed_of_oriented`

じゃ。

実装では、以前から存在する

`residual_isCofixedOn_of_oriented`

へ、新たに証明した大域二択を渡している。

重要なのは、この Cofixed 選択が、先ほどの \(p\) 上の局所条件だけで決まるわけではないこと。

局所二択を大域化した後、NOTE-030 の有理 torsion 排除によって Fixed 側を消している。

これで、031-001〜005 と NOTE-030 が一つの証明経路になった。

## 5. 可約性から Cofixed 安定直線を抽出

新しい公開定理、

`residual_exists_cofixed_line_of_not_irreducible`

は次を証明している。

\[ \boxed{ \begin{aligned} &\neg\operatorname{Irreducible}(\rho_{E,p})\\ &\Longrightarrow \exists L\subset E[p],\quad \dim L=1,\quad \operatorname{Stable}(L),\quad \operatorname{Cofixed}(L). \end{aligned} } \]

必要な追加条件は、\(p\ge5\) と `Even S.b` じゃ。

この証明の経路は、

\[ \begin{aligned} \neg\operatorname{Irreducible}(\rho) &\Longrightarrow \exists\text{ 安定直線 }L\\ &\Longrightarrow \operatorname{Fixed}(L)\lor\operatorname{Cofixed}(L)\\ &\Longrightarrow \operatorname{Cofixed}(L). \end{aligned} \]

というもの。

ここで旧 API の

`residual_exists_cofixed_line_of_oriented`

は、従来どおり `hcases` を明示引数に取る一般形として残されている。

新しい定理は、その引数に証明済みの

`residual_stable_line_fixed_or_cofixed`

を渡している。

これは設計上もよい判断じゃ。

旧定理の意味を変更せず、新しい算術的成果を上位 API に追加している。

## 6. 可約性と Cofixed 直線存在の同値

今回さらに興味深い定理が追加されていた。

`residual_not_irreducible_iff_exists_cofixed_line_of_oriented`

じゃ。

これは、同じ向き付き Source に対して、

\[ \boxed{ \begin{aligned} &\neg\operatorname{Irreducible}(\rho)\\ &\qquad\iff\\ &\exists L,\quad \dim L=1\land \operatorname{Stable}(L)\land \operatorname{Cofixed}(L) \end{aligned} } \]

を証明している。

左から右は、今回完成した成果を使う。

右から左は、安定直線が存在すれば既約ではないという、既存の二次元表現の定理から従う。

ここでの重要な意味は、残った未証明条件 `hno` が、正確に既約性の障害として位置づけられたことじゃ。

`hno` は、

\[ \boxed{ \neg\exists L,\quad \dim L=1\land \operatorname{Stable}(L)\land \operatorname{Cofixed}(L) } \]

である。

したがって、今回の成果によって「何を否定できれば既約性が完成するか」が、曖昧さなく一つの命題に固定された。

ただし、この同値は `hno` の証明ではない。

## 7. 整数反例からの入口も確認

`ofCounterexample_residual_exists_cofixed_line`

では、整数

\[ a^p+b^p=c^p \]

を満たす非零の \(a,b,c\) から、既存の `Source.ofCounterexample` を利用している。

この定理は、選択された同じ Source について、

\[ 4\mid S.a+1,\qquad \operatorname{Even}(S.b) \]

を保持する。

加えて、`PrimitiveReduction` と `OrientationTrace` の存在証拠も結論に残している。

その上で、選択済み Source の残余表現が可約なら、Cofixed 安定直線が存在すると結論する。

この実装を確認した結果、元の整数反例と正規化済み Source の座標を無条件に同一視するような操作は見当たらなかった。

また、可約性は引数として明示されている。Fermat 反例や可約性の存在を構成したわけではない。

## 8. 監査とビルドの検証

保存された [validation-note031-005.txt](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/docs/dev/FLT-GN-regular-261018-v0/evidence/validation-note031-005.txt?utm_source=chatgpt.com) を確認した。

| 検証項目                    | 記録された結果                              |
| --------------------------- | ------------------------------------------- |
| 新規公開定理                | 8件                                         |
| 回帰定理                    | 7件                                         |
| 型・証明本体の依存監査      | 12経路                                      |
| 公開入力監査                | 7件                                         |
| 実装集中ビルド              | 4,029 jobs 成功                             |
| 監査込み集中ビルド          | 4,043 jobs 成功                             |
| 統合ビルド                  | 11,789 jobs 成功                            |
| 最終 API の依存公理         | `propext`, `Classical.choice`, `Quot.sound` |
| 新規コードの警告・エラー    | なしとの記録                                |
| 既存の無関係な `sorry` 警告 | 5件                                         |

[依存監査ソース](https://github.com/Deskuma/dkmath/blob/dev/FLT-GN-regular-261018-v0/lean/dk_math/DkMathTest/FLT/Note031StableLineLocalGlobalDependencyAudit.lean?utm_source=chatgpt.com) も確認した。

特に重要なのは、監査が次の依存経路を実際に要求していることじゃ。

- \(p\) 上：031-004 の共通側の二択
- 2上：031-003 の Fixed/Cofixed 両側固定
- その他：031-002 の全残余点の慣性固定
- 大域化：031-001 の絶対慣性生成と Minkowski
- Cofixed 選択：NOTE-030 の有理 torsion 排除と付値軌道

`FoldedValuationOrbit` についても、局所合流・大域二択の証明には依存しない一方、NOTE-030 の固定点排除経路では使われるという違いが、監査に反映されている。

全8本体定理と7回帰定理の公理監査には、標準の論理公理以外を許容しない設定になっていた。

ただし、わっち自身による Lean の独立再ビルドは未実施じゃ。ここでの検証は、GitHub 上のソースコードと保存されたビルド・公理監査記録の照合に基づく。

### 回帰テスト

今回の回帰で特に評価できるのは、次の二つじゃ。

指数2の具体例を使い、\(p\ge5\) の条件を無闇に外せないことを確認している。

また、各局所群では Fixed または Cofixed が成立しても、それぞれ異なる側を選んだ場合には大域二択にならない有限表現を使用している。

後者は、031-005 の最も重要な論理的注意点を、実際の反例として固定したものじゃ。

## 9. NOTE-031 全体の完成状況

これで五段階を改めて整理できる。

| 段階    | 数学的な成果                                | 判定 |
| ------- | ------------------------------------------- | ---- |
| 031-001 | 全局所慣性から大域的 Fixed/Cofixed への輸送 | 完了 |
| 031-002 | \(q\ne2,p\) で全残余点が慣性固定            | 完了 |
| 031-003 | \(q=2\) で安定直線と商がともに慣性固定      | 完了 |
| 031-004 | \(q=p\) で全場所共通の局所二択              | 完了 |
| 031-005 | 三経路の合流、大域二択、`hcases` 供給       | 完了 |

NOTE-029 の段階では、既約性への証明経路に三つの算術的条件が存在した。

\[ \begin{aligned} \texttt{hrat}&:\text{ 有理 }p\text{-torsion の排除},\\ \texttt{hcases}&:\text{ 安定直線の Fixed/Cofixed 二択},\\ \texttt{hno}&:\text{ Cofixed 安定直線の不存在}. \end{aligned} \]

現在は、

\[ \boxed{ \begin{aligned} \texttt{hrat}&:\checkmark\quad\text{NOTE-030}\\ \texttt{hcases}&:\checkmark\quad\text{NOTE-031}\\ \texttt{hno}&:\text{未証明} \end{aligned} } \]

となった。

これは単なる進捗表の更新ではない。

元々外部条件だった三つのうち二つが、実際の Frey 曲線の算術から供給されるようになったという変化じゃ。

## 10. 賢狼の総合判定

NOTE-031-005 は、指定コミット時点でソースレビューと保存された検証記録の照合に合格。実装完了として固定してよい。

今回の証明は約140行の新規本体モジュールにまとまっているが、それは数学が浅かったからではない。

031-001〜004 が複雑な算術を個別に定理化したおかげで、最終段階が明快な合成として書けたのじゃ。

特に、

\[ \boxed{ \text{局所慣性} \longrightarrow \text{全素数共通の側} \longrightarrow \text{大域二択} \longrightarrow \text{Cofixed 安定直線} } \]

という経路が Lean によって一続きになった。

ここから先は、これまでと問題の性格が変わる。

局所算術の不足ではなく、大域的な Cofixed 安定直線の存在を排除する算術が、残された障害となる。

そしてこれは、非零ガロア固定点の排除だけでは解決しない。

Cofixed であっても直線上の作用は非自明であり得るためじゃ。

NOTE-031、全5段階の完了、お見事じゃ。🍎🐺

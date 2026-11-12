# NOTE-030 最終部: 有理torsion排除からガロア固定点の消滅へ

日付: 2026-10-22（JST）。**030-008を実装し、NOTE-030の全8ステップが完了した。**
030-007の有理p-torsion排除を、既存のガロア固定点の有理点への降下に接続した。
素数p≥5・b偶数の同じFrey Sourceについて、同じ残余表現の`NoNonzeroFixed`を証明した。
hratを外部入力に要求しないcofixed抽出・条件付き既約性の入口も追加した。

本体1ファイルに公開定理7個、回帰に定理10個を追加した。
全公開宣言に教科書docstring、全新規Leanファイルに指定の`#print "file: ..."`を付けた。
既存Sourceモジュール2個では説明だけを更新し、通常のFLT・テスト入口へ接続した。
fixed/cofixed二択とcofixed不存在は引き続き別の算術入力であり、無条件既約性・一般FLTは未完成である。

## 1. 公開入口と正確な到達範囲

`DkMath.FLT.FreyRationalTorsionBridge`の中心は次の定理である。

```text
S : Frey.Source p
hp : p.Prime
hp5 : 5 ≤ p
hbe : Even S.b
──────────────────────────────────────────────────────────
S.residual_noNonzeroFixed_of_oriented ... :
  NoNonzeroFixed S.residualRepresentation
```

同じ実際のp-torsion空間を使い、

\[
\forall P\in E[p],\quad (\forall\sigma,\rho(\sigma)P=P)\Longrightarrow P=0
\]

を得る。幾何学的なE[p]そのものが零になるという主張ではない。
既存の幾何学的次元2や位数p²とは両立する。

裸のSourceにp≥5やb偶数を暗黙に追加しない。
既存の正規化を持つSourceではa₄の付値評価にb偶数が必要であり、
a≡3 mod4を別の追加引数として要求する必要はなかった。

## 2. 降下の数学と、今回供給したhrat

固定点Pは同じ曲線の代数閉包上のp-torsion点である。
有限点なら、そのx,y座標は絶対ガロア群の全元で固定される。
標数0の固定体の定理により、両座標はℚからの像となる。
曲線方程式と非特異性を単射な基底変換で引き戻し、同じ有理曲線上の点Qを得る。
無限遠点は最初から零として処理する。

さらにpP=0を基底変換の加法準同型と単射性で引き戻すため、
単なる有理座標の存在だけでなく、実際にpQ=0を満たす有理点へ降下する。
030-007からQ=0となり、その基底変換であるPも零になる。

この一般の降下はNOTE-029の
`EllipticTorsionRepresentation.noNonzeroFixed_iff_rational_torsion`として既存である。
今回の中心証明は、同じSourceの
`residual_noNonzeroFixed_iff_rational_torsion`へ
`rational_p_torsion_eq_zero`を供給するだけで閉じた。

hratを仮定から別名で隠したのではない。
依存経路は、絶対ガロア固定体・基底変換の単射性・同じSourceの係数・実際の付値軌道・整数折り返し核へ到達する。
新しい固定体や降下の証明を再移植する必要はなかった。

## 3. 固定部分加群とcofixedへの入口

| 新しい定理 | 結果と残す条件 |
|---|---|
| `residual_fixed_eq_zero_of_oriented` | 全ガロア元で固定される同じPは零 |
| `residual_fixed_submodule_eq_bot_of_oriented` | 点ごとに固定される部分加群Lは⊥ |
| `residual_isCofixedOn_of_oriented` | L≠⊥とLのfixed/cofixed二択があればcofixed側を選ぶ |
| `residual_exists_cofixed_line_of_oriented` | 可約性hredと全安定直線の二択hcasesからcofixed直線を抽出する |
| `residual_isIrreducible_of_oriented_no_cofixed_line` | hcasesとcofixed不存在hnoが別途得られれば既約となる |

後二つは既存の一般形にhratを今回の証明から供給した薄い入口である。
`[Fact p.Prime]`でFₚを体として扱い、p≥5・b偶数を明示する。

点ごとの固定と、集合としての安定性は異なる。
NoNonzeroFixedは全ての安定直線を消す定理ではない。
またcofixedは商空間の固定条件であり、元の空間に固定ベクトルがあることと同一ではない。
従ってhcasesとhnoは引数に残し、無条件の既約性とは呼ばない。

## 4. 元の整数反例との関係を保持する入口

`Source.ofCounterexample_residual_noNonzeroFixed`は、任意の非零整数反例から選ぶ
**同じ**`Source.ofCounterexample`について、次をまとめて返す。

```text
4 ∣ S.a+1
Even S.b
∃ R : PrimitiveReduction p a b c,
  OrientationTrace R.A R.B R.C S.a S.b S.c
NoNonzeroFixed S.residualRepresentation
```

PrimitiveReductionは元のa,b,cと原始化後のA,B,Cの共通因子scaleを保持し、
OrientationTraceは符号と置換の関係を保持する。
選択済みSを作り直したり、元の座標と正規化後の座標を同一視したりしない。

この入口では、b偶数を`Source.ofCounterexample_spec`から実際に取り出す。
この入口は非零整数と反例等式を明示的な仮定として受け取る。
FLTの完成定理による空虚なSource構成は使わない。

## 5. 回帰で保持した数学的境界

Source 37で、同じ残余点の消滅、NoNonzeroFixed、固定部分加群の消滅、
hrat不要のcofixed抽出、hcases・hnoを残す条件付き既約性を型検査した。
整数反例から選ぶ同じSource 37の正規化証拠を含む入口も検査した。
これらはSourceや整数反例の存在を主張しない。

既存の実在するSource 2には、非零固定2-torsion点がある。
裸のSourceへ条件なしに結論を拡張できない境界を回帰に残した。
この例はb=3であり、p≥5とb偶数の両方を満たさない。p≥5だけの必要性を示す反例とはしない。

さらに、NOTE-029で構成した有限二次元表現

\[
G=\mathbf F_5^\times,\qquad \rho(g)=\operatorname{diag}(g^2,g^3)
\]

について、今回はNoNonzeroFixedを追加で証明した。
g=2では固有値が4と3で、いずれも1でないため、全群で固定される両座標は零になる。
それでも第一軸は一次元の安定部分空間なので可約であり、
第一軸もその商も自明な指標ではないため、fixed/cofixed二択も成り立たない。

この実例はFrey表現や絶対ガロア表現の代用品ではない。
**固定点消滅からhcasesや既約性を導いてはいけない**という線形代数上の境界を検査する。

## 6. NOTE-030の八段階の現在地

| ステップ | 完成した内容 |
|---|---|
| 001 | 零を許すLowerと非零のExact、2進付値の演算 |
| 002 | 同じSourceの係数とγ=p·v₂(b)−4 |
| 003 | 負付値の倍点降下と有限軌道による非負下界 |
| 004 | 単元付値0の排除と正の下界 |
| 005 | T=(0,0)の反射と上界γ−1 |
| 006 | 接線分母のExact、実際の倍点・和差恒等式と非零因子 |
| 007 | 同じQから全七条件を証明し、整数核で有理p-torsion排除 |
| 008 | 固定点の降下へhratを供給し、同じ残余表現の非零固定点を排除 |

次の独立した課題は局所慣性などからのhcases供給と、cofixed直線の不存在hnoである。
これらがそろうと、今回用意した条件付き入口が既約性を返す。
NOTE-030の完成だけから、既約性・モジュラー性・レベル降下・一般FLTは結論しない。

## 7. 依存監査と検証

今回のbridgeはDkMathの既存APIを接続したもので、新たな外部コードの移植は行っていない。
既存の一般降下と030-001〜007の証明・帰属を保持し、再利用した。
`FreyStableLine`と`FreyRationalTorsion`では、未供給だったhratの説明を更新した。
これら二つの既存モジュールではimport・定理の型・証明を変更していない。

`Note030BridgeDependencyAudit`は、新規本体7個・回帰10個の公理を検査する。
主要10経路では型とopaque本体も走査し、絶対ガロア固定体・基底変換の単射性・有理torsion排除・整数核への到達を要求する。
整数反例の入口では同じSourceの選択・仕様・原始化・向き付けへの到達も要求する。
公開型の3検査では、hrat/hzero入力がないことと、必要なhp5・hbe・hcases・hnoが残ることを検査する。

許容公理は`propext`、`Classical.choice`、`Quot.sound`だけである。
旧FLT終点、外部FltRegular/P2M/P2MW/FreyPackage、Kummer終点、sorryAxは禁止する。
有限線形代数の境界例は、Frey・楕円曲線・整数折り返し核に依存しないことも検査する。

focused build（3,277 jobs）、通常ルート・Lib・FLT・テストを含むビルド（11,694 jobs）、
ルートsmoke、テスト入口の直接検査、マーカー照合、`git diff --check`は全て成功した。
新規コードに警告はない。全体ビルドで再掲された既存の別モジュールの`sorry`警告5件は今回の証明経路と区別する。

検証のコマンド・結果は[evidence/validation-note030-008.txt](evidence/validation-note030-008.txt)に記録する。

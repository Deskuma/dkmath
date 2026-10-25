# NOTE-032-005C₂c₁ — 有限次数・モニック関係・条件付き固定体生成

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `69770a06657f9423169e273c674c6c7d2bdabcb9`、作業ツリーはcleanだった。
前回の同じ正規化関数X_H,Y_Hについて、有限正次数・次数の塔・実際のモニック関係を証明した。
正確な次数2|H|,3|H|が供給された場合の固定体生成も証明した。
**総極位数と関数体次数の同定は未供給で、005C₂c全体の完了ではない。**

## 1. 所有者

| 所有者 | 定理・定義 | 内容 |
| --- | --- | --- |
| [TranscendentalFiniteDegree](../../../DkMath/Lib/Algebra/TranscendentalFiniteDegree.lean) | 2定理 | 二元生成からの有限性、超越元の交換 |
| [CoprimeFieldGeneration](../../../DkMath/Lib/Algebra/CoprimeFieldGeneration.lean) | 3定理 | 相対次数・周囲次数から同じ中間体を生成 |
| [EllipticFiniteKernelDegree](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelDegree.lean) | 8定理・1定義 | 同じ二関数の有限正次数、生成体、包含、モニック関係、塔、条件付き生成 |
| [FreyFiniteKernelDegree](../../../DkMath/FLT/FreyFiniteKernelDegree.lean) | 4定理 | 同じSource・同じ直線の構成済み関数への接続 |

合計17定理・1定義。Libの公開宣言には `[DkMath.Lib]` と教科書docstringを付けた。
既存の関数・平行移動・固定体・実点部分群・全点付値の所有者は変更していない。
Lib側では任意の体K、同じ楕円曲線E、代数閉包上の同じ有限実点部分群Hを扱う。
標数0・素数位数・奇数位数・安定性・Cofixed性は要求しない。

## 2. 有限性を正確な次数から切り分ける

kを係数体、Fを同じ全体の関数体とする。まず一般核で

```text
F=k(x,y), yがk(x)上整 ⇒ [F:k(x)]は有限
```

を証明した。同じ二元生成表示が必要であり、yの整関係だけで任意の周囲の体の有限性を結論しない。
楕円関数体では既存の `functionField_adjoin_X_Y` と一般座標の実際の二次関係を使う。
一般x座標についての有限性には、楕円性の仮定自体は不要である。

次にF/k(x)が有限で、xとzがk上超越的なら、代数的交換補題からxはk(z)上代数的。
k(z,x)とk(x,z)の同じ中間体を二つの塔として比較し、F/k(z)の有限性を得る。
特定のRatFunc代数構造を別途選ぶ必要はない。
楕円曲線への適用では、一般xのOでの極から超越性を供給する。
前回証明した同じX_H,Y_Hの個別の超越性を使い、

```text
[F:k(X_H)] < ∞,  [F:k(Y_H)] < ∞
```

を追加providerなしで内部供給した。非零の関数体なので両finrankは正である。
これは二関数の代数的独立性を意味しない。

## 3. 実際の多項式関係と次数の塔

F/k(X_H)の有限性から、同じY_Hの最小多項式を取れる。
実際に次を満たす多項式qを構成した。

```text
q ∈ k(X_H)[T], qはmonic, 0 < natDegree q, q(Y_H)=0
```

係数はk(X_H)の元である。次数2、係数がk[X_H]に属すること、Weierstrass形、
標的の非特異性はここからまだ得ていない。

同じ二関数で生成する実際の中間体 `veluCoordinateField` を定義した。
前回の平行移動不変性から、この中間体は同じ核の固定体F_Hに含まれる。
既存の `[F:F_H]=|H|` と塔を使って

```text
[F_H:k(X_H)] · |H| = [F:k(X_H)]
[F_H:k(Y_H)] · |H| = [F:k(Y_H)]
```

を証明した。これらの相対次数が2,3であることはまだ入力されていない。

## 4. 互いに素な次数が閉じる部分

一般の同じ周囲の体Fの中でA,B⊆Nとする。
J=A∨Bなら `[N:J]` は `[N:A]` と `[N:B]` をともに割る。
二つの相対次数が互いに素なら `[N:J]=1`、したがってJ=N。

周囲の次数を使う入口では

```text
[F:A]=m·d, [F:B]=n·d, [F:N]=d, d≠0, gcd(m,n)=1
```

を仮定して共通因子dを消去する。d≠0を落としてはいけない。
Leanのfinrankは無限拡大の場合0なので、0での消去は正当でない。

これをA=k(X_H), B=k(Y_H), N=F_H、m=2,n=3,d=|H|へ適用した。
部分群HはOを含むので |H|≠0。従って

```text
[F:k(X_H)]=2|H| ∧ [F:k(Y_H)]=3|H|
  ⇒ k(X_H,Y_H)=F_H
```

を得た。この二つの正確な次数は定理の仮定に明示的に残っている。
前回の「総極位数2|H|,3|H|」を、この次数の仮定として流用していない。

## 5. 同じSourceへの接続と境界例

Source側は同じ残余空間の同じ次元1直線Lを保持し、実点部分群の位数pから有限性を内部供給する。
同じ `residualKernelX/residualKernelY` の有限性、固定体への包含、実際のモニック関係を公開した。
固定体生成には正確な次数2p,3pが入力に残る。

[Source37 smoke](evidence/Note032FiniteKernelDegreeSmoke.lean) は同じSource37で有限性・モニック関係を確認する。
生成の例では次数74,111を明示的に仮定した。
同じE₀[37]への同定を組み合わせた例でも、同じLの大域Cofixed性を保持する。
Source37・Cofixed直線の存在や、標的零成分への輸送は結論していない。

[通常テスト](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelDegree.lean) と
[独立境界例](evidence/Note032FiniteKernelDegreeBoundary.lean) は次を検査する。

- 任意の体kの実際の有理関数体で `[k(t):k(tⁿ)]=n`。k=ℚにも特殊化できる。
- n>0で同じtからtⁿへの超越元交換を適用。
- 次数2,3の部分体は同じk(t)全体を生成。
- 次数4,6の部分体は同じk(t²)を生成。周囲の全体と取り違えない。
- 同じ次数2の部分体二つは全体を生成しない。
- t⁰の部分体では周囲finrankは0、自己相対次数は1。仮想的な比2への消去はできない。
- 前回と同じ曲線y²=x³−x、同じH={O,(1,0)}について、同じ関数の有限正次数とモニック関係。

## 6. 由来・調査範囲

超越元交換の証明は、checkout内のMathlib `NumberTheory/FunctionField.lean` の
`FunctionField.finiteDimensional_of_adjoin_transcendental` を読み、
有限なk(x)拡大を直接入力するDkMath所有者へ再構成した。
Anne Baanen・Ashvni Narayananの著作権とApache-2.0表示を新所有者に保持した。

一般座標の二次関係は既存 `EllipticMultiplicationFunctionDegree` の証明を同じ座標へ適用した。
同所有者が記録するAnthropic由来blob `346a32fb08ba430a7125a16d9c7b96c9608ea417`、
Apacheライセンス・NOTICEへの参照を保持した。外部模範解答のimportは追加していない。
次数と生成はMathlibの `Relrank`、境界例の有理関数次数は `RatFunc.IntermediateField` を再利用した。

現checkoutのDkMath LibとMathlibの関数体・次数APIを調べた範囲では、
今回の総極位数をそのまま関数体次数へ変換する一般定理を確認できなかった。
既存の倍写像次数証明は、明示的除法多項式と二次関係の共役を用いる別の計算である。
この調査を「一般定理が存在しない」という主張にはしていない。

## 7. 検証と次の境界

`lake build DkMath.FLT.FreyFiniteKernelDegree` が成功した（4068 jobs、警告0）。
4つの新production所有者を含む対象ビルドである。
独立境界例・Source37・axiom監査、禁止構文、マーカー、Lib依存閉包、
既存所有者の保護、入口登録、リンク、差分の検査は
[validation](evidence/validation-note032-005c2c1.txt) と [JSON evidence](evidence/note032-005c2c1.json) に記録した。
独立境界例とSource37はいずれも警告0で通り、31宣言のaxiom監査は標準の
`propext`・`Classical.choice`・`Quot.sound` の範囲だった。
通常テストの証明本文は独立境界例と一致させ、独立にelaborateした。
入口登録は静的確認であり、root・DkMathTest・lake testのビルドは利用者側の分担として実行していない。

次の005C₂c₂では、同じ関数の総極位数から関数体次数への定理、
または独立した明示的な次数計算を供給し、今回の条件付き生成定理を無条件で適用する。
標的方程式・係数・非特異性、実際の点写像・加法性・核・同変性、
005C₁のhom入力、標的の零成分への輸送、大域脱出元は依然として残る。
関数体の点付値と係数体の2進付値は同一視していない。
一般hno・Mazur Step Three・安定な巡回塔・一般FLTは未証明である。

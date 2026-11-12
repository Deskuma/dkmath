# NOTE-032-005C₂c — 次数・固定体生成の残件を一括して閉じる

2026-10-25。branch `dev/FLT-GN-regular-261018-v0`。
開始時HEADは `4769788b39e7fbafc8c8fa0c47a3c2801bff280f`、作業ツリーはcleanだった。
内部の枝番は追加せず、前回仮定に残った正確な次数と固定体生成をまとめて証明した。
本体は6所有者、27定理・2定義、781行である。

**同じX_H,Y_Hについて、相対次数2,3、周囲の次数2|H|,3|H|、総極位数と次数の一致、
固定体生成、最小多項式の正確な二次性が確定した。**
これらの次数・生成を外部providerに要求する仮定はなくなった。
係数はなおk(X_H)上であり、標的のWeierstrass方程式・非特異性・点isogenyは未構成。
従って005Cの商楕円曲線構成全体やhnoの完了を意味しない。

## 1. 完了した数学と所有者

以下でkはKの代数閉包、Fは同じEの幾何学的関数体、N=F_Hは同じ有限核Hの平行移動固定体。
新しい代替関数や代替核を選ばず、既存 `veluX/veluY` を保持した。

| 所有者 | 定理・定義 | 内容 |
| --- | --- | --- |
| [ValuationPoleSpace](../../../DkMath/Lib/Algebra/ValuationPoleSpace.lean) | 7定理・1定義 | 剰余の定数性、最高項相殺、単純体の値の合同類、整元の正則性、極空間の次元上界 |
| [PoleSpaceDegree](../../../DkMath/Lib/Algebra/PoleSpaceDegree.lean) | 4定理 | 整基底と冪の独立性・次元の増大からの次数上界 |
| [ValuationDegreeLower](../../../DkMath/Lib/Algebra/ValuationDegreeLower.lean) | 1定理 | 異なる付値合同類から実際の一次独立族を構成 |
| [EllipticPoleDegree](../../../DkMath/Lib/NumberTheory/EllipticPoleDegree.lean) | 4定理・1定義 | 全点正則なら定数、同じ核での付値一致、核外正則部分代数、相対次数の上下界 |
| [EllipticFiniteKernelGeneration](../../../DkMath/Lib/NumberTheory/EllipticFiniteKernelGeneration.lean) | 6定理 | 相対次数2,3、周囲次数、固定体生成、総極位数との一致、二次最小多項式・関係 |
| [FreyFiniteKernelGeneration](../../../DkMath/FLT/FreyFiniteKernelGeneration.lean) | 5定理 | 同じSource・同じ直線・同じ実点核への接続 |

Lib側は任意の体K、同じ楕円曲線E、代数閉包上の任意の有限実点部分群Hを扱う。
標数0、奇数位数、素数位数、ガロア安定性、Cofixed性は不要。
有限列挙は既存の座標和と同じFintype Hを使う。
公開Lib宣言は `[DkMath.Lib]` と日本語の教科書docstringを持つ。
各新ファイルにはimport直後の `#print "file: ..."` を置いた。

## 2. 一般の因子理論を避ける選択

[模範解答の上界証明](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean)
は、整基底に関数の冪を掛けた独立族と、Riemann–Roch空間の次元上界を比較していた。
同時に、一般の総極因子次数定理と明示的Vélu座標の有理式の証明も閲覧した。
前者には一般の場所・因子・空間の所有者が必要で、後者には奇数巡回核の代表集合と有理式の接続が必要だった。

今回必要なのは、既に構成済みの**同じ不変関数の次数**である。
そこで一般の因子型を移植する代わりに、H不変性を使ってH上の極条件をOの一つの条件へまとめた。
この選択により、点付値・固定体・座標環という既存のDkMath所有者の上に次数公式を構成できた。
外部の `P2M/Definitions/Theorems` はimportしていない。

整基底の増大の議論を再構成した `PoleSpaceDegree` にはAnthropicの著作権・Apache-2.0・NOTICEを保持した。
取得した上界証明のGit blobは `3c0bfbe2ef83931a739635809490b5a7f4db654e` と照合した。
最高項相殺と一つの付値の極空間は、その議論に必要な部分をDkMathで新たに証明した。

## 3. 最高項相殺を、剰余体の大きな理論なしに示す

vは定数上自明な一変数関数体Fの整数値付値、xは極を持つ超越元とする。
F/k(x)が有限で、v(z)=1なら

```text
あるc∈kについて v(z−c)<1
```

が成り立つ。もし全てのz−cの値が1なら、kの代数閉性による多項式の一次分解から、
全ての非零pについてv(p(z))=1となる。従ってzは超越的で、k(z)の全非零元も値1。
超越元交換からxはk(z)上代数的である一方、k(z)上自明な付値でxは極を持つので超越的となり、矛盾する。

同じ非零値を持つf,gにこれをf/gで適用すれば

```text
v(f−c g)<v(g)
```

となる。剰余を勝手に係数体と同一視する仮定は追加していない。
定数上自明であること、一変数の有限性、代数閉性、極の存在を証明に保持した。

## 4. Oでの極空間の次元は高々n+1

Rを同じNの中でHの外で正則な元の部分代数とする。
Hの平行移動不変性により、Rの関数はH上の全点でOと同じ値を持つ。

Oでも正則なRの関数は全点で正則となる。
有限場所の整性判定で座標環へ戻し、Oでのノルム次数が0であることから、
p(x)+q(x)yのq成分が消え、pも定数となることを証明した。
従ってRの極位数0の空間は定数の一次元空間に含まれる。

`poleSpace R v n` はRの中でv(f)≤exp(n)の関数空間である。
nからn+1へ進む際、新しい最高項があれば一つgを選ぶ。
他の関数の同じ最高項をスカラー倍gで消せるので

```text
L_(n+1) ⊆ L_n + k·g,  dim_k L_n ≤ n+1
```

となる。整数値付値なので「exp(n+1)未満」は「exp(n)以下」である。
有限次元性もこの帰納法で内部供給した。
これは今回の上下界に必要な弱い次元評価であり、一般のRiemann–Roch公式やdim L_n=nを主張しない。

## 5. 整基底の増大が次数の上界を与える

f∈NがHの外で正則で、Oで極位数d>0を持つとする。
前回の有限性によりN/k(f)は有限である。r=[N:k(f)]とおく。
k[f]の分数体がk(f)であることを供給し、k[f]上整な基底u₁,…,uᵣを取る。

整元は、fと定数が正則な点では正則である。これは同じ付値環の整閉性で証明した。
従って全uᵢはRに入り、Oでの極位数を同時に抑えるc≥0を取れる。
超越元fの冪と基底の塔から

```text
fʲuᵢ  (0≤j<m, 1≤i≤r)
```

はk上独立。このmr個の関数は全てL_(c+dm)に入るので

```text
m r ≤ c + d m + 1
```

を得る。m=c+2を使うとr>dは矛盾し、r≤dとなる。
相対次数そのものを入力する包装ではなく、実際の独立族から数値上界を得ている。

## 6. 付値合同類が次数の下界を与える

v(f)=exp(d)なら、k(f)の非零元aはp(f)/q(f)と書け、

```text
v(a)=exp(d·(deg p−deg q))
```

となる。従って係数を掛けても値の指数はmod dで変わらない。
異なる合同類を持つ関数族には、任意の非零線形結合で唯一の最大付値項があり、相殺しない。
この独立性を一般補題として固定した。

同じX=X_H,Y=Y_Hには、前回確定したv_O(X)=exp(2), v_O(Y)=exp(3)を使う。

- k(X)上では1,Yの指数0,3がmod 2で異なる。よって[N:k(X)]≥2、上界と合わせて2。
- k(Y)上では1,X,X²の指数0,2,4がmod 3で異なる。よって[N:k(Y)]≥3、上界と合わせて3。

これは標数に依存しない値の計算であり、分離性を次数の下界に仮定していない。

## 7. 固定体生成、総極位数、二次関係まで閉じる

既存の[F:N]=|H|と次数の塔を使い

```text
[F:k(X_H)]=2|H|,  [F:k(Y_H)]=3|H|
```

を内部供給した。前回の `veluCoordinateField_eq_fixedField_of_degrees` にこれらを渡すと

```text
k(X_H,Y_H)=F_H
```

が無条件に得られる。前回まで残っていた次数仮定は、新しい公開入口には存在しない。

既存の実点位数の総和2|H|,3|H|と照合し、**同じ二関数の総極位数＝実際の関数体次数**も証明した。
任意の曲線の任意の有理関数に対する一般定理には拡張していない。

さらにk(X_H)(Y_H)=Nと相対次数2から、実際の最小多項式の次数は正確に2となる。
`exists_velu_quadratic_relation` は同じY_Hが満たすモニック二次多項式を構成する。
これは係数体k(X_H)上の関係であり、k係数のWeierstrass方程式・標的の非特異性とは別である。

## 8. 同じSourceと検証

Source側は同じSource、同じ次元1の直線L、同じ実点部分群を保持する。
位数pから有限性を内部供給し、相対次数2,3、周囲次数2p,3p、固定体生成、最小多項式の二次性を公開した。
ガロア安定性やCofixed性を次数計算へ追加していない。

[境界例](evidence/Note032FiniteKernelGenerationBoundary.lean) は前回と同じ曲線y²=x³−x、
同じH={O,(1,0)}で相対次数2,3、周囲次数4,6、固定体生成、最小多項式二次性と実際の二次関係を検査した。
自明核でも周囲次数2,3と生成を確認し、核の非自明性・奇数性をLibへ混ぜていない。
[通常テスト](../../../DkMathTest/Lib/NumberTheory/EllipticFiniteKernelGeneration.lean) と証明本文を一致させ、独立にelaborateした。

[Source37 smoke](evidence/Note032FiniteKernelGenerationSmoke.lean) は次数74,111を計算し、
次数の仮定なしの固定体生成・二次関係・最小多項式次数2を確認した。
同じE₀[37]への同定の例では、必要な大域Cofixed性を引き続き保持している。
Source37や直線の存在、標的の零成分への輸送を結論していない。

`lake build DkMath.FLT.FreyFiniteKernelGeneration` は4074 jobs、警告0で成功した。
独立境界例7定理、Source37の5定理、全41宣言のaxiom監査は警告0で成功。
監査の依存は `propext`・`Classical.choice`・`Quot.sound` の範囲だった。
[JSON evidence](evidence/note032-005c2c.json) と [validation](evidence/validation-note032-005c2c.txt) に静的検査を含めて記録した。
フル/root/DkMathTest/lake testビルドは利用者側の分担で、今回の入口登録は静的検査である。

## 9. 残る構成境界

今回、**次数と固定体生成の未供給入力は閉じた**。
残るのは、k(X_H)上の二次関係をk係数のWeierstrass方程式へ整形すること、
標的の非特異性、実点写像の正則延長・加法性・正確な核・ガロア同変性である。
005C₁の実際の点準同型の入力、標的への零成分輸送、大域脱出元も未供給。

関数体の点付値と係数体の2進付値は区別している。
無条件の固定体生成は証明済みだが、商楕円曲線・isogeny・一般hno・一般FLTの完成はまだ主張しない。

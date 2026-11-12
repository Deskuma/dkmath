# NOTE-030 第5部: 実際の付値軌道から有理p-torsion排除へ

日付: 2026-10-22（JST）。**030-007を実装し、有理p-torsion排除を閉じた。**
同じFrey Sourceと同じ有理点Qから整数核の全入力を証明し、
素数p≥5・b偶数の条件の下で`p • Q = 0 → Q = 0`を得た。
位数・整数列・非零因子・排除結論のproviderを仮定していない。

新規本体2ファイル、既存付値APIへの補題1個、回帰・監査を追加した。
新規の公開定義・定理は本体13個、回帰13個である。
教科書docstringと指定の`#print "file: ..."`を備え、Lib・FLT・テストの通常入口へ接続した。
030-008のガロア固定点からの降下との接続、hratの供給は次段階に残る。

## 1. 到達した公開定理

`DkMath.FLT.FreyRationalTorsion`の入口は次の通りである。

```text
S : Frey.Source p
hp : p.Prime
hp5 : 5 ≤ p
hbe : Even S.b
Q : S.rationalCurve.toAffine.Point
hQp : p • Q = 0
───────────────────────────────────
S.rational_p_torsion_eq_zero ... : Q = 0
```

`S.rational_p_torsion_iff`は`p • Q = 0 ↔ Q = 0`を返す。
Q≠0は公開入力ではなく、背理法の中で仮定して位数pを証明する。
同じSのa,b,c、非零性、互いに素という情報、正規化、有理モデルと同じQを保持する。
裸のSourceにb偶数を暗黙に追加していない。

## 2. 一般層とSource層を分ける

| 配置 | 内容 |
|---|---|
| `RationalTwoAdicBounds.Exact.sub_valuation_spec` | 差が非零のとき、異なる深さのmin等式と一致時の下界をまとめる |
| `DkMath.Lib.NumberTheory.WeierstrassValuationOrbit` | 実際のQから四つの値を定義し、七条件を証明し、既存整数核を適用する |
| `DkMath.FLT.FreyRationalTorsion` | 同じSourceの係数・γを一般定理へ供給する |
| `DkMathTest.FLT.FreyRationalTorsion` | minの打ち消し、実在する位数5の全七条件、シフト条件の必要性、具体モデル、Source 37 |
| `DkMathTest.FLT.Note030TorsionDependencyAudit` | 新規宣言の公理と、主要経路の型・opaque本体・必須providerを検査する |

一般層はa₁=1、a₃=a₆=0、a₂の2進整性、`Exact γ a₄`、1≤γを取る。
最後の排除に必要な追加条件はγ=pv−4である。
`prime_torsion_eq_zero`はこれらの条件を満たす任意の有理モデルについて使える。
Source層は既存の係数定理を供給するだけであり、一般Libの証明はDkMath.FLTに依存しない。

## 3. 整数列は同じ点の座標から定義する

Qの実際の座標`Point.xc`を使って次を定義した。

| ノートの記号 | 新しい定義 | 内容 |
|---|---|---|
| e(k) | `xValuation Q k` | v₂(x(kQ)) |
| A(k) | `productGapValuation Q k` | v₂(x(kQ)x(Q)−a₄) |
| B(k) | `differenceValuation Q k` | v₂(x(kQ)−x(Q)) |
| A₁ | `squareGapValuation Q` | v₂(x(Q)²−a₄) |

`OrbitConditions Q p γ`はこれらの**定義された値**に対する七条件の命題である。
自由な整数列を受け取るproviderではなく、`orbit_conditions`が以下を全て証明する。

| 整数核の入力 | 供給する証明 |
|---|---|
| 全1≤k≤p−1で1≤e(k)≤γ−1 | 030-005の同じ倍点の区間定理 |
| 2e(1)≠γならA₁=min(2e(1),γ)、一致時γ≤A₁ | x(Q)²のExact、a₄のExact、030-006の倍点分子非零 |
| e(2)+2e(1)=2A₁ | 030-006の実際の倍点付値等式 |
| A(k)の非一致時min・一致時下界 | x(kQ)x(Q)のExact、a₄のExact、和差分子非零 |
| B(k)の非一致時min・一致時下界 | 各xのExact、x(kQ)≠x(Q) |
| e(k+1)+e(k−1)+2B(k)=2A(k) | 030-006の実際の和差付値等式 |
| e(p−1)=e(1) | (p−1)Q=−Qとx座標の符号反転不変性 |

内部の添字範囲は2≤k≤p−2である。
Sourceからの条件付き入力構成だけを読める入口として`S.valuationOrbit_conditions`も公開した。

## 4. 一致付値で零を混同しない

`Exact n q`と`Exact m r`に対し、n≠mならq−rは非零で、付値はmin(n,m)となる。
n=mの場合は打ち消しが起き得るので、まず`Lower m (q−r)`しか言えない。
**q−r≠0を確認して初めて**m≤v₂(q−r)を取り出す。

新しい`Exact.sub_valuation_spec`はこの二つを一つのAPIにまとめる。
軌道で必要な差の非零性は、030-006の倍点・和差恒等式と位数の議論から既に得ている。
従って一致時に非零性を追加仮定する必要も、零の便宜的な付値を押しつぶす必要もない。

回帰では、3−5=−2の付値が1へ上がる例と、
4−4=0では`Lower 2`が成立しても生の数値下界2≤v₂(0)が偽になる例を証明した。

## 5. 端点と素数シフトが矛盾を閉じる

pQ=0から

\[
(p-1)Q+Q=0,\qquad (p-1)Q=-Q
\]

を得る。負の点もx座標を保つので、e(p−1)=e(1)となる。
この端点補題自体には係数評価・素数性・Qの非零性は不要であり、p≥1だけで成立する。

`no_prime_shifted_torsion`は全七条件を構成した後、
既存の`FoldedValuationOrbit.no_prime_shifted_valuation_orbit`へ渡す。
ε=e(1)とすると、整数核は付値を法2γの合同軌道の折り返しとして追い、
端点条件から内部の深さ0または2γ∣pεを導く。
前者は正の下界に反し、後者は素数の約分と0<ε<γに反する。

約分が可能なのはγ=pv−4のときp∤2γだからである。
pが2γも割れば8=2³を割ることになり、p≥5という素数条件に反する。
この約分はNOTE-029で実装済みの整数核を再利用し、再移植していない。

最後に非零p倍零点の位数がpであることを素数性から証明し、一般モデルの`prime_torsion_eq_zero`を得る。
Frey Sourceでは

\[
\gamma=p\,v_2(S.b)-4
\]

が定義通りであり、`a₄_twoAdic_exact`、`one_le_twoAdicGamma`、`a₂_twoAdic_integral`を渡して閉じる。
a₂の整性は既存の`curve_map`に、a₄の付値はb偶数と原始性からのa奇数に到達する。

## 6. 位数5の実例を誤って排除しない

前章までのモデル(1,−24,0,160,0)と位数5のQ=(4,−20)を再利用した。
この点はγ=5に対する**全七条件を実際に満たす**。
新しい定義でもe(1)=2、e(2)=4、A₁=4、A(2)=5、B(2)=2となり、端点も一致する。

しかし5=5v−4を満たす整数vは存在しない。
実際に法2γ=10では10∣5·2だが10∤2であり、5を約分できない。
従って全七条件だけから一般の有理5-torsionまで排除してはいけない。
回帰はこの算術的な境界を保持している。

別の具体的モデル(1,0,0,2,0)はγ=1=5·1−4を持つため、全ての5倍零点が零になる。
一方、この同じモデルには実際の非零2-torsion T=(0,0)が存在する。
p-torsion排除を、零点や全torsionの不存在と混同しない。

Source 37についても、明示されたb偶数条件の下で`37 • Q = 0 → Q = 0`と同値入口を型検査した。
Sourceや非零有理37-torsionの存在を主張する定理ではない。

## 7. 原典・依存監査・検証

前段で取得した[Anthropicの原典](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean)
（blob `fe61fd5d4f94d55b5a9da38d1541903c84397df0`）の
S04におけるmin条件・端点・`arith_core`適用を参照した。
DkMathの030-001〜006と既存整数核を再利用し、実際の点からの供給を一般層へ分離した。
新規の一般モジュールはApache-2.0の帰属、blob、既存LICENSE/NOTICEへのパスを保持する。
既存の`FoldedValuationOrbit`では、未接続という古い説明を更新した。定理の型・証明・importは変更していない。

新規本体13個・回帰13個の公理検査と、主要8経路の型・opaque本体走査は合格した。
今回初めて整数核を必須providerに加え、実際の座標・非零min条件・倍点・和差・端点・素数約分・Source係数を要求する。
一般Libの経路にはDkMath.FLTを禁止し、位数5の七条件の回帰には整数核への依存を禁止する。
旧FLT終点、外部FltRegular/P2M/P2MW/FreyPackage、Kummer終点、sorryAxは禁止する。
許容公理は`propext`、`Classical.choice`、`Quot.sound`のみである。

focused build（3,167 jobs）、通常ルート・Lib・FLT・テストを含むビルド（11,691 jobs）、
ルートsmoke、テスト入口の直接検査、マーカー照合、`git diff --check`は全て成功した。
新規コードに警告はない。全体ビルドで再掲された既存の別モジュールの`sorry`警告5件は今回の証明経路と区別する。

検証のコマンド・結果は[evidence/validation-note030-007.txt](evidence/validation-note030-007.txt)に記録する。

## 8. 現在の完成範囲と次の開始点

030-001〜007が完成し、**向き付き条件を明示したFrey Sourceの有理p-torsion排除**まで到達した。
次の030-008では、既存のガロア固定点の有理点への降下にこの定理を接続し、hratを供給する。

hratの公開bridgeは今回まだ実装していない。
局所慣性からのfixed/cofixed二択、cofixed不存在、残余表現の無条件既約性、一般FLTは別の未完成課題である。
有理p-torsion排除だけから、それらが完成したとは主張しない。

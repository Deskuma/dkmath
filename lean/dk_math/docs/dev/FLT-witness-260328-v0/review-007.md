# review: boundary-core route の数学核が actual theorem で閉じました

うむ。これは **かなり大きな節目** じゃ。
今回はもう「候補を整理した」ではない。 **本線候補だった boundary / arithmetic-core route の数学核そのものが actual theorem で閉じた**、という更新じゃ。

## 1. いま何が起きたか

今回 `exceptional_boundary_datum_prepared_arithmetic_core_divData_default` が入ったことで、前回まで残核として切り出していた

$$
d \mid \mathrm{core},\qquad
d \nmid \mathrm{core}/d,\qquad
1 < \mathrm{core}/d
$$

の三点が、**仮の target ではなく実証明で通った**。
つまり `proof-004` で言っていた step 2–5 が Lean 上で閉じたわけじゃ。

ここでの core は

$$
\mathrm{core}:=\operatorname{boundaryCyclotomicPrimeCore}(.right,d,x,u)
$$

で、証明はこれを

$$
A := d\cdot u^{d-1},\qquad B := \sum_{k\ge 1}\cdots
$$

に分け、

* (d\mid x) と (d) prime から (d^2\mid B)
* Wieferich 条件 (u^{d-1}\equiv 1 \pmod{d^2}) から (A\equiv d \pmod{d^2})

を出し、全体として

$$
\mathrm{core}\equiv d \pmod{d^2}
$$

へ落としておる。そこから上の三条件を回収した、という流れじゃ。

## 2. 何が嬉しいのか

これは単に補題が 1 本増えた、ではない。

前回の時点では、

* false route は全部切れた
* boundary route は生きている
* step 1 と step 4-5 は橋として閉じた
* だが valuation / (d^2) 側が最後の残核

という状態じゃった。

今回、その **最後の残核** が actual theorem で埋まった。
ゆえに、`ExceptionalBoundaryDatumPreparedArithmeticCoreDivDataTarget` はもう未解決 target ではなく、`..._default` で満たされる concrete theorem になったのじゃ。

## 3. 状況分析

いまの battlefield を率直に言うぞい。

### 3.1. もう死んだ枝

これは変わらぬ。

* same-(q) route
* body-only witness route
* two-witness route（現 statement のまま）

この三つは false として閉じた。もう本線ではない。

### 3.2. 生き残った枝

boundary / arithmetic-core route が current canonical route じゃ。
しかも今回は「有望候補」ではなく、**actual theorem を持つ実動 route** に昇格した。

### 3.3. この route のどこまで閉じたか

今回の `...divData_default` と、前回までに入っていた

* `exceptional_boundary_core_concrete_of_div_data`
* `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_divData`

を合わせると、boundary-core route は

$$
\text{div-data}
\to
\text{prepared arithmetic core concrete}
$$

まで no-sorry で通っておる。
報告にも「`ExceptionalBoundaryDatumPreparedArithmeticCoreConcreteTarget` は `...of_divData` 経由で no-sorry で到達できる」と明記されておる。

## 4. では、いま残っているものは何か

ここが大事じゃな。
今回の数学核自体は通ったので、**いま残っているのはこの定理の中身ではない**。

報告の書き方に従えば、残っているのは

* warning の整理
* この default theorem を mainline 側の canonical entrance として読む薄い wrapper を足すかどうか
* あるいは、そのまま次の witness route へ進むか

という **整流・運用の判断** じゃ。

つまり、前までのような

$$
\text{「この theorem は真か偽か」}
$$

という段ではもうない。
今回については、**真で、しかも証明済み** じゃ。

## 5. 今のルートを式で書くと

流れはかなり綺麗になったの。

まず exceptional 仮定から `...divData_default` で

$$
d \mid \mathrm{core},\qquad
d \nmid \mathrm{core}/d,\qquad
1<\mathrm{core}/d
$$

を得る。

そこから `exceptional_boundary_core_concrete_of_div_data` で prime witness (q) を取り、

$$
q \mid \mathrm{core},\qquad q\nmid x
$$

を得る。

さらに `exceptional_boundary_datum_prepared_arithmetic_core_concrete_of_divData` で prepared arithmetic core concrete に落とし、そこから既存 bridge で mainline / primitive packet descent へ流す。
つまり、いまの本線はもう

$$
\text{exceptional assumptions}
\to
\text{div-data}
\to
\text{concrete witness}
\to
\text{prepared arithmetic core concrete}
\to
\text{mainline / packet descent}
$$

という一本道になっておる。

## 6. 賢狼の判断

わっちの判断をはっきり言うぞい。

### 6.1. これは「正解ルート候補」ではなく「正解ルート本体」

boundary / arithmetic-core route は、もう候補ではない。
少なくとも `proof-004` の核については、**actual theorem として通った route** じゃ。

### 6.2. 次の課題は数学核ではない

次の仕事は、新しい valuation 補題を探すことではなく、

* canonical entrance の薄い wrapper を足すか
* そのまま次の downstream witness route へ進むか

の選択じゃ。
数学の本丸は、この件については一段落しておる。

### 6.3. ただし全プロジェクト全体では終わりではない

もちろん FLT 全体や Branch A 全体が終わったわけではない。
しかし **`dev/FLT-witness-260328-v0` で追っていた「どの witness route が生きるか」問題に関しては、boundary-core 側が勝った** と言ってよい。

## 7. 総括

一言でまとめると、こうじゃ。

**偽枝をすべて切ったあとに残った boundary / arithmetic-core route について、最後の残核だった `div-data` が `exceptional_boundary_datum_prepared_arithmetic_core_divData_default` により actual theorem で閉じた。よって current proof exploration の数学核はこの route 上で通っており、残る作業は warning 整理や canonical wrapper 追加などの整流であって、もはや「この route が本当に進むのか」を疑う段ではない。**

よい。
これはかなり胸を張ってよい進展じゃ。
やっと「候補の森」を抜けて、**通れる道を石で固めた** 段まで来たのじゃよ。

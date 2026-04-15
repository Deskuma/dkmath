# review: FLT-Primitive-260327-v0: selected route の未解決核をさらに圧縮して、current canonical route を selected-core-on-witness 版へ寄せる

うむ、今回はさらに一段、 **未解決核の“名前”と“居場所”が下へ降りた** の。
かなり良い整理じゃ。

結論から言うと、いまの current direct concrete theorem 候補は、もう

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget}
$$

でよい。
そして `SelectedCoreOnWitness` は、独立核というより **splice point**、つまり既存 route を selected 語彙へ読み替える中継点としての性格が強くなった。

## 1. 今回なにが進んだか

今回の差分は 2 段じゃ。

### 1.1. `SelectedCoreOnWitness` の位置づけが固定された

まず

* `exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_diffPow`
* `..._of_diffPowModEq`
* `..._of_congruenceKernel`

が入った。
これで

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedCoreOnWitnessTarget}
$$

は、既存の

* diffPow divisibility
* diffPow ModEq
* congruence kernel

から **直接落ちてくる** と固定された。
つまりこれは「新しい独立核」ではなく、既存 route を selected-core-on-witness 語彙で読むための canonical splice point じゃ、という理解がコード化されたわけじゃな。

### 1.2. さらに direct body を residual sum まで下げた

次に

* `ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget`
* `exceptional_boundary_datum_prepared_selectedCoreOnWitness_of_selectedResidual`
* `..._selectedResidualOnWitness_of_residual`
* `..._of_diffPow`
* `..._of_diffPowModEq`
* `..._of_congruenceKernel`

が入った。
これで selected-core-on-witness の直下に、

$$
q \mid \sum_{k \in \mathrm{range}(d)} (u-1)^k u^{d-1-k}
$$

という **residual sum divisibility** の形が、direct concrete theorem 名として置かれたのじゃ。

## 2. 状況分析

いまの proof file の地形は、だいぶ見やすくなっておる。

### 2.1. 上流の強い route

上流にはまだ

* universal congruence kernel
* diffPow ModEq
* diffPow divisibility

がある。
ただし、これらはもはや「そのまま直接 mainline へ入る唯一の入口」ではない。
selected route へ落とす橋が十分に揃ったからじゃ。

### 2.2. 中継点としての `SelectedCoreOnWitness`

これは現在、

$$
\text{diffPow系} ;\Rightarrow; \text{SelectedCoreOnWitness}
$$

という読み替えの中心じゃ。
だが、この theorem 自体を concrete に攻める必要は薄くなった。
なぜなら、その下にさらに natural な direct body が置かれたからの。

### 2.3. 直下の direct body としての `SelectedResidualOnWitness`

これが今回いちばん大きい。
`cyclotomicPrimeCore d 1 (u-1)` と residual sum の一致を使って、

$$
\texttt{SelectedCoreOnWitness}
$$

の direct body を

$$
\texttt{ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget}
$$

として追えるようになった。しかもこの residual route も、既存の residual / diffPow / ModEq / congruence-kernel 群から自然に降りてくる。

## 3. 判断

ここでの判断ははっきりしておる。

## 3.1. current missing theorem の置き場所

**current direct concrete theorem 名は `ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget` に置くのが自然** じゃ。

理由は単純で、

* `SelectedCoreOnWitness` は splice point としての役割が強い
* `SelectedResidualOnWitness` の方が direct body に近い
* 既存 residual route とも最も接続がよい

からじゃ。

## 3.2. `SelectedCoreOnWitness` の扱い

これは今後も useful ではある。
されど、 **主戦場ではなく中継点** と見てよい。
つまり theorem 名として残す価値は大きいが、次に concrete 本体を切る候補としては一段上すぎる、という判断じゃ。

## 4. 数学的な意味

今回の整理の良さは、未解決核がますます **表示変換に依存しない本体** へ寄ったことじゃ。

もともと議論は

$$
(u-1)^d \equiv u^d \pmod q
$$

という合同で見てもよかったし、

$$
q \mid \texttt{cyclotomicPrimeCore}\ d\ 1\ (u-1)
$$

という core divisibility で見てもよかった。
いまはさらに

$$
q \mid \sum_{k \in \mathrm{range}(d)} (u-1)^k u^{d-1-k}
$$

という residual sum divisibility まで降りた。
これは CFBRC 側の“見えている本体”にかなり近い。つまり、対象がより algebraic body に近づいたということじゃ。

## 5. では次に何をするか

次の一手も、かなり明確じゃ。

**`ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget` の concrete theorem 本体を切る。**

履歴にもある通り、もし residual でもまだ重いなら、そのさらに下に

* diffPow local body

を direct concrete theorem 名で切ればよい。
ただ、今の段階ではまず residual を主戦場にするのが筋じゃろう。

## 6. 賢狼の見立て

わっちの見立てでは、ここまでで証明責務の分離はかなり成功しておる。

* witness selection は arithmetic witness concrete が持つ
* existential packaging もほぼ整理済み
* stronger route から selected route への橋も揃った
* core divisibility と residual divisibility の往復も見えた

ゆえに、次に考えるべきはもう「どの名前で追うか」ではない。
**選ばれた witness (q) が、なぜ residual sum を割るのか**、そこだけじゃ。

## 7. 総括

今回の差分を総括すると、

**`SelectedCoreOnWitness` は既存 diffPow / ModEq / congruence kernel を selected 語彙で読む splice point として固定され、その直下の direct body として `ExceptionalBoundaryDatumPreparedSelectedResidualOnWitnessTarget` が導入された。したがって current direct concrete theorem 候補は residual-on-witness 版であり、次はその concrete 本体を切るのが自然である。**

よい流れじゃ。
もうかなり、“どこを殴るか” が見えておる。

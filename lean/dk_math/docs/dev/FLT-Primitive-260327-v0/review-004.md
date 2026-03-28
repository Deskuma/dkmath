# Git Diff Report: Branch A Primitive Route Implementation

うむ、状況はさらに一段きれいになったの。
今回の整理で、primitive mainline の未完核が **ほぼ見切れた** と言ってよい。貼り付けの要旨を数学的にほどくと、次のような戦況じゃ。

## 1. 何が新しく切り出されたか

今回、新たに導入されたのは大きく二つじゃ。

* `PrimeGe5BranchAPrimitiveDistinguishedPrimeArithmeticTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

これは以前の

* distinguished prime を取る
* その prime から smaller packet を復元する

という二段のあいだに、さらに **arithmetic fallout** という中間層を明示した、という意味じゃな。

つまり流れが

$$
\text{Zsigmondy existence}
;\to;
\text{distinguished prime}
;\to;
\text{arithmetic fallout}
;\to;
\text{restore from arithmetic}
$$

へ整流されたわけじゃ。

## 2. arithmetic fallout とは何か

ここでいう arithmetic fallout は、distinguished prime (q) を 1 本得たあと、復元側が本当に必要としている局所算術データをまとめたものじゃ。

貼り付けでは具体的に、

$$
q \mid s,\qquad q \nmid t,\qquad \gcd(q,y)=1,\qquad q \ne p
$$

を restoration 側の入力として独立化しておる。

これは良い分解じゃ。
なぜなら「prime を取ること」と「その prime が復元に使える性質を持つこと」は、似ておるようで別の責務だからじゃな。

以前はこの二つが暗にくっついておった。
今回はそれを

* prime selection
* prime から得られる算術的帰結
* その帰結を使った復元

へ分けた。ここが大きい。

## 3. default arithmetic が既に閉じた

さらに重要なのは、`primeGe5BranchAPrimitiveDistinguishedPrimeArithmetic_default` が追加されており、arithmetic fallout 自体は **既に default 実装で機械的に出る** と示されたことじゃ。

この定理の中身は、ざっくり言えばこうじゃ。

distinguished prime (q) が

$$
q \mid GN,p,(z-y),y,\qquad q \nmid (z-y)
$$

を満たすなら、

* (q=p) は不可能
* (q \mid t) も不可能
* (GN = p\cdot s^p) から (q \mid s)
* (s \perp y) から (q \perp y)

が次々に落ちる。

つまり arithmetic fallout は、もはや未完数学ではなく、 **prime を 1 本取れた後の整理補題** へ落ちたわけじゃな。

これは戦況としてかなり良い。
敵が減った、ということじゃ。

## 4. それで何が橋だけで閉じるようになったか

今回追加された橋は、要するに

* `primeGe5BranchAPrimitiveWieferichPacket_of_zsigmondy_arithmetic_and_restore`
* `primeGe5BranchAPrimitivePacketDescent_of_zsigmondy_arithmetic_and_restore`

じゃ。

これによって、primitive packet descent 全体は

$$
\text{zsigmondy existence}
;+;
\text{arithmetic fallout}
;+;
\text{restore-from-arithmetic}
$$

の 3 段から閉じる、と明示された。
しかも arithmetic fallout は default があるので、実質的には

$$
\text{zsigmondy existence}
\quad\text{と}\quad
\text{restore-from-arithmetic}
$$

の 2 本が未完核じゃ、と履歴でも整理されておる。

## 5. いま何が終わり、何が残ったか

いまの状態を整理すると、こうじゃ。

### 5.1. ほぼ終わったもの

* provider 側 adapter の配線
* distinguished prime から arithmetic fallout への橋
* arithmetic fallout から packet restore target へ渡す API 整理
* primitive mainline を 3 段へ落とす wrapper 群
* build 成功確認
  `TriominoCosmicBranchA` と `TriominoCosmicGapInvariant` はどちらも通っておる。

### 5.2. 残った本命

* `PrimeGe5BranchAPrimitiveZsigmondyTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmeticTarget`

つまり今後の concrete math は本当にこの二つだけを見ればよい、という段まで来た。

## 6. 数学的に何が見えるようになったか

これは実装整理に見えて、実は数学の切れ目も露出しておる。

いまの Branch A primitive route は、構造的には

$$
\text{反例 normal form}
\to
\text{GN 側で新しい素数 } q \text{ を取る}
\to
q \text{ が } s \text{ 側に乗ることを示す}
\to
q \text{ を使って smaller packet を復元する}
$$

という流れになっておる。

このうち中央の

$$
q \mid s,\quad q \nmid t,\quad q \perp y,\quad q\ne p
$$

は、もう片付いた。
ゆえに残っているのは本当に

* **どうやって (q) を取るか**
* **その (q) からどう smaller packet を組み戻すか**

の二点だけじゃ。

これはたいそう重要な進展じゃな。
証明の「もやもやした難所」が、もう二つの核へ縮んだということだからの。

## 7. 次の自然な一手

貼り付け文の結論どおり、次の本命はまず

$$
\text{PrimeGe5BranchAPrimitiveZsigmondyTarget}
$$

を既存の `PrimitiveBeam` / `ZsigmondyCyclotomic` 補題へどう接続するか、じゃ。
ただしここでは Branch A 特有の

$$
p \mid (z-y)
$$

があるので、既存の一般形をそのまま流すだけで済むかは怪しい。
おそらく **Branch A 専用の薄い existence wrapper** が要る、という読みが自然じゃろう。

もう一方の `RestoreFromArithmetic` 側は、逆に仮定がだいぶ絞られたので、
ここからは「どの normal form packet をどう再構成するか」という、より純粋な構成論の勝負になったと言える。

## 8. 賢狼の総評

一言でまとめるなら、今回は

$$
\text{primitive route の霧が晴れた}
$$

回じゃな。

以前:

* primitive packet descent 全体が大きく見えていた

いま:

* `zsigmondy existence`
* `arithmetic fallout`
* `restore-from-arithmetic`

の三段に分かれ、しかも真ん中は既に default で閉じた。
したがって未完核は **実質 2 本** と断言できるところまで来た。

これは設計上かなり強い。
降下法の「何を証明すれば勝ちか」が、もう隠れておらぬからじゃ。

次をわっちがやるなら、まず
`PrimeGe5BranchAPrimitiveZsigmondyTarget` を **既存補題群との対応表** にして、

* どの仮定がそのまま使えるか
* どこで Branch A 専用 wrapper が要るか
* 最小追加補題は何か

を、Lean 宣言案つきで書き下すのが最短手じゃろう。

# TriominoCosmicBranchA の primitive route を二段分解した

うむ、状況はかなり整理されてきたの。
今回の一手は、primitive route の「まだ正体が大きすぎた核」を、さらに **二分割** して見える形にした、というのが本質じゃ。

## 1. 何が進んだのか

もともと `PrimeGe5BranchAPrimitiveWieferichPacketTarget` は、

* Branch A normal form
* primitive 条件
* Wieferich witness
* そして smaller packet の復元

までを、ひとまとまりで背負っておった。
これでは「何が本当に難所なのか」が少し見えにくい。

そこで今回、それを次の二段へ割ったわけじゃ。

* `PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreTarget`

これはたいそう良い分解じゃ。
なぜなら、数学的責務が

$$
\text{prime を取る段}
\quad\text{と}\quad
\text{取った prime から復元する段}
$$

に分かれたからじゃ。

## 2. 二段分解の意味

### 2.1. distinguished-prime selection 段

最初の target は、

$$
q \mid GN, p,(z-y),y,\qquad q \nmid (z-y)
$$

を満たす素数 (q) を 1 つ得る段じゃ。

これは言い換えると、

* GN 側には確かに「新しい側の素数」がいる
* しかも gap 側 (z-y) に埋もれていない

ということを取り出す局面じゃな。

この見え方はとても大事で、ここはまさに

* cyclotomic
* primitive prime divisor
* Zsigmondy 型存在

と親和的じゃ。
貼り付け文でも、次の自然な寄せ先は distinguished-prime selection を cyclotomic / Zsigmondy 語彙に移すことだと明言しておる。

### 2.2. packet restoration 段

二つ目の target は、その (q) を受けて

$$
\exists, pkt' : PrimeGe5BranchANormalFormPacket, p,\quad pkt'.z < z
$$

を作る段じゃ。

つまりこちらは existence ではなく **構成** の側じゃな。

* distinguished prime を得た
* それをどう normal form に戻すか
* どう smaller packet を立てるか

ここが restoration の責務になる。

ゆえに今回の分解で、

$$
\text{存在論}
\quad+\quad
\text{再構成論}
$$

という形が、かなりはっきりしたのじゃ。

## 3. 追加された橋の役割

今回追加された

`primeGe5BranchAPrimitiveWieferichPacket_of_distinguishedPrime_and_restore`

は、この二本が揃えば、元の witness 付き primitive packet target が **橋だけで閉じる** ことを示す定理じゃ。

これは設計としてたいそう美しい。

つまり今や、

$$
\text{primitive Wieferich packet}
$$

そのものを直接証明対象と見る必要は薄くなり、

$$
\text{distinguished prime を取る}
;\Longrightarrow;
\text{packet を復元する}
$$

の二部品が揃えばよい、と API が明確化されたのじゃ。

## 4. provider 側で何が起きたか

`TriominoCosmicGapInvariant.lean` 側にも、

* `BranchAPrimitiveDistinguishedPrimeAdapterTarget`
* `BranchAPrimitivePacketRestoreAdapterTarget`
* `branchAPrimitiveWieferichPacketAdapter_of_distinguishedPrime_and_restore`

が追加されておる。

これは provider 層でも同じ分解を保った、ということじゃ。
つまり branchA 本体だけでなく、外から差し込む contract も同じ二段構成になった。

ここが良い。
数学の核と provider の配線が、同じ切れ目で揃っておるからの。
あとで concrete 実装を差し替えるときも、責務がぶれにくい。

## 5. build 観点での状況

貼り付け文では、

* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicBranchA`
* `lake build DkMath.FLT.PrimeProvider.TriominoCosmicGapInvariant`

の両方が成功しておる。

ゆえに今回の変更は、単なる設計メモではなく、 **ビルド済みの安定分解** と見てよい。
これは実装上かなり重要じゃな。分けたが壊れた、ではない。

## 6. いま何が「本命」か

貼り付け文自身が、次の焦点は

$$
\text{この二段のうち、どちらが本命か}
$$

だと述べておる。
そして今の workspace では、まず distinguished-prime selection を cyclotomic / Zsigmondy 側へ寄せるのが自然、と判断しておる。

わっちも、この見立てに賛成じゃ。

なぜなら restoration は、ある意味では「prime が取れた後の幾何・代数の整理」になりやすい。
一方で distinguished-prime selection は、

$$
GN p (z-y) y
$$

の中から「本当に欲しい新素数」を選べるかどうか、という existence の心臓部じゃ。
ここが決まると、その後の packet 復元はかなり方向が定まりやすい。

## 7. 全体の戦況整理

いまの状況を一列に並べると、こうじゃ。

$$
\text{PrimitivePacketDescentTarget}
$$

を直接見るのではなく、まず

$$
\text{PrimitiveWieferichPacketTarget}
$$

へ縮約し、さらに今回それを

$$
\text{DistinguishedPrimeTarget}
\quad+\quad
\text{PacketRestoreTarget}
$$

へ割った。
そしてこの二本から元へ戻す橋も既に置いた。

ゆえに、数学的難所はかなり露出したと言ってよい。

* 以前は「primitive packet descent 全体」が難所
* いまは「distinguished prime をどう取るか」と「その prime からどう復元するか」

へ分離された

これは大きい前進じゃな。

## 8. 賢狼の総評

今回の仕事は、証明を進めたというより、 **難所の輪郭を削り出した** 一手じゃ。
しかもその削り方が良い。

* witness を含む大きな塊を
* existence 部と restoration 部へ分離し
* thin bridge で再接続し
* provider API まで同じ切れ目で揃えた

この形なら、次に攻める数学が見える。
とくに distinguished-prime 側は、Zsigmondy や cyclotomic と接続しやすいので、ここを本命視するのは自然じゃろう。

一言で言えば、

$$
\text{「降下法の核」}
$$

が、

$$
\text{「新素数の抽出」}
\quad\text{と}\quad
\text{「小 packet の復元」}
$$

に分かれて、ようやく本当の敵が見えた、という局面じゃな。

次に進めるなら、わっちは
`PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget` を **Zsigmondy / cyclotomic 既存補題群へどう接続できるか** を、仮定ごとに分解して設計図にしてみせるぞい。

# consider-017: FLT 側証明は「干渉縞の確定」と見ると非常に自然

うむ、かなり本質を突いておる。
わっちの見立てでも、**この流れの FLT 側証明は「干渉縞の確定」** と見るのがよい。

## 1. 何が干渉しておるのか

いま Branch A で見えておるのは、少なくとも 2 系統の縞じゃ。

ひとつは、gap-shape から来る **p-adic head 縞** じゃ。
つまり

$$
z-y = p^{p-1} t^p,\qquad GN,p,(z-y),y = p,s^p
$$

から

$$
s^p \equiv y^{p-1} \pmod{p^2},
\qquad
s^p \equiv y^{p-1} \pmod{p^3}
$$

のような congruence が **自動で確定する**。これはもうコード化されておる。

もうひとつは、witness (q) から来る **q-adic / cyclotomic 縞** じゃ。
つまり

$$
q \mid s,\quad q \nmid t,\quad q \nmid y,\quad q \nmid z,\quad q \nmid (z-y),\quad p \mid (q-1),\quad q^p \mid GN
$$

という束じゃ。
これは `BranchAContradictionWithWitnessSourceTarget` として、いま mainline の open kernel に持ち上げられた側じゃな。

だから構図としては、

$$
\text{p-adic head pattern}
\quad\text{と}\quad
\text{witness } q \text{ pattern}
$$

の **重なり方** を見ておる。

## 2. なぜ「干渉縞」なのか

ここが面白いところじゃ。

もし片方だけなら、ただの制約じゃ。
たとえば

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

だけ見ても、それは Branch A normal form の帰結として整然と成立する。
これ自体は矛盾ではない。実際、`ModP3SourceTarget` の否定側は同じ局所前提からは供給できぬと確認された。

しかし、そこへ witness (q) の縞を重ねると話が変わる。
円分核・GN・差分商の橋ができた今、

$$
\text{cyclotomicPrimeCore}
;\leftrightarrow;
GN
;\leftrightarrow;
\frac{(x+u)^p-u^p}{x}
$$

という同じ対象の別の顔から、
**同じ点が本当に許されるのか** を調べられるようになった。

つまり FLT 側の証明は、

$$
\text{「どの縞が立つか」}
$$

だけでなく、

$$
\text{「その縞どうしは同じ場所で共存できるか」}
$$

を確定する作業なんじゃな。
この意味で、ほんに「干渉縞」じゃ。

## 3. いま確定した縞、まだ未確定な縞

現時点で確定したのは、まず p-adic head 側じゃ。

$$
s^p = y^{p-1} + p^3 M
$$

という explicit な形まで出たので、ここはもう縞が見えておる。
GTail 側でも

$$
GN \equiv p,u^{p-1} \pmod{p^2},
\quad
GN = p,u^{p-1} + p^2 M,
\quad
\text{条件付きで } p^3 \text{ 精度}
$$

まで整っておるから、head の骨格はかなり見える。

未確定なのは、witness (q) 側の縞が **どの式として干渉してくるか** じゃ。
だからこそ `BranchAContradictionWithWitnessSourceTarget` が新設された。
これは「mod (p^k) の head congruence の否定」ではなく、witness (q) の構造そのものを使う source じゃ。
ここが今の open kernel の本丸じゃな。

## 4. 数学的に言い換えると

この route の FLT 証明を、もう少し数式寄りに言えばこうじゃ。

### 4.1. first pattern

gap-shape から

$$
z-y = p^{p-1} t^p,\qquad GN = p s^p
$$

が出る。
これにより

$$
s^p \equiv y^{p-1} \pmod{p^3}
$$

が固定される。

### 4.2. second pattern

witness (q) から

$$
q^p \mid GN,\qquad q \nmid (z-y),\qquad q \equiv 1 \pmod p
$$

などが出る。
これは cyclotomic / root-of-unity 的な rigid な制約の影じゃ。

### 4.3. proof as fringe determination

この 2 つの pattern を同時に満たす点が存在しない、と示せれば `False` じゃ。
つまり

$$
\text{「反例がある」}
$$

とは、2 系統の縞が同じ点で強め合うという主張であり、
FLT の証明とは、その **強め合いが起こらぬ** ことを示すことじゃ。

## 5. だから今やるべきこと

この見方に立つと、次の課題も綺麗に見える。

いま必要なのは、新しい縞を増やすことではなく、
**witness (q) 側の縞を、p-adic head 側と同じ座標系に落とすこと** じゃ。

つまり、

* GN を cyclotomic core として見る
* GN を差分商として見る
* GN を mod (p^3) head として見る
* そこへ (q)-witness の位数・整除・非整除条件を重ねる

この 4 層を同じ図に重ねることじゃな。

## 6. ひとことで言えば

$$
\boxed{
\text{そうじゃ。いまの FLT 側証明は、干渉縞の確定と見ると非常に自然じゃ。}
}
$$

より正確には、

$$
\boxed{
\text{Branch A normal form が作る p-adic 縞と、}
\newline
\text{witness } q \text{ が作る cyclotomic/q-adic 縞の共存不可能性を示す作業}
}
$$

と言える。

これは、かなり良い見取り図じゃよ。
そしてその図が見えたからこそ、いまの mainline が `ModP3Source` ではなく witness-aware source へ移ったのも、ちゃんと意味を持つのじゃ。

次に進むなら、この「干渉縞」の図をそのまま **設計メモ / 実装計画の概念図** にしておくと、道を見失いにくいぞい。

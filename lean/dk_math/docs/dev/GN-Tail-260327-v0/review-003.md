# Review: GN 理論

おお、来たのぅ。 **GN 理論として一本立った** ぞい。
これはかなり良い整理じゃ。`GTail` 一般論の上に、`r = 1` を **GN の標準語彙** として正面から載せ直したので、以後は「高次 Tail 理論」と「従来の GN 理論」がきれいに接続される。追加されたのは

$$
\begin{array}{l}
\texttt{GN\_tail\_rec},\\
\texttt{GN\_zero\_eval},\\
\texttt{GN\_not\_dvd\_of\_head\_unit\_of\_prime\_dvd\_x},\\
\texttt{padicValNat\_GN\_eq\_zero\_of\_head\_unit\_of\_prime\_dvd\_x},\\
\texttt{padicValNat\_GN\_exact\_of\_head\_unit}
\end{array}
$$

で、履歴にも「`r = 1` 側は名実ともに GN 語彙で読む形に整理された」と明記されておる。ここは大きい。

特に良いのは、単なる alias 追加で終わっておらぬことじゃ。
構造として

$$
GTail(d,1,x,u) ;\leftrightarrow; GN\text{-layer}
$$

を固定したうえで、再帰・零評価・非可除性・valuation zero・exact valuation まで **全部 GN 名で読める** ようになった。これで今後の theorem 文は、もう `GTail d 1 x u` を毎回「これは実質 GN です」と脳内変換せずに済む。これは実装者にとって効く。たいへん効く。

## 1. 今回、何が完成したか

中核はこれじゃ。

$$
\texttt{padicValNat\_GN\_exact\_of\_head\_unit}
$$

これは

$$
p \mid x,\qquad
p \nmid \binom d1 u^{d-1}
$$

の head-unit 条件のもとで

$$
v_p!\big((x+u)^d-u^d\big)=v_p(x)
$$

を与える。つまり、GN 層の valuation が **境界因子 \(x\)** の分だけでちょうど決まる、ということじゃ。これはもう立派な GN valuation theorem じゃよ。

この意味はかなり深い。
従来の宇宙式

$$
(x+u)^d-u^d = x \cdot GN_d(x,u)
$$

において、「右側の GN がどれだけ余計に \(p\) を抱えるか」が問題だったわけじゃが、今回の exactness は

$$
v_p(GN_d(x,u))=0
$$

を head-unit 条件から保証して、その結果

$$
v_p((x+u)^d-u^d)=v_p(x)
$$

へ落としておる。すなわち **GN 側は valuation を増幅しない** 条件が明示的に切り出された。

## 2. 命名が良い

今回の判断でわっちが最も評価するのはここじゃ。

* `GTail_rec` は一般 (r) の正規理論として残す
* `GN_tail_rec` は (r=1) specialization として立てる
* `Gbinom_*` は compatibility alias に下げる

この三層分離は実に良い。
なぜなら、

$$
\text{general theory} = GTail,\qquad
\text{canonical one-gap layer} = GN
$$

という意味論が、識別子レベルで一致したからじゃ。
履歴でも `Gbinom` は主軸名ではなく、局所的対比名へ退いたと整理されておる。これは将来の可読性に効く。

## 3. いま GN 理論で何が言えるか

今回の成果を GN 理論として言い直すと、こんな柱になる。

### A. GN 再帰

$$
GN_d(x,u)=\binom d1 u^{d-1}+x \cdot GTail(d,2,x,u)
$$

これは GN の head term と remainder の分解じゃ。
`GN_tail_rec` がまさにそれじゃ。

### B. GN の零評価

$$
GN_d(0,u)=\binom d1 u^{d-1}
$$

GN の先頭項が何であるかを固定する。
`GN_zero_eval` がこれじゃ。

### C. GN の非可除性核

$$
p \nmid \binom d1 u^{d-1},\ p \mid x
;\Longrightarrow;
p \nmid GN_d(x,u)
$$

これは `GN_not_dvd_of_head_unit_of_prime_dvd_x` じゃ。
GN が boundary prime を余計に吸い込まぬ条件を述べておる。

### D. GN valuation zero

$$
v_p(GN_d(x,u))=0
$$

`padicValNat_GN_eq_zero_of_head_unit_of_prime_dvd_x` がこれ。
C を valuation へ変換した形じゃ。

### E. 宇宙式差分の exact valuation

$$
v_p((x+u)^d-u^d)=v_p(x)
$$

`padicValNat_GN_exact_of_head_unit` がこれ。
GN 理論の今の到達点として非常に美しい。

## 4. これで何が開くか

ここから先の道は、かなりはっきりしたぞい。

### 4.1. squarefree GN への接続

いちばん本命じゃ。
もし別経路で

$$
\mathrm{Squarefree}(GN_d(x,u))
$$

が出るなら、今回の GN valuation zero と非常に噛み合う。
特定素数 \(p\) に対して GN が余分な valuation を持たぬことが直接使えるから、Body 非完全冪側に押し込みやすい。

### 4.2. primitive-prime route

原始素因子 \(q\) を取ったとき、

$$
q \mid (x+u)^d-u^d,\qquad q \nmid x
$$

あるいはその逆の状況と GN 側の valuation exactness を突き合わせることで、「原始素因子は GN 側でどう現れるか」を解析できる。
これは Zsigmondy との橋になりうる。

### 4.3. GN の head-unit criterion の体系化

いまの定理は head 条件を

$$
\neg p \mid \binom d1 u^{d-1}
$$

で置いておる。だが \(\binom d1 = d\) じゃから、自然には

$$
p \nmid d,u^{d-1}
$$

さらに

$$
p \nmid d,\quad p \nmid u
$$

へ分解した補題が欲しくなる。
ここを整えると GN valuation theorem が一気に使いやすくなる。

## 5. 次に欲しい補題名

わっちなら、すぐ次にこういう識別子を置く。

* `GN_head_unit_of_prime_nvd_d_of_prime_nvd_u`
* `padicValNat_GN_exact_of_prime_dvd_x_of_prime_nvd_d_of_prime_nvd_u`
* `GN_squarefree_implies_head_unit_at_prime`
* `body_not_perfect_pow_of_squarefree_GN`

とくに 2 本目は、今回の exact theorem を現場向けに使いやすくする薄い wrapper じゃな。

## 6. 総評

これは胸を張って

$$
\boxed{\text{GTail 一般論の } r=1 \text{ 側を GN 理論として確立した}}
$$

と言ってよい。
単に名前を変えたのではない。**GN の再帰・評価・非可除性・valuation exactness が一列に揃った** のじゃ。
これで GN はもう「宇宙式の見た目の多項式」ではなく、p-進評価を伴う理論対象として読める。

次は、`body_not_perfect_pow_of_squarefree_GN` の theorem 文まで一気に切れるぞい。

### x が任意の値であることについての補足

今回の GN 理論で重要なのは、\(x\) が「何でもよい」ということではなく、「**任意の値を取れる**」ということじゃ。
つまり

$$
\text{for any } x \in \mathbb{N},\quad p \mid x
$$

のような条件が入ると、\(x\) は単なる変数ではなく「差分を生む境界因子」としての役割を持ち始める。今回の valuation exactness も、まさにこの \(x\) が差分の valuation を決める境界因子であることが前提になっておる。だから「何でもよい」ではなく、「任意の値を取れる」ということが重要なのじゃ。

宇宙式の \(x\) は任意の値で実数。何でも良い。

$$
f(x) = (x+1)^2 - x(x+2) = 1
$$

という項だったから、何の意味もないと思ってたけど、ここでは主役だね

---

その通りじゃ。
そこが今回かなり大事な **見え方の反転** じゃよ。

もともと宇宙式では

$$
(x+u)^d - x^d = u \, GN_d(x,u)
$$

あるいは

$$
(x+u)^d - u^d = x \, GN_d(x,u)
$$

の \(x\) は、まず **任意の変数** として置かれておる。
この段階では、ぬしの言う通り「何でもよい」。ただの自由変数じゃ。
解析でも代数でも、恒等式としては \(x\) に特別な意味はまだない。

だがの、ひとたび

$$
x \in \mathbb{N},\quad p \mid x
$$

のような **整数条件** や **可除性条件** を入れた瞬間、\(x\) はただの座標ではなくなる。

## 1. 恒等式の中では自由変数

恒等式として見ると、

$$
(x+u)^d - u^d = x \, GN_d(x,u)
$$

は「どんな \(x\) でも成り立つ分解式」に過ぎぬ。
ここでの \(x\) は、絵を描くための横軸のようなものじゃ。

この意味では、\(x\) は主役ではない。
式全体の一部でしかない。

## 2. 可除性を入れると \(x\) が境界因子になる

ところが整数論に入ると事情が変わる。

$$
(x+u)^d - u^d = x \cdot GN_d(x,u)
$$

と因数分解されている以上、\(x\) は **差分全体を支える最前面の因子** になる。
つまり \(x\) は、単なる変数ではなく

$$
\text{boundary factor}
$$

じゃ。

今回の GN 理論で起きたことはまさにこれで、

* \(p \mid x\)
* しかし head term は \(p\) で割れない

なら

$$
p \nmid GN_d(x,u)
$$

となって、

$$
v_p\!\big((x+u)^d-u^d\big)=v_p(x)
$$

が出る。

ここでは差分の \(p\)-進評価は **全部 \(x\) が持っていく**。
つまり \(x\) は、もはや「何でもよい添え物」ではなく、 **valuation を決める境界の担い手** になっておる。

## 3. 宇宙式では自由、数論では役割を持つ

ここを整理すると、\(x\) には二つの顔がある。

### A. 連続変数としての \(x\)

$$
x \in \mathbb{R}
$$
なら、宇宙式は滑らかな恒等式じゃ。
このとき \(x\) は自由度そのもの。

### B. 離散境界としての \(x\)

$$
x \in \mathbb{N},\quad p \mid x
$$
なら、\(x\) は差分に埋め込まれた **整数的境界** になる。
このとき \(x\) は valuation や可除性を支配する主役になる。

つまり同じ記号 \(x\) でも、

$$
\text{解析の } x \quad\longrightarrow\quad \text{自由変数}
$$

$$
\text{数論の } x \quad\longrightarrow\quad \text{境界因子}
$$

と役割が変わるわけじゃ。

## 4. これはむしろ宇宙式の強み

ここが面白いところでの。
「\(x\) は何でもよい」というのは、何の意味もないのではなく、

$$
\text{あとから意味を載せられる}
$$

ということじゃ。

* 実数として見れば、連続変形の座標
* 整数として見れば、境界因子
* 素数で割れるものとして見れば、valuation の担い手
* \(x \to 0\) と見れば、微分や極限の核

となる。

つまり宇宙式の \(x\) は、最初は空の器じゃが、
文脈を入れると急に役者になる。
これは「何の意味もない」のではなく、 **意味を後付けできるだけの汎用性がある** ということじゃよ。

## 5. 今回見えた本質

今回の GN 理論で見えた本質は、こう言える。

$$
(x+u)^d-u^d
$$

の中で \(x\) は単なる変数ではなく、

$$
\text{差分を生む最小境界}
$$

として働いている。

そして head-unit 条件の下では、その境界が持つ \(p\)-進情報がそのまま差分全体の \(p\)-進情報になる。

ゆえに \(x\) は

$$
\text{自由変数} \quad\text{であると同時に}\quad \text{境界の主役}
$$

なのじゃ。

実に宇宙式らしい二面性じゃな。
最初はただの記号に見えて、深く潜ると王座に座っておる。よい発見じゃ。

次はこの視点をはっきり言葉にして、 **「\(x\) は boundary factor である」** という短い設計メモに起こすと、今後の実装コメントにも使いやすいぞい。

# FLT Branch A の干渉縞 bundle から得られた新しい cross-modular 制約の意味

うむ、今回は **かなり良い意味で「本丸の姿が濃くなった」** の。
ただの配線整理ではなく、干渉縞どうしを重ねたときに **何が必ず起こるか** が、数式として一歩深く見えた。

## 1. 状況分析

最新差分の本質は、`BranchAInterferenceFringeBundle` の上で、3 つの候補ルートをちゃんと精査し、その結果を **新しい cross-modular 制約** として固定したことじゃ。結論だけ言えば、

$$
\text{Route 1 }(q^p \mid GN \ \text{と head}) \ \text{は新規情報を生む}
$$

$$
\text{Route 2 }(p \mid q-1 \ \text{と Wieferich}) \ \text{は descent 不変量を生む}
$$

$$
\text{Route 3 }(q \nmid gap \ \text{と gap shape}) \ \text{は既知の再確認}
$$

という整理になった。しかも、それが `TriominoCosmicBranchARestore.lean` に 7 補題として sorry なしで実装されておる。

いちばん重要なのは 2 本で、

$$
\texttt{branchA\_fringe\_q\_not\_dvd\_tail\_coeff}
$$

と

$$
\texttt{branchA\_fringe\_sprime\_congr\_one\_mod\_p}
$$

じゃ。前者は tail 係数 \(M\) の \(q\)-進構造を固定し、後者は descent のたびに \(\bmod p\) 合同が保たれることを示す。つまり、**縞の重なりから新しい拘束が本当に出た** のじゃ。

## 2. 数学的解説

まず Branch A の第一縞、すなわち p-adic head 側では、すでに

$$
s^p = y^{p-1} + p^3 M
$$

という形が見えておる。
他方、第二縞の witness 側では

$$
q \mid s,\qquad q \nmid y
$$

がある。
ここで最新差分は、もし仮に \(q \mid M\) なら

$$
q \mid p^3 M
$$

となり、さらに

$$
q \mid s^p = y^{p-1} + p^3 M
$$

だから差を取って

$$
q \mid y^{p-1}
$$

となり、prime \(q\) より

$$
q \mid y
$$

が出る。これは witness 条件 \(q \nmid y\) に反する。
よって

$$
\boxed{q \nmid M}
$$

じゃ。これは見た目以上に強い。

なぜなら、同時に

$$
q^p \mid s^p = y^{p-1} + p^3 M
$$

でもあるからじゃ。
しかも \(q \nmid y\) と今示した \(q \nmid M\) から、

$$
v_q(y^{p-1}) = 0,\qquad v_q(p^3 M)=0
$$

じゃ。
それなのに

$$
v_q!\bigl(y^{p-1}+p^3 M\bigr)\ge p
$$

が起こる。
つまり **\(q\)-進評価 0 の 2 項が、和では一気に \(q^p\) まで持ち上がる**。
これが報告にある “massive cancellation” の意味じゃ。これはまさに、p-adic head 縞と q-adic witness 縞の **干渉** そのものじゃよ。

## 3. もう一つの重要な結論

もう一本の核心は、

$$
s \equiv 1 \pmod p,\qquad q \equiv 1 \pmod p,\qquad s = q s'
$$

から

$$
\boxed{s' \equiv 1 \pmod p}
$$

が出ることじゃ。
これは「descent で \(s\) を \(q\)-free quotient \((s' = s/q)\) に落としても、mod \(p\) の合同類が壊れない」という不変量じゃ。
言い換えると、降下操作は単に値を小さくするだけでなく、**縞模様の位相を保ちながら縮む**。ここはかなり面白い。

## 4. では矛盾はもう出たのか

そこまではまだ行っておらぬ。
今回得られたのは、

$$
q \nmid M
$$

と

$$
s' \equiv 1 \pmod p
$$

という、かなり非自明な拘束じゃが、直ちに `False` にはなっておらぬ。
つまり最新状態は、

$$
\text{干渉縞の共存不可能性が見え始めた}
$$

段階であって、

$$
\text{まだ最後の contradiction は出ていない}
$$

段階じゃ。

ただし、前よりずっと良い。
以前は「どこを殴ればよいか」が曖昧だった。今ははっきり

$$
q^p \mid \bigl(y^{p-1}+p^3 M\bigr),\qquad q \nmid y,\qquad q \nmid M
$$

という **極端な q-adic cancellation** が、次の山だと見えておる。
これは単なる合同式ではなく、円分核 \(\Phi_p(z,y)\) の q-adic 内部構造を反映した現象だ、と報告にも整理されておる。

## 5. FLT 証明への道の推論

ここから先の本線は、かなり絞られた。
賢狼の見立てでは、次の 3 段じゃ。

### 5.1. 第一段

今得た

$$
q^p \mid \bigl(y^{p-1}+p^3 M\bigr),\qquad q \nmid y,\qquad q \nmid M
$$

を、単なる整除事実で終わらせず、**q-adic valuation theory** として言い換える。
ここでは「二項がどのような条件のときに高次 cancellation を起こしうるか」を、一般補題として抜き出すのがよい。報告でも次課題として cyclotomic valuation theory が挙がっておる。

### 5.2. 第二段

$$
\omega = z y^{-1} \pmod q
$$

の primitive \(p\)-th root 的構造を、\(\mathbb Z/q^p\mathbb Z\) あるいは q-adic lift の言葉へ持ち上げる。
これは既存の `PrimeGe5BranchAPrimitiveRestoreQAdicLiftSeed` の延長として自然じゃ。
もしこの lift が、上の massive cancellation と整合しないと分かれば、干渉縞 bundle から `False` が出る。

### 5.3. 第三段

descent 不変量

$$
s' \equiv 1 \pmod p
$$

を鎖として追う。
もし各段で \(s \mapsto s' = s/q\) が strict に減少しながら、なお mod \(p\) の縞を保ち続けるなら、有限降下の末端でどの形が強制されるかを調べられる。
特に \(s'=1\) や極小値近傍で、先ほどの cancellation 構造と矛盾する可能性がある。報告でもこの finite-step の停止解析が次課題に挙がっておる。

## 6. いまの段階をどう評価するか

ひとことで言えば、

$$
\boxed{
\text{本丸はまだ open。だが、干渉縞の「形」はかなり確定した。}
}
$$

今回の最大の成果は、Branch A の contradiction を

* ただの mod \(p^k\) conflict
* ただの q-witness existence

としてではなく、

$$
\text{p-adic head} \quad+\quad \text{q-adic witness}
$$

の **cross-modular interference** として見えるようにしたことじゃ。
特に

$$
q \nmid M
$$

と

$$
q^p \mid \bigl(y^{p-1}+p^3M\bigr)
$$

の同時成立は、今後の理論を刺すべき一点をかなり鮮明にしておる。

## 7. 総括

だから現状の数学的解説としては、こうまとめるのがよい。

Branch A では、normal form が p-adic head 縞

$$
s^p = y^{p-1}+p^3M
$$

を固定し、witness \(q\) が q-adic/cyclotomic 縞

$$
q \mid s,\quad q \nmid y,\quad q^p \mid GN,\quad q \equiv 1 \pmod p
$$

を固定する。
今回の実装は、この二系統の縞を bundle 上で掛け合わせた結果として

$$
q \nmid M,\qquad s' \equiv 1 \pmod p
$$

を導いた。
前者は **massive cancellation** の存在を、後者は **descent の縞不変性** を表す。
よって FLT 証明への次の道は、この cancellation が本当に自然数世界で起こりうるのかを、cyclotomic valuation / Hensel lifting / descent chain のいずれかで否定することにある。

よい進み方じゃ。
いまは「森を彷徨う段」ではなく、「獲物の足跡がはっきり 2 本の縞として見えた段」じゃよ。

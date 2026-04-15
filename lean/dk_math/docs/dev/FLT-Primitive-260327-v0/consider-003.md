# Branch A の primitive input と Zsigmondy / cyclotomic 語彙の接続について

うむ、接続の筋は **かなりはっきり** しておる。
結論から言うと、

$$
\text{distinguished-prime target}
$$

は本質的に

$$
\text{「指数 } p \text{ の冪差に対する primitive prime divisor」}
$$

そのものじゃ。いま切り出した target も、まさに
(q \mid GN,p,(z-y),y) かつ (q \nmid (z-y)) を要求しておる。これは packet restoration から独立した「prime を 1 本取る段」として分離された、という整理じゃな。  

## 1. いちばん自然な接続

まず指数 (p) の冪差を

$$
a := z,\qquad b := y,\qquad d := p
$$

と置く。すると

$$
z^p-y^p=(z-y),\Phi_p(z,y)
$$

で、(p) が素数のとき

$$
\Phi_p(z,y)=z^{p-1}+z^{p-2}y+\cdots+y^{p-1}
$$

じゃ。
そしてこの homogeneous cyclotomic factor が、ちょうど

$$
GN,p,(z-y),y
$$

と一致する見え方になっておる。つまり distinguished-prime target は、実質

$$
\exists q,\quad q\mid \Phi_p(z,y),\quad q\nmid(z-y)
$$

を取れ、という話なんじゃよ。

これはまさに Zsigmondy / cyclotomic 語彙に寄せた言い換えそのものじゃ。

## 2. 既存エンジンとの接続点

INDEX の整理でも、FLT 幹線は

* `DiffPow` が差の冪の分解装置
* `GcdDiffPow` / `GcdLemmas` が gcd 制御
* `ZsigmondyCyclotomic` が原始素因子エンジン

という流れで組まれておる。さらに Zsigmondy 側には

* `exists_prime_divisor_not_dividing_diff_of_prime_exp`
* `exists_primitive_prime_factor_basic`
* `pow_sub_pow_factor_cosmic_N`
* `cyclotomic_*`
* `padicValNat_of_primitive_prime_factor_via_G`

のような、まさに今回の橋に使いたい部品群が並んでおる。  

ゆえに、設計としては

$$
\text{difference-of-powers primitive prime}
;\Longrightarrow;
\text{GN 側 distinguished prime}
$$

という薄い adapter を 1 本置けばよい。

## 3. 実際の橋の形

理想的には、次の 2 段じゃな。

### 3.1. cyclotomic / Zsigmondy 側で prime を取る

まず Zsigmondy 側で

$$
\exists q,\quad \text{Nat.Prime } q \land q\mid z^p-y^p \land q\nmid(z-y)
$$

を得る。

### 3.2. cosmic factorization で GN 側へ落とす

次に

$$
z^p-y^p=(z-y),GN,p,(z-y),y
$$

を使う。
(q\nmid(z-y)) かつ (q\mid z^p-y^p) なら、素数の Euclid 的性質から

$$
q\mid GN,p,(z-y),y
$$

が従う。
するとそのまま distinguished-prime target の返り値

$$
\exists q,\ \text{Nat.Prime }q \land q\mid GN,p,(z-y),y \land q\nmid(z-y)
$$

になる。

つまり **数学の中身は Zsigmondy、target への着地は cosmic factorization** じゃ。

## 4. ただし、ここにひとつ大きな段差がある

ここが今回いちばん大事なところじゃ。

お主の current Branch A primitive input には

$$
p \mid (z-y)
$$

が **最初から入っておる**。一方、既存の prime-exponent の primitive-prime existence は、少なくとも設計上は
「差の側に指数 (p) がべったり乗っていない」型、すなわち `¬ p ∣ a-b` を前提にしている流れで整理されておる。 INDEX でも、gcd 制御で「既知の素因子」と「新しい素因子」を分離する層が先にあり、その上に `exists_prime_divisor_not_dividing_diff_of_prime_exp` や `exists_primitive_prime_factor_basic` が載っておる。

ゆえに、 **既存の basic Zsigmondy existence をそのまま (a=z,b=y,d=p) に代入して終わり** 、とはならぬ可能性が高い。

ここは正直に言えば、

$$
\text{Branch A は Zsigmondy の「例外寄り局所枝」}
$$

として扱うのが自然じゃな。

## 5. したがって接続案は 2 本ある

### 5.1. 王道案

`ZsigmondyCyclotomic` に **Branch A 専用の存在補題** を足す。

形は例えばこんな感じじゃ。

$$
\forall \cdots,\
p\mid(z-y)\ \to
y^{p-1}\equiv 1 \pmod{p^2}\ \to
\exists q,\ \text{Nat.Prime }q \land q\mid z^p-y^p \land q\nmid(z-y)
$$

そしてその後で cosmic factorization により distinguished target へ落とす。

これは「cyclotomic / Zsigmondy 語彙へ寄せる」という今の方針と最も整合的じゃ。

### 5.2. 軽量算術案

いま既に input に

$$
GN,p,(z-y),y = p\cdot s^p,
\qquad \gcd(t,s)=1,
\qquad p\nmid s,
\qquad z-y=p^{p-1}t^p
$$

が入っておるので、実は distinguished prime は
**(s) の素因子** から直接取れる可能性がある。

なぜなら (z-y) の素因子は (p) と (t) から来るが、(s) は

* (p) と互いに素
* (t) と互いに素

だから、(s) の素因子 (q) は自動的に

$$
q\mid GN,p,(z-y),y,\qquad q\nmid(z-y)
$$

を満たすからじゃ。

この案の弱点は、 **(s>1) をどう保証するか** が別問題になること。
もし (s=1) が落とせぬと、(GN=p) のような退化が残る。
ゆえに、お主のメモにある「local arithmetic 条件をさらに足すか」の判断がここへ直結しておる。

## 6. わっちの見立て

いまの目的が **target を cyclotomic / Zsigmondy 語彙へ寄せること** なら、先に置くべきはこれじゃ。

## A. 提案する新補題

`PrimeGe5BranchA_cyclotomic_distinguished_prime`

中身:

* Branch A primitive normal form の仮定
* (p\mid(z-y))
* Wieferich witness
* 必要なら小さな local arithmetic 追加条件

から

$$
\exists q,\ \text{Nat.Prime }q \land q\mid(z^p-y^p) \land q\nmid(z-y)
$$

を返す。

## B. その後の薄い橋

`distinguishedPrimeTarget_of_cyclotomic_prime`

中身:

* 上の (q)
* `pow_sub_pow_factor_cosmic_N`

から

$$
q\mid GN,p,(z-y),y
$$

を導き、目標 target に着地する。

---

つまり、接続はこうじゃ。

$$
\text{Branch A primitive data}
$$

$$
\Longrightarrow
\text{cyclotomic / Zsigmondy existence on } z^p-y^p
$$

$$
\Longrightarrow
q\nmid(z-y),\ q\mid(z^p-y^p)
$$

$$
\Longrightarrow
q\mid GN,p,(z-y),y
$$

$$
\Longrightarrow
\text{PrimeGe5BranchAPrimitiveDistinguishedPrimeTarget}
$$

この形が、いちばん綺麗で再利用性も高い。

ただし本音を言うと、Branch A では (p\mid(z-y)) が強く効いておるので、 **既存 Zsigmondy 補題の単純再利用ではなく、Branch A 専用の cyclotomic existence 補題を 1 本新設する** のが筋が良いと思うぞい。

次に進めるなら、わっちはその補題の **Lean 宣言案と仮定最小化** を、いまの target 形に合わせてそのまま書き下せる。

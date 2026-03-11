# なぜ Zsigmondy の中心は GN になるのか

What is the reason why GN becomes the center of Zsigmondy?

> 👩‍⚕️私D.:

「GN が Zsigmondy の中心になる理由」

> 🐺賢狼:

うむ、ではそこを切ろう。
これはかなり大事な話じゃ。結論から言えば、

\[
\boxed{GN \text{ は } a^n-b^n \text{ の「境界を剥いだ本体」だから}}
\]

じゃな。

もっと露骨に言うと、Zsigmondy が追っているのは
「**今回の指数 \(n\) で初めて現れる新しい素数**」であり、
その新しさはふつう

\[
a-b
\]

のような **古い境界因子** には宿らぬ。
宿るのは、その先にある内部核――つまり

\[
\frac{a^n-b^n}{a-b}
\]

じゃ。
ぬしの記法では、それがまさに \(GN\) / Kernel 側なんじゃ。

---

## 1. 出発点は差の冪因数分解

古典の基本はこれじゃ。

\[
a^n-b^n = (a-b)\sum_{i=0}^{n-1} a^{n-1-i}b^i
\]

ここで

\[
a=x+u,\qquad b=u
\]

と置けば

\[
a-b=x
\]

で、

\[
a^n-b^n = x \cdot GN(n,x,u)
\]

というぬしの宇宙式になる。

つまり GN は

\[
GN(n,x,u)=\frac{(x+u)^n-u^n}{x}
\]

であり、**Body を boundary \(x\) で割った内部商** じゃな。

Zsigmondy は
「\(a^n-b^n\) を割る素数のうち、過去の \(a^m-b^m\) (\(m<n\)) には出てこなかったもの」
を探す理論じゃから、最初からいる \(a-b\) の因子は主役ではない。

この時点で、中心が \(GN\) に寄る理由が見えておる。

---

## 2. boundary は“古い”、GN は“今回の本体”

\(a^n-b^n\) を割る素数 \(q\) を見たとき、まず二種類ある。

### A. 古い素数

\[
q \mid a-b
\]

これは指数 \(n\) とは無関係に、最初から境界差に付いている。
新しさがない。

### B. 今回の内部素数

\[
q \nmid a-b,\qquad q \mid a^n-b^n
\]

このとき

\[
q \mid \frac{a^n-b^n}{a-b}
\]

じゃ。

つまり、**primitive prime になりうる候補は GN 側に落ちる**。
ぬしが Lean で作った

``` id="0zv0m4"
q ∣ Body, q ∤ boundary → q ∣ Kernel / GN
```

という API は、まさにこの数論的本質を形式化したものなんじゃ。

---

## 3. primitive の“新しさ”は GN にしか現れない

primitive prime divisor の条件は

\[
q \mid a^n-b^n
\]

だが

\[
q \nmid a^m-b^m \qquad (0<m<n)
\]

じゃったな。

ところが \(a-b\) は

\[
a^1-b^1
\]

そのものじゃ。
だから

\[
q \mid a-b
\]

なら、その時点で \(m=1\) に出てしまう。
それは primitive ではありえぬ。

ここが決定的じゃ。

つまり primitive prime は構造上、

\[
q \nmid a-b
\]

でなければならぬ。
ゆえに

\[
q \mid \frac{a^n-b^n}{a-b}
\]

へ強制的に押し込まれる。
**この“primitive の定義そのもの”が GN を中心へ押し上げる** のじゃ。

---

## 4. 群論でも中心は GN に寄る

Zsigmondy の深い中身は、位数 `orderOf` の話じゃ。

\(q \nmid ab\) として mod \(q\) で見ると、

\[
a^n \equiv b^n \pmod q
\]

だから

\[
\left(a b^{-1}\right)^n \equiv 1 \pmod q
\]

となる。
つまり

\[
\operatorname{ord}_q(a/b) \mid n.
\]

さらに primitive なら lower exponent では割らないので、

\[
\operatorname{ord}_q(a/b)=n
\]

となる。

さて、この議論で重要なのは \(a-b\) そのものではない。
重要なのは **\(a/b\) が \(n\) 次の回転を初めて閉じること** じゃ。

この「今回初めて閉じる」情報は、境界 \(a-b\) にはなく、

\[
a^n-b^n
\]

の内部商、すなわち GN 側にある。

だから群論的に見ても、Zsigmondy の核は boundary ではなく GN なんじゃ。

---

## 5. cyclotomic 的にも GN が本体

さらに古典数論では

\[
a^n-b^n=\prod_{d\mid n}\Phi_d(a,b)
\]

と分解する。
ここで primitive prime は本質的に

\[
\Phi_n(a,b)
\]

を割る素数じゃ。

この \(\Phi_n\) は「今回の \(n\) に対応する新しい層」であって、
\(a-b\) のような最初の線形因子ではない。

ぬしの宇宙式で言えば、

- boundary \(x=a-b\) は最初の外殻
- GN はその外殻を剥いだ内部本体
- \(\Phi_n\) はその内部本体の中でも「今回の次数だけに属する純核」

という感じじゃな。

だから cyclotomic の立場でも、Zsigmondy の中心は GN 側にある。

---

## 6. FLT に効くのも GN 側

FLT 的に重要なのは
「\(a^n-b^n\) が \(n\) 乗らしく見えてしまうのを壊す新しい素数」
じゃ。

その新しい素数がもし boundary \(a-b\) にいるだけなら、話は弱い。
境界は昔からある因子だからの。

だが primitive prime が GN を割るなら、
それは **高次内部構造そのものに新しい素数が食い込む** ことを意味する。

これが valuation や squarefree 制御に直結する。

とくに \(n=3\) では

\[
GN(3,x,u)=x^2+3xu+3u^2
\]

で、ぬしの \(S0\) と一致する。
つまり FLT \(d=3\) での矛盾核は、

\[
a^3-b^3 = (a-b)\,S0
\]

のうち、**新しい素数が S0 側に現れる** ことにある。
ここで GN が本丸になるわけじゃ。

---

## 7. Beam ではなく GN が中心になる理由

ここで Beam と比べると、差がはっきりする。

### Beam

\[
Body = Core + Beam
\]

これは **和の分解**。
構造観測には向くが、

\[
q \mid Body
\]

から直接

\[
q \mid Beam
\]

は言えぬ。

### GN

\[
Body = boundary \cdot GN
\]

これは **積の分解**。

\[
q \mid Body,\ q \nmid boundary
\Rightarrow q \mid GN
\]

が即座に出る。

Zsigmondy は「新しい prime がどこへ落ちるか」を扱う理論じゃから、
**和より積の分解のほうが圧倒的に強い**。
ゆえに GN が中心になる。

---

## 8. 宇宙式の言葉でまとめると

ぬしの語彙で言うなら、こうじゃ。

- **Big**
  \[
  (x+u)^n
  \]

- **Gap**
  \[
  u^n
  \]

- **Body**
  \[
  (x+u)^n-u^n
  \]

- **boundary**
  \[
  x
  \]

- **GN**
  \[
  \frac{Body}{x}
  \]

ここで primitive prime は
「Gap を引いた差分世界 Body のうち、さらに boundary を剥いだ内部核」
に現れる。

つまり GN とは、ぬしの宇宙式で言えば

\[
\boxed{\text{“今回初出の素因子が宿る最初の内部核”}}
\]

なんじゃ。

これはなかなか美しい位置づけじゃよ。

---

## 9. 一言で本質

一番短く言えばこうじゃ。

\[
\boxed{
\text{Zsigmondy は } a^n-b^n \text{ の新因子理論であり、}
a-b \text{ は古すぎる。だから中心は } GN.
}
\]

あるいは

\[
\boxed{
\text{primitive prime は boundary を避けるので、必然的に GN に落ちる。}
}
\]

これじゃな。

---

## 10. 賢狼の見立て

わっちの見立てでは、ぬしの DkMath において GN は単なる補助多項式ではない。
かなり本質的に

- 差の冪因数分解
- primitive prime divisor
- cyclotomic 新因子
- FLT の矛盾核

をまとめる **中心座標** になっておる。

Beam は景色を見せる。
GN は敵を刺す。
そういう役割分担じゃな。

次に掘るなら、かなり面白いのは

\[
GN(p,x,u)\equiv p\,u^{p-1}\pmod{x}
\]

や

\[
\gcd(x,GN(p,x,u))\mid p\,u^{p-1}
\]

が、なぜ primitive の“新しさ”と噛み合うのか、という点じゃ。
ここは Zsigmondy と gcd 制御がきれいに接続する場所なんじゃ。

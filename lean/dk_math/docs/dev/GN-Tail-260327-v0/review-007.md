#

うむ、推論できる。
しかも、いまのワークスペース状況から見ると、 **次に探すべき数学はかなり絞れておる** 。

## 1. 結論

わっちの見立てはこうじゃ。

* **composite reduction** は標準補題の整備で埋まる
* **Branch A 最終核** は、比較路線の続きではなく
  **shape から Wieferich 型合同を引く補題** が本命

つまり、重い新発見が要るのは Branch A のほうじゃ。

---

## 2. composite reduction は、ほぼ設計問題

ここはお主の整理どおりで、基本は

$$
n = m p
$$

と書いて

$$
X := x^m,\quad Y := y^m,\quad Z := z^m
$$

と置けば、

$$
x^n + y^n = z^n
$$

から

$$
X^p + Y^p = Z^p
$$

へ落ちる、という縮約じゃな。

必要なのは、ほぼ次の 2 本だけじゃ。

### 2.1. 指数縮約補題

$$
n \text{ composite},\ n \ge 4
\Rightarrow
n = 4 \text{ or } \exists p,\ p \text{ odd prime},\ p \mid n
$$

### 2.2. 冪のまとめ上げ補題

$$
x^n+y^n=z^n,\quad n=mp
\Rightarrow
(x^m)^p + (y^m)^p = (z^m)^p
$$

さらに coprime は

$$
\gcd(x,y)=1 \Rightarrow \gcd(x^m,y^m)=1
$$

で保存されるから、prime exponent case へそのまま渡せる。

これは **新しい数論の山** ではなく、Lean の段取りの山じゃ。
だから順番としては、こっちを先に埋めるのが得策じゃよ。

---

## 3. Branch A は comparison の続きではなさそう

ここが本題じゃ。

お主が挙げた残り形は

$$
u = p^{p-1} t^p,
\qquad
GN(p,u,y)=p,s^p,
\qquad
\gcd(t,s)=1
$$

のようなものじゃったな。

この形を見たとき、まず起きる大事なことは

$$
(u+y)^p - y^p = u \cdot GN(p,u,y)
$$

なので、

$$
(u+y)^p - y^p=
p^{p-1} t^p \cdot p s^p = p^p (ts)^p=
(pts)^p
$$

となることじゃ。

つまり shape が出た時点で、差冪はもう

$$
a^p - b^p = T^p
$$

という **完全な FLT 形** になっておる。

ただし、ここで primitive-prime route は使えぬ。
なぜなら今回の stubborn branch は

$$
p \mid u
$$

だからじゃ。
ゆえにこれは「primitive prime 不在 branch」であり、別の obstruction が要る。

---

## 4. 本命推論. shape から Wieferich が出る

わっちがいちばん有望と見るのはこれじゃ。

(u = p^{p-1} t^p) を (GN) に代入すると、

$$
GN(p,u,y) =
\sum_{k=0}^{p-1} \binom{p}{k+1} u^k y^{p-1-k}
$$

で、先頭項は

$$
p,y^{p-1}
$$

じゃ。

そして (k \ge 1) の項は、(u) が (p^{p-1}) を含むせいで、全部かなり高い (p)-冪で割れる。
実際には

$$
GN(p,u,y)=p,y^{p-1}+p^p M
$$

という形が見えるはずじゃ。

いま仮定で

$$
GN(p,u,y)=p,s^p
$$

だから、割って

$$
s^p = y^{p-1} + p^{p-1} M
$$

となる。

ここで (p \ge 5) なら (p-1 \ge 2) なので、

$$
s^p \equiv y^{p-1} \pmod{p^2}
$$

じゃ。

さらに (y) は (p) と互いに素、したがって (s) も (p) と互いに素になる。
mod (p) で見ると

$$
y^{p-1}\equiv 1 \pmod p
$$

だから

$$
s^p \equiv 1 \pmod p
$$

よって

$$
s \equiv 1 \pmod p
$$

が出る。すると

$$
s^p \equiv 1 \pmod{p^2}
$$

なので、結局

$$
y^{p-1}\equiv 1 \pmod{p^2}
$$

じゃ。

これはもう **Wieferich 型合同** そのものじゃよ。

---

## 5. つまり Branch A の出口候補はこれ

推論としては、Branch A の shape は

$$
\text{shape}
\Rightarrow
\text{Wieferich witness}
$$

を生む可能性が高い。

しかも (u) は (p^{p-1}) を含むから (p^2 \mid u) でもあり、

$$
z = y+u \equiv y \pmod{p^2}
$$

なので、そこから

$$
z^{p-1} \equiv y^{p-1} \equiv 1 \pmod{p^2}
$$

まで伸びるかもしれぬ。

これはかなり強い。
つまり探すべき新補題は、抽象的な「smaller counterexample」そのものではなく、まずは

$$
\boxed{
u = p^{p-1} t^p,\ GN = p s^p
\Rightarrow
y^{p-1}\equiv 1 \pmod{p^2}
}
$$

という合同補題じゃ。

---

## 6. Lean で狙うべき補題名

わっちなら、先にこの 3 段で切る。

### 6.1. GN の合同展開

$$
GN(p,p^{p-1}t^p,y)\equiv p,y^{p-1}\pmod{p^p}
$$

候補名:
`GN_prime_gap_shape_mod_p_pow`

### 6.2. shape から divided congruence

$$
GN = p s^p
\Rightarrow
s^p \equiv y^{p-1} \pmod{p^2}
$$

候補名:
`shapeValue_divided_implies_pthpow_congr`

### 6.3. Wieferich 帰結

$$
s^p \equiv y^{p-1}\pmod{p^2},\ s\equiv 1\pmod p
\Rightarrow
y^{p-1}\equiv 1\pmod{p^2}
$$

候補名:
`branchA_shape_implies_wieferich`

これが通れば、その先は既存の Wieferich/No-Wieferich/descent 機械へ差し込める可能性が高い。

---

## 7. いま本当に探すべきもの

だから、問いにまっすぐ答えるとこうじゃ。

### 7.1. まず埋めるべき

**composite exponent reduction**

これは工程を閉じるための標準補題じゃ。

### 7.2. 本当の新数学として探すべき

**Branch A shape (\Rightarrow) Wieferich witness**

comparison route をもう少し掘るのではなく、
shape の持つ (p)-進合同を抽出する方向へ舵を切るべきじゃ。

---

## 8. わっちの見立てを一文で

$$
\boxed{
\text{Branch A の残核は descent そのものではなく、
まず「shape から Wieferich」を証明せよ}
}
$$

その後に既存の descent / no-Wieferich bridge に渡す。
この順がいちばん筋が良い。

次に詰めるなら、わっちなら
**`GN(p, p^(p-1)t^p, y) = p y^(p-1) + p^p M` の補題文**
から起こすぞい。

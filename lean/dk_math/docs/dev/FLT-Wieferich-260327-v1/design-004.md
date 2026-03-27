# PrimeGe5BranchASmallerCounterexampleTarget をどう攻めるか

うむ。ここは、かなりはっきり言える。

**いきなり ((x',y',z')) を当てに行ってはならぬ。**
作るべきはまず **より小さい Branch A normal-form packet** じゃ。
その packet さえ作れれば、`\(\texttt{PrimeGe5CounterexamplePack}\)` への再包装は機械的にできる。

## 1. . まず何を作るべきか

いま手元にあるのは Branch A の正規形

$$
u := z-y = p^{p-1} t^p,
\qquad
GN\bigl(p,u,y\bigr) = p,s^p,
\qquad
x = p(ts),
$$

じゃな。

ここから本当に欲しいのは、直接の

$$
x'^p + y'^p = z'^p
$$

ではなく、同じ形の **小さい packet**

$$
u' = z'-y' = p^{p-1} {t'}^p,
\qquad
GN\bigl(p,u',y'\bigr) = p,{s'}^p,
\qquad
x' = p(t's'),
\qquad
z' < z.
$$

これが取れた瞬間に、

$$
x'^p
====

# u' \cdot GN(p,u',y')

# (z'-y') \cdot GN(p,z'-y',y')

z'^p-y'^p
$$

より

$$
x'^p + y'^p = z'^p
$$

が復元できる。
つまり、 **smaller counterexample は smaller normal-form packet から作る** のじゃ。

これが第一の答えじゃよ。

---

## 2. . Lean ではこの型に切るのがよい

わっちなら、先にこれを定義する。

```lean
structure PrimeGe5BranchANormalFormPacket (p : ℕ) where
  x y z t s : ℕ
  pack : PrimeGe5CounterexamplePack p x y z
  hp_dvd_gap : p ∣ (z - y)
  hgap : z - y = p ^ (p - 1) * t ^ p
  hsGN : GN p (z - y) y = p * s ^ p
  hsx : x = p * (t * s)
```

そして、

```lean
theorem counterexamplePack_of_branchANormalFormPacket
    {p : ℕ} (pkt : PrimeGe5BranchANormalFormPacket p) :
    PrimeGe5CounterexamplePack p pkt.x pkt.y pkt.z := pkt.pack
```

はただの再利用でよい。

次に本命はこれじゃ。

```lean
abbrev PrimeGe5BranchASmallerPacketTarget : Prop :=
  ∀ {p x y z t s : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
```

そして最後に

```lean
theorem primeGe5BranchASmallerCounterexample_of_smallerPacket
    (hSmall : PrimeGe5BranchASmallerPacketTarget) :
    PrimeGe5BranchASmallerCounterexampleTarget := by
  ...
```

で落とす。
つまり、 **smaller counterexample target の中身は、smaller packet target に吸わせる** のが筋じゃ。

---

## 3. . では、その smaller packet をどう作るか

ここが本丸じゃ。
結論から言うと、道は二本ある。

### 3.1. . 第一の道. (p)-進深さを 1 段剥く

まず

$$
\nu_p(u) = \nu_p(z-y) = (p-1) + p,\nu_p(t)
$$

じゃ。
したがって、もし (p \mid t) なら

$$
\nu_p(u) \ge (p-1)+p
$$

で、gap に **余分な (p^p)** が入っておる。

この場合、狙うべきは「即 smaller counterexample」ではなく、

$$
u = p^{p-1} t^p = p^{p-1} (p t_1)^p = p^{2p-1} t_1^p
$$

という **余剰 (p)-深さ** を、別の Branch A packet へ移送する補題じゃ。
つまり、

$$
\text{余分な distinguished-prime 深さ}
;\Longrightarrow;
\text{smaller packet}
$$

という contract を切る。

Lean ではたとえば

```lean
abbrev PrimeGe5BranchAValuationPeelTarget : Prop :=
  ∀ {p x y z t s : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    p ∣ t →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
```

こんな切り方じゃな。

この route の良いところは、 **完全に Nat / valuation 層のまま進める** ことじゃ。
いまの workspace に一番馴染む。

---

### 3.2. . 第二の道. primitive distinguished-prime core に入ったら descent を作る

もし

$$
p \nmid t
$$

なら、もう gap の (p)-進深さは最小形

$$
\nu_p(z-y)=p-1
$$

まで剥けておる。
このときは、Nat の式変形だけで新しい ((x',y',z')) を作るのは、かなり難しい。

ここでは、はっきり言う。
**この場合の本命は cyclotomic / Kummer 型の下降じゃ。**

つまり、Branch A は本質的に「FLT 第二場合」の形なので、

$$
z^p-y^p = (z-y)\prod_{k=1}^{p-1}(z-\zeta^k y)
$$

の側で distinguished prime ((1-\zeta)) を剥き、

$$
z-\zeta y = \varepsilon (1-\zeta)\alpha^p
$$

型の表示を作り、その (\alpha) から **小さい packet** を再構成する。
古典の流儀そのものじゃ。

いまの DkMath の流れで言えば、ここで作るべき target は

```lean
abbrev PrimeGe5BranchACyclotomicDescentTarget : Prop :=
  ∀ {p x y z t s : ℕ},
    PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    z - y = p ^ (p - 1) * t ^ p →
    GN p (z - y) y = p * s ^ p →
    x = p * (t * s) →
    Nat.Coprime t s →
    ¬ p ∣ t →
    ¬ p ∣ s →
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
```

のようなものじゃな。

これは「Nat だけで直接 ((x',y',z')) を書け」という要求ではない。
**cyclotomic 層で smaller packet の存在を返し、Nat 側ではそれを再包装する** という設計にするのが、いちばん美しい。

---

## 4. . 何を新しい種にするか

ここでひとつ、重要な式がある。

$$
GN\bigl(p,p^{p-1}t^p,y\bigr) = p,s^p
$$

を (p) で割ると、

$$
s^p
===

y^{p-1}
+
p^{p-1} t^p , B
$$

という形の整数 (B) が出る。
なぜなら (GN) の先頭項は (p,y^{p-1}) で、残りはすべて (u = p^{p-1}t^p) を 1 回以上含むからじゃ。

この式はとても大事じゃ。

$$
\boxed{
s^p - y^{p-1} = p^{p-1} t^p,B
}
$$

つまり、Branch A packet の内部には、もう一つの **差分核** が埋まっておる。
わっちの見立てでは、smaller packet を作るなら、この (B) が種になる。

ただし注意点として、これだけではまだ

$$
x'^p + y'^p = z'^p
$$

の形にはなっておらぬ。
なので、この式は **そのまま counterexample ではなく、descent の入力核** として使うべきじゃ。

---

## 5. . だから、いま何から始めるべきか

順番はこうじゃ。

### 5.1. . 先に mechanical layer を固める

まず `SmallerCounterexampleTarget` の前に `SmallerPacketTarget` を置く。
これは必須じゃ。ここを分けぬと、どの descent が成功したのかが見えぬ。

### 5.2. . その次に valuation peel を試す

(p \mid t) の場合に smaller packet を返す route を、Nat / valuation だけで詰める。
これは比較的近い。

### 5.3. . primitive case は cyclotomic descent に切る

$$
p \nmid t
$$
まで来たら、もう Nat だけで explicit に三つ組をひねり出そうとせず、
distinguished-prime descent の algebraic kernel を切る。

---

## 6. . 一番大事な一文

要するに、こうじゃ。

$$
\boxed{
\text{smaller counterexample は直接作らぬ。
先に smaller Branch A normal-form packet を作り、それを再包装する。}
}
$$

そしてその packet の生成法は二段構え：

$$
\text{(p)-進深さが余るときは valuation peel},
\qquad
\text{primitive core では cyclotomic descent}.
$$

これが、いまの workspace に最も噛み合う道筋じゃよ。

必要なら次に、`PrimeGe5BranchANormalFormPacket` と `SmallerPacketTarget` の Lean 雛形を、そのまま貼れる形で起こす。

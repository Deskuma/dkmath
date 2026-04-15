# Review: GN 理論の primitive prime factor を使った obstruction への進展

おお、これはかなり良いぞい。
しかも今回は、ただ theorem を足しただけではなく、 **primitive-prime 路線を squarefree 路線と対称な設計へ揃えた** のが本質じゃ。そこを解説込みで整理するぞい。

## 1. 今回なにをしたのか

追加された核は 2 本じゃ。

### 1. `PrimitiveBeam` 側の pure obstruction

$$
\texttt{primitive_prime_factor_forbids_perfect_pow_diff}
$$

これは差冪そのもの

$$
a^d - b^d
$$

が (d) 乗完全冪になれないことを、 **primitive prime factor の存在** から直接示す定理じゃ。

### 2. `Gcd.GN` 側の Body 座標 wrapper

$$
\texttt{body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add}
$$

これは

$$
a := x+u,\qquad b := u
$$

と置いて、Body 座標

$$
(x+u)^d-u^d
$$

の形から、上の pure obstruction を起動する wrapper じゃ。

つまり構造はこうなった。

$$
\text{diff-side pure theorem}
\quad\Longrightarrow\quad
\text{Body coordinate wrapper}
$$

この二層構成は、先に作った squarefree route とぴたり対称じゃ。

---

## 2. `primitive_prime_factor_forbids_perfect_pow_diff` の中身

この定理の意味を、Lean の流れに沿って噛み砕くぞい。

仮定はおおむねこうじゃ。

* (d) は素数
* (d \ge 3)
* (b < a)
* (b > 0)
* (\gcd(a,b)=1)
* (d \nmid (a-b))

このとき

$$
a^d - b^d = t^d
$$

となる (t) は存在しない、という主張じゃ。

### 証明の骨格

まず primitive prime factor (q) を 1 本とる。

$$
q \mid a^d-b^d,\qquad q \nmid a-b
$$

で、しかも (q) は素数じゃ。これは
`exists_primitive_prime_factor_as_prop` で得ておる。

次に、もし

$$
a^d-b^d=t^d
$$

だったと仮定すると、

$$
q \mid t^d
$$

となるので、素数性から

$$
q \mid t
$$

が従う。すると

$$
v_q(t)\ge 1
$$

ゆえに

$$
v_q(t^d)=d,v_q(t)\ge d
$$

となる。ここは `padicValNat_pow` と `dvd_of_dvd_pow` を使ってきれいに押しておる。

一方で primitive prime factor については、

$$
q \nmid a-b
$$

という「boundary を割らない」性質がある。
すると既存の valuation 上界補題から

$$
v_q(a^d-b^d)\le 1
$$

が出る。

しかし (a^d-b^d=t^d) だから

$$
v_q(a^d-b^d)=v_q(t^d)\ge d
$$

で、(d\ge 3) だからこれは

$$
v_q(a^d-b^d)\le 1
$$

と両立せぬ。矛盾じゃ。

### 要するに何が起きているか

primitive prime factor (q) は、

* 差冪 (a^d-b^d) には現れる
* だが boundary (a-b) には現れない

という「新しい素因子」じゃ。
そのため、その (q) に関する valuation は高くならず、せいぜい 1 回しか現れない。
ところが完全 (d) 乗なら、素因子の指数は全部 (d) の倍数にならねばならぬ。
この衝突で完全冪が折れるわけじゃ。

---

## 3. これがなぜ美しいか

今回の pure obstruction は、実はかなり重要な位置におる。

先の squarefree route は、ざっくり言うと

$$
\text{GN が squarefree}
\Rightarrow
\text{ある素因子の指数が }1
\Rightarrow
\text{完全 }d\text{ 乗でない}
$$

という流れじゃった。
今回の primitive-prime route は

$$
\text{primitive prime factor の存在}
\Rightarrow
\text{その素因子の指数が高々 }1
\Rightarrow
\text{完全 }d\text{ 乗でない}
$$

という流れじゃ。

つまり両者とも本質は同じで、

$$
\text{ある素数で valuation が }1\text{ しか立たない}
$$

ことを obstruction にしておる。
ただ、その「指数 1 の素数」を得る原理が違うだけじゃ。

* squarefree route: kernel 自体の平方自由性
* primitive-prime route: primitive prime の新出性

この対称性が、とても良い。

---

## 4. `body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add` の意味

こちらは Body 座標で使いやすくする薄い wrapper じゃ。

仮定は

* (d) は素数
* (3 \le d)
* (x>0)
* (u>0)
* (\gcd(x+u,u)=1)
* (d \nmid x)

で、結論は

$$
\neg \exists t>0,\ (x+u)^d-u^d=t^d
$$

じゃ。

### 何をしているか

単に

$$
a:=x+u,\qquad b:=u
$$

と置き換えて、diff-side theorem を呼び出しているだけじゃ。
だが、これが大事なのは、利用者がもう

$$
a,b
$$

の差冪世界で考えなくてよく、最初から宇宙式の Body 座標で使えることじゃな。

しかも

$$
a-b=(x+u)-u=x
$$

だから、

$$
d \nmid (a-b)
$$

という primitive-prime theorem 側の仮定は、そのまま

$$
d \nmid x
$$

に読み替わる。
この読み替えが `simpa [Nat.add_sub_cancel_left]` で綺麗に片付いておる。ここは実装として上手い。

---

## 5. いま理論全体がどう見えるか

今回で obstruction 層は、かなり整った。

### A. squarefree route

* pure obstruction は `CosmicFormulaBinom`
* coprime supply / wrapper は `Gcd.GN`

### B. primitive-prime route

* pure obstruction は `PrimitiveBeam`
* Body wrapper は `Gcd.GN`

つまり役割分担はこうじゃ。

$$
\text{pure theorem} \quad+\quad \text{coordinate wrapper}
$$

を各 route ごとに持つ、という統一設計になった。

これは後で theorem を増やすときにも効く。
「本体はどこに置くか」「Body 座標化はどこでやるか」が、もう迷わずに済む。

---

## 6. 宇宙式の (x) がまた主役になっている

ここも面白いところじゃな。
先ほど話した通り、宇宙式では (x) は最初ただの自由変数に見える。
だが Body 座標に入ると、

$$
(x+u)^d-u^d
$$

の boundary は

$$
x=(x+u)-u
$$

になる。
primitive-prime route でも squarefree route でも、この (x) が

* boundary
* gap difference
* divisibility condition の担い手

として主役に立っておる。

今回の wrapper でも仮定が

$$
d \nmid x
$$

という boundary 条件になっておるのは、その表れじゃ。
つまり (x) は単なる任意変数ではなく、 **Body と Gap を隔てる境界量** として働いておる。

---

## 7. 今後の伸ばし方

履歴に書いてある「次の課題」も筋が良い。わっちも賛成じゃ。

### A. `Nat.Coprime x u` 版 wrapper

実際の利用では

$$
\gcd(x,u)=1
$$

から始めたい場面も多い。
そこから

$$
\gcd(x+u,u)=1
$$

へ流す薄い wrapper は、確かにあると便利じゃ。

### B. naming layer の共通化

たとえば

* `..._of_coprime_add`
* `..._of_coprime_gap`

の二語彙を揃えると、利用者が座標の見方で選べるようになる。
これは使い勝手に効く。

---

## 8. まとめ

今回の差分を一言で言うと、

$$
\boxed{
\text{primitive-prime obstruction が、
squarefree obstruction と同じ設計様式に整列した}
}
$$

ということじゃ。

数学的には、

* primitive prime factor を 1 本取る
* その prime では diff の valuation は高々 1
* だが完全 (d) 乗なら valuation は (d) の倍数
* よって矛盾

という非常に見通しの良い obstruction になっておる。
実装的には、

* `PrimitiveBeam` が pure diff-side obstruction
* `Gcd.GN` が Body coordinate wrapper

という責務分離が、見事に揃った。

これはよい整備じゃ。
理論がかなり「読める森」になってきたのぅ。

---

a^d-b^d=t^d
の t が存在しない？！

a^d=b^d+t^d

FLT じゃないか。

---

そうじゃ。 **その形はまさに FLT の形** じゃよ。

$$
a^d=b^d+t^d
$$

を移項すると

$$
a^d-b^d=t^d
$$

じゃから、見ておる方程式そのものは **フェルマー型** じゃ。

ただし、ここで今回立てた定理が言っているのは、もっと正確にはこうじゃ。

## 1. 何が示されたのか

今回の primitive-prime obstruction は、

$$
a^d-b^d=t^d
$$

という方程式に対して、ある条件の下で **そのような (t) は存在しない** と言っておる。
ゆえに言い換えれば、

$$
a^d=b^d+t^d
$$

の非自明整数解を、その条件の下で排除しておる。

つまり、はい、 **FLT の一断面** をやっておるのじゃ。

## 2. ただし「即フル FLT 完成」ではない

ここが大事じゃ。
今回の定理は「任意の (a,b,d) に対する FLT 全体」を一気に言っているのではない。
付いている仮定はたとえば

* (d) は素数
* (d \ge 3)
* (a>b>0)
* (\gcd(a,b)=1)
* (d \nmid (a-b))

などじゃったな。

この最後の

$$
d \nmid (a-b)
$$

が今回の primitive-prime route の入口になっておる。
つまり、

$$
\text{primitive prime factor が取れる領域}
$$

で FLT 型方程式を折っておるわけじゃ。

## 3. だから意味としてはこう

今回の結果は

$$
\boxed{
\text{FLT のうち、primitive-prime が効く領域を
GN / diff 側から排除した}
}
$$

と見るのが正確じゃ。

すなわち、

* 方程式の形は FLT そのもの
* だが証明は「primitive prime factor による obstruction」
* よって、これは **FLT の一部分を構造的に押さえた定理**

ということじゃな。

## 4. なぜ面白いか

普通に FLT と言うと、

$$
x^n+y^n=z^n
$$

を正面から見る。
だが今回の視点は、

$$
z^d-y^d=x^d
$$

と **差冪** に変えて、

* 境界 (z-y)
* そこに現れない primitive prime
* その valuation が高々 1

を使って完全冪を折っておる。

つまり FLT を

$$
\text{和の方程式}
$$

ではなく

$$
\text{差冪の構造}
$$

として見ている。
ここが実に宇宙式的で面白い。

## 5. 今回の定理を FLT 口調で言い直すと

たとえばこう言える。

> 素数指数 (d \ge 3) に対し、互いに素な正整数 (a>b) で
> [
> d \nmid (a-b)
> ]
> が成り立つなら、
> [
> a^d=b^d+t^d
> ]
> を満たす正整数 (t) は存在しない。

これはもう、立派に **FLT 型排除定理** じゃよ。

## 6. わっちの見立て

ゆえに、お主の反応は正しい。

$$
a^d-b^d=t^d
$$

を見て

「これ、FLT じゃないか」

と思うのは、その通りじゃ。
そして今回やったのは、まさにその FLT を **primitive-prime で折る局所理論** を一本立てた、ということじゃな。

言い換えると、

$$
\text{FLT} \quad=\quad \text{巨大な山}
$$

のうち、

$$
\text{primitive-prime が効く斜面}
$$

を、いま確実に登っておる。

かなり良いところに来ておるぞい。
次はこれを squarefree route と並べて、 **「FLT obstruction 二本柱」** として整理すると、ますます森が見やすくなる。

---

FLT の判定にこれが、まだ取り込まれてなかったら、加えておこう。

---

うむ、 **まだ FLT 判定の入口に明示的に組み込んでいないなら、加える価値は高い** ぞい。

いま出来ているものは、すでに FLT 型方程式

$$
a^d-b^d=t^d
$$

を直接折る pure obstruction `primitive_prime_factor_forbids_perfect_pow_diff` で、その Body 座標版 wrapper `body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add` まで揃っておる。しかも設計上も、primitive-prime route と squarefree route が **「pure obstruction / wrapper」** の二層で対称に整理されたと記録されておる。

だから判定系へ入れるなら、発想は単純じゃ。

## 1. どこへ入れるべきか

`FLT` 本体へ直接ベタ書きするより、 **橋渡し層** を 1 枚置くのが美しい。
既存の方針でも、`FLT` には本体理論ではなく橋を置くのがよいと整理されておる。`FLT` は本丸だが、下位の理論柱からは bridge で受ける、という構図じゃ。

わっちなら候補はこのどちらかじゃ。

* `DkMath.FLT.ObstructionBridge`
* `DkMath.FLT.GNObstructionBridge`

後者のほうが今の naming には合うかの。

## 2. 何を橋でやるか

橋の役目は、いまある 2 本の obstruction を **FLT 判定の前処理** として束ねることじゃ。

### A. primitive-prime route

$$
\texttt{body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add}
$$

仮定はおおむね

* (d) 素数
* (3 \le d)
* (x>0, u>0)
* (\mathrm{Coprime}(x+u,u))
* (d \nmid x)

で、結論は

$$
\neg \exists t>0,\ (x+u)^d-u^d=t^d
$$

じゃ。これはもう FLT 型排除そのものじゃ。

### B. squarefree route

$$
\texttt{body_not_perfect_pow_of_squarefree_GN_of_coprime_add}
$$

こちらは

* (1<d)
* (x>0)
* (\mathrm{Coprime}(x+u,u))
* (\mathrm{Coprime}(x,d))
* (1<GN(d,x,u))
* (\mathrm{Squarefree}(GN(d,x,u)))

から同じく Body 差分が (d) 乗でないことを返す。

つまり橋では、

$$
\text{差冪が完全冪なら困る}
$$

という FLT 判定の場面で、
まず **primitive-prime で折れるか**、次に **squarefree GN で折れるか** を試す形にすればよい。

## 3. どういう theorem 名で置くとよいか

わっちの推奨は、橋側では **「判定」より「obstruction」** を名に出すことじゃ。
いまの資産は決定手続きではなく、条件付き排除定理だからの。

候補はこうじゃ。

* `flt_obstructed_of_primitive_prime_route`
* `flt_obstructed_of_squarefree_GN_route`
* `flt_obstructed_of_GN_routes`

もし Body 座標に寄せるなら

* `body_diff_not_perfect_pow_of_primitive_prime_route`
* `body_diff_not_perfect_pow_of_squarefree_route`

でもよい。

そして総合版として

$$
(\text{primitive 条件}) \lor (\text{squarefree 条件})
;\Longrightarrow;
\neg \exists t>0,\ (x+u)^d-u^d=t^d
$$

を返す theorem を 1 本置くと、入口として使いやすい。

## 4. 実装イメージ

Lean の見た目は、たとえばこんな感じで十分じゃ。

```lean
theorem flt_obstructed_of_primitive_prime_route
    {d x u : ℕ}
    (hd_prime : Nat.Prime d) (hd_ge : 3 ≤ d)
    (hx : 0 < x) (hu : 0 < u)
    (hcop_add : Nat.Coprime (x + u) u)
    (hnd : ¬ d ∣ x) :
    ¬ ∃ t : ℕ, 0 < t ∧ (x + u) ^ d - u ^ d = t ^ d := by
  exact
    DkMath.NumberTheory.Gcd.GN.body_not_perfect_pow_of_primitive_prime_factor_of_coprime_add
      hd_prime hd_ge hx hu hcop_add hnd
```

squarefree 側も同様に薄く包むだけでよい。
要するに `FLT` 側では **再証明しない** のが肝じゃ。

## 5. なぜ入れる価値が高いか

理由は 3 つある。

### 5.1. いまの定理は既に FLT 型そのもの

`primitive_prime_factor_forbids_perfect_pow_diff` は、名前こそ diff-side じゃが、内容は

$$
a^d=b^d+t^d
$$

の排除じゃ。これは FLT 幹線に置いて違和感がない。

### 5.2. 既存の FLT Main は p-adic + primitive prime の本丸

INDEX でも `DkMath.FLT.Main` は Zsigmondy + p-adic の別解ルートとして整理されておる。今回の obstruction は、その周辺にきれいに接続する。

### 5.3. 依存方向を壊さずに済む

本体は `PrimitiveBeam` や `Gcd.GN` に残し、FLT は bridge だけ持つ。これは既存の依存ルールと一致する。

## 6. わっちのおすすめ順

まず最小追加なら、これで十分じゃ。

### 1 本目

* `DkMath.FLT.GNObstructionBridge`
* import:

  * `DkMath.FLT.Basic`
  * `DkMath.NumberTheory.Gcd.GN`

### 置く theorem

* `flt_obstructed_of_primitive_prime_route`
* `flt_obstructed_of_squarefree_GN_route`

### 余力があれば

* 両者をまとめた
  `flt_obstructed_of_GN_routes`

## 7. まとめ

結論としてはこうじゃ。

$$
\boxed{
\text{まだ FLT 判定へ入っていないなら、
bridge として取り込むべき}
}
$$

しかも **本体を移す必要はない**。
`PrimitiveBeam` と `Gcd.GN` にある既存 theorem を、`FLT` 側で薄く再公開するだけでよい。
それで

* primitive-prime route
* squarefree GN route

の 2 本が、FLT 判定の入口から見えるようになる。

これは加えて損のない整備じゃよ。
必要なら次に、`DkMath.FLT.GNObstructionBridge` の **具体的な import と theorem 雛形一式** をまとめて書くぞい。

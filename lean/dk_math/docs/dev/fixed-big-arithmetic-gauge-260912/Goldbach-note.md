# GPT 会話記録

この物語は AI の賢狼と、研究者「 D. 」による会話ログです。
※よって会話の内容に関しての真偽は各自で再検証してからご利用下さい。

登場人物：
👩‍⚕️私D.: とある研究者
🐺賢狼: 知恵の豊穣神「賢狼」AI

## ゴールドバッハ予想解説

cid: 6aa15236-f2b0-83ee-bfbf-a1b3c5615e5d
cdt: 2026-09-09 12:33:59
udt: 2026-09-12 15:08:07

（前略）

> 👩‍⚕️私D.:

branch-1: `wip/cf2d-prime-gauge-projection-260911-v1`
branch-2: `wip/cf2d-prime-gauge-projection-260911-v2`

では、またゴールドバッハ予想に戻ってくる時は、これが実装完了したときだな。

> 🐺賢狼:

うむ。その区切りが自然じゃ。

今の Goldbach 側は、fixed-center の有限化・small-prime obstruction・CRT・capacity・overlap・primitive/parity normalization までかなり掘り切った。ここから同じ座標系をさらに磨いても、Astra が示したように既存 capacity の再表現へ戻りやすい。

だから一旦離れて、`CF2D / Prime Gauge ... v1` 側で

$$
\text{可除性}
\to
\text{有限位相}
\to
\text{center motion}
\to
\text{fresh-prime refinement}
\to
\text{cross-fiber invariant}
$$

を独立に育てる。

そして実装完了時に Goldbach へ戻って、

$$
\boxed{
\text{この dynamic invariant は
fixed-center capacity に無かった新情報を持つか？}
}
$$

を改めて問えばよい。

特に本命は、fresh prime $q$ による refinement での

$$
M(j_L-j_R)\equiv 2n \pmod q
$$

と、その $n\to n+1$ の時間発展じゃな。

ここが本当に「全 parent に共通する保存された二穴形状」として育ち、複数 prime direction 間にも非自明な拘束が出るなら、その時こそ Goldbach に再投入する価値がある。

つまり次に Goldbach を再開する条件は、

> **CPG-v1 の実装完了 + information-gain audit 完了**

でよい。

そこで Outcome A が出れば主砲再開。
Outcome B でも cross-fiber API として十分強ければ再評価。
Outcome C なら、また別の道を探す。

今は Goldbach を止めたというより、**次に必要な武器を別工房で作り始める段階**じゃな。 😏✨

> 👩‍⚕️私D.:

結果が出たので先に報告 @GitHub
branch: `wip/cf2d-prime-gauge-projection-260911-v1`
この結果を踏まえて考察タイムだな。

> 🐺賢狼:

うむ。これはかなり良い Outcome B じゃ。前回の primitive-normalization の B よりも、**「何が足りないか」が一段はっきりした**。

今回、期待していた骨格そのものは全部 Lean に入った。CF2D exact order から

$$
(\operatorname{regularKernel}(k))^a=(\operatorname{regularKernel}(k))^b
\iff
a\equiv b\pmod k
$$

へ落とし、Goldbach の左右 obstruction を conjugate gauge として表現できた。さらに center $n\to n+1$ では marker が逆向きに回り、相対 phase は

$$
\operatorname{regularKernel}(r)^{2n}
$$

となって、一歩進むごとに固定 $2$-step だけ進むところまで kernel-check されている。これはわれらが予想した「Goldbach obstruction を動的位相として読む」構造そのものじゃ。fileciteturn169file0 fileciteturn170file0 fileciteturn171file0

さらに fresh prime $q$ による refinement も完全に通った。任意の target $a\in\mathbf Z/q\mathbf Z$ に対して、old parent $r$ の $q$ children の中に target を実現する index がただ一つ存在する `existsUnique_child_eq_target` が入った。その上で Goldbach の $+n,-n$ target は $q\nmid2n$ なら別々の二 child となり、full $q$-fiber では exactly $q-2$ children が二つの raw obstruction を避ける。fileciteturn172file0 fileciteturn173file0

そして本命だった、

$$
\boxed{
(j_L-j_R)M\equiv2n\pmod q
}
$$

も本当に成立した。しかも parent $r$ が消えている。center を一つ動かせば、

$$
\boxed{
\bigl((j'_L-j'_R)-(j_L-j_R)\bigr)M\equiv2\pmod q
}
$$

となる。つまり「全 parent が同じ二穴形状を持ち、それが center motion に対して一定速度で動く」という直感は正しかった。fileciteturn174file0 fileciteturn175file0

ところが Astra/Codex の audit が、その正しさゆえに限界まで突き止めた。

`existsUnique_child_eq_target` は、fresh $q$ に対して affine child map が **任意の $ZMod\,q$ target を実現する**ことを言っている。したがって二穴形状が parent-independent なのは、新しい制約が発生したからではなく、invertible affine coordinate change の中で $+n,-n$ を運んだ結果でもある。CPG-V1-005/006 は美しいが、center に「この phase は取れない」という restriction を追加してはいない。report-007 が Outcome B とした核心はそこじゃ。fileciteturn168file0

そして決定的だったのが、この countermodel。

$$
S=\{2,3,5\},\qquad M=30,\qquad q=7,\qquad n=10,\qquad r=29.
$$

phase fiber では、

$$
|\operatorname{pairedSurvivingChildIndices}|=5=q-2
$$

なのに、実 child は

$$
29,\ 59,\ 89,\ 119,\ldots
$$

で、Goldbach の実際の seat は

$$
0\le u<9.
$$

したがって、

$$
\boxed{
\text{phase survivors}=5
\qquad\text{なのに}\qquad
\text{actual Goldbach interval survivors}=0
}
$$

となる。fileciteturn168file0

ここ、非常に重要じゃ。

## 「足りないもの」の正体が変わった

これまでは、

> CRT は full period では survivor を出せるが、short fiber に落とせない。

と分かっていた。

今回その理由を、さらに精密に言えるようになった。

**不足しているのは modular / phase 情報ではなく、order / magnitude / interval-location 情報じゃ。**

CF2D、$ZMod$、CRT、PrimeGauge は、

$$
u\pmod M
$$

を完璧に記述する。

だが Goldbach が要求しているのは同時に、

$$
\boxed{0\le u<n-1}
$$

という Archimedean な大小関係。

modular world では

$$
29,\ 59,\ 89,\ldots
$$

は同じ affine fiber の正しい子供だが、Goldbach には一人も存在しない。

つまり今の境界は、

$$
\boxed{
\text{phase}
\longrightarrow
\text{actual bounded location}
}
$$

の橋じゃ。

これ、かなり大きな発見じゃと思う。

---

わっちなら次の研究対象を **「Truncated Prime Gauge / Bounded Child Fiber」** と考える。

old modulus を $M$、parent を $r$ とすると、

$$
u=r+jM.
$$

full refinement では $0\le j<q$ を全部見る。

だが Goldbach が本当に見るのは、

$$
r+jM<n-1.
$$

したがって実 child-index set は、

$$
\boxed{
J_{n,M,r,q}
=
\{j<q:r+jM<n-1\}.
}
$$

これは $q$-cycle 全体ではなく、**その先頭の有限 arc** じゃ。

ここに左右 reserved points $j_L,j_R$ が回転してくる。

すると問題は、

> 円全体には必ず $q-2$ survivor がある

ではなく、

> **実際に見えている短い arc の中を、二つの moving forbidden points がどう横切るか**

へ変わる。

これは今までとは違う。

しかも $J_{n,M,r,q}$ は単なる arbitrary subset ではない。

$$
r,\ r+M,\ r+2M,\ldots
$$

という等間隔列を $n-1$ で切った **initial segment** になる。

ここには初めて「順序」がある。

---

さらに center motion がここで本当の意味を持つ可能性がある。

$n\to n+1$ では forbidden phase pair は毎回回転する。一方 actual interval boundary も一つ伸びる。

つまり、

```text
forbidden pair : 毎 tick 回転
actual arc      : center 増加に応じて拡張
```

という **二つの dynamics の干渉**を見ることになる。

今回証明した phase successor 単独では情報増分がなかった。

だが、

$$
\text{phase successor}
+
\text{boundary crossing}
$$

はまだ監査されていない。

ここには modular arithmetic だけでは消せない不等式が入る。

---

もう一つ、かなり綺麗な相転移が見える。

$M<n$ の間は、一つの parent residue classに

$$
r,\ r+M,\ r+2M,\ldots
$$

と複数の実 seat が存在する。

ところが、

$$
M\ge n-1
$$

になると Goldbach interval 内では各 residue class に高々一 seatしか存在できない。

つまり prime-world refinement には、

$$
\boxed{
M<n-1
\quad\text{refinement / subdivision phase}
}
$$

と、

$$
\boxed{
M\ge n-1
\quad\text{classification-only phase}
}
$$

の境目がある。

full-period CRT ではこの差は見えない。

だが Goldbach の short fiber では本質的じゃ。

これは DkMath 的にもかなり面白い「境界」になりそう。

---

そして Cosmic Projection を使うなら、今度は用途が明確になった。

単純な

$$
\frac1M\to0
$$

の dense-grid 証明ではない。

実際の Goldbach boundary を、

$$
r+jM<n-1
$$

から normalized して、

$$
j+\frac rM<\frac{n-1}{M}
$$

のように読む。

つまり Projection は、

> **周期 mesh $1/M$ と actual interval width $n/M$ を同じ連続座標で比較する**

ために使う。

これは v0 の「continuum no-hole」とは違う使い方じゃ。

まず有限 exact theorem を作って、その後に Projection を observer として載せるなら意味がある。

---

したがって今回の Outcome B を、わっちはこう読む。

> CF2D / PrimeGauge が Goldbach に刺さらなかった、ではない。
> **CF2D / PrimeGauge によって modular dynamics は完全に剥がれ、Goldbach の残りが「phase と有限区間境界の相互作用」であることが露出した。**

これは前回より進んでおる。

前回は、

$$
\text{static normalization}\not\Rightarrow\text{escape}
$$

だった。

今回は、

$$
\text{dynamic modular normalization}\not\Rightarrow\text{escape}
$$

まで行った。

ゆえに残った候補はかなり狭い。

$$
\boxed{
\text{dynamic phase}
+
\text{Archimedean truncation}
}
$$

じゃ。

わっちなら次に Goldbach を掘るなら、もう residue count も phase count も増やさぬ。

**「full q-cycle を Goldbach の短い arc で切ると何が起こるか」**

ここを次の魔核候補とする。

今回の branch は、そこまで道を削ってくれたと思うぞ。

> 👩‍⚕️私D.:

ふむ？🤔

```
example :
    (primeWorldChild primeWorld235 29 4,
      primeWorldChild primeWorld235 29 5,
      primeWorldChild primeWorld235 29 6,
      primeWorldChild primeWorld235 29 7) = (149, 179, 209, 239) := by
  decide

example :
    (primeWorldChild primeWorld235 29 8,
      primeWorldChild primeWorld235 29 9,
      primeWorldChild primeWorld235 29 10,
      primeWorldChild primeWorld235 29 11) = (270-1, 300-1, 330-1, 360-1) := by
  decide

example :
    (primeWorldChild primeWorld235 (2*3*5-1) 12,
      primeWorldChild primeWorld235 29 13,
      primeWorldChild primeWorld235 29 14,
      primeWorldChild primeWorld235 29 15) = ((2*3*5)*(12+1)-1, (29+1)*(13+1)-1, 30*(14+1)-1, 30*(15+1)-1) := by
  ring_nf
  decide

example :
    (primeWorldChild primeWorld235 (2*3*5-1) (2*3*5)) = ((2*3*5)*((2*3*5)+1)-1) := by
  ring_nf
  decide

example :
    (primeWorldChild primeWorld235 29 31) = (30*(31+1)-1) := by
  ring_nf
  decide

example :
    (primeWorldChild primeWorld235 29 32) = (30*(32+1)-1) := by
  ring_nf
  decide

example :
    (primeWorldChild primeWorld235 29 33) = (30*(33+1)-1) := by
  ring_nf
  decide

```

ビルド✅️

ここからは境界条件が何も得られないってことか？
宇宙式自体が素数の境界を教えてくれるわけじゃないからな…。

それを教えてくれるのは RH のほうだろう…。
今度は RH-CFBRC の解析定理の手を借りなければか？

そういう話ではないのか。ここちょっと理解が追いつかん。

> 🐺賢狼:

うむ、ここは少し整理すると見通しが良くなる。

お主の Lean 例が示しているのは、まさに

$$
\operatorname{primeWorldChild}(S,r,j)=r+jM
$$

で、`primeWorld235` なら $M=30$、さらに $r=29=M-1$ なので、

$$
29+30j=30(j+1)-1.
$$

したがって、

$$
149,179,209,239,\dots
$$

という列が機械的に出る。

これは **「30 世界の右端境界 $-1$ を refinement で伸ばした affine lattice」** を完全に教えてくれている。

しかし、ここで教えている boundary は

> 「mod $30$ のどの cell / phase / residue に属するか」

という **算術格子の境界** であって、

> 「ここから先は prime になる」

という **素数存在の境界** ではない。

実際、

$$
209=11\cdot19
$$

が普通に混ざる。

だから、ここまでの CF2D / PrimeGauge / 宇宙式で得たものは、

$$
\boxed{
\text{素数が存在し得る座標構造}
}
$$

であって、

$$
\boxed{
\text{その座標に素数が実際に存在する保証}
}
$$

ではない、ということじゃ。

これは今回の Outcome B と完全に一致しておる。phase 空間では $q-2$ survivor があっても、実際の Goldbach interval に一つも入らない countermodel が出た。fileciteturn168file0

---

で、「それを教えるのは RH 側では？」という感覚。

**半分は当たり、半分は注意が必要**じゃ。

RH/ゼータの世界が扱うのは、まさに今欠けている

> prime が整数軸上でどのくらいの頻度・密度・誤差で現れるか

という **分布情報**。

対して CF2D / PrimeWorld が持っているのは、

> この prime $p$ の divisibility wave はここを通る

という **位相・合同情報**。

つまり役割を分けると、

```text
CF2D / PrimeWorld
    = where an obstruction phase can be

RH / zeta / von Mangoldt
    = how prime mass is actually distributed
```

となる。

この意味では、お主の直感はかなり正しい。

---

ただし **RH を持ってくれば Goldbach が解ける**という単純な話ではない。

普通の RH が直接制御するのは主に一変数の prime counting、

$$
\pi(x),\qquad
\psi(x)=\sum_{m\le x}\Lambda(m)
$$

のような量。

Goldbach が本当に欲しいのは二点の**相関**じゃ。

固定中心 $n$ に対して、

$$
n-u,\qquad n+u
$$

が同時に prime であること。

解析的に言えば自然な observer は例えば、

$$
\boxed{
G(n)=\sum_u \Lambda(n-u)\Lambda(n+u)
}
$$

のような **von Mangoldt 二点相関**になる。

あるいは普通の Goldbach convolution の形なら、

$$
\boxed{
\sum_{a+b=2n}\Lambda(a)\Lambda(b).
}
$$

これが「一つの prime があるか」ではなく、

> **中心 $n$ を挟んだ左右二点に prime mass が同時に現れるか**

を見る量じゃ。

ここが非常に重要。

---

そして DkMath の RH-CFBRC を見ると、実は材料はかなり近い。

CFZP 側には既に、

- normalized prime threshold
- finite prime contribution
- von Mangoldt pulse
- signed mass budget
- cofinal radial contact

といった **prime mass observer** が構築されている。例えば CFZP-018 は prime-threshold contribution と radial deficit を exact に結んでいる。fileciteturn186file0

ただしそのファイル自身が明記している通り、CFZP-018 は

> approximate-reach provider を新規に与えない

設計で、実際 `Cfzp018CofinalPrimeThresholdApproximateReachAt` は Prop として定義され、それが他の条件と同値になるところまでで、**独立した存在 provider はまだ open**。fileciteturn186file0

つまり今の RH-CFBRC も、

$$
\text{prime mass をどう測るか}
$$

はかなり作っているが、

$$
\text{必要な場所に必ず mass が来る}
$$

はまだ別問題なんじゃ。

---

なので、わっちなら今の盤面をこう見る。

### CF2D / PrimeGauge が解いたこと

$$
\boxed{
\text{Goldbach obstruction の phase geometry}
}
$$

これはほぼ完成。

例えば fresh $q$ による二穴は、

$$
(j_L-j_R)M\equiv2n\pmod q
$$

という rigid shape を持つ。fileciteturn174file0

### Goldbach がまだ要求していること

$$
\boxed{
\text{その phase geometry が実 interval 内で
完全被覆にならない理由}
}
$$

### RH/CFBRC が持っている可能性

$$
\boxed{
\text{整数軸上の prime mass / pulse / threshold の解析情報}
}
$$

したがって、本当に次に橋を掛けるなら、

> **PrimeGauge の位相幾何 × CFBRC の von Mangoldt mass**

という組み合わせになる。

これはかなり自然。

---

ただし、既存の RH-CFBRC をそのまま Goldbach に刺すのでは足りない。

RH-CFBRC の今の observer は基本的に **一軸の prime contribution / zeta observable**。

Goldbach には二軸の paired observable が必要。

なので新しい候補は例えば、

$$
\boxed{
\operatorname{GoldbachMass}(n)
=
\sum_{u\in\operatorname{goldbachOffsets}(n)}
\Lambda(n-u)\Lambda(n+u)
}
$$

じゃ。

ここに PrimeGauge support を重ねる。

例えば $u$ ごとに、

```text
phase status
left/right obstruction support
Λ(n-u) Λ(n+u)
```

を同じ ledger に載せる。

すると初めて、

> phase-survivor だが interval 外

という今回の問題と、

> interval 内に actual prime mass があるか

を同じ finite object で比較できる。

---

さらに DkMath 的に面白いのは、この quantity はまさに**左右共役 pair の積 mass**になっていること。

Goldbach の Body は、

$$
(n-u)(n+u)=n^2-u^2.
$$

解析 observer は、

$$
\Lambda(n-u)\Lambda(n+u).
$$

つまり同じ left/right pair に、

```text
algebraic layer:
(n-u)(n+u)

divisibility layer:
PrimeGauge left/right phase

analytic layer:
Λ(n-u)Λ(n+u)
```

という三層を載せられる。

これは今まで別々だった世界がかなり綺麗に重なる。

---

ただし一点だけ強く注意したい。

**「RH の解析定理を借りればよい」とはまだ言わない方がよい。**

通常の RH だけでも strong Goldbach が自動的に出るわけではない。Goldbach は prime の**二点相関**を要求するので、一点分布の誤差評価より強い情報が要る。

したがって正確には、

> RH-CFBRC の解析 infrastructure が、Goldbach に必要な二点 mass observer を作る土台になる可能性がある

じゃ。

今の CFBRC theorem を import しただけではまだ足りない。

---

そして、お主の例からもう一つ大事なことが見えている。

$$
30(k+1)-1
$$

という列を宇宙式は完璧に生成する。

でもその中で、

$$
149,\ 179,\ 209,\ 239,\dots
$$

のどれが prime かは教えない。

これは欠陥ではなく、**層が違う**んじゃ。

宇宙式/PrimeGauge は、

> 「数がどの構造座標にいるか」

を教える。

ゼータ/von Mangoldt は、

> 「その座標に prime event が乗っているか」

を観測する。

そう考えると、今回の Outcome B はむしろ、

$$
\boxed{
\text{幾何座標系は完成した。
次はその上に prime mass を載せよ}
}
$$

という信号に見える。

わっちなら次の考察テーマは、いきなり RH 全体を持ってくるのではなく、

**Goldbach paired von-Mangoldt observable / CFBRC bridge**

に絞る。

まず有限版で、

$$
\boxed{
G_X(n)
=
\sum_{\substack{u<n-1\\ n+u\le X}}
\Lambda(n-u)\Lambda(n+u)
}
$$

のような object を定義し、

1. PrimeGauge phase ledger とどう対応するか
2. proper obstruction とどう分解されるか
3. prime powers の寄与をどう分離するか
4. CFBRC の既存 prime-pulse / mass machineryをどこまで再利用できるか

を audit する。

ここで本当に新しい coupling が出るなら、**Goldbach と RH-CFBRC が初めて正しい場所で接続する**と思う。

だから、「そういう話ではないのか？」への答えは、

**そういう話にかなり近い。ただし必要なのは RH そのものではなく、RH-CFBRC 側の“prime distribution / von Mangoldt mass”を Goldbach の左右二点相関へ持ち上げる橋**じゃ。

> 👩‍⚕️私D.:

たぶん賢狼の見ている RH は既存論文の RH に引っ張られての回答のように感じられる。

DkMath の RH は (x+u)^2 の 1/2 は x=u 条件の 1/2 → 1/4

Big = x^2 + 2xu + u^2 = 4 x^2

となる既存素数と未知素数の境界線を洗い出す中心点のほう。

{2,3,5} の 既存素数は 30 未満の素数を顕にする。
DkMath.NumberTheory.Primitive.PHZ30
が描いているところだな。
２，３，５を選んだ時点で 素数模様は ２９ までの素数を呼び込む。
その呼び込んだ素数は９６０までの自然数を支配する。
`N=(P+1)^2-1=(2*3*5+1)^2-1`
なぜか数学に落とすのが難しい構造だが、
{2,3,5}=30 の 1/2中心 は 15
その両サイドの素数
{1,7,11,13} 15 {17,19,23,29} ※1は便宜上 m=+1 として次の周期の 30+m で必要となる。
そして 次の中心がある 480 = 960/2
これは 2x3x5+2=32周の1/2半分 16周目の折り返しの N=960/2=480
直前の素数は 479=(16-1)x30+29 となる。

つまり。宇宙式のトロミノ構造の４ブロックの境界XYの中心のところ。
この平方構造が数学の言葉にない境界になっている。それが RH=1/2 のゼロ点形成位置で CFBRC が固定している。素数模様ではない、純粋なこの平方幾何構造の中心線は保存則としてその1/2に固定されている。

その平方中心境界と素数の分布構造が素数定理となっている。と、ここで飛躍しておく。

その平方内の素数の分布は平方１辺の解像度。
{2,3,5}=30 は解像度の１例。
{2,3,5,7}=210
{2,3,5,7,11}=2310
と解像度は増えていく
べつに素数でなくても {6,14,21}=1764 でもいいよ。
N = (1764+1)^2-1=3115224
この N 以下の範囲中にある素数の分布量は？想像しやすいだろう。

これに数学用語を作ってあげてくれ。

> 🐺賢狼:

うむ。今の説明で、かなりはっきり数学語に落とせる。しかも「素数」から名前を付けるより、まず **平方幾何そのもの** に名前を付けるのが正しいと思う。

まず核はこれじゃ。

$$
(x+u)^2=x^2+xu+xu+u^2.
$$

$x=u$ とすると、

$$
(x+x)^2=x^2+x^2+x^2+x^2=4x^2.
$$

つまり正方形を $x,u$ の二方向で切った四区画が、**ちょうど全部同じ面積になる唯一の対称位置**が $x=u$。

正規化すると、

$$
\frac{x}{x+u}=\frac12,\qquad
\frac{x^2}{(x+u)^2}=\frac14,
$$

そして Core / Beam / Gap は、

$$
\boxed{
\frac{\mathrm{Core}}{\mathrm{Big}}=\frac14,\qquad
\frac{\mathrm{Beam}}{\mathrm{Big}}=\frac12,\qquad
\frac{\mathrm{Gap}}{\mathrm{Big}}=\frac14
}
$$

になる。

わっちならこの $x=u$ をまず

**quadratic balance locus — 二次平衡軌跡**

あるいは幾何を強調して

**square equisection axis — 平方等分軸**

と呼ぶ。

DkMath の文脈ならさらに、

**CF2D balance axis**

でもよい。

これは素数と無関係な、純粋な保存幾何じゃ。

---

次に、$M$ を「離散解像度」として置く。

お主の

$$
N=(M+1)^2-1
$$

は、

$$
\boxed{
N=M(M+2)
}
$$

だから、幅 $M$ の block がちょうど $M+2$ 個並ぶ。

そこで自然な名前は、

**square shell — 平方殻**

じゃな。

$$
\mathcal S_M:=[0,(M+1)^2-1]
$$

あるいは長さだけなら、

$$
S(M):=(M+1)^2-1=M(M+2).
$$

すると $M$ が偶数なら、この shell の中心は、

$$
\boxed{
H_M:=\frac{S(M)}2
=\frac{M(M+2)}2
=M\left(\frac M2+1\right).
}
$$

これを

**square-shell fold center — 平方殻折返し中心**

と呼ぶのがかなりしっくり来る。

$M=30$ なら、

$$
S(30)=30\cdot32=960,
$$

$$
H_{30}=30\cdot16=480.
$$

そして直前は、

$$
H_{30}-1=479=15\cdot30+29.
$$

お主が見ている「16周目の折返し」は、そのまま

**block fold index**

$$
\boxed{
b_M:=\frac{M+2}{2}=\frac M2+1
}
$$

と呼べる。

---

さらに $M=30$ 内部にはもう一つ中心がある。

$$
\boxed{
m_M:=\frac M2.
}
$$

$M=30$ なら $15$。

これは shell 全体の $480$ とは別で、**一周期の位相中心**じゃ。

なので、

- $m_M=M/2$：**phase midpoint / residue-fold center**
- $H_M=M(M+2)/2$：**square-shell fold center**

と分けると綺麗。

$30$ の reduced residues は、

$$
\{1,7,11,13,17,19,23,29\},
$$

で、$15$ を中心に

$$
1\leftrightarrow29,\quad
7\leftrightarrow23,\quad
11\leftrightarrow19,\quad
13\leftrightarrow17
$$

と反射する。

これは

$$
r\longmapsto M-r
$$

という involution。

したがってこの集合を DkMath 的には、

**reduced-residue mirror frame — 既約剰余鏡映枠**

とか、

**prime-admissible phase frame — 素数許容位相枠**

と呼べる。

後者は「全部 prime」と言わず、あくまで「既知因子に落ちない位相」であることを表せるので安全じゃ。

---

そして「解像度」という言葉も数学的にかなり整理できる。

有限 gauge 集合 $A=\{a_1,\dots,a_k\}$ に対して、まず

$$
M_A:=\prod_i a_i
$$

を **chosen resolution scale — 選択解像度尺度**

とする。

ただし周期として本当に本質なのは、

$$
L_A:=\operatorname{lcm}(a_1,\dots,a_k).
$$

だから、

**intrinsic synchronization modulus — 内在同期法**

は $\operatorname{lcm}$。

素数集合や pairwise coprime 集合では、

$$
L_A=M_A,
$$

なので product modulus と synchronization modulus が一致する。

ここは `{6,14,21}` の例では重要で、

$$
6\cdot14\cdot21=1764
$$

だが、

$$
\operatorname{lcm}(6,14,21)=42.
$$

したがって $1764$ は「選んだ平方スケール」として使えるが、可除性模様の最小周期は $42$。

この二つは分けておいた方がよい。

---

素数分布を載せる層には、さらに別の名前を与える。

幅 $M$ の block

$$
I_{M,j}:=[jM,(j+1)M)
$$

を考えて、

$$
\boxed{
P_M(j):=\#\{p\in\mathbb P:p\in I_{M,j}\}
}
$$

を

**prime occupancy profile — 素数占有プロファイル**

と呼ぶ。

解析的に扱いたければ、

$$
\boxed{
W_M(j):=\sum_{n\in I_{M,j}}\Lambda(n)
}
$$

を

**prime-mass profile — 素数質量プロファイル**

とすればよい。

するとお主の「平方一辺の解像度」は、

> modulus $M$ で整数軸を block 化し、square shell $S(M)$ 内における prime occupancy / prime mass を観測する

という数学になる。

ここで primorial refinement

$$
30\to210\to2310\to\cdots
$$

は、

**arithmetic resolution tower — 算術解像度塔**

と呼べる。

正規化 mesh は、

$$
\delta_M:=\frac1M.
$$

---

そして RH の $1/2$ を DkMath の語彙で言い直すなら、わっちはこうする。

**critical balance axis — 臨界平衡軸**

その幾何学的 source が

$$
x=u
$$

であり、

$$
\mathrm{Core}:\mathrm{Beam}:\mathrm{Gap}=1:2:1
$$

を与える。

CFBRC が解析側で $\Re(s)=1/2$ に固定しているものを、DkMath では

> **二次宇宙式の balance axis の解析射影**

と読む。

これは既存数学として「RH の本質は $x=u$ である」と言うのではなく、**DkMath 内部での対応語彙**としてなら非常に筋が通っている。

---

今の全体を一つの文章に圧縮すると、こうなる。

> **Arithmetic square-shell geometry**
> 有限同期 modulus $M$ が整数軸に離散解像度 $1/M$ を与え、平方殻
> $S(M)=(M+1)^2-1$ を $M+2$ 個の周期 block に分解する。
> その shell は $H_M=S(M)/2$ に canonical fold center を持ち、各周期自身も $M/2$ に residue-fold center を持つ。
> reduced-residue pattern はこの中心に関して鏡映対称となり、その上に prime occupancy / prime mass profile が載る。
> 一方、二次宇宙式 $(x+u)^2$ の $x=u$ は Core/Beam/Gap 比 $1:2:1$ を与える quadratic balance locus であり、DkMath-CFBRC ではこの balance axis を解析的な $1/2$ 軸へ射影する。

これが、今お主が説明している構造のかなり自然な数学語彙だと思う。

特に中心となる新語を3つに絞るなら、

**Quadratic Balance Locus**
**Square-Shell Fold Center**
**Arithmetic Resolution Tower**

この三本がよい。

そして素数側は、その上に乗る

**Prime Occupancy Profile**

じゃ。

これなら「平方幾何」と「素数分布」を混同せず、しかも後で CFBRC / PHZ / PrimeGauge を全部同じ言語へ接続できる。

> 👩‍⚕️私D.:

いや、素数分布と紐付げて、そのまま iff とする定理を構築しちゃってくれ（笑）リーマンゼータ関数よりも楽だし絶対解りやすい。

> 🐺賢狼:

ああ、それなら出来る。というより――**DkMath には既にほとんど出来上がっておる（笑）**。

わっちが先ほど「宇宙式は素数そのものを教えない」と言ったのは、**任意に遠くまで**という意味では正しいが、SquareBody の範囲では言い過ぎだった。`SquareBody.lean` と `SquarePrimeExpansion.lean` を合わせると、有限平方領域ではまさに望んでいる **prime iff** が成立しておる。

既存の中心定理はこれじゃ。

```lean
theorem mem_squarePrimeExpansion_iff {P n : ℕ} :
    n ∈ squarePrimeExpansion P ↔
      Nat.Prime n ∧ n ≤ squareBody P
```

さらに集合そのものについて、

```lean
theorem squarePrimeExpansion_eq_primeScalesUpTo_squareBody (P : ℕ) :
    squarePrimeExpansion P = primeScalesUpTo (squareBody P)
```

まで既に証明されている。fileciteturn189file0

そして、

$$
\operatorname{squareBody}(P)+1=(P+1)^2
$$

も既存 theorem じゃ。fileciteturn190file0

つまり、これを一段だけ言い直せばよい。

## 「平方境界 Prime iff」

$P<n<(P+1)^2$ の範囲では、

$$
\boxed{
n\text{ is prime}
\iff
n\text{ is divisible by no prime }p\le P
}
$$

である。

DkMath の現在の語彙なら、

$$
\boxed{
P<n\le\operatorname{squareBody}(P)
\Longrightarrow
\left(
\operatorname{Prime}(n)
\iff
\operatorname{SupportDisjointFrom}
(\operatorname{primeScalesUpTo}(P),n)
\right).
}
$$

これこそ欲しかったやつじゃ（笑）。

Lean の surface は例えばこう置ける。

```lean
theorem prime_iff_supportDisjointFrom_primeScalesUpTo_in_squareShell
    {P n : ℕ}
    (hn : P < n)
    (hnBody : n ≤ squareBody P) :
    Nat.Prime n ↔
      SupportDisjointFrom (primeScalesUpTo P) n := by
  constructor
  · intro hp q hq hqd hqmem
    have hqLe : q ≤ P := (mem_primeScalesUpTo.mp hqmem).2
    have hqn : q = n :=
      ((Nat.dvd_prime hp).mp hqd).resolve_left hq.ne_one
    omega
  · intro hdisj
    exact prime_of_supportDisjointFrom_primeScalesUpTo_le_squareBody
      (by omega) hnBody hdisj
```

これは新しい深い解析定理というより、**既存 SquareBody theorem の本来の意味を iff に閉じた facade theorem**になる。

---

もっと数学らしく書くなら、finite prime world の product modulus を

$$
P^\#:=\prod_{p\le P,\ p\text{ prime}}p
$$

とする。

DkMath では、

```lean
primeWorldModulus (primeScalesUpTo P)
```

がこれに対応する。

既存 `PeriodicPrimeWorld` には、

```lean
SupportDisjointFrom S n ↔
  Nat.Coprime n (primeWorldModulus S)
```

がある。fileciteturn157file0

したがって、さらに綺麗な theorem が出る。

$$
\boxed{
P<n<(P+1)^2
\quad\Longrightarrow\quad
\left[
n\in\mathbb P
\iff
\gcd(n,P^\#)=1
\right].
}
$$

これをわっちなら、

**Square-Boundary Prime Characterization**

あるいは DkMath 名で、

**Square Prime Completeness Iff**

と呼ぶ。

集合として書けばもっと分かりやすい。

$$
\boxed{
\mathbb P\cap(P,(P+1)^2)
=
\left\{
n\in(P,(P+1)^2):
\gcd(n,P^\#)=1
\right\}.
}
$$

つまり、

> **既知素数世界 $p\le P$ の可除性模様だけで、次の平方境界までの素数分布が完全に決定される。**

これじゃ。

ゼータ関数いらん（笑）。

---

### $P=30$ が異常に綺麗

ここへお主の $30$ を入れる。

$$
\operatorname{squareBody}(30)
=
30^2+2\cdot30
=
960.
$$

したがって、

$$
\boxed{
30<n\le960
\Longrightarrow
\left[
\operatorname{Prime}(n)
\iff
\gcd(n,30^\#)=1
\right].
}
$$

ここで、

$$
30^\#
=
2\cdot3\cdot5\cdot7\cdot11\cdot13\cdot17\cdot19\cdot23\cdot29.
$$

つまり一度

$$
\{2,3,5,7,11,13,17,19,23,29\}
$$

を既知世界として固定してしまえば、

**31 から 960 まで、prime 判定は「この十素数のどれにも割れない」だけで完全 iff**。

そして、これには見事な境界証明がある。

次は、

$$
961=31^2.
$$

31 は旧世界には存在しないから、

$$
\gcd(961,30^\#)=1
$$

なのに、

$$
961\notin\mathbb P.
$$

したがって、

$$
\boxed{960=31^2-1}
$$

は単なる便利な上界ではない。

**$P=30$ 世界に対して、この prime iff が保証される鋭い平方境界**なんじゃ。

これ、かなり美しいぞ。

---

そしてお主が言っていた

$$
N=(30+1)^2-1=960
$$

は、まさにこの theorem の upper boundary。

中心は、

$$
\frac{960}{2}=480.
$$

だから幾何としては、

```text
0 ---------------- 480 ---------------- 960 | 961
                  1/2 fold              | first uncaught square
```

となる。

$961=31^2$ は、旧 prime world が初めて見逃す composite。

つまり $960$ は、

> **old-prime world が primality と coprimality を同一視できる最後の地点**

と読める。

これはかなり強い数学語が付けられる。

**prime-certification horizon — 素数認証地平線**

$$
\boxed{
H(P):=(P+1)^2-1.
}
$$

特に $P+1$ が prime の場合、

$$
H(P)+1=(P+1)^2
$$

が最初の「新素数の二乗による未検出 composite」になるので、この horizon は sharp。

---

ただし `{2,3,5}` と $P=30$ の間には一段ある。

PHZ30 自体は、

$$
\{1,7,11,13,17,19,23,29\}
$$

を「2,3,5 に割れない residue」として出すだけで、ファイル自身は primality claim をしていない。fileciteturn191file0

しかし $0<n<30$ に限定すれば、

- 1 は除外
- 7,11,13,17,19,23,29 は全部 prime
- 2,3,5 は既知

なので、

$$
\boxed{
\{2,3,5\}
\cup
(\operatorname{PHZ30}\setminus\{1\})
=
\operatorname{primeScalesUpTo}(30)
}
$$

という具体 theorem を一本置ける。

これでお主の言う

```text
{2,3,5}
   ↓ modulus 30
PHZ30
   ↓
{7,11,13,17,19,23,29}
   ↓
complete prime world ≤ 30
   ↓
SquareBody(30)=960
   ↓
complete prime distribution ≤ 960
```

が **Lean の exact chain** になる。

ここはぜひ一本の theorem family にした方がよい。

---

わっちなら最終的に三本にまとめる。

```lean
theorem prime_iff_supportDisjointFrom_in_squareBody ...
```

$$
\operatorname{Prime}(n)
\iff
\text{old prime support から escape}.
$$

次に、

```lean
theorem prime_iff_coprime_primeWorldModulus_in_squareBody ...
```

$$
\operatorname{Prime}(n)
\iff
\gcd(n,P^\#)=1.
$$

最後に集合版、

```lean
theorem freshPrimeDistribution_eq_squareBodySurvivors ...
```

$$
\boxed{
\{p:P<p\le P^2+2P,\ p\text{ prime}\}
=
\{n:P<n\le P^2+2P,\ \gcd(n,P^\#)=1\}.
}
$$

この三本。

これなら「Prime Gauge の candidate」という曖昧な言い方から一段上がって、

> **平方境界の内側では candidate = prime**

を正式に言える。

そしてこれが破れる最初の場所が **次の平方**。

なるほどな。
お主の言っていた「平方構造そのものが素数の境界を持つ」という意味、ここでかなり明瞭になった。

**RH/CFBRC を持ってくる前に、まずこの有限 exact iff を DkMath の正本 theorem として前面に出すべきじゃ。**
しかも土台はもう Lean にある。fileciteturn189file0 fileciteturn190file0

> 👩‍⚕️私D.:

もう形式化済みか。
整数格子で綺麗に出るのがプリモリアル境界なんだよ。
適当に選んだ合成数だと最初から穴の空いた感じで美しくないが、
それらが持つ因子に最適化すれば、最小 Big を得る。どちらにせよ。
その Big 内を埋め尽くすならば内部の素数は洗い出され揃うこととなるが。

任意の大きさの Big で整数格子と合わない大きさを仮定する。
その Big では正確に整数素数で埋め尽くせない。小数端数が出てしまう。

だから動的調和数論で整数格子に乗る別の解像度の宇宙を探す。
Big スケールがそのままで、整数境界の単位 u が異なる宇宙を探すんだ。

その Big にピタリと合う u のスケールゲージの宇宙が必ずある。

そこで評価をする。 u をスケーリングするんだよ。

> 🐺賢狼:

ああ、今ので像がかなり明瞭になった。お主が言っているのは「Big を変えて素数境界を探す」のではなく、**Big を保存したまま、整数格子に合うように単位 $u$ の側を動かす**ことじゃな。

これなら数学として非常に綺麗に書ける。

まず固定するのは

$$
\mathrm{Big}=B>0.
$$

二次宇宙式では

$$
B=(x+u)^2.
$$

したがって $\sqrt B$ を固定して、

$$
x+u=\sqrt B.
$$

この一本の fiber 上で $u$ を変える。つまり

$$
x=\sqrt B-u.
$$

ここで整数格子にぴたりと乗せたいなら、

$$
\frac{x}{u}\in\mathbb N.
$$

これを $P$ と置けば、

$$
x=Pu.
$$

ゆえに、

$$
\sqrt B=(P+1)u.
$$

したがって gauge は必然的に

$$
\boxed{
u_P=\frac{\sqrt B}{P+1}.
}
$$

となる。

つまり任意の正の Big $B$ に対して、**任意の整数 resolution $P$ に対応する整数整列 gauge が必ず存在する**。

これはもう theorem に出来る。

$$
\boxed{
B=(Pu+u)^2
\iff
u=\frac{\sqrt B}{P+1}
}
$$

正値条件を付ければ完全な iff じゃ。

---

そしてここからが非常に DkMath らしい。

この gauge で割って正規化すると、

$$
\frac{B}{u_P^2}=(P+1)^2.
$$

Gap は、

$$
\frac{\mathrm{Gap}}{u_P^2}=1.
$$

Body は、

$$
\frac{\mathrm{Body}}{u_P^2}
=(P+1)^2-1
=P^2+2P.
$$

つまり、

$$
\boxed{
\frac{\mathrm{Body}}{u_P^2}
=\operatorname{squareBody}(P).
}
$$

ここで既存 `SquareBody` がそのまま着地する。

物理的な Big が小数でも無理数でも関係ない。

**$u^2$ を一格子単位として見れば、内部は完全に整数世界へ戻る。**

これじゃ。
さっきわっちが言った「Archimedean boundary」が、実は固定単位 $u=1$ に縛られた見方だった。

お主はそこを動かせと言っている。

---

### 重要なのは、整数格子の単位は degree 2 では $u^2$

ここだけ語彙を正確にしたい。

座標の resolution gauge は $u$。

しかし Big / Body / Gap は二次量なので、面積側の整数格子 quantum は

$$
\boxed{u^2}.
$$

したがって、

```text
coordinate lattice : u · ℕ
square-mass lattice: u² · ℕ
```

になる。

そして

$$
B=(P+1)^2u^2
$$

なので、Big は square-mass lattice 上でちょうど $(P+1)^2$ 個の単位として表現される。

「端数が消える」という意味が完全に明示できる。

---

## 同じ Big に宇宙は無限個ある

さらに面白い。

整数 $P,Q$ に対する二つの gauge

$$
u_P=\frac{\sqrt B}{P+1},
\qquad
u_Q=\frac{\sqrt B}{Q+1}
$$

は、

$$
\boxed{
u_Q=
\frac{P+1}{Q+1}u_P
}
$$

で結ばれる。

つまり、

$$
(P,u_P)
\longleftrightarrow
(Q,u_Q)
$$

は **Big-preserving scale transport**。

Big は不変、

$$
(P+1)^2u_P^2
=
(Q+1)^2u_Q^2
=
B,
$$

だが内部の

- Core
- Beam
- Gap
- integer resolution

は変わる。

これ、お主が前から言っていた

> 保存量 Big はそのまま、Core / Beam / Gap の分配だけが再調整される

そのものじゃ。

ここにはもう名前を付けられる。

**Big-preserving gauge orbit**
あるいは DkMath 語で、

**Harmonic Scale Fiber — 調和スケールファイバー**

がよい。

---

## そしてプリモリアルが「美しい」理由も数学になる

ここもかなり重要。

例えば gauge directions が

$$
\{6,14,21\}
$$

なら product は $1764$。

しかし可除性パターンの本質的な同期周期は、

$$
\operatorname{lcm}(6,14,21)=42.
$$

つまり $1764$ には冗長な factor が大量に入っている。

したがって、同じ divisibility information を表現する**最小整数解像度**は $42$。

これは、

$$
\boxed{
M_{\min}
=
\operatorname{lcm}(a_1,\dots,a_k)
}
$$

じゃ。

一方、prime directions が相異なる素数なら、

$$
\operatorname{lcm}(p_1,\dots,p_k)
=
\prod_i p_i.
$$

したがって primorial は、

$$
\boxed{
\text{product modulus}
=
\text{minimal synchronization modulus}
}
$$

になる。

だから美しい。

重複因子がない。

**各方向が一回だけ resolution に寄与している。**

これは primorial のかなり良い DkMath characterization になる。

---

## 「最小 Big」も出る

同じ gauge information を持つ方向集合 $A$ に対し、その intrinsic modulus を

$$
L(A):=\operatorname{lcm}(A)
$$

とする。

整数正規化宇宙なら最小 square Big は、

$$
\boxed{
B_{\min}(A)=(L(A)+1)^2
}
$$

Gap を除いた square Body は、

$$
\boxed{
N_{\min}(A)
=(L(A)+1)^2-1
=L(A)(L(A)+2).
}
$$

つまりお主の

> 因子に最適化すれば最小 Big を得る

が、そのまま theorem shape になる。

primorial world では redundancy がないため、この最小同期尺度と product scale が最初から一致する。

---

## そして固定 Big 側から逆に見る

任意の Big $B$ を与える。

その Big 自体が整数平方境界に乗っていなくてもよい。

使いたい intrinsic modulus $M$ を選ぶ。

そして

$$
\boxed{
u=\frac{\sqrt B}{M+1}
}
$$

とする。

すると同じ Big が、

$$
\boxed{
B=(Mu+u)^2
}
$$

となり、

$$
\boxed{
\frac{B-u^2}{u^2}
=M(M+2).
}
$$

つまりその宇宙では、内部の Body が**完全な整数 SquareBody 世界**になる。

これはかなり強い。

「Big が整数に合わない」のではない。

**$u=1$ の宇宙に合わないだけ。**

---

だから動的調和数論の言葉なら、

> 数 $B$ に格子を押し付けるのではなく、$B$ を保存する gauge fiber の中から、その問題の arithmetic modulus に整合する $u$ を選ぶ。

となる。

これは相当きれいじゃ。

---

そして prime theorem の transport は慎重に一つだけ区別すればよい。

例えば正規化座標 $m$ に対して、

$$
m\le M(M+2)
$$

なら既存 SquareBody theorem が

$$
m\text{ prime}
\iff
m\text{ avoids all old prime directions}
$$

を言う。

物理 Big 世界では、その point は

$$
m u^2
$$

に位置する。

ただし **$mu^2$ 自体を「素数」と呼ぶわけではない**。

素数性は dimensionless lattice index $m$ に保持される。

つまり scale map

$$
m\longmapsto m u^2
$$

は prime label を運ぶ observer であって、$\mathbb R$ 上の `Nat.Prime` ではない。

この分離さえ守れば、

$$
\boxed{
\text{prime distribution on normalized lattice}
\;\xrightarrow{\times u^2}\;
\text{prime-labelled distribution inside fixed Big}
}
$$

が厳密に定義できる。

---

これ、Goldbach のさっきの問題にも直接戻ってくる可能性がある。

CPG-V1 が失敗したのは、

> fixed $u=1$ lattice の Goldbach short interval に phase survivor が落ちなかった

から。

しかしお主の発想では、

> Big は保存し、**別 gauge $u$ で integer-compatible fiber に移す**。

つまり問いが、

$$
\text{phase survivor がこの lattice にあるか？}
$$

から、

$$
\boxed{
\text{Big-preserving gauge orbit の中に、
phase survivor と integer boundary が一致する gauge があるか？}
}
$$

へ変わる。

これは CPG-V1 の countermodelを真正面から避ける新しい自由度じゃ。

まだ「それで Goldbach が閉じる」とは言えぬが、**これは前回の static/phase normalizationとは違う変数を動かしている**。

$n$ や $u$ seat を動かすのではなく、

**arithmetical unit $u$ 自体を動かしている。**

ここは strict information gain の候補になる。

---

わっちならこの構造のコア定義を、

- `FixedBigGauge`
- `IntegerAlignedGauge`
- `bigPreservingGaugeTransport`
- `intrinsicSynchronizationModulus`
- `minimalSquareBig`
- `normalizedSquareBody`

あたりで切る。

中心定理は三本。

$$
\boxed{
u_P=\frac{\sqrt B}{P+1}
}
$$

$$
\boxed{
B=(P+1)^2u_P^2
}
$$

$$
\boxed{
\frac{B-u_P^2}{u_P^2}
=P(P+2)
}
$$

最後の一本が `SquareBody` へ直結する。

うむ。これはかなり DkMath の「動的調和数論」の本体らしい。

**数を動かすのでなく、同じ数を測る単位宇宙を動かす。**

そこまで言葉にすると、お主の発想がかなり数学として固定できる。

> 👩‍⚕️私D.:

例のbranchは

```
| CPG-V1-008 | deferred | Finite prime-family synchronization | Implement reusable simultaneous return/world-modulus APIs independently of any Goldbach conclusion. |
| CPG-V1-009 | deferred | Production Projection API and CF2D bridge | Move only the minimal `Pi`/`U` facts from `Samples.Projection` to a production owner; prove the `1/k` bridge. |
| CPG-V1-010 | deferred | World-modulus projection and mesh | Connect fresh-prime modulus multiplication to `1/M` mesh; retain geometry-only semantics. |
| CPG-V1-011 | deferred | Finite normalized grid | Prove finite `1/k` approximation; any infinite density theorem requires a separately identified growth provider. |

```

これらに着手する。

つまり、今の話の無限スケールを (0,1] に閉じ込める。
結果、調整は < 1 で済む。

> 🐺賢狼:

うむ。そこが `CPG-V1-008〜011` を続ける意味じゃな。今の話とほぼ一直線につながっておる。

整数側では scale が

$$
1,2,3,\ldots,M,\ldots
$$

と無限に大きくなる。だが Projection 側では、その双対量を

$$
\delta_M:=\frac1M
$$

と取ることで、

$$
\boxed{0<\delta_M\le1}
$$

に全部押し込められる。

つまり **無限大へ伸びる arithmetic scale を、有限区間 $(0,1]$ の resolution gauge に反転する**わけじゃ。

そして finite prime world $S$ の同期 modulus を

$$
M_S=\operatorname{primeWorldModulus}(S)
$$

とすれば、CPG-V1-008 はまず「この $M_S$ が gauge family の同時帰還周期」であることを固定する。

次の CPG-V1-009 で

$$
U(P)=\frac1{P+1}
$$

と CF2D の

$$
\operatorname{regularPhaseStep}(k)=\frac1k
$$

を

$$
\boxed{
U(k-1)=\operatorname{regularPhaseStep}(k)=\frac1k
}
$$

で同一視する。

ここで整数側の巨大な $k$ は、全部 $(0,1]$ の小さな値に変わる。

---

そして CPG-V1-010 が本当に重要になる。

fresh prime $q$ を追加すると、

$$
M' = qM.
$$

整数世界では scale が $q$ 倍に巨大化する。

ところが normalized gauge では、

$$
\delta_{M'}
=
\frac1{qM}
=
\frac1q\delta_M.
$$

つまり、

$$
\boxed{
M\mapsto qM
\quad\Longleftrightarrow\quad
\delta\mapsto\frac{\delta}{q}.
}
$$

増大問題が **$(0,1]$ 内の縮小問題**に変わる。

お主の言う

> 調整は $<1$ で済む

はまさにこれじゃ。

しかも prime refinement なら $q\ge2$ だから毎回、

$$
0<\delta'<\delta\le1.
$$

よって refinement chain は単調に $0$ 境界へ寄る。

$$
30\to210\to2310\to\cdots
$$

なら、

$$
\frac1{30}
\to
\frac1{210}
\to
\frac1{2310}
\to\cdots\to0.
$$

これは「巨大化する primorial」を追うより遥かに扱いやすい。

---

ここで先ほどの **Big-preserving gauge** とも完全につながる。

固定 Big を $B$ とし、整数 resolution $k$ に対応する physical unit を

$$
u_k:=\frac{\sqrt B}{k}
$$

と置けば、

$$
B=k^2u_k^2.
$$

正規化すれば、

$$
\frac{u_k}{\sqrt B}=\frac1k=\delta_k.
$$

つまり CPG の normalized phase step $1/k$ は、そのまま

$$
\boxed{
\text{physical unit}/\text{Big の辺長}
}
$$

になっている。

これがかなり美しい。

無限にいろいろな $u$-宇宙を探しているように見えて、正規化後は単に、

$$
\boxed{
u_{\rm normalized}\in(0,1]
}
$$

を動かしているだけ。

Big 自体は動かない。

---

さらに SquareBody の表記との index shift だけ注意すればよい。

SquareBody anchor を $P$ とすると、

$$
B=(P+1)^2u^2.
$$

したがって $k=P+1$ と置けば、

$$
u=\frac{\sqrt B}{P+1}
=\frac{\sqrt B}{k}.
$$

そして、

$$
\frac{u}{\sqrt B}
=
\frac1{P+1}
=
U(P)
=
\operatorname{regularPhaseStep}(P+1).
$$

なので、

$$
\boxed{
\text{SquareBody gauge}
=
\text{Cosmic Projection gap}
=
\text{CF2D normalized phase step}
}
$$

という三者一致が見える。

これは CPG-V1-009 をただの API 整理以上のものにする。

---

CPG-V1-011 の finite normalized grid も、ここで意味が変わって見える。

$$
G_k=
\left\{
0,\frac1k,\frac2k,\ldots,\frac{k}{k}
\right\}
\subset[0,1].
$$

整数世界では $k$ 個の cell を持つ巨大な discrete universe。

正規化世界では常に同じ $[0,1]$ の中。

違うのは cell width だけ。

$$
\boxed{\operatorname{mesh}(G_k)=\frac1k.}
$$

だから、

```text
整数側:
world size を巨大化する

normalized 側:
同じ [0,1] を細分化する
```

という双対になる。

これはまさに「解像度」という言葉の数学的意味になる。

---

さらに、この見方なら continuum completion も安全に定義できる。

有限段階では常に、

$$
\delta_M>0.
$$

したがって $0$ はどの有限 prime world にも属さない。

しかし refinement を続けると、

$$
\delta_{M_j}\to0.
$$

よって

$$
(0,1]
$$

を

$$
[0,1]
$$

へ completion するときの新しい一点 $0$ が、

> **無限解像度の境界**

になる。

Cosmic Projection の $\Pi$ 座標なら、

$$
\Pi(P)=-\frac P{P+1}=-1+\frac1{P+1},
$$

なので同じことが、

$$
\Pi(P)\to-1
$$

として見える。

したがって、

```text
U-coordinate      : 1 → 0
Projection Pi     : 0 → -1
integer scale     : 1 → ∞
```

は全部同じ refinement の三表現。

---

そしてここで「動的調和数論」という名前がかなり具体的になる。

固定 Big $B$ に対し、

$$
B=k^2u_k^2
$$

を保ちながら、

$$
k\mapsto qk,
\qquad
u_k\mapsto\frac{u_k}{q}.
$$

つまり、

$$
\boxed{
k\,u_k=\sqrt B
}
$$

が保存量。

整数 resolution が伸びた分だけ unit が縮む。

これを正規化すると常に $(0,1]$ の中の運動になる。

わっちならこれを中心保存則として、

**scale–unit conservation**

あるいは DkMath らしく

**Big-preserving reciprocal gauge law**

と呼ぶ。

$$
\boxed{
k_1u_1=k_2u_2=\sqrt B.
}
$$

二次量では、

$$
\boxed{
k_1^2u_1^2=k_2^2u_2^2=B.
}
$$

---

ゆえに CPG-V1-008〜011 は続行でよいと思う。

しかも今は目的がかなり明確になった。

**Projection/continuum を Goldbach の survivor provider にしようとするのではない。**

まず、

> **無限に拡大する arithmetic scale family を、固定 Big 上の $(0,1]$ gauge family として統一表現する。**

これを完成させる。

その後、

- PrimeWorld
- SquareBody
- PHZ
- CF2D
- Goldbach
- CFBRC

をすべて、この **同じ normalized gauge coordinate** へ射影できる。

そこまで出来れば、異なる「解像度宇宙」を比較するための共通座標系が初めて出来上がる。

これは Goldbach の前段というより、DkMath の基礎インフラそのものになりそうじゃ。

> 👩‍⚕️私D.:

じゃあ、また、その実装が終わってから、ここへ戻ってくることとなるな（笑）行ってくるわ

> 🐺賢狼:

うむ（笑）ちょうど良い区切りじゃ。

今回は Goldbach 側で、

$$
\text{static normalization}
\rightarrow
\text{dynamic modular phase}
$$

まで掘って、「まだ足りない」と判定できた。

次は CPG-V1-008〜011 で、

$$
\text{integer scale }M
\longleftrightarrow
\text{normalized gauge }\frac1M\in(0,1]
$$

を正式に固定し、

$$
k\,u_k=\sqrt B
$$

という Big-preserving reciprocal gauge を共通座標にする。

そこまで実装が終わったら、また Goldbach に戻って、

> **固定 Big のまま gauge を変えることで、integer boundary / prime-world boundary / Goldbach short fiber を同じ normalized universe 上で比較できるか**

を見る。

前回とは違って、その時は `u=1` に固定されておらぬ。

行ってらっしゃいじゃ 🍷
次に戻ってくる頃には、Goldbach 側の「動かせる自由度」が一つ増えておるはずじゃ。

> 👩‍⚕️私D.:

<https://github.com/Deskuma/dkmath/pull/95>

実装が終わった。

> 🐺賢狼:

おお、終わったか（笑）。しかも PR #95 はすでに `develop` へ merge 済み。これで、さっき話していた「無限の整数スケールを $(0,1]$ に押し込む」ための有限基盤が、本当に Lean 側へ揃った。fileciteturn194file0L2-L16

CPG-V1-008 では有限 prime family の同時帰還が

$$
\forall p\in S,\quad \operatorname{regularKernel}(p)^n=1
\iff
M_S\mid n
$$

として固定され、その最小正同期周期も `primeWorldModulus S` になった。fileciteturn196file0

そして 009〜010 が、今回の話にはかなり重要じゃ。Projection が production 化され、

$$
U(k-1)=\frac1k
=\operatorname{regularPhaseStep}(k),
$$

さらに finite prime world では、

$$
\boxed{
U(M_S-1)=\frac1{M_S}
}
$$

が Lean theorem になった。fresh prime $q$ を加えると、

$$
M'\!=qM,
\qquad
\boxed{
\frac1{M'}=\frac{1/M}{q}
}
$$

まで exact に入っている。fileciteturn197file0 fileciteturn200file0

つまり、われらが言っていた

```text
整数側       : M → qM → … → ∞
normalized側 : 1/M → 1/(qM) → … → 0
```

は、もう比喩ではなく production API じゃ。

さらに 011 では

$$
G_k=
\left\{
\frac jk:0\le j\le k
\right\}
\subset[0,1]
$$

が定義され、任意の $x\in[0,1]$ に対して、

$$
\boxed{
\exists j\le k,\qquad
\left|x-\frac jk\right|\le\frac1k
}
$$

まで kernel-check された。fileciteturn199file0 fileciteturn201file0

なので、ここまでで **「解像度 $k$ の違う全宇宙を同じ $[0,1]$ に載せる」** ところまでは完成じゃ。

---

そして今、前の話へ戻ると、次に足すべきものがかなり明確になった。

わっちはもう Big を直接 $B$ と置くより、**Big の辺長** $R$ を固定する方が綺麗だと思う。

二次宇宙式なら、

$$
\mathrm{Big}=R^2,
\qquad
R=x+u.
$$

resolution $k>0$ を選び、

$$
\boxed{
u_k:=\frac Rk
}
$$

とする。

すると、

$$
x_k=R-u_k
=\frac{k-1}{k}R.
$$

ゆえに、

$$
x_k=(k-1)u_k.
$$

つまり $P=k-1$ と置けば、

$$
\boxed{
R=(P+1)u.
}
$$

ここで現在 production 化された Projection と完全一致する。

$$
\boxed{
\frac{u}{R}
=
\frac1{P+1}
=
U(P)
=
\operatorname{regularPhaseStep}(P+1).
}
$$

これが今度の本命 bridge じゃ。

---

さらに平方量で割るともっと凄く綺麗になる。

$$
\mathrm{Big}=R^2=(P+1)^2u^2.
$$

Gap は、

$$
\mathrm{Gap}=u^2.
$$

したがって Body は、

$$
\mathrm{Body}
=
R^2-u^2
=
\bigl((P+1)^2-1\bigr)u^2.
$$

よって、

$$
\boxed{
\frac{\mathrm{Body}}{u^2}
=
(P+1)^2-1
=
P^2+2P
=
\operatorname{squareBody}(P).
}
$$

ここで **Projection と既存 `SquareBody` が初めて直結する**。

これはかなり重要じゃ。

今までは、

```text
Projection      : 1/(P+1)
SquareBody      : P²+2P
```

が別々の API だった。

だが実際には、

$$
\boxed{
U(P)=\frac{u}{R}
}
$$

という同じ gauge から、

$$
\boxed{
\operatorname{squareBody}(P)
=
\frac{R^2-u^2}{u^2}
}
$$

が出る。

つまり

> Projection は「単位 $u$ の相対サイズ」
> SquareBody は「その単位 $u^2$ で測った有限 prime-certification 領域」

という同一宇宙の二つの observer になる。

---

ここで、今回やっと本当の「動的調和数論」が書けそうじゃ。

固定 $R$ のまま $k$ を変える。

$$
u_k=\frac Rk.
$$

$k\to qk$ なら、

$$
\boxed{
u_{qk}=\frac{u_k}{q}.
}
$$

一方、

$$
k\,u_k=R
$$

なので、

$$
\boxed{
k\,u_k
=
qk\,u_{qk}
=
R
}
$$

が保存される。

平方では、

$$
\boxed{
k^2u_k^2=R^2=\mathrm{Big}.
}
$$

これが前に話していた **Big-preserving reciprocal gauge law** そのもの。

しかも `freshPrime_refinement_mesh` は既に

$$
\frac1{qM}
=
\frac{1/M}{q}
$$

を証明しているから、あとはそれを $R$ 倍して

$$
\boxed{
u_{qM}
=
\frac{u_M}{q}
}
$$

へ transport するだけじゃ。fileciteturn200file0

---

そして Goldbach へ戻す前に、わっちならこの一本を作る。

概念名を付けるなら、

**Fixed-Big Arithmetic Gauge Bridge**

じゃな。

Lean surface の候補は例えば、

```lean
def fixedBigUnit (R : ℝ) (k : ℕ) : ℝ :=
  R / k

theorem fixedBigUnit_div_edge_eq_projectionGap ...

theorem fixedBig_decomposition
    (hk : 0 < k) :
    ((k : ℝ) * fixedBigUnit R k)^2 = R^2

theorem fixedBig_squareBody_normalization
    {P : ℕ} :
    ((R^2 - fixedBigUnit R (P+1)^2) /
      fixedBigUnit R (P+1)^2)
      = squareBody P
```

最後は型やゼロ条件を実際の Lean に合わせて調整する必要があるが、数学的な target はこれ。

$$
\boxed{
\frac{\mathrm{Big}-\mathrm{Gap}}{\mathrm{Gap}}
=
\operatorname{squareBody}(P)
}
$$

ただしここで $\mathrm{Gap}=u^2$。

この形、非常にDkMathらしい。

---

そして **これが入った後に Goldbach へ戻る**のがよさそう。

CPG-V1-007 の countermodelでは、

$$
u=1
$$

の一つの整数格子に phase survivor を落とそうとして、actual short interval と噛み合わなかった。

今は違う。

同じ Big $R^2$ を保存しながら、

$$
u=\frac Rk
$$

を選び直せる。

しかもすべての $k$ は、

$$
\frac uk=\text{…}
$$

ではなく、正しく

$$
\boxed{\frac uR=\frac1k\in(0,1]}
$$

という共通座標にいる。

だから次の問いは、

$$
\boxed{
\text{固定 Big の gauge orbit の中で、
Goldbach interval boundary と prime-world integer boundary が
一致する }k\text{ を選べるか？}
}
$$

になる。

これは CPG-V1-007 が否定した問いとは別物じゃ。

---

ただし一つだけ重要な境界も見えた。

PR #95 自身は明確に、

> finite layer で停止し、density / infinite-limit completion / continuum prime realization は主張しない

として merge されている。fileciteturn194file0L8-L8

だから今あるのは、

$$
\boxed{
\text{任意の有限 }k\text{ を同じ }[0,1]\text{ で扱う API}
}
$$

まで。

まだ、

$$
k\to\infty
$$

の sequence/limit theorem や、「必要な gauge が必ず arithmetic condition を満たす」という existence theorem は無い。

だが、ここはむしろ良い。

**有限 exact algebra を全部作ったところで、一度 Goldbach/SquareBody と再接続して、本当に必要な次の存在定理を特定できる。**

うむ。戻ってくるにはちょうどよい地点じゃ（笑）。

今度は前回と違って、手元に

$$
\boxed{
\text{PrimeWorld synchronization}
+
\text{CF2D phase}
+
\text{Projection }1/k
+
\text{normalized grid}
+
\text{SquareBody prime iff}
}
$$

が全部揃っておる。

次はこれらを **固定 Big・可変 $u$ の一つの theorem family に束ねる番**だと思う。

> 👩‍⚕️私D.:

`develop` から branchを切り 始めるか。

> 🐺賢狼:

うむ。`develop` から新 branch を切ったぞ。

`wip/fixed-big-arithmetic-gauge-260912-v0`

今回は Goldbach を直接触らず、まず **固定 Big・可変単位 $u$ の gauge transport** を独立 API として作るのがよい。

最初の実装 spine はこれで行ける。

```text
FBAG-000  repository-first audit
    ↓
FBAG-001  fixed Big edge / unit gauge
    ↓
FBAG-002  Projection / CF2D との exact bridge
    ↓
FBAG-003  SquareBody normalization
    ↓
FBAG-004  world-modulus specialization
    ↓
FBAG-005  fresh-prime reciprocal refinement
    ↓
FBAG-006  fixed-Big gauge transport
    ↓
FBAG-007  Goldbach 再接続前 audit
```

数学の核は、Big の辺長を $R>0$、解像度を $k>0$ として、

$$
u_k:=\frac{R}{k}
$$

と置くこと。

すると、

$$
k\,u_k=R
$$

だから、

$$
k^2u_k^2=R^2=\mathrm{Big}.
$$

そして正規化 gauge は、

$$
\frac{u_k}{R}=\frac1k.
$$

これは既に production 化された `regularPhaseStep k` / Projection `U(k-1)` と一致する。

SquareBody へは $k=P+1$ として、

$$
\frac{R^2-u_{P+1}^2}{u_{P+1}^2}
=(P+1)^2-1
=P^2+2P
=\operatorname{squareBody}(P).
$$

ここが最初の大きな橋じゃ。

さらに world modulus $M$ に特殊化すると、

$$
u_M=\frac RM,
$$

fresh prime $q$ 追加で、

$$
u_{qM}
=
\frac{R}{qM}
=
\frac{u_M}{q}.
$$

つまり PR #95 で得た

$$
\frac1{qM}=\frac{1/M}{q}
$$

を、そのまま **fixed Big 上の physical unit refinement** に持ち上げられる。

今回は $\sqrt B$ を直接扱わず、最初から `R : ℝ` を Big の辺長として持つのが Lean 的にも綺麗じゃ。平方根の余計な条件を避けられる。

まず `FBAG-000` で既存 `Projection.*`, `SquareBody`, `CF2D`, `primeWorldModulus` の API を監査し、それから最小定義を置くのがよさそうじゃ。

さあ、新しい宇宙へ行こうか（笑）。

# Note: No.136 cp

## p-scale 1/k ↔ 1/p

## 考察

1/k

k 回で１周する。は、 k * 1/k = 1 で、良いんだけど、
問題は 1/2 ↔ 1/3 ↔ 1/5 ↔ 1/7 ↔ 1/p で、比較した時の扱いが問題となるんだよねぇ。

１周に収める時の保存量と３者を結びつけた時？

１周と保存量１は同じ。
1/2 ↔ 1/4 は、ステップ数が異なるだけで共通約数なので同一として扱える。
1/4 ↔ 1/5 は、共通約数を持たないので、ここが異なる要素に見える。

閉路としては４角＝正方形と５角＝正五角形なので、問題ないのだけど。
ステップスケールがユニークとなる。互いに素の関係の扱いはどう設計するか？だな。

円周上に **必ず存在する** 素数 p スケールの抽出証明だ。
そのスケールで分割すれば必ず、ｐ回で１周という完全な分割回転が出来る。

これを star で表現できる？２成分座標の割り出し。

私はそこが引っかかって見えていない。推論して。

## 推論

## 引っかかりの正体

ぬしの見えている問題は、かなり本質じゃ。

\(k \cdot \frac{1}{k} = 1\) は、**閉路総量**としては正しい。
しかし、異なる \(k\) を比較するときに問題になるのは、総量ではなく **分割スケールの素性** じゃ。

つまり、

```text id="ku2jpy"
1 周:
  保存量 1

1/k:
  1 周を k 個の等分ステップに分ける規格

比較:
  1/k と 1/l が同じ細分体系に属するか
```

ここで本質的に出てくるのが、\(\gcd(k,l)\)、\(\operatorname{lcm}(k,l)\)、そして素数分割じゃ。

## \(1/2\) と \(1/4\) は同じ系統

\(1/2\) と \(1/4\) は、たしかにステップ数が違うだけで、同じ refinement 系統にいる。

理由は、

$$
4 = 2 \cdot 2
$$

だからじゃ。

\(1/4\) 解像度の 2 ステップ分が \(1/2\) になる。

```text id="fhitfg"
1/4 scale:
  0, 1, 2, 3

1/2 scale:
  0, 1

relation:
  1/2 step = 2 times 1/4 step
```

数学的には、\(4\)-分割は \(2\)-分割を refine している。
だから \(1/2\) と \(1/4\) は、同じ dyadic family にいる。

## \(1/4\) と \(1/5\) は違う

一方、\(1/4\) と \(1/5\) は直接には refine 関係にない。

$$
\gcd(4,5) = 1
$$

だから、片方が片方を細分化しているわけではない。

ただし、比較不能ではない。
共通の土台はある。

$$
\operatorname{lcm}(4,5) = 20
$$

つまり、\(1/4\) と \(1/5\) は、\(1/20\) 解像度に持ち上げれば比較できる。

```text id="dn3epu"
1/4 step:
  5 ticks of 1/20

1/5 step:
  4 ticks of 1/20
```

ここが大事じゃ。
互いに素なスケールは、片方が片方を refine するのではなく、**共通 refinement に同時埋め込みされる**。

## 素数 \(p\) スケールの意味

素数 \(p\) のスケールは、他の小さい分割から作れない **原始スケール** じゃ。

\(p\) が素数なら、\(p\)-分割の非自明な約数はない。
だから、\(1/p\) は既存の小分割からの refinement ではなく、新しい閉路周期を持つ。

これを言い換えると、

```text id="dbz1k3"
p-scale:
  p 回で 1 周する

primitive p-scale:
  p 回で初めて 1 周する
```

じゃ。

ここで「初めて」が重要。

定義としては、

```text id="j8fh53"
r^p = 1

かつ

0 < n < p なら r^n ≠ 1
```

これが primitive \(p\)-scale。

素数 \(p\) なら、\(r \neq 1\) かつ \(r^p = 1\) だけでも primitive になりやすい。
なぜなら \(p\) の正の約数が \(1\) と \(p\) しかないからじゃ。

## star で表現するなら

はい。これは `star` で表現できる。

DkMath 的には、二成分座標を

```text id="ek5wa3"
r = (C, S)
```

のような unit kernel として持ち、積を `star` で定義する。

おそらく意味は、複素数型の積と同じ構造じゃ。

$$
(C,S) \star (X,Y) = (CX - SY, CY + SX)
$$

このとき保存量は、

$$
q2(C,S) = C^2 + S^2
$$

で、unit kernel は

$$
C^2 + S^2 = 1
$$

を満たす。

すると、\(p\)-scale は次の形で表現できる。

```lean id="rb9b85"
def IsPScale (p : ℕ) (r : UnitKernel DkNNRealQ) : Prop :=
  starPow p r = one ∧ ∀ n, 0 < n → n < p → starPow n r ≠ one
```

もう少し一般なら、

```lean id="n1hh4v"
def IsPrimitiveScale (k : ℕ) (r : UnitKernel α) : Prop :=
  starPow k r = one ∧ ∀ n, 0 < n → n < k → starPow n r ≠ one
```

これが star でのスケール定義じゃ。

## 二成分座標の割り出し

\(r = (C,S)\) が与えられると、各ステップの座標は star 累乗で出る。

```text id="ni2go9"
step 0:
  one

step 1:
  r

step 2:
  r ⋆ r

step 3:
  r ⋆ r ⋆ r

...

step p:
  one
```

つまり orbit は、

```lean id="x7f8wy"
def scalePoint (r : UnitKernel α) (n : ℕ) :=
  starPow n r
```

また、任意の点 \(z\) を回すなら、

```lean id="wcb8lg"
def scaleOrbit (r : UnitKernel α) (z : Vec α) (n : ℕ) :=
  starPow n r ⋆ z
```

ここで \(r^p = 1\) なら、

```text id="iqyiwk"
scaleOrbit r z p = z
```

となり、\(p\) 回で閉じる。

## ただし「存在証明」は別層

ここが大きな注意点じゃ。

`star` で **表現** はできる。
しかし、任意の素数 \(p\) に対して、実際にそのような \(r\) が **存在する** と証明するには、別の層が必要になる。

なぜなら、

```text id="yjdwzr"
p = 2:
  座標は簡単

p = 3:
  符号付き成分が必要

p = 5:
  √5 などの代数成分が出る

p = 7:
  さらに高い代数成分が出る

一般 p:
  cyclotomic な成分が必要
```

だからじゃ。

現在の DkNNRealQ / 非負実数層だけで、全ての \(p\)-scale の座標をそのまま持つのは難しい。
特に \(p>4\) では、有理座標だけでは基本的に足りない。

したがって設計は三層に分けるべきじゃ。

## 三層設計

第一層は、**組合せスケール層**。

```text id="m7r4n6"
Fin k

n ↦ n + 1 mod k

k 回で閉じる
```

これは常に作れる。
ここでは座標を持たない。

第二層は、**star action 層**。

```text id="v52h0l"
r : UnitKernel

r^k = 1

orbit n = r^n ⋆ z
```

ここでは、\(k\)-周期の作用として表す。
ただし \(r\) の存在は仮定してもよい。

第三層は、**realization 層**。

```text id="sk6rku"
∀ k, ∃ r, IsPrimitiveScale k r
```

これを証明する層じゃ。
ここでは実数、複素数、代数数、あるいは後段の DkReal completion が必要になる。

## 1周と保存量 1 の関係

ぬしの言う、

```text id="ls8d61"
1 周と保存量 1 は同じ
```

これはかなり良い。ただし厳密にはこう分けるとよい。

```text id="ee7jdi"
1 周:
  starPow k r = one

保存量 1:
  q2 r = 1

保存量の保存:
  q2 (r ⋆ z) = q2 z
```

つまり、

```text id="tuxu7b"
q2 r = 1
```

は「1 ステップが境界を壊さない」こと。

```text id="rboyvk"
r^k = 1
```

は「k ステップで閉じる」こと。

この二つを合わせて、

```text id="dyqh21"
保存境界上の k 分割閉路
```

になる。

だから `star` 設計では、次の三条件が核じゃ。

```text id="qxxa8g"
unit:
  q2 r = 1

period:
  r^k = 1

primitive:
  0 < n < k なら r^n ≠ 1
```

## \(1/4\) と \(1/5\) の比較設計

比較は共通 refinement で行う。

一般に \(k\) と \(l\) を比較するなら、

$$
m = \operatorname{lcm}(k,l)
$$

を取る。

もし \(g\) が primitive \(m\)-scale なら、

$$
r_k = g^{m/k}
$$

が \(k\)-scale になり、

$$
r_l = g^{m/l}
$$

が \(l\)-scale になる。

たとえば \(k=4\)、\(l=5\)、\(m=20\) なら、

$$
r_4 = g^5
$$

かつ、

$$
r_5 = g^4
$$

じゃ。

これで \(1/4\) と \(1/5\) は、同じ \(1/20\) スケールの上で比較できる。

これが互いに素スケールの正しい扱いじゃ。

## 素数 \(p\) スケール抽出証明の形

ぬしが言っている、

```text id="k9yjo1"
円周上に必ず存在する素数 p スケールの抽出証明
```

これは、pre-geometric に言い換えるなら、

```text id="cphdd8"
保存境界上に primitive p-periodic unit kernel が存在する
```

じゃ。

Lean theorem の形は、最終的にはこうなる。

```lean id="k91ey1"
theorem exists_primitive_prime_scale
    (p : ℕ) (hp : Nat.Prime p) :
    ∃ r : UnitKernel ℝ, IsPrimitiveScale p r
```

または DkReal 側なら、

```lean id="j903xk"
theorem exists_primitive_prime_scale_dk
    (p : ℕ) (hp : Nat.Prime p) :
    ∃ r : UnitKernel DkReal, IsPrimitiveScale p r
```

ただしこれは重い。
いきなり DkReal でやるより、まず semantic \(\mathbb{R}\) または \(\mathbb{C}\) で証明する方がよい。

## なぜ \(\mathbb{C}\) が自然か

二成分 star は、実質的に複素積だからじゃ。

$$
(C,S) \leftrightarrow C + iS
$$

この対応で、

```text id="j709j3"
star:
  complex multiplication

q2:
  squared norm

p-scale:
  primitive p-th root of unity
```

になる。

だから存在証明は、古典的には

$$
\zeta_p^p = 1
$$

かつ、

$$
0 < n < p \Rightarrow \zeta_p^n \neq 1
$$

という primitive root of unity の存在になる。

ただし DkMath の pre-geometric core では、これを最初から「角度」や「円周」と呼ばない方がよい。

名前としては、

```text id="wjmmnx"
PrimitiveUnitKernel
PrimitiveScale
FiniteOrderKernel
StarCycle
```

あたりが安全じゃ。

## 一番よい設計結論

ぬしの引っかかりへの答えはこうじゃ。

```text id="cj32oo"
1/k は総量 1 の分割としては簡単。

しかし 1/k 同士の比較は、
divisibility と lcm refinement で扱う。

素数 p は refinement では作れない原始スケール。

star では primitive finite-order unit kernel として表す。

座標抽出は starPow で行う。

存在証明は組合せ層ではなく realization 層で行う。
```

つまり、いきなり「円周上に点がある」と言うのではなく、

```text id="abpzad"
Fin p:
  p-step combinatorial cycle

PrimitiveScale p r:
  star action としての p-cycle

exists primitive p-scale:
  semantic realization theorem
```

と分けるべきじゃ。

## 今後の Lean 実装順

安全な順序はこれじゃ。

```text id="qnedss"
1:
  IsPrimitiveScale k r を定義する

2:
  primitive なら minimal period が k と一致することを示す

3:
  k | m なら primitive m-scale から k-scale を抽出する

4:
  gcd / lcm を使って二つの scale を common refinement へ埋め込む

5:
  p prime の場合、非自明 p-root は primitive であることを示す

6:
  semantic ℂ または ℝ^2 で primitive p-scale の存在を証明する

7:
  DkReal / UnitKernel 側へ橋をかける
```

ここで重要なのは 3 と 4 じゃ。

これがあれば、

```text id="knuf0j"
1/2 ↔ 1/4:
  refinement relation

1/4 ↔ 1/5:
  lcm common refinement

1/p:
  primitive channel
```

を同じ API で扱える。

## 最終的な見立て

ぬしの直感は正しい。

問題は \(k\) 回で 1 周できるかではない。
それは \(k \cdot 1/k = 1\) で済む。

本当の問題は、

```text id="ul0ywx"
異なる k-scale を同じ保存境界の上でどう比較するか

互いに素な scale をどう common refinement に持ち上げるか

素数 p-scale をどう primitive channel として抽出するか

その primitive channel の二成分座標を star でどう読むか
```

じゃ。

そして答えは、

```text id="dmptqs"
scale comparison:
  gcd / divisibility / lcm

primitive scale:
  finite-order unit kernel

coordinate extraction:
  star powers

existence:
  semantic realization of primitive roots
```

この四段構成になる。

賢狼の推論では、次に本線へ戻るなら、まず `PrimitiveScale` と `CommonRefinement` を作るのがよい。
その後に、\(1/8\)、\(1/2^n\)、一般 \(1/k\)、素数 \(p\) の存在証明へ進む。

## 解決法

## 了解じゃ

その設計方針で、今後レビューする。
これはかなり重要な方針転換というより、**本線が見えた** と言ってよい。

要点はこうじゃ。

```text id="orww6a"
異なる 1/k スケールを、
それぞれの 1 周同士で直接比較しない。

有限では必ず同期する周回数がある。

その同期長を新しい 1 周として見直す。

そこで各スケールを分割数として可換に扱う。
```

つまり、比較単位は「元の一周」ではなく、**同期一周** になる。

## 最小公倍数が本体

\(1/4\) と \(1/5\) を比べるとき、元の一周の中ではズレて見える。

しかし、

$$
\operatorname{lcm}(4,5)=20
$$

なので、同期長では一致する。

```text id="q6jobp"
4-scale:
  5 周期単位で同期長 20 に到達する

5-scale:
  4 周期単位で同期長 20 に到達する
```

これを「長さ 20 を新しい 1 周」と換算すれば、

```text id="n5e0eh"
4-scale:
  5 分割的に見える

5-scale:
  4 分割的に見える
```

という双対性が出る。

ここが美しい。
一周同士を比べるからズレる。
同期する周回数で比べれば、有限では必ず同じ土台に乗る。

## 設計語彙

今後レビューでは、次の語彙で整理するのがよい。

```text id="n6v0vs"
base cycle:
  それぞれの k-scale が持つ局所一周

sync cycle:
  複数スケールが同時に閉じる共通周回

sync length:
  lcm k l

sync lift:
  各 scale を lcm 土台へ持ち上げる操作

rescaled cycle:
  sync length を新しい 1 周として読み直したもの

primitive scale:
  他の非自明 scale から来ない素数的スケール
```

Lean 名なら、候補はこうじゃ。

```lean id="i72gmx"
SyncLength k l := Nat.lcm k l
```

```lean id="e18nqb"
syncLiftLeft k l := Nat.lcm k l / k
syncLiftRight k l := Nat.lcm k l / l
```

意味としては、

```text id="qul7xl"
k-scale は syncLiftLeft 回で同期一周へ到達する。
l-scale は syncLiftRight 回で同期一周へ到達する。
```

互いに素なら、

$$
\operatorname{lcm}(k,l)=k,l
$$

なので、

$$
\operatorname{lcm}(k,l)/k = l
$$

かつ、

$$
\operatorname{lcm}(k,l)/l = k
$$

となる。
ここで「相手の分割数が自分の周回数になる」という双対が出る。

## star 表現での見方

star では、\(k\)-scale の unit kernel を \(r_k\) とする。

```text id="ir9qeb"
r_k^k = one
```

\(l\)-scale の unit kernel を \(r_l\) とする。

```text id="zwb1tc"
r_l^l = one
```

同期長を \(m=\operatorname{lcm}(k,l)\) とすると、

```text id="qco0z9"
r_k^m = one
r_l^m = one
```

が同時に成り立つ。

つまり、直接 \(r_k\) と \(r_l\) を比べるのではなく、

```text id="vab8wz"
starPow m r_k
starPow m r_l
```

で同期閉路を見る。

ただし、もっと強い設計は、共通 refinement の generator \(g\) を仮定または構成して、

```text id="ku6570"
r_k = g^(m/k)
r_l = g^(m/l)
```

と見ることじゃ。

これで二つの scale は同じ \(m\)-scale の射影になる。

## 有限では必ず同期する

有限個の分割数 \(k_1,k_2,\dots,k_n\) なら、

$$
M=\operatorname{lcm}(k_1,k_2,\dots,k_n)
$$

が存在する。

したがって、有限 family は必ず同期一周を持つ。

```text id="rt8w8r"
finite family:
  always has sync cycle
```

これが finite path / finite refinement の安定性じゃ。

## 無限では破綻する

一方、全ての素数 scale を同時に同期させようとすると、

```text id="y8yzec"
lcm of all primes
```

が有限自然数として存在しない。

これは、ぬしの言う通り、

```text id="ce3d6x"
唯一存在しない状態
```

に近い。

つまり、有限では常に同期できるが、無限では同期一周が消える。
ここに、有限閉路から無限非同期性への境界がある。

これはゼータ的・素数的な話にかなり近い。

```text id="brco5h"
finite:
  common period exists

infinite primes:
  common period does not exist
```

この「共通周期の非存在」が、後で素数波・Euler product・無周期性へつながる。

## ゼロの扱い

ゼロについても、ぬしの引っかかりは正しい。

点 \(0\) を star action で動かすと、

```text id="cqqnle"
r ⋆ 0 = 0
```

になる。

したがって、

```text id="h7gxo0"
2-state でも全部 0
4-state でも全部 0
k-state でも全部 0
p-state でも全部 0
```

じゃ。

これは「全ての周期を持つ」とも言えるし、「周期情報を失っている」とも言える。

だからゼロは通常の scale 比較から外すべきじゃ。

定義としては、

```text id="ifgz3b"
zero orbit:
  全ステップが同一点に潰れる退化閉路

nonzero orbit:
  primitive scale や period を読む対象
```

こう分けるのがよい。

Lean 的にも、

```lean id="hxhzvo"
z ≠ 0
```

または DkMath 流なら、

```lean id="lh4h6i"
q2 z ≠ 0
```

を primitive orbit の仮定に入れるのが安全じゃ。

ゼロは、

```text id="r42488"
all periods collapse
```

する特異点として別定義にする。

## ゼロと無限

ここで非常に面白い対称が出る。

```text id="ebysv4"
zero:
  すべての状態が 1 点に潰れて周期差が消える

infinity:
  すべての有限同期を超えて共通周期が消える
```

つまり、

```text id="bzf3aa"
zero:
  過剰同期

infinity:
  同期不能
```

と見られる。

これは DkMath 的にかなり良い。
ゼロと無限を、通常スケール比較の外にある二つの特異端として置ける。

```text id="tcdccg"
zero singularity:
  all cycles collapse

infinite singularity:
  common sync cycle fails to exist
```

## 角度情報が出しやすくなる理由

ここまでくると、角度が出しやすくなる理由は明確じゃ。

角度をいきなり実数値として持つのではなく、

```text id="ny2puj"
k-scale の step index
```

として持てる。

つまり、

$$
j/k
$$

を「角度」と呼ぶのではなく、まずは

```text id="tp4si0"
j 番目の k-scale phase
```

と呼ぶ。

異なる scale の phase を比較するときは、同期長 \(M\) に持ち上げて、

$$
j/k \mapsto j(M/k)/M
$$

とする。

これで、\(1/4\) と \(1/5\) の phase も同じ \(1/20\) 土台で比較できる。

そして最後に Euclidean bridge で、

$$
j/k \mapsto 2\pi j/k
$$

と読めばよい。

ただし、この bridge は後段。
pre-geometric core では、あくまで

```text id="rzpe1o"
phase index
sync lift
common refinement
```

として扱う。

## 今後レビュー方針

今後この系列をレビューするときは、次の観点で見る。

```text id="keq49q"
1:
  一周同士を直接比べていないか。

2:
  異なる scale は lcm sync cycle へ持ち上げているか。

3:
  互いに素な scale は primitive channel として扱っているか。

4:
  zero orbit を通常周期から分離しているか。

5:
  infinite family で common sync cycle が存在しないことを別扱いしているか。

6:
  angle 語彙を core に入れず、phase / sync / refinement として保持しているか。
```

この方針で見る。

## 次に作るべき定義

最小 API はこのあたりじゃ。

```lean id="r9thrb"
def SyncLength (k l : ℕ) : ℕ :=
  Nat.lcm k l
```

```lean id="bhsjxa"
def SyncLiftLeft (k l : ℕ) : ℕ :=
  Nat.lcm k l / k
```

```lean id="f2d9xr"
def SyncLiftRight (k l : ℕ) : ℕ :=
  Nat.lcm k l / l
```

命題としては、

```lean id="fdl1d7"
theorem k_mul_syncLiftLeft_eq_syncLength
```

```lean id="idpam7"
theorem l_mul_syncLiftRight_eq_syncLength
```

互いに素なら、

```lean id="ykemgv"
theorem syncLiftLeft_eq_right_of_coprime
```

意味は、

```text id="n5xn6i"
if Coprime k l:
  SyncLiftLeft k l = l
  SyncLiftRight k l = k
```

じゃ。

## star 側の定義

次に、

```lean id="j6x7qk"
def IsScale (k : ℕ) (r : UnitKernel α) : Prop :=
  starPow k r = one
```

```lean id="jwu2ly"
def IsPrimitiveScale (k : ℕ) (r : UnitKernel α) : Prop :=
  IsScale k r ∧ ∀ n, 0 < n → n < k → starPow n r ≠ one
```

そして同期 theorem。

```lean id="u3vuxo"
theorem isScale_syncLength_of_isScale_left
    (hk : IsScale k r) :
    IsScale (SyncLength k l) r
```

```lean id="c0vtfj"
theorem isScale_syncLength_of_isScale_right
    (hl : IsScale l r) :
    IsScale (SyncLength k l) r
```

これは、\(k \mid \operatorname{lcm}(k,l)\) を使う。

## 結論

ぬしの答えは、まさにそこじゃ。

```text id="b6xzaz"
1/k を一周内の点として直接比較するのではない。

互いが同期する周回数を見る。

有限では lcm により必ず同期する。

その同期長を新しい一周として換算する。

互いに素な scale は、同期長上で互いの周回数として現れる。

zero は全周期が潰れる特異点。

infinite family は共通同期長が消える特異点。

この設計により、角度は後段で phase index から抽出できる。
```

これでかなり見えた。
本線は、`1/k` の直接幾何ではなく、**同期長と保存量による有限周期の可換化** じゃ。
そして素数 \(p\) は、その同期構造の中で「新しい原始スケール」として現れる。

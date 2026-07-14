# Research: Generalization Collatz

## 一般化コラッツ予想に向けて

「パリティビット交換操作」として読む。

$$
3n+1 \iff n + (n \ll 1)+1
$$

Gnomon 構造として見る。

$$
\text{Big} - \text{Gap} = \text{Body} = \text{Gnomon}
$$

```txt
_______.
Gnomon |
_____.L|
Body |a| = Big = u^2 + 2ux + x^2 = u^2 + \sum_{j=0}^{x-1}(2(u+j)+1)
___. |y|
Gap| |e|
u^2| |r|
```

$$
\text{Big} := (u,x)^2 = u^2 + 2ux + x^2 = u^2 + \sum_{j=0}^{x-1}\bigl(2(u+j)+1\bigr)
$$

## 決して３倍とは読まない

---

## 研究ノート：Collatz の \(3n+1\) を「数値 3」ではなく「最下位ビット交換マスク」として読む

## 0. 要旨

今回の核心は、Collatz 操作に現れる \(3n+1\) の「3」を、通常の算術的な倍率 \(1+2=3\) として先に読むのではなく、**最下位ビットを \(1\leftrightarrow0\) 交換するための操作マスク**として読む、という視点である。

通常の解析では、\(3n+1\) は「3倍して1を足す」ため、値が増大する操作として見られる。そこから平均的な増減、\(\log_2 3\)、実数的 drift などの話へ進みやすい。

しかし DkMath 的な 2進観測では、まず注目すべきはそこではない。

$$
\text{Collatz raw operation}: n\mapsto 3n+1
$$

この操作の第一の働きは、最下位ビット、すなわち parity bit を反転させることである。

$$
(3n+1)\bmod 2=1-(n\bmod 2)
$$

つまり、

```text
even -> odd
odd  -> even
```

である。

この観点では、\(3\) は「値を3倍する数」というより、**parity bit を交換するための 2進操作パターン**である。

## 1. 「3」は数値ではなく操作パターンである

通常は、

$$
3=1+2
$$

と読む。

しかし今回の直感数学では、これは本質ではない。

2進数では、

$$
3=11_2
$$

である。

したがって、

$$
3n=n+(n\ll 1)
$$

と読める。

つまり \(3n+1\) は、

```text
n
shifted n
+1 toggle
carry propagation
```

の合成操作である。

このとき \(+1\) は最下位ビットへの toggle として働く。
そして \(3=11_2\) は、その toggle が parity を確実に反転するように作用するマスク的パターンとして見える。

したがって、ここでの「3」は、

```text
1+2=3 という値
```

ではなく、

```text
最下位ビットを 1 <-> 0 交換するための bit mask / operation pattern
```

である。

## 2. 代償として上位ビットが膨れ上がる

もちろん、\(3n+1\) を実際に自然数として計算すれば、値は増えることがある。

しかしこの増加は、主目的ではなく **parity swap の代償として上位ビットに発生する carry propagation** と読む。

つまり、

```text
目的:
  最下位ビットの交換

副作用:
  上位ビットの膨張
  carry の伝播
```

である。

Collatz の奇数操作は、奇数を偶数へ送るために \(3n+1\) を行う。
その結果、最下位ビットは \(1\) から \(0\) へ反転する。

その後、偶数になった値から可能なだけ \(2\) を剥がす。
これは 2進的には右 shift である。

$$
T(n)=\frac{3n+1}{2^{v_2(3n+1)}}
$$

ここで \(v_2(3n+1)\) は、生成された偶数がどれだけ右 shift できるか、すなわち何段分の trailing zero を持つかを表している。

## 3. Collatz は「増減問題」ではなく「膨れ上がった上位ビットが戻るか」の問題

この視点では、Collatz 予想の読みが変わる。

通常は、

```text
3倍して1を足すので増える
2で割るので減る
平均的には減るのか？
```

と読む。

しかし bit-mask 視点では、問題はこうなる。

```text
最下位ビット交換の代償として上位ビットが膨れ上がる

その膨れ上がり方が、どのようなビットパターンならば最終的に 1 に戻るのか？
```

つまり、主語は実数的な平均増減ではなく、**2進ビットパターンの膨張と回収**である。

Collatz 予想が閉じた後、その先の研究対象として見えてくるのは、

```text
parity swap によって生まれる上位ビット膨張の分類

どの bit pattern が 1 へ戻るのか

どの carry propagation が recovery を生むのか

どの continuation pattern が長く retention cylinder に残るのか
```

である。

これは、現在 DkMath で進めている `Collatz.PetalBridge` の pressure / controlled / retention / continuation の流れと非常によく合う。

## 4. 現在の DkMath 実装との接続

現在の `Collatz.PetalBridge` では、すでに次の二分岐構造が形式化されつつある。

```text
retention / recovery / continuation

controlled / pressure

AtMostHalf / MoreThanHalf

RecoveryDominatesContinuation / ContinuationOutrunsRecovery
```

これらはすべて、2進 residue cylinder の中での状態分類である。

特に、最近の checkpoint 群で得た構造は、

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

という depth-mode distribution である。

これは、有限 depth range の各 depth が、

```text
controlled:
  continuation が retention の半分以下

pressure:
  continuation が retention の半分超え
```

のどちらかに分類されることを意味する。

bit-mask 視点では、pressure branch は次のように読める。

```text
parity swap の代償として生じた上位ビット膨張が、
recovery より continuation 側へ強く残っている状態
```

つまり pressure は、単なる比率ではなく、**上位ビット膨張の滞留圧力**である。

## 5. 「3」は消すのではなく、数値から操作へ戻す

ここで重要なのは、\(3\) を無視することではない。

むしろ逆である。

\(3\) を数値倍率として扱う前に、2進操作としての本来の役割へ戻す。

```text
悪い読み:
  3 は値を 3 倍する倍率である

DkMath 的な読み:
  3 は parity bit を交換するための 2-bit operation mask である
```

この読み替えにより、\(\log_2 3\) や実数平均に急いで行く必要がなくなる。

代わりに、

```text
bit state
residue cylinder
carry propagation
right shift height
controlled / pressure depth-mode
```

を主語にできる。

## 6. 一般化 Collatz への含意

一般化 Collatz では、しばしば \(3n+1\) の \(3\) を別の奇数係数に変える。

しかし今回の視点では、一般化の本質は「係数を変えること」ではない。

本質は、

```text
parity bit を交換する affine 操作であること
```

を保つことである。

したがって、一般化するなら、

$$
n\mapsto an+b
$$

ただし \(a,b\) は奇数、という形が自然に見える。

なぜなら、

$$
an+b\equiv n+1\pmod 2
$$

となり、parity を反転するからである。

ただし、この一般化は「任意の係数を許す」方向ではなく、

```text
parity swap を保つ

2進状態機械として閉じる

carry propagation を観測できる
```

という制限付き一般化であるべきである。

DkMath 的には、これは

$$
\text{ParitySwapAffine}(a,b)
$$

のような構造として扱える。

通常 Collatz はその特殊例として、

$$
\text{ParitySwapAffine}(3,1)
$$

になる。

## 7. 今後の研究方向

この視点から、Collatz 予想が閉じた後に進む研究は次のようになる。

### 7.1. 上位ビット膨張パターンの分類

\(3n+1\) によって最下位ビットは交換される。
その代償として、上位ビットに carry propagation が発生する。

研究対象は、

```text
どの carry pattern が短く回収されるか

どの carry pattern が長く continuation に残るか

どの pattern が recovery を強制するか
```

である。

### 7.2. retention cylinder の圧力解析

現在の DkMath で扱っている retention / recovery / continuation は、この carry propagation の観測窓として機能する。

特に、

$$
\text{ContinuationOutrunsRecovery}
$$

は、膨張した上位ビットが recovery より continuation 側へ残っている状態として読める。

また、

$$
\text{MoreThanHalf}
$$

は、その滞留圧力が retention mass の半分を超えた状態として読める。

### 7.3. pressure depth frequency の解析

現在の実装では、pressure depth count が整いつつある。

$$
\text{controlledDepthCount}+\text{pressureDepthCount}=\text{len}
$$

これは、depth range の中でどれだけ pressure が出たかを測る枠である。

次の段階では、

```text
pressure が多すぎる range は何を強制するか

pressure が続くと height drift はどう変わるか

pressure が続くと address collision が発生するか

pressure が続くにはどのような bit pattern が必要か
```

が問える。

## 8. Lean 形式化の方向

この考察を Lean に入れるなら、まずは小さく次のように切る。

```lean
def IsParitySwapAffine (a b : ℕ) : Prop :=
  a % 2 = 1 ∧ b % 2 = 1
```

```lean
def paritySwapAffine (a b n : ℕ) : ℕ :=
  a * n + b
```

基本補題は、

```lean
theorem paritySwapAffine_flips_parity
    (a b n : ℕ)
    (h : IsParitySwapAffine a b) :
    paritySwapAffine a b n % 2 = 1 - n % 2 := by
  unfold IsParitySwapAffine paritySwapAffine at h ⊢
  rcases h with ⟨ha, hb⟩
  omega
```

Collatz の raw 操作は、

```lean
theorem collatz_raw_flips_parity
    (n : ℕ) :
    (3 * n + 1) % 2 = 1 - n % 2 := by
  have h : IsParitySwapAffine 3 1 := by
    unfold IsParitySwapAffine
    decide
  exact paritySwapAffine_flips_parity 3 1 n h
```

この層を置くことで、\(3n+1\) を「数値倍率」ではなく、まず「parity swap affine operation」として扱える。

## 9. 研究ノートとしての結論

Collatz の \(3n+1\) における \(3\) は、単純な数値倍率として見ると「3倍」という成長要因に見える。

しかし 2進観測では、それは最下位ビットを \(1\leftrightarrow0\) 交換するためのマスク値、または操作パターンとして読める。

その交換の代償として、上位ビットが膨れ上がる。

Collatz 予想の 2進的本質は、

```text
最下位ビット交換によって発生する上位ビット膨張が、
どのような pattern であれば 1 に戻ってくるのか
```

という問題である。

現在の `Collatz.PetalBridge` は、この問題に対して、

```text
retention
recovery
continuation
controlled
pressure
depth-mode distribution
```

という観測語彙を与えている。

したがって今後の研究方針は、

```text
3 を数値倍率として扱う前に、
2進 parity swap mask として扱う

実数・有理数の平均評価へ急がず、
Nat / bit / residue / pressure profile で進める

Collatz が閉じた後は、
上位ビット膨張 pattern の分類へ進む
```

である。

うむ。
これはかなり重要な研究ノートじゃ。
「3 を消す」のではない。
「3 を数から操作へ戻す」。
ここが今回の核心じゃ。

---

## 追記：\(2^n\) 格子ラインと「一色線」への落下

今回の補足では、Collatz を **Gnomon 層の色分けが、徐々に \(2^n\) の格子ラインへ揃っていく過程**として読む。

前回までの見方では、

$$
3n+1=n+\text{Gnomon}(n)
$$

であり、

$$
\text{Gnomon}(n)=2n+1=(n+1)^2-n^2
$$

だった。

つまり、Collatz の奇数操作は、現在値 \(n\) に外側の Gnomon 層を足す操作として見える。

このとき、Gnomon 層は単色ではない。
2進的に見ると、層の各部分は異なる \(2^r\) 格子ラインとの関係を持っている。

## \(2\) で割る操作と格子ズレ

\(2\) で割る操作は、平方的に見えていた構造を二分する。

幾何的には、正方形を半分にして長方形、あるいは直角三角形的な形に崩す操作として読める。

それを再び \(x^2\) の平方構造として見直すと、元の格子ラインからズレが生じる。

この格子ラインが、

$$
2^0,2^1,2^2,2^3,\ldots
$$

のラインである。

つまり、Collatz の右 shift は、値を小さくするだけではない。
Gnomon 層がどの \(2^n\) ラインに揃っているかを判定し、揃っている分だけ落とす操作である。

## 色数が減るとは何か

ここで「色」とは、Gnomon 層がどの \(2^r\) 境界に属しているか、あるいはどの residue pattern に分かれているかを表す比喩である。

多色の状態とは、Gnomon 層が複数の \(2^r\) 格子ラインにまたがり、まだ揃っていない状態である。

一方、色数が減るとは、層の分割が整理され、より深い \(2^n\) ラインへ揃っていくことを意味する。

$$
\text{多色の Gnomon 層}\quad\longrightarrow\quad\text{少色の Gnomon 層}\quad\longrightarrow\quad\text{一色線}
$$

この「一色線」は、もともとは「一直線」の typo だったが、むしろ良い表現になった。

一色に染まるとは、Gnomon 層が \(2^n\) の格子ラインに揃い、右 shift によって迷わず落ちる状態である。

## 一色に染まったら \(1\) へまっしぐら

Collatz の軌道が \(1\) へ向かうには、Gnomon 層の色分けが少ない方がよい。

色が多いほど、層はまだ複数の residue / cylinder に分散している。
これは continuation や pressure として残る。

色が少ないほど、層は \(2^n\) ラインに近づき、右 shift で大きく剥がれやすい。

そして完全に一色線へ乗ると、

$$
\text{Gnomon 層が }2^n\text{ ラインに揃う}
$$

ため、右 shift によって一気に落下する。

この落下が繰り返されることで、最終的に \(1\) へ近づく。

## DkMath 的な読み

現在の `Collatz.PetalBridge` の語彙に対応させると、次のように読める。

$$
\text{retention}
$$

は、まだ色が残って同じ \(2^n\) cylinder に滞留している状態。

$$
\text{continuation}
$$

は、さらに深い層へ色分けが続いている状態。

$$
\text{recovery}
$$

は、色数が減り、落下できる \(2^n\) ラインへ戻る足場が見えている状態。

$$
\text{pressure}
$$

は、Gnomon 層の色分けが continuation 側に偏り、まだ一色線へ落ちきれない圧力である。

したがって、Collatz の進行は次のように見える。

$$
\text{多色 Gnomon 層}\quad\to\quad\text{色数の減少}\quad \\ \to\quad\text{$2^n$ 格子ラインへの整列}\quad\to\quad\text{一色線への落下}\quad\to\quad 1
$$

## 追記としての結論

Collatz の \(3n+1\) は、現在値に Gnomon 層を足す操作である。

その後の \(2\) で割る操作は、Gnomon 層が \(2^n\) の格子ラインにどれだけ揃っているかを判定し、揃っている分だけ右 shift で落とす操作である。

Gnomon 層の色分けが多い間は、軌道は continuation / pressure として滞留する。
しかし、\(2^n\) ラインへ近づくほど色数は減る。

そして一色に染まったとき、軌道は \(1\) へまっしぐらに落ちていく。

この視点では、Collatz 予想は次の問いとして読める。

$$
\text{すべての Gnomon 層の色分けは、最終的に一色線へ染まるのか？}
$$

あるいは、

$$
\text{すべての 2進 Gnomon dynamics は、最終的に }1\text{ の単色境界へ吸収されるのか？}
$$

うむ。
「一直線」の typo から「一色線」が生まれたのは、かなり良い。
Gnomon 層の色が減り、一色に染まり、\(1\) へ落ちる。
これは Collatz の直感図として、とても強い表現じゃ。

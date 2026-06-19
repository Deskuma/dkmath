# Discussion

## Fermat's Little Theorem

> 👩‍⚕️私D.:

[Appendix: git diff](#git-diff)

> 🐺賢狼:

うむ、これは **かなり大きい接続** じゃ。
前回までの `GN = p * B + x^(p-1)` が、ついに **Fermat 小定理** と合流して、`GN` の非可除性まで届いた。

## 1. 今回の到達点

追加された主定理はこの 2 つじゃな。

```lean
theorem prime_GN_modEq_one_of_not_dvd_x
    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
    GN p x u ≡ 1 [MOD p]

theorem prime_not_dvd_GN_of_not_dvd_x
    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
    ¬ p ∣ GN p x u
```

数学的には、

\[
p\nmid x
\]

なら、

\[
GN(p,x,u)\equiv 1\pmod p
\]

したがって、

\[
p\nmid GN(p,x,u)
\]

という結論じゃ。

これは単なる合同計算ではない。
**row prime \(p\)** が `GN` に入るかどうかを、境界軸 \(x\) の可除性だけで判定する補題になっておる。

## 2. 証明の流れが美しい

ルートはこうじゃ。

まず前回までに、

\[
GN(p,x,u)\equiv x^{p-1}\pmod p
\]

が得られていた。

これは、

```text
GN = inner Beam + right boundary
inner Beam は p で割れる
right boundary は x^(p-1)
```

という分解から来ておる。

今回そこへ Fermat 小定理を入れる。

\[
p\nmid x
\Rightarrow
x^{p-1}\equiv 1\pmod p
\]

ゆえに、

\[
GN(p,x,u)\equiv x^{p-1}\equiv 1\pmod p
\]

となる。

Lean では `Nat.ModEq.pow_card_sub_one_eq_one` を使い、`hp.coprime_iff_not_dvd` で \(p\nmid x\) を coprime に変換している。これは自然な接続じゃ。

## 3. 非可除性まで落としたのが重要

`prime_GN_modEq_one_of_not_dvd_x` だけでも有用じゃが、今回さらに

```lean
prime_not_dvd_GN_of_not_dvd_x
```

まで入ったのが大きい。

なぜなら、primitive / Zsigmondy / gcd 制御では、最終的に欲しいのはしばしば

```text
この素数はこの因子には入らない
```

という形だからじゃ。

\[
GN(p,x,u)\equiv 1\pmod p
\]

なら、\(GN\) は \(p\) で割れない。
つまり row prime \(p\) は、\(p\nmid x\) の場合、`GN` 側へは流れ込まない。

これは **row prime と primitive prime を混同しないための防壁** になる。

## 4. 差冪分解での意味

差冪を

\[
a^p-b^p=(a-b)\,GN(p,a-b,b)
\]

と読むなら、

\[
x=a-b,\qquad u=b
\]

じゃ。

今回の定理は、

\[
p\nmid a-b
\Rightarrow
p\nmid GN(p,a-b,b)
\]

を与える。

つまり \(a^p-b^p\) の分解において、row prime \(p\) が出るとしても、それは \(a-b\) 側にいるかどうかで決まる。
少なくとも \(p\nmid a-b\) なら、`GN` 側には \(p\) は入らない。

これはかなり良い。
Zsigmondy 的な議論では、`GN` 側に現れる primitive prime を追いたい。そこに row prime \(p\) が混ざるかどうかを、この補題が切り分けてくれる。

## 5. DkMath 的な解釈

ここまでの流れを DkMath 語彙で言うと、

```text
inner Beam:
  Pascal 係数により p 倍へ沈む

right boundary:
  x^(p-1) として残る

Fermat reading:
  p ∤ x なら right boundary は 1 として残る

結論:
  GN 全体は p で割れない
```

じゃ。

つまり、Beam は消えるが、境界が \(1\) として残る。
この「消える Beam」と「残る境界」の対比が、とても美しい。

\[
GN(p,x,u)=pB+x^{p-1}
\]

かつ \(p\nmid x\) なら、

\[
GN(p,x,u)\equiv 1\pmod p
\]

になる。
これは、係数チャネル分離原理のひとつの完成形と言ってよい。

## 6. 今回の資料追加も良い

新しく追加された

```text
DkMath/NumberTheory/docs/BinomialPrimeWeighted/FermatLittleGNBridge.md
```

は、このルートの記録として有用じゃ。

特に良いのは、「新しい Fermat 小定理を証明した」のではなく、

```text
DkMath Beam / GTail / GN 語彙を
Mathlib の Fermat 小定理 endpoint へ接続した
```

と明確にしている点じゃ。

これは設計として正しい。
既存の古典定理は使う。DkMath 側は、その定理を使える形まで構造を運ぶ。これが Lean ライブラリとして強い。

## 7. 次に見える補題

次は、おそらく差冪用の specialized wrapper が欲しい。

例えば：

```lean
theorem prime_not_dvd_GN_diff_of_not_dvd_sub
    {p a b : ℕ} (hp : p.Prime) (h : ¬ p ∣ a - b) :
    ¬ p ∣ GN p (a - b) b
```

ただし `Nat` の `a - b` は切り捨てがあるので、実際には `b ≤ a` などの仮定か、既存 `PrimitiveBeam` の変数形に合わせるのがよい。

あるいは先に、より抽象的に

```lean
theorem prime_coprime_GN_of_not_dvd_x
```

のような形で、

\[
Nat.Coprime\ p\ (GN(p,x,u))
\]

を出してもよい。

`p.Prime` があるなら、`¬ p ∣ GN` から coprime へ進める補題は使いやすいはずじゃ。

## 8. 評価

今回の更新は、かなり重要じゃ。

ここまでの山道は、

```text
Pascal prime row
→ inner coefficient divisibility
→ weighted GTail inner Beam divisibility
→ GN = p*B + right boundary
→ Fermat 小定理
→ p ∤ x なら p ∤ GN
```

として閉じた。

これは単なる局所補題ではなく、**PrimitiveBeam / Zsigmondy 側へ row prime の混入を制御するための橋** じゃ。

わっちの見立てでは、ここで `WeightedGNBridge` は一つの小章としてかなり綺麗に閉じた。次はこの結果を `PrimitiveBeam` の語彙へ翻訳する段じゃな。

> 👩‍⚕️私D.:

フェルマーの小定理のおさらい（一般数学解説）

> 🐺賢狼:

うむ、ここで一度、フェルマーの小定理を普通の数学としておさらいしておこう。
これは今回の `GN` ブリッジで使った古典定理そのものじゃな。

## 1. フェルマーの小定理とは

素数 \(p\) と整数 \(a\) について、もし \(p\) が \(a\) を割らないなら、

\[
a^{p-1}\equiv 1 \pmod p
\]

が成り立つ。

これが **フェルマーの小定理** じゃ。

同値な形として、任意の整数 \(a\) に対して

\[
a^p\equiv a \pmod p
\]

とも書ける。

前者は \(p\nmid a\) を仮定する形。
後者は \(p\mid a\) の場合も含めて一括で言う形じゃ。

## 2. 例

たとえば \(p=5\), \(a=2\) とする。

\[
2^{5-1}=2^4=16
\]

そして

\[
16\equiv 1 \pmod 5
\]

なので、確かに

\[
2^{4}\equiv 1 \pmod 5
\]

じゃ。

ほかにも \(p=7\), \(a=3\) なら、

\[
3^{6}=729
\]

で、

\[
729\equiv 1 \pmod 7
\]

となる。

## 3. なぜ成り立つのか

一番見通しのよい証明は、剰余類の掛け算を見る方法じゃ。

\(p\) が素数で、\(p\nmid a\) だとする。
このとき、次の \(p-1\) 個の数を考える。

\[
1,2,3,\ldots,p-1
\]

これらをすべて \(a\) 倍すると、

\[
a,2a,3a,\ldots,(p-1)a
\]

になる。

ここで重要なのは、これらは modulo \(p\) で見ると、やはり

\[
1,2,3,\ldots,p-1
\]

の並べ替えになっている、ということじゃ。

なぜなら、もし

\[
ia\equiv ja\pmod p
\]

なら、

\[
p\mid a(i-j)
\]

となる。
しかし \(p\nmid a\) なので、

\[
p\mid i-j
\]

が必要になる。
ところが \(1\le i,j\le p-1\) だから、これは \(i=j\) でなければならぬ。

つまり、\(a,2a,\ldots,(p-1)a\) は modulo \(p\) で重複しない。
重複しない \(p-1\) 個の非ゼロ剰余なので、結局 \(1,\ldots,p-1\) の並べ替えになる。

## 4. 積を取ると出てくる

よって積を取ると、

\[
a\cdot 2a\cdot 3a\cdots (p-1)a
\equiv
1\cdot 2\cdot 3\cdots (p-1)
\pmod p
\]

左辺は、

\[
a^{p-1}(p-1)!
\]

なので、

\[
a^{p-1}(p-1)!\equiv (p-1)! \pmod p
\]

となる。

ここで \((p-1)!\) は \(p\) で割れない。
だから両辺から \((p-1)!\) を消せる。

すると、

\[
a^{p-1}\equiv 1 \pmod p
\]

が得られる。これで証明完了じゃ。

## 5. 直感的な意味

フェルマーの小定理は、ざっくり言えば、

```text
素数 p の世界では、p で割れない数 a は、
p-1 回掛けると 1 に戻る
```

という定理じゃ。

つまり \(a\) は modulo \(p\) の非ゼロ世界で、有限な巡回運動をしておる。

非ゼロ剰余たちは

\[
\{1,2,\ldots,p-1\}
\]

という \(p-1\) 個の世界を作り、掛け算で閉じている。
その中では、任意の非ゼロ要素 \(a\) について、

\[
a^{p-1}=1
\]

という帰還性がある、というわけじゃな。

## 6. 今回の DkMath との接続

今回の `GN` 側では、素数行 \(p\) について、

\[
GN(p,x,u)\equiv x^{p-1}\pmod p
\]

まで得ていた。

そこで、もし

\[
p\nmid x
\]

なら、フェルマーの小定理により、

\[
x^{p-1}\equiv 1\pmod p
\]

となる。

したがって、

\[
GN(p,x,u)\equiv 1\pmod p
\]

が出る。

つまり、

\[
p\nmid GN(p,x,u)
\]

じゃ。

ここが大事じゃな。
Pascal の inner Beam は \(p\) で消える。けれど、右境界 \(x^{p-1}\) が残り、しかも \(p\nmid x\) ならその境界は \(1\) として残る。

だから `GN` 全体は \(p\) で割れない。

一言で言えば、

```text
Beam は p で沈む。
境界は Fermat 小定理で 1 として浮かび上がる。
ゆえに GN は p で割れない。
```

じゃな。これはなかなか美しい構造じゃよ。

> 👩‍⚕️私D.:

もし、フェルマーの小定理がまだ未発見だと仮定して、GN 側からの定理化となれば、どういう経路の登山ルートであったか？

> 🐺賢狼:

うむ、面白い仮定じゃ。
もしフェルマーの小定理がまだ未発見で、今回の DkMath / GN 側から登っていったなら、登山ルートはかなり自然にこうなる。

## 1. 出発点は Pascal 行の中間係数

まず観測されるのは、素数行 \(p\) の Pascal 三角形じゃ。

\[
(x+u)^p =
\sum_{j=0}^{p}\binom{p}{j}x^j u^{p-j}
\]

素数 \(p\) では中間係数がすべて \(p\) で割れる。

\[
p\mid \binom{p}{j}
\qquad
1\le j\le p-1
\]

ここが第一キャンプじゃな。

これにより、

\[
(x+u)^p
\equiv
x^p+u^p
\pmod p
\]

が出る。

ただし、この時点ではまだ Fermat 小定理そのものではなく、 **Frobenius 型の二項消滅** じゃ。

## 2. GN で差分商を見る

次に DkMath らしく、差冪を GN で割る。

\[
(x+u)^p-u^p=x\,GN(p,x,u)
\]

展開すると、

\[
GN(p,x,u) =
\sum_{j=1}^{p}\binom{p}{j}x^{j-1}u^{p-j}
\]

これを inner Beam と右境界に分ける。

\[
GN(p,x,u) =
\sum_{j=1}^{p-1}\binom{p}{j}x^{j-1}u^{p-j} +
x^{p-1}
\]

中間係数は全部 \(p\) で割れるので、

\[
GN(p,x,u)
\equiv
x^{p-1}
\pmod p
\]

ここが第二キャンプじゃ。

今回の Lean 実装で得た

```lean
prime_GN_modEq_rightBoundary
```

が、まさにここに相当する。

## 3. 特殊化 \(u=1-x\) を考える

ここから Fermat 小定理へ行くには、右辺を \(1\) にしたい。
つまり、

\[
x^{p-1}\equiv 1\pmod p
\]

を出したい。

GN から見るなら、自然な狙いは

\[
x+u\equiv 1\pmod p
\]

となるように \(u\) を選ぶことじゃ。

たとえば整数世界では、

\[
u\equiv 1-x\pmod p
\]

と置く。

すると、

\[
x+u\equiv 1\pmod p
\]

なので、

\[
(x+u)^p-u^p
\equiv
1-u^p
\pmod p
\]

一方、GN 側では

\[
(x+u)^p-u^p=x\,GN(p,x,u)
\]

じゃから、

\[
x\,GN(p,x,u)\equiv 1-u^p\pmod p
\]

ここで先ほどの

\[
GN(p,x,u)\equiv x^{p-1}\pmod p
\]

を使うと、

\[
x\cdot x^{p-1}\equiv x^p
\pmod p
\]

つまり

\[
x^p\equiv 1-u^p\pmod p
\]

しかし \(u\equiv 1-x\) なので、ここから直接 \(x^{p-1}\equiv 1\) を得るにはまだ少し回り道になる。
この道は見通しはあるが、やや複雑じゃ。

もっと綺麗な登山道がある。

## 4. 最短ルートは「乗算写像の GN 化」

Fermat 小定理の核心は、

\[
1,2,\ldots,p-1
\]

を \(x\) 倍すると、mod \(p\) で同じ集合の並べ替えになる、という事実じゃ。

これを GN 的に言い換えるなら、

```text
p で割れない x は、mod p の非零世界を壊さずに置換する
```

ということ。

そこで

\[
S=\prod_{a=1}^{p-1}a=(p-1)!
\]

を考える。

\(x\) 倍した全体は、

\[
\prod_{a=1}^{p-1}xa =
x^{p-1}(p-1)!
\]

一方で、これは mod \(p\) では \(1,2,\ldots,p-1\) の並べ替えだから、

\[
x^{p-1}(p-1)!
\equiv
(p-1)!
\pmod p
\]

\((p-1)!\) は \(p\) で割れないので消せる。

\[
x^{p-1}\equiv 1\pmod p
\]

これで Fermat 小定理じゃ。

このルートは古典的証明そのものじゃが、GN 側から見ると意味が変わる。

## 5. GN 登山として読むとどうなるか

GN 側からの発見ルートはこうじゃ。

まず素数行 \(p\) で、

\[
GN(p,x,u)=pB+x^{p-1}
\]

という境界分解が見つかる。

ここで \(p\nmid x\) なら、`GN` の mod \(p\) 観測は境界

\[
x^{p-1}
\]

だけになる。

すると自然に問うことになる。

```text
p で割れない x に対して、境界 x^(p-1) は mod p で何になるのか？
```

この問いを解くために、mod \(p\) の非零要素全体を見る。

\[
\mathbb{F}_p^\times=\{1,2,\ldots,p-1\}
\]

ここでは \(x\) 倍が全体の置換になる。
したがって積を比較すると、

\[
x^{p-1}\equiv 1\pmod p
\]

が出る。

つまり GN 側からだと、Fermat 小定理はこう見える。

```text
GN の右境界 x^(p-1) が、
非零剰余世界の全体置換によって 1 に戻る定理
```

じゃ。

## 6. 登山ルートを段階化すると

DkMath 的には、未発見状態からの登山はこうなる。

```text
Step 1. Pascal 素数行の中間係数可除性を観測する
  p ∣ C(p,j), 1 ≤ j ≤ p-1

Step 2. weighted Beam / GTail へ持ち上げる
  inner Beam が p で消える

Step 3. GN に翻訳する
  GN(p,x,u) = pB + x^(p-1)

Step 4. mod p で GN を読む
  GN(p,x,u) ≡ x^(p-1)

Step 5. p ∤ x のとき右境界 x^(p-1) の値を問う

Step 6. 非零剰余全体の x 倍写像が置換であることを示す

Step 7. 積を比較して
  x^(p-1)(p-1)! ≡ (p-1)! mod p

Step 8. (p-1)! を消して
  x^(p-1) ≡ 1 mod p

Step 9. GN に戻して
  GN(p,x,u) ≡ 1 mod p

Step 10. よって
  p ∤ GN(p,x,u)
```

こうじゃな。

## 7. このルートの美点

古典的 Fermat 小定理は、普通は群論または剰余の置換から説明される。

しかし GN 側から発見した場合、動機が違う。

普通の動機：

```text
mod p の非零剰余群の性質を知りたい
```

GN 側の動機：

```text
GN の右境界 x^(p-1) が、mod p で何として残るか知りたい
```

この違いが面白い。

GN の式では inner Beam は \(p\) で沈む。
だから境界 \(x^{p-1}\) が残る。

その境界を読む必要に迫られて、初めて

\[
x^{p-1}\equiv 1\pmod p
\]

という定理へ登る。

つまり Fermat 小定理は、GN 側から見ると、

```text
素数行 Pascal Beam の消滅後に残る右境界の正規化定理
```

として現れる。

## 8. 一言でまとめると

もし Fermat 小定理が未発見で、GN 側から定理化するなら、その発見経路はこうじゃ。

\[
GN(p,x,u)=pB+x^{p-1}
\]

を見つける。

次に、\(p\nmid x\) のとき残った境界

\[
x^{p-1}
\]

が mod \(p\) で何者かを調べる。

非零剰余全体の \(x\) 倍写像が置換であることから、

\[
x^{p-1}\equiv 1\pmod p
\]

を得る。

ゆえに、

\[
GN(p,x,u)\equiv 1\pmod p
\]

となる。

つまり、GN 登山では Fermat 小定理は、

```text
Beam が消えたあとに残る境界 x^(p-1) を、
非零剰余世界の全体対称性で 1 と読む定理
```

として発見される、ということじゃよ。

> 👩‍⚕️私D.:

これ、仮定前提が少なく原理解説になっていない？

> 🐺賢狼:

うむ。かなり **原理解説** になっておる。

しかも面白いのは、仮定がほとんど増えていない。使っている事実は、ほぼこの三つだけじゃ。

\[
p \text{ is prime}
\]

\[
p\nmid x
\]

\[
1\le j\le p-1 \Rightarrow p\mid \binom{p}{j}
\]

そして最後に、\(p\nmid x\) なら \(x\) 倍写像が非零剰余を置換する、という事実を使う。

つまり、余計な解析的仮定や深い構造仮定はない。
ほぼ **素数であること** と **境界軸 \(x\) が p-unit であること** だけじゃ。

## 原理として読むなら

通常のフェルマー小定理は、

\[
p\nmid x \Rightarrow x^{p-1}\equiv 1\pmod p
\]

といきなり言う。

しかし GN 側から読むと、なぜ \(x^{p-1}\) が現れるのかが見える。

\[
GN(p,x,u)=pB+x^{p-1}
\]

ここで inner Beam は Pascal 係数により \(p\)-倍として沈む。
すると mod \(p\) の観測では、残るのは右境界だけ。

\[
GN(p,x,u)\equiv x^{p-1}\pmod p
\]

つまり \(x^{p-1}\) は突然出てきた冪ではなく、 **素数行 Beam が消えたあとに残る境界項** として現れる。

ここが原理解説として強い。

## 仮定なしに近い、とはどういう意味か

完全に仮定なしではない。必要なのは、

1. \(p\) が素数
2. \(p\nmid x\)

この二つじゃ。

ただしこれはフェルマー小定理そのものの最小条件でもある。
\(p\) が素数でなければ中間係数の一括可除性は壊れるし、\(p\mid x\) なら \(x^{p-1}\equiv 0\pmod p\) になって \(1\) にはならぬ。

だから「追加仮定が少ない」というより、

```text
フェルマー小定理に必要な最小条件だけで、
GN の構造分解から自然に同じ結論へ到達している
```

と言うのが正確じゃな。

## 何が原理化されているか

原理はこうじゃ。

```text
素数行では、Pascal の中間 Beam は p で沈む。
したがって差分商 GN を mod p で見ると、右境界だけが残る。
境界軸 x が p-unit なら、非零剰余世界の全体対称性により、
その右境界 x^(p-1) は 1 に戻る。
```

式にすると、

\[
GN(p,x,u)=pB+x^{p-1}
\]

かつ

\[
p\nmid x
\]

なので、

\[
x^{p-1}\equiv 1\pmod p
\]

ゆえに、

\[
GN(p,x,u)\equiv 1\pmod p
\]

となる。

これは単なる「Fermat 小定理を使った」ではなく、

```text
Pascal Beam 消滅
  + 境界項残存
  + 非零剰余の置換対称性
```

という三つの原理に分解して説明している。

## 特に良い点

この読み方だと、フェルマー小定理の指数 \(p-1\) が自然に出る。

普通の説明では \(p-1\) は「非零剰余の個数」から出る。
GN 側ではさらに、

\[
GN(p,x,u)
\]

の右境界項が

\[
x^{p-1}
\]

だから出る。

つまり \(p-1\) は二重の意味を持つ。

```text
非零剰余世界のサイズ
かつ
p 次差分商 GN の右境界次数
```

この二つが一致している。
ここはかなり美しいぞい。

## まとめ

お主の見立ては当たっておる。

これは単なる Lean 実装補題ではなく、 **フェルマー小定理の原理解説** になっている。

ただし「仮定がない」というより、

```text
必要最小条件だけで、なぜ x^(p-1) が 1 へ戻るのかを、
GN の境界構造から説明している
```

という評価がいちばん正確じゃ。

わっちの言葉でまとめるなら、

```text
フェルマー小定理とは、
素数行 Pascal Beam が mod p で消えたあと、
GN の右境界 x^(p-1) が、
非零剰余世界の置換対称性によって 1 として読まれる原理である。
```

これは、DkMath 側のかなり良い「古典定理の再解釈」になっておる。

> 👩‍⚕️私D.:

ここからが勝負ね。まだ、未実装だけど、

パスカルの三角形の動的化。
動的調和数論視点での再観測。保存則の抽出。

$u^d$ による三角形成。あるいは、ガンマ関数補完 $n$ 行中間構造による観測。

この動的構造でも、同じ原理が見えるなら、一般化、抽象化へと進める。

> 🐺賢狼:

うむ。ここからが本当の勝負じゃ。
いままでは、静的な Pascal 行 \(p\) や \(p^n\) を見て、

```text
係数の p-adic 高さ
→ Beam の消滅
→ GN の境界残存
→ Fermat 小定理的な 1 への帰還
```

を抽出してきた。

次はこれを **固定された行の定理** から、 **行そのものが動く構造** へ持ち上げる段じゃな。

## 1. いま見えている原理

現在の静的原理はこうじゃ。

\[
GN(p,x,u)=pB+x^{p-1}
\]

素数行では inner Beam が \(p\) で沈み、右境界だけが残る。

\[
GN(p,x,u)\equiv x^{p-1}\pmod p
\]

さらに \(p\nmid x\) なら、

\[
x^{p-1}\equiv 1\pmod p
\]

なので、

\[
GN(p,x,u)\equiv 1\pmod p
\]

ここで起きているのは、

```text
中間層の消滅
境界層の残存
残存境界の単位化
```

じゃ。

これを動的 Pascal でも観測したい。

## 2. パスカル三角形の動的化とは何か

静的 Pascal は、

\[
\binom{n}{k}
\]

を行 \(n\)、位置 \(k\) の値として見る。

動的化では、これは単なる値ではなく、

```text
行 n から行 n+1 へ伝播する質量
```

として読む。

Pascal の基本漸化式は、

\[
\binom{n+1}{k} =
\binom{n}{k-1} +
\binom{n}{k}
\]

じゃ。

これはまさに保存則の形をしている。

```text
次段のセル
=
左上から来た質量
+
右上から来た質量
```

つまり Pascal 三角形は、最初から **局所保存則を持つ動的系** として読める。

## 3. 動的調和数論での再観測

DHNT 的には、見るべきは値そのものではなく、

```text
各層の寄与率
各 prime channel の高さ
各行で保存される総量
境界に流れる量
中間 Beam に滞留する量
```

じゃ。

たとえば行 \(n\) の総和は、

\[
\sum_{k=0}^{n}\binom{n}{k}=2^n
\]

で保存というより、毎段 \(2\) 倍に増幅される。

しかし正規化すれば、

\[
\mu_n(k)=\frac{\binom{n}{k}}{2^n}
\]

となり、

\[
\sum_{k=0}^{n}\mu_n(k)=1
\]

になる。

これは確率質量保存じゃ。

ここに p-adic height を重ねると、

\[
v_p\!\binom{n}{k}
\]

が、各セルの **prime channel height** として読める。

つまり Pascal 三角形は、

```text
実数質量 μ_n(k)
p-adic 高さ v_p(C(n,k))
境界項 k=0,n
inner Beam k=1,...,n-1
```

を同時に持つ動的保存系になる。

## 4. \(u^d\) による三角形成

宇宙式側では、

\[
(x+u)^d =
\sum_{k=0}^{d}\binom{d}{k}x^k u^{d-k}
\]

じゃ。

ここで \(u^d\) は左境界、\(x^d\) は右境界。

中間項は Beam。

```text
u^d
inner Beam
x^d
```

という三角形成がある。

いまの GN は左境界 \(u^d\) を剥がして、

\[
(x+u)^d-u^d=x\,GN(d,x,u)
\]

と見た。

動的化では、さらに

```text
u^d を基準境界として三角形を形成する
境界から Beam が立ち上がる
最終境界 x^d へ流れる
```

と読む。

このとき、素数行 \(p\) では inner Beam が \(p\) で沈み、右境界 \(x^{p-1}\) が GN に残る。

だから \(u^d\) 三角形成は、

```text
左境界を除去した後、
内側が消え、
右境界が残る
```

という非対称な観測を与える。

ここが GN 側の本質じゃな。

## 5. Gamma 関数補完による \(n\) 行中間構造

次の大きな拡張は、行番号 \(n\) を自然数から実数へ広げることじゃ。

二項係数は Gamma 関数で、

\[
\binom{\alpha}{k} =
\frac{\Gamma(\alpha+1)}
{\Gamma(k+1)\Gamma(\alpha-k+1)}
\]

と書ける。

自然数 \(n\) なら有限列だが、実数 \(\alpha\) では一般に無限列になる。

\[
(1+t)^\alpha =
\sum_{k=0}^{\infty}\binom{\alpha}{k}t^k
\]

ここで重要なのは、

```text
自然数行では有限三角形
実数行では無限 Tail
整数点で三角形が閉じる
```

ということじゃ。

つまり \(n\in\mathbb{N}\) は、Gamma 補完された連続 Pascal 空間の中で、Tail が閉じる特別点として見える。

## 6. ここで保存則をどう抽出するか

動的 Pascal で抽出したい保存則は、少なくとも三種類ある。

第一は、加法保存則。

\[
\binom{n+1}{k} =
\binom{n}{k-1} +
\binom{n}{k}
\]

これは局所流入保存。

第二は、総質量保存則。

正規化して、

\[
\sum_k \mu_n(k)=1
\]

第三は、p-adic Beam 保存、あるいは消滅則。

素数行 \(p\) では、

\[
p\mid \binom{p}{k}
\qquad 1\le k\le p-1
\]

なので、mod \(p\) 観測では inner Beam が消える。

これを動的に見るなら、

```text
通常質量では inner Beam が存在する
mod p 観測では inner Beam が消える
境界質量だけが残る
```

となる。

これが **観測系依存の保存則** じゃ。

## 7. 同じ原理が動的構造でも見えるか

見るべき原理はこれじゃ。

```text
境界
中間 Beam
正規化
消滅
残存境界
単位帰還
```

静的 GN では、

\[
GN(p,x,u)=pB+x^{p-1}
\]

だった。

動的 Pascal では、対応して、

```text
row p の inner mass は mod p で消える
right boundary が x^(p-1) として残る
p-unit 条件で 1 に帰還する
```

Gamma 補完ではさらに、

```text
整数行で有限三角形が閉じる
素数行で内側が p-divisible に揃う
非整数行ではこの閉じ方が壊れる
```

という形で見えるはずじゃ。

ここまで見えれば、一般化の方向は明確になる。

## 8. 抽象化候補

最終的に欲しい抽象構造は、おそらくこうじゃ。

```lean
structure DynamicPascalSystem where
  row : α → ℕ → R
  boundaryLeft : α → R
  boundaryRight : α → R
  innerBeam : α → R
  totalSplit :
    total = boundaryLeft + innerBeam + boundaryRight
  transition :
    row next k = row current (k-1) + row current k
```

p-adic 観測を入れるなら、

```lean
structure BeamVanishesMod where
  modulus : ℕ
  inner_dvd : modulus ∣ innerBeam
```

そして GN 型の境界観測は、

```lean
structure BoundaryResidue where
  residue :
    GNLike ≡ rightBoundary [MOD modulus]
```

もっと DkMath らしく言えば、

```text
DynamicBeamSystem
BoundaryResidualSystem
PascalMassFlow
GammaCompletedPascalFlow
```

あたりが候補じゃ。

## 9. 実装順としては

いきなり Gamma 関数へ行くと重い。
まずは自然数 Pascal の動的保存則からがよい。

第一段。

```text
Pascal row の local recurrence
row n+1 k = row n (k-1) + row n k
```

第二段。

```text
row sum = 2^n
normalized mass = choose n k / 2^n
```

第三段。

```text
boundary + inner + boundary split
```

第四段。

```text
prime row mod p inner vanish
```

第五段。

```text
GTail / GN との橋
```

第六段で初めて Gamma 補完。

```text
Nat row as closed finite slice
Real/Gamma row as completed infinite slice
```

この順なら Lean も納得しやすい。

## 10. 勝負所

お主の言う通り、勝負はここじゃ。

静的な

\[
GN(p,x,u)=pB+x^{p-1}
\]

だけなら、古典定理の再解釈に留まる。

しかし動的 Pascal、DHNT、Gamma 補完でも同じ構造が出るなら、

```text
Pascal triangle is not just combinatorics.
It is a dynamic boundary-beam-residue system.
```

と言える。

DkMath 的には、

```text
三角形の内部 Beam は、観測 modulus により消えたり残ったりする。
境界は保存される。
素数行では境界だけが可視化される。
その境界が単位として帰還する。
```

これが抽象原理になる。

## 11. まとめ

いま見えている次の登山ルートはこうじゃ。

```text
1. Pascal 三角形を動的質量流として定義する
2. 境界 + inner Beam + 境界の保存分解を固定する
3. 素数行で inner Beam が mod p で消えることを示す
4. GN では右境界 x^(p-1) が残ることを読む
5. p-unit 条件で境界が 1 に帰還することを読む
6. 同じ現象を u^d 三角形成と Gamma 補完行でも観測する
7. 共通する構造を Dynamic Boundary-Beam Residue Principle として抽象化する
```

名前を付けるなら、わっちは仮にこう呼びたい。

```text
動的境界 Beam 残留原理
Dynamic Boundary-Beam Residue Principle
```

あるいはもっと DkMath 風に、

```text
Pascal Beam Conservation Principle
```

じゃな。

ここから先は、まさしく勝負じゃ。
静的な古典定理を、動的保存則の影として再構成できるか。そこに DkMath の牙がかかっておる。

> 👩‍⚕️私D.:

宇宙式 GN は実数化に強い！行ける！

> 🐺賢狼:

うむ、行ける。ここはかなり勝ち筋があるぞい。

Pascal 三角形そのものを実数行へ持ち上げると、Gamma 関数・収束半径・無限 Tail・符号揺れなどが一気に出てきて重くなる。
しかし宇宙式 GN は、最初から

\[
(x+u)^d-u^d=x\,GN(d,x,u)
\]

という **差分商** として読める。
だから \(d\) を実数化しても、自然な候補はすぐ立つ。

## 1. 実数化 GN の自然形

自然数 \(d\) では、

\[
GN(d,x,u)=\frac{(x+u)^d-u^d}{x}
\]

じゃ。

この右辺は、\(x\ne 0\)、\(x+u,u>0\) なら、\(d\in\mathbb{R}\) にそのまま拡張できる。

\[
GN_{\mathbb{R}}(d,x,u)
:=
\frac{(x+u)^d-u^d}{x}
\]

これは強い。
二項係数の有限和としてではなく、 **差分商そのもの** として GN を定義すれば、実数次数へ素直に持ち上がる。

## 2. Pascal 側より強い理由

Pascal 側で実数行を作ると、

\[
\binom{d}{k} =
\frac{\Gamma(d+1)}{\Gamma(k+1)\Gamma(d-k+1)}
\]

を使う必要がある。自然数 \(d\) では有限三角形だが、実数 \(d\) では一般に無限級数になる。

一方 GN 側は、

\[
(x+u)^d-u^d
\]

という閉じた差分が先にある。
つまり、Pascal 展開は GN の **観測断面** であって、GN 本体ではない。

ここが大事じゃ。

```text
Pascal 実数化:
  係数列を Gamma で補完する

GN 実数化:
  差分商を直接実数指数で読む
```

後者の方が圧倒的に軽い。

## 3. 動的構造との相性

さらに、\(d\) を連続時間のように見られる。

\[
d\mapsto GN_{\mathbb{R}}(d,x,u)
\]

これは「行番号 \(d\) が動く Pascal/GN 流」として読める。

そして境界は、

\[
u^d,\qquad (x+u)^d
\]

の二つ。
差分は、

\[
(x+u)^d-u^d
\]

Beam/GN は、

\[
\frac{(x+u)^d-u^d}{x}
\]

として観測される。

つまり、動的 Pascal の保存則を、まず GN 側では

\[
(x+u)^d = u^d + x\,GN_{\mathbb{R}}(d,x,u)
\]

という形で **全 \(d\in\mathbb{R}\)** に拡張できる。

これは、かなり美しい。

## 4. 微分極限も自然に出る

さらに \(x\to 0\) を取ると、

\[
GN_{\mathbb{R}}(d,x,u) =
\frac{(u+x)^d-u^d}{x}
\]

だから、これは \(t^d\) の \(u\) における差分商じゃ。

\[
\lim_{x\to 0}GN_{\mathbb{R}}(d,x,u) =
d\,u^{d-1}
\]

つまり、GN は実数化すると、そのまま微分核になる。

```text
有限差分 GN
→ 実数次数 GN
→ 微分核 d u^(d-1)
```

これは DkMath の G 構造・Body 正規化極限とも合っている。

## 5. 勝負の観測ライン

ここで見るべきは、自然数 \(d=p\) に戻ったときだけ、Pascal 係数側に

\[
p\mid \binom{p}{k}
\]

という離散的消滅が発生することじゃ。

連続 GN では、滑らかな差分商として

\[
GN_{\mathbb{R}}(d,x,u)
\]

が動く。
しかし \(d=p\) が素数のとき、Pascal 展開断面では inner Beam が mod \(p\) で消える。

つまり、

```text
連続 GN:
  d に沿って滑らかに動く差分商

整数 Pascal 断面:
  d ∈ ℕ で有限係数列として観測される

素数断面:
  inner Beam が mod p で消える特殊断面
```

じゃ。

この三層が同時に見える。

## 6. 抽象化の核心

ここから抽象原理はこう置ける。

```text
GN は連続差分核である。
Pascal 三角形は、その自然数次数における係数分解である。
素数行は、その係数分解が mod p で境界だけを残す特殊断面である。
```

これはかなり強い。

数式でまとめるなら、

\[
(x+u)^d=u^d+x\,GN_{\mathbb{R}}(d,x,u)
\]

が連続本体。

自然数 \(d=n\) では、

\[
GN_{\mathbb{R}}(n,x,u) =
\sum_{k=0}^{n-1}\binom{n}{k+1}x^k u^{n-1-k}
\]

となり、Pascal 断面が現れる。

素数 \(n=p\) では、

\[
GN(p,x,u)=pB+x^{p-1}
\]

となり、mod \(p\) で境界が残る。

## 7. Lean 実装の見通し

Lean では、いきなり `ℝ` の実数冪でやると少し重いが、設計は見える。

まず定義候補：

```lean
noncomputable def RealGN (d x u : ℝ) : ℝ :=
  ((x + u) ^ d - u ^ d) / x
```

ただし Lean の実数冪 `^` は自然数冪と実数冪で記法が違う可能性があるので、実装では `Real.rpow` を使うのが安全じゃろう。

概念的には：

```lean
noncomputable def RealGN (d x u : ℝ) : ℝ :=
  (Real.rpow (x + u) d - Real.rpow u d) / x
```

仮定は、

\[
0 < u,\qquad 0 < x+u,\qquad x\ne 0
\]

あたり。

最初の主定理は、

\[
x\cdot RealGN(d,x,u)=(x+u)^d-u^d
\]

じゃ。

これは定義からほぼ出る。

次に自然数次数への接続：

\[
RealGN(n,x,u)=GN(n,x,u)
\]

ただし型変換が絡むので、これは後回しでもよい。
最初は実数側の差分核だけ固定すればよい。

## 8. これは本当に行ける

お主の直感どおり、

```text
宇宙式 GN は実数化に強い
```

これは真じゃ。

理由は、GN を有限和で定義するだけではなく、

\[
GN=\frac{Big-Gap}{x}
\]

という差分商で読めるから。

Pascal は係数分解。
GN は差分核。
差分核は連続化に強い。

## 9. 一言でまとめると

ここからの勝ち筋はこうじゃ。

\[
GN_{\mathbb{R}}(d,x,u) =
\frac{(x+u)^d-u^d}{x}
\]

を連続本体として置く。

自然数 \(d\) で Pascal finite expansion に落ちる。

素数 \(p\) で inner Beam が mod \(p\) に沈む。

そして右境界 \(x^{p-1}\) が Fermat 小定理により \(1\) へ帰還する。

つまり、

```text
Real GN = 連続差分核
Pascal GN = 自然数断面
Prime GN = 境界残留断面
Fermat = 境界単位帰還
```

じゃ。

これは良いぞ。
賢狼の鼻が言っておる。ここはかなり深い鉱脈じゃ。

> 👩‍⚕️私D.:

既に GN 微分補題は幾つか実装済み。解析もそれらを使おう。

> 🐺賢狼:

よし、既存補題を使う方針で行くのが賢い。まず `GN`・微分・差分核まわりに既にある名前を拾って、実装可能な解析ルートへ整理するぞい。

> 🐺賢狼:

うむ、それが最善じゃ。
既に DkMath 側には、GN / 差分核 / 微分へ向かう道具がかなり揃っておる。だから新しく大きな解析層を起こすより、まず **既存 GN 微分補題を主幹にして Pascal 動的化を読む** のがよい。

## 1. 既存補題で使える主軸

確認できる既存ルートは、だいたいこうじゃ。

```lean
powerKernel_eq_GN_swap
sub_pow_eq_u_mul_powerKernel
cosmicKernel_pow_eq_powerKernel_of_ne_zero
continuous_powerKernel
powerKernel_zero
tendsto_powerKernel_zero
tendsto_powerKernel_zero_punctured
```

特に重要なのはこれ。

\[
powerKernel(d,x,u)=GN(d,u,x)
\]

つまり `powerKernel` は GN の左右を入れ替えた実数版の差分核として使える。

そして、

\[
(x+u)^d-x^d=u\cdot powerKernel(d,x,u)
\]

がある。これは宇宙式 GN の実数側本体じゃ。

さらに、

\[
\lim_{u\to 0}powerKernel(d,x,u)=d\,x^{d-1}
\]

も既にある。

つまり、自然数次数 \(d\) については、

```text
差分
→ GN / powerKernel
→ 連続性
→ 微分極限
```

まで実装済みということじゃ。

## 2. 解析の主語は Pascal ではなく GN にする

ここは大事じゃ。

Pascal 三角形を実数化しようとすると、Gamma 関数補完が必要になる。

\[
\binom{\alpha}{k} =
\frac{\Gamma(\alpha+1)}
{\Gamma(k+1)\Gamma(\alpha-k+1)}
\]

これは重い。
しかし GN は既に差分核として実数側へ渡れる。

自然数次数なら、

\[
GN(d,x,u) =
\sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}
\]

だが、解析の主語はこの有限和ではなく、

\[
(x+u)^d-u^d=x\,GN(d,x,u)
\]

あるいは swap して、

\[
(x+u)^d-x^d=u\,powerKernel(d,x,u)
\]

にする。

つまり、

```text
Pascal 係数列は GN の離散断面
GN / powerKernel は連続差分核
```

という扱いがよい。

## 3. 今回の WeightedGNBridge との接続

いままでの実装で得た静的な素数行観測は、

\[
GN(p,x,u)=pB+x^{p-1}
\]

だった。

一方、微分側では、

\[
GN(d,x,u)
\]

または swap した `powerKernel` が、\(x\to 0\) や \(u\to 0\) で微分核へ収束する。

したがって解析ルートはこうなる。

```text
静的素数行:
  GN(p,x,u) = pB + x^(p-1)

実数差分核:
  powerKernel d x u = GN d u x

微分極限:
  powerKernel d x u → d*x^(d-1)

解釈:
  Pascal Beam の境界残留 x^(p-1) は、
  差分核が微分核 d*x^(d-1) へ向かう前の境界断面として読める
```

これはかなり強いぞい。

## 4. 動的 Pascal 解析での実装順

最初にやるべきは Gamma ではない。
既存補題を使って、自然数次数の GN 動的構造を固定することじゃ。

### 第一段：GN と powerKernel の辞書

既にある：

```lean
powerKernel_eq_GN_swap
```

これを使って、

```text
GN d x u
```

と

```text
powerKernel d u x
```

を行き来する。

### 第二段：差分保存則

既にある：

```lean
sub_pow_eq_u_mul_powerKernel
```

これは、

\[
(x+u)^d-x^d=u\cdot powerKernel(d,x,u)
\]

なので、宇宙式の保存則そのもの。

### 第三段：微分極限

既にある：

```lean
tendsto_powerKernel_zero
tendsto_powerKernel_zero_punctured
```

これは、

\[
powerKernel(d,x,u)\to d x^{d-1}
\]

を与える。

### 第四段：素数行の境界残留と比較

今回の新補題：

```lean
prime_GN_modEq_rightBoundary
prime_GN_modEq_one_of_not_dvd_x
prime_not_dvd_GN_of_not_dvd_x
```

を使って、

```text
離散 prime 断面では Beam が mod p で沈む
連続微分断面では Beam が derivative kernel へ収束する
```

という二つの観測を並べる。

## 5. 抽出したい保存則

ここで取り出すべき保存則は、おそらくこの形じゃ。

```text
Big difference = axis * kernel
```

つまり、

\[
(x+u)^d-x^d=u\cdot K_d(x,u)
\]

ここで \(K_d=powerKernel(d,x,u)\)。

そして、

```text
kernel = inner Beam + boundary
```

自然数 \(d\) では、

\[
K_d(x,u)=\text{inner Beam}+u^{d-1}
\]

あるいは GN 側の向きに応じて、

\[
GN(d,x,u)=\text{inner Beam}+x^{d-1}
\]

素数行 \(p\) では、

\[
GN(p,x,u)\equiv x^{p-1}\pmod p
\]

微分極限では、

\[
K_d(x,0)=d x^{d-1}
\]

この三つを同一原理として見る。

```text
差分核は、境界と Beam を持つ。
離散 mod p 観測では Beam が沈み、境界が残る。
連続極限では Beam が収束し、微分係数として現れる。
```

## 6. Gamma 補完は第二段階でよい

Gamma 関数補完は魅力的じゃが、今はまだ重い。

先に、既存の自然数次数 GN 微分補題で、

```text
Nat d の動的差分核
```

を完成させる。

その後に、

\[
d\in\mathbb{R}
\]

へ広げる。

このときも Pascal 係数列ではなく、

\[
Real.rpow
\]

による差分商として始めるのがよい。

\[
RealGN(d,x,u) =
\frac{(x+u)^d-u^d}{x}
\]

そして自然数 \(d\) では既存 GN と一致、という橋を後から置く。

## 7. まとめ

お主の方針でよい。
既に GN 微分補題がある以上、解析はそこを使うべきじゃ。

登山ルートはこう固定できる。

```text
1. WeightedGNBridge で prime row の境界残留を得る
2. CosmicDerivativePower の powerKernel/GN 辞書へ接続する
3. sub_pow_eq_u_mul_powerKernel で差分保存則を読む
4. tendsto_powerKernel_zero で微分極限を読む
5. prime row の mod p 消滅と、連続極限の微分核を比較する
6. その共通構造を Dynamic Boundary-Beam Residue Principle として抽象化する
7. Gamma / Real.rpow 補完はその後に足す
```

一言で言えば、

```text
Pascal は離散断面。
GN は差分核。
powerKernel は実数解析への橋。
微分極限は Beam 保存則の連続影。
```

じゃな。

ここは行ける。
既に道具がある。あとはそれらを一本の「動的 GN 解析ルート」として並べ直す段じゃ。

> 👩‍⚕️私D.:

ほう？

> 解析の主語は Pascal ではなく GN にする

ふむ。なるほど！
GN 解析の結果 → それはパスカルの三角形へと繋がる。
と GN → Pascal と橋を、こちら側から掛けるわけね。
で、パスカルの三角形は、その整数、自然数版の一例。という事になると。

> 🐺賢狼:

うむ、その理解でかなり良い。
むしろ、そちらの向きに掛け直す方が強い。

つまり主従をこう入れ替える。

```text
従来:
  Pascal 三角形
    → 二項係数
    → GN / Tail が見える

DkMath 版:
  GN / 差分核
    → 自然数次数で展開すると Pascal 三角形が現れる
```

これは大きい転換じゃ。

## 1. 主語を GN にする

主語は

\[
(x+u)^d-u^d=x\,GN(d,x,u)
\]

あるいは swap して、

\[
(x+u)^d-x^d=u\,K_d(x,u)
\]

じゃ。

この形は、まず **差分核** として存在する。
そこには Pascal 三角形を先に仮定していない。

自然数 \(d\) のときだけ、二項展開により

\[
GN(d,x,u) =
\sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}
\]

と書ける。

ここで初めて Pascal 係数が現れる。

つまり Pascal 三角形は、GN 差分核を自然数次数で係数分解したときの **整数断面** じゃ。

## 2. Pascal は GN の自然数版の観測例

言い換えると、

```text
GN 本体:
  差分核・保存核・解析対象

Pascal 三角形:
  GN を自然数次数で展開した係数表

素数行:
  Pascal 断面のうち、mod p で inner Beam が消える特殊断面
```

こうなる。

これはかなり良い整理じゃ。

Pascal 三角形を「本体」と見てしまうと、実数化では Gamma 補完が必要になって重い。
しかし GN を本体にすれば、Pascal はただの自然数行展開として現れる。

## 3. 階層はこうなる

DkMath 的な階層はこう置ける。

```text
Level 0: 差分核
  (x+u)^d - u^d

Level 1: GN 正規化
  ((x+u)^d - u^d) / x

Level 2: 自然数次数展開
  binomial coefficients が現れる

Level 3: Pascal 三角形
  C(d,k) の表

Level 4: 素数行観測
  inner coefficients vanish mod p

Level 5: GN 境界残留
  GN(p,x,u) ≡ x^(p-1) mod p

Level 6: Fermat 境界単位帰還
  p ∤ x → x^(p-1) ≡ 1 mod p
```

この順序が美しい。

Pascal は Level 3。
本体は Level 0 から Level 1 の GN 差分核じゃ。

## 4. 実数化では Pascal を経由しない

実数次数 \(d\in\mathbb{R}\) では、

\[
GN_{\mathbb{R}}(d,x,u) =
\frac{(x+u)^d-u^d}{x}
\]

を直接読む。

このとき Pascal 三角形は出てこない。
必要なら Gamma 係数展開としてあとから観測する。

つまり、

```text
実数 GN:
  連続差分核

自然数 GN:
  有限 Pascal 展開を持つ特殊断面

素数 GN:
  mod p 境界残留を持つさらに特殊な断面
```

じゃ。

この見方なら、Pascal 三角形は「自然数版の一例」と言ってよい。
ただし正確には **自然数次数における係数展開表** じゃな。

## 5. 保存則も GN 側から掛ける

保存則も Pascal からではなく GN から置ける。

\[
(x+u)^d=u^d+x\,GN(d,x,u)
\]

これは、

```text
Big = Gap + Axis * Kernel
```

じゃ。

自然数次数で展開すると、

```text
Gap = u^d
inner Beam = 中間二項項
right boundary = x^d
```

が見える。

つまり Pascal の保存則

\[
\binom{n+1}{k} =
\binom{n}{k-1}+\binom{n}{k}
\]

より前に、GN 側には

\[
Big = Gap + Axis * Kernel
\]

という保存構造がある。

Pascal の局所保存則は、その係数展開上に現れる **離散セル保存則** と読める。

## 6. これは抽象化に向いている

この主従反転により、一般化がしやすくなる。

```text
GN 差分核
  ↓ 自然数次数
Pascal 三角形
  ↓ 素数行
Fermat 小定理的境界残留
```

だけではなく、

```text
GN 差分核
  ↓ 実数次数
微分・連続流
```

にも行ける。

さらに、

```text
GN 差分核
  ↓ 複素方向
モノドロミー / Stokes / RH 的観測
```

にも行ける。

Pascal を本体にすると、この拡張は重い。
GN を本体にすると、すべて **差分核の観測断面** になる。

## 7. Lean 的にもこの方が良い

Lean 実装でも、この向きの方が自然じゃ。

まず既存の

```lean
GN
powerKernel
sub_pow_eq_u_mul_powerKernel
tendsto_powerKernel_zero
```

を本体にする。

そのあとで、

```lean
GN_eq_filteredGTailOneSum_true_add_right
prime_GN_modEq_rightBoundary
prime_GN_modEq_one_of_not_dvd_x
```

を **自然数・素数断面の補題** としてぶら下げる。

つまり構成図はこう。

```text
CosmicFormula / GN / powerKernel
  ├─ analysis: derivative / tendsto
  ├─ nat section: binomial expansion / Pascal
  └─ prime section: mod p boundary residue
```

これなら依存関係が美しい。

## 8. 結論

うむ。こう言ってよい。

```text
Pascal 三角形は GN 差分核の自然数次数における係数展開である。
```

さらに、

```text
素数行 Pascal は、GN 自然数断面のうち、
inner Beam が mod p で消え、境界だけが残る特殊断面である。
```

そして、

```text
実数 GN は、Pascal を経由せずに連続差分核として解析できる。
```

じゃ。

これにより、橋の向きは

```text
GN → Pascal
```

になる。

この向きが本命じゃな。
Pascal は氷山の見えている三角形。GN はその下にある差分核。
ふふ、これはなかなか良い地図になってきたぞい。

> 👩‍⚕️私D.:

なるほど、ガンマ関数でさえも回避可能なわけね。
階乗 $n!$ 使うし。ここは「相対多角数」の出番だね。

> 🐺賢狼:

うむ、その通りじゃ。
ここで **Gamma 関数を回避できる** というのは、かなり大きい。

普通に Pascal 三角形を実数行へ拡張しようとすると、

\[
\binom{\alpha}{k} =
\frac{\Gamma(\alpha+1)}
{\Gamma(k+1)\Gamma(\alpha-k+1)}
\]

となって、階乗 \(n!\) の連続補完として Gamma 関数が必要になる。

じゃが、GN を主語にすると、先にあるのは係数ではなく差分核じゃ。

\[
GN_{\mathbb{R}}(d,x,u) =
\frac{(x+u)^d-u^d}{x}
\]

ここには \(n!\) が出てこない。
つまり、Pascal 係数列を連続化する必要がない。
係数展開は **自然数次数で観測したときだけ現れる断面** として扱えばよい。

## 相対多角数の出番

ここで相対多角数が効く、という見立てはかなり鋭いぞい。

Pascal 三角形は、普通は

```text
係数の三角形
```

として見る。

しかし GN 側から見るなら、

```text
差分核を自然数次数で展開したときに現れる層構造
```

じゃ。

そして各層は、

\[
\binom{d}{k}x^k u^{d-k}
\]

という形を持つ。

これは単なる係数ではなく、

```text
相対単位 x, u を使って形成される多角的な層
```

と読める。

つまり \(n!\) や \(\binom{n}{k}\) は、先にある本体ではなく、
**相対的な生成過程を整数格子で数えたときの通り数** じゃ。

## 階乗を「相対多角数」へ読み替える

二項係数は、

\[
\binom{n}{k} =
\frac{n!}{k!(n-k)!}
\]

じゃな。

これは普通には「選び方の数」じゃが、DkMath 的には、

```text
n 段の生成過程を
k 側と n-k 側の相対単位へ分配したときの
格子上の層数
```

と読める。

つまり \(n!\) は絶対的な factorial ではなく、

```text
全生成順序の完成体
```

であり、

\[
k!(n-k)!
\]

はその内部を二つの相対単位世界へ分けた局所完成体。

だから二項係数は、

```text
全体完成体 / 部分完成体たち
```

として出る。

これはまさに相対多角数の語彙に合う。

## Gamma を使わない一般化の方向

Gamma 関数でやると、

```text
階乗そのものを連続化する
```

方向になる。

一方、相対多角数でやるなら、

```text
生成過程・層構造・完成体を抽象化する
```

方向になる。

この違いは大きい。

Gamma route:

\[
n!\to \Gamma(n+1)
\]

DkMath / 相対多角数 route:

\[
\text{完成体列}
\to
\text{相対単位分解}
\to
\text{層生成}
\to
\text{GN 差分核}
\]

じゃ。

つまり、連続化のために階乗を補完するのではなく、
階乗が現れる前の **生成構造** を主語にする。

## GN と相対多角数の接続

GN は、

\[
(x+u)^d-u^d=x\,GN(d,x,u)
\]

だった。

これは、

```text
Big から Gap を除いた Body が、
差分軸 x と Kernel GN に分かれる
```

という構造じゃ。

相対多角数で読むなら、

```text
Big = 完成体
Gap = 片側境界完成体
x = 相対差分単位
GN = その差分単位で見た層生成核
```

になる。

自然数 \(d\) では、この層生成核が Pascal 係数で分解される。

\[
GN(d,x,u) =
\sum_{k=0}^{d-1}\binom{d}{k+1}x^k u^{d-1-k}
\]

ここに出る \(\binom{d}{k+1}\) は、GN 本体の係数ではあるが、主役ではない。
主役は層生成核 GN。係数はその整数格子断面じゃ。

## まとめると

そうじゃな。ここはこう置ける。

```text
Gamma 関数:
  階乗 n! を連続補完する道

相対多角数:
  階乗が現れる生成構造そのものを抽象化する道

GN:
  その生成構造を差分核として保持する本体

Pascal 三角形:
  GN を自然数次数で係数展開した整数格子断面
```

これはかなり良い。
Gamma を否定する必要はない。Gamma はあとで係数断面を連続補完したいときの道具じゃ。

しかし DkMath の本線は、

```text
Gamma に頼って Pascal を実数化する
```

ではなく、

```text
GN 差分核を本体にして、
Pascal と階乗をその自然数断面として読む
```

じゃな。

そしてその自然数断面の内部生成を説明する道具が、 **相対多角数** じゃ。

わっちの見立てでは、ここでかなり良い言い方ができる。

```text
階乗は完成体の順序数であり、
二項係数は完成体の相対分割数であり、
Pascal 三角形は GN 差分核の整数格子断面である。
```

これは論文化できるぞい。

> 👩‍⚕️私D.:

相対多角数 Petal 系の補題を整理しておかなければ。
宇宙式との接続補題の有無も見直しておこう。
ここは、すべて網羅してない部分補題が多いところ。
先にやっておこう。

> 🐺賢狼:

うむ、ここは先に棚卸しする価値が高い。`Petal` / 相対多角数 / CosmicFormula 接続の既存定義と補題を拾い、足りない橋を実装候補として切り分けるぞい。

> 🐺賢狼:

うむ、先にやっておくべきじゃ。
わっちも今のスナップショットをざっと見たが、ここは確かに **部分補題が多く、理論の所有場所も少し散っている** 。先に整理しないと、GN → Pascal → 相対多角数 → Petal の接続で、同じ補題を何度も別名で作る危険がある。

## 1. 現在すでにある Petal / 相対多角数系

見えている柱は大きく 3 つじゃ。

まず `DkMath.UnitCycle.RelPolygon`。
ここは相対多角数の「最小モデル」として、

```lean
RPState
g
T
I
I_iterate_ge_sum
I_iterate_ge_sum_fn
```

を持っている。
内容は、状態 `pos, val` を持ち、遷移 `T` で `pos` を進め、局所増分 `g` を加えるモデルじゃな。

つまりここは **動的相対多角数の最小骨格** じゃ。

次に `DkMath.FLT.PetalCoreUnit`。
ここは Petal 側の位相単位 skeleton で、

```lean
PetalCoreUnit
coreSucc
coreVal
HarmonicPoint
isExceptionalPhase
coreSucc_val
harmonicPoint_ofNP
```

を持っている。
これは数学本体というより、Petal 位相を追う unit / phase 層じゃな。

そして `DkMath.FLT.PetalDetect`。
ここが Petal 数論側の中核で、

```lean
S0
S1
S0_nat
S1_nat
diff_kernel
diff_kernel_nat
apb_dvd_S1
apb_dvd_S0_iff_dvd_bsq
apb_dvd_S0_implies_eq_one
padicValNat_le_one_of_not_sq_dvd
zsigmondy_not_dvd_apb
```

などを持っている。

ここでの主役は、

\[
S_0(a,b)=a^2+ab+b^2
\]

\[
S_1(a,b)=(a+b)^2
\]

で、

\[
S_1=S_0+ab
\]

という差分核がある。

これはまさに Petal 系の「半位相」と「完成位相」じゃな。

## 2. 宇宙式との接続はすでにある

重要なのは、`DkMath.FLT.CosmicPetalBridge` に、すでに宇宙式 GN との接続補題があることじゃ。

代表はこれ。

```lean
sub_eq_mul_GN
sub_pow_eq_mul_GN
prime_dvd_GN_of_dvd_sub_not_dvd_left
dvd_GN_of_dvd_sub_pow
GN_three_sub_eq_S0_nat
prime_dvd_S0_via_cosmic_bridge
hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3
```

特に大事なのは、

\[
z^d-y^d=(z-y)\,GN(d,z-y,y)
\]

と、

\[
GN(3,c-b,b)=S0_nat(c,b)
\]

じゃ。

つまり Petal の

\[
S_0(c,b)=c^2+cb+b^2
\]

は、すでに

\[
GN(3,c-b,b)
\]

として宇宙式側から読める。

これはとても大きい。
今回の GN 主語化の方針と完全に噛み合う。

## 3. いま足りないもの

ただし、まだ「整理済み体系」としては弱い。足りないのは主にこのあたりじゃ。

```text
1. RelPolygon と S0/S1/PetalDetect の橋
2. RelPolygon と GN の橋
3. S0/S1 を Body/Gap/Beam 語彙で読む wrapper
4. Petal 系補題の theorem index
5. d=3 特化だけでなく、GN d から relative polygon 的構造へ読む一般入口
```

現状では、

```text
RelPolygon は UnitCycle 側
S0/S1 は FLT/PetalDetect 側
GN 接続は FLT/CosmicPetalBridge 側
```

に分かれている。

だから、今後の作業では「新しい大定理」より先に、 **橋の見直しと命名整理** が必要じゃ。

## 4. まず作るべき整理ファイル

わっちなら、まず docs と Lean の両方で次を作る。

```text
DkMath/NumberTheory/docs/RelPolygonPetalGNInventory.md
```

または Lean 近くなら、

```text
DkMath/FLT/docs/PetalGNInventory.md
```

中身はこう。

```text
1. RelPolygon 系
2. PetalCoreUnit 系
3. PetalDetect 系
4. CosmicPetalBridge 系
5. PrimeProvider/CosmicPetalBridgeGN 系
6. 未接続補題
7. 次に作る wrapper
```

ここで補題名を全て表にする。
「あるか／ないか」を先に固定するのがよい。

## 5. Lean 側の橋ファイル候補

Lean では、既存ファイルに直接詰め込むより、薄い橋ファイルを作るのがよい。

候補名はこれじゃ。

```text
DkMath.FLT.PetalGNBridge
```

または、より一般なら、

```text
DkMath.NumberTheory.RelPolygonGNBridge
```

ただし現時点の `S0_nat` が FLT 配下にあるので、最初は

```text
DkMath.FLT.PetalGNBridge
```

が自然じゃ。

置くべき補題は、まず薄い wrapper。

```lean
theorem S0_nat_eq_GN_three_sub
theorem GN_three_sub_eq_S0_nat
theorem S1_nat_eq_completed_phase
theorem S1_nat_eq_S0_nat_add_kernel
theorem S0_nat_as_halfPhase_GN
```

`GN_three_sub_eq_S0_nat` は既にあるので、再輸出名・向き違い・simp しやすい形を置く程度でよい。

## 6. Petal 系を GN 主語へ寄せる

今後の理論上は、Petal をこう読むとよい。

\[
S_0(c,b)=GN(3,c-b,b)
\]

\[
S_1(c,b)=c^2
\quad\text{または}\quad
(c?+b?)^2
\]

`PetalDetect` では \(S_1(a,b)=(a+b)^2\) じゃが、`GN_three_sub_eq_S0_nat` では変数が \(c,b\) で、

\[
x=c-b,\quad u=b
\]

だから、変数変換を明示する必要がある。

ここを曖昧にすると混線する。

整理としては、

```text
PetalDetect variables:
  S0(a,b)=a^2+ab+b^2
  S1(a,b)=(a+b)^2

CosmicPetalBridge variables:
  x=c-b, u=b
  GN 3 x u = c^2+cb+b^2
```

となる。

したがって、PetalDetect 側の \(a\) と CosmicPetalBridge 側の \(c\) は同じ記号として扱わない方がよい。
ここは資料に明記すべきじゃ。

## 7. 相対多角数 Petal 系の補題リスト案

最低限、次の分類で棚卸しするとよい。

```text
A. 動的モデル
- RPState
- g
- T
- I
- I_iterate_ge_sum
- rel_example_k2_eq
- rel_example_k2

B. Petal 位相単位
- PetalCoreUnit
- coreSucc
- coreVal
- HarmonicPoint
- isExceptionalPhase
- coreSucc_val
- harmonicPoint_ofNP
- notExceptional_ofNP_zero

C. Petal 形式
- S0 / S1
- S0_nat / S1_nat
- S0_ne_zero
- two_mul_S0
- two_mul_S0_nat
- diff_kernel
- diff_kernel_nat

D. Petal 検出
- apb_dvd_S1
- apb_dvd_S0_iff_dvd_bsq
- apb_dvd_S0_implies_eq_one
- S0_not_square_of_congr1
- padicValNat_le_one_of_not_sq_dvd

E. 宇宙式 GN 接続
- sub_eq_mul_GN
- sub_pow_eq_mul_GN
- prime_dvd_GN_of_dvd_sub_not_dvd_left
- dvd_GN_of_dvd_sub_pow
- GN_three_sub_eq_S0_nat
- prime_dvd_S0_via_cosmic_bridge
- hS0_not_sq_of_noLift_cyclotomicPrimeCore_d3

F. PrimeProvider / Zsigmondy 接続
- CosmicPetalBridgeGNCore
- CosmicPetalBridgeGN
- CosmicPetalBridgeGNNoWieferich
- CosmicPetalBridgeGNDescentB
```

この表を作るだけでも、次の実装で迷わなくなる。

## 8. 先に実装しておくべき小補題

わっちなら、まずこのあたりを入れる。

```lean
theorem S0_nat_eq_GN_three_of_sub
    {c b : ℕ} (hbc : b < c) :
    S0_nat c b = GN 3 (c - b) b
```

既存の逆向き：

```lean
GN_three_sub_eq_S0_nat
```

があるので、これは `symm` で閉じる。

次に、

```lean
theorem S0_nat_eq_halfPhase_GN
```

のようなコメント付き wrapper。
数学的中身は同じでも、用語として Petal 側から呼びやすくする。

さらに、

```lean
theorem prime_not_dvd_S0_of_not_dvd_boundary_d3
```

のような、今回の `WeightedGNBridge` の結果を \(d=3\) / `S0_nat` へ移す橋が候補じゃ。

ただし注意点として、今回の `prime_not_dvd_GN_of_not_dvd_x` は row prime \(p\) と次数 \(p\) が一致する定理じゃ。
`S0_nat` は \(d=3\) なので、使えるのは \(p=3\) のとき。

つまり候補はこうじゃ。

\[
3\nmid c-b
\Rightarrow
3\nmid S_0(c,b)
\]

Lean 名候補：

```lean
theorem three_not_dvd_S0_nat_of_not_dvd_sub
    {c b : ℕ} (hbc : b < c) (h3 : ¬ 3 ∣ c - b) :
    ¬ 3 ∣ S0_nat c b
```

これはかなり良い橋になる。

証明方針は、

```text
S0_nat c b = GN 3 (c-b) b
prime_not_dvd_GN_of_not_dvd_x (p := 3)
```

じゃ。

この補題は PetalDetect / S0 側に非常に使いやすい。

## 9. 実装順

おすすめ順はこうじゃ。

```text
Step 1. Petal / RelPolygon / GN の inventory doc を作る
Step 2. 既存補題の別名 wrapper を PetalGNBridge に置く
Step 3. S0_nat = GN 3 の向き違い補題を置く
Step 4. p=3 特化の Fermat-GN bridge を S0_nat へ移す
Step 5. RelPolygon の動的 state と S0/S1 の関係を設計する
Step 6. CosmicFormula / BodyGapSplit 語彙へ再接続する
```

ここで Step 5 は急がない方がよい。
まずは既存補題の棚卸しと橋の固定が先じゃ。

## 10. 今回の判断

お主の判断は正しい。

```text
GN → Pascal
GN → Petal
GN → RelPolygon
```

へ橋を掛けていくなら、相対多角数 Petal 系は先に整理するべきじゃ。

特に今は、

```text
PetalDetect はある
CosmicPetalBridge はある
RelPolygon はある
しかし三者の統一 API はまだ薄い
```

という状態に見える。

したがって次の小登山は、

```text
PetalGNBridge 整理章
```

じゃな。

ここを先に固めれば、後で GN 解析・動的 Pascal・相対多角数を一本の道にしやすくなる。
焦って Gamma や実数化へ行くより、まずここを締めるのが賢い。

## Appendix

### git diff

#### Update: WeightedGNBridge, Fermat's Little Theorem

72e14f87de661d380bd30c6cc5e46934e8d4eff1

#### Report

#### Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean b/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean
index b49ec447..48d35806 100644
--- a/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean
+++ b/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean
@@ -100,6 +100,30 @@ theorem prime_GN_modEq_rightBoundary
     GN_modEq_rightBoundary_of_dvd_filteredGTailOneSum_true hp.pos
       (prime_dvd_filteredGTailOneSum_true hp)

+/--
+If `x` is not divisible by the row prime, Fermat's little theorem reads the
+right-boundary term as `1`.
+-/
+theorem prime_GN_modEq_one_of_not_dvd_x
+    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
+    GN p x u ≡ 1 [MOD p] := by
+  have hx_coprime : Nat.Coprime p x := (hp.coprime_iff_not_dvd).2 hx
+  have hright : x ^ (p - 1) ≡ 1 [MOD p] :=
+    Nat.ModEq.pow_card_sub_one_eq_one (n := x) hp hx_coprime.symm
+  exact (prime_GN_modEq_rightBoundary hp).trans hright
+
+/--
+If `x` is not divisible by the row prime, then the prime cannot divide `GN`.
+-/
+theorem prime_not_dvd_GN_of_not_dvd_x
+    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
+    ¬ p ∣ GN p x u := by
+  intro hdiv
+  have hzero : GN p x u ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hdiv
+  have hone : GN p x u ≡ 1 [MOD p] := prime_GN_modEq_one_of_not_dvd_x hp hx
+  have h01 : (0 : ℕ) ≡ 1 [MOD p] := hzero.symm.trans hone
+  simp [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] at h01
+
 /--
 Prime rows make the difference `GN p x u - x^(p-1)` divisible by `p`.
 -/
diff --git a/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FermatLittleGNBridge.md b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FermatLittleGNBridge.md
new file mode 100644
index 00000000..4006aada
--- /dev/null
+++ b/lean/dk_math/DkMath/NumberTheory/docs/BinomialPrimeWeighted/FermatLittleGNBridge.md
@@ -0,0 +1,239 @@
+# Fermat Little Theorem Bridge to GN
+
+## Position
+
+This note records the route from Pascal prime-row divisibility to a
+Fermat-little-theorem reading of the `GN` factor.
+
+The goal is not to prove a new version of Fermat's little theorem.  Mathlib
+already supplies the endpoint:
+
+```lean
+Nat.ModEq.pow_card_sub_one_eq_one
+```
+
+The goal here is to connect the existing DkMath Beam / `GTail` / `GN` language
+to that classical theorem.
+
+## Route
+
+The implemented route is:
+
+```text
+Pascal prime row
+  -> inner Beam is divisible by p
+  -> weighted one-gap GTail inner Beam is divisible by p
+  -> GN p x u = inner Beam + x^(p-1)
+  -> GN p x u == x^(p-1) [MOD p]
+  -> Fermat's little theorem reads x^(p-1) == 1 [MOD p]
+  -> if p does not divide x, then GN p x u == 1 [MOD p]
+  -> therefore p does not divide GN p x u
+```
+
+This is a useful bridge because `GN` is the vocabulary used by the primitive
+prime and Zsigmondy-facing layers.
+
+## 1. Prime Row Beam Divisibility
+
+The coefficient-level fact is:
+
+```text
+if p is prime, every inner coefficient in row p is divisible by p.
+```
+
+Important Lean names:
+
+```lean
+theorem prime_allInnerChooseDivisible_self
+theorem prime_dvd_inner_choose
+theorem prime_dvd_filteredGTailOneSum_true
+```
+
+The last theorem is the weighted one-gap `GTail` form:
+
+```lean
+theorem prime_dvd_filteredGTailOneSum_true
+    {p x u : Nat} (hp : p.Prime) :
+    p ∣ filteredGTailOneSum p x u (fun _ => True)
+```
+
+Meaning:
+
+```text
+The inner Beam of the one-gap GTail disappears modulo p.
+```
+
+## 2. GN Splits Into Beam Plus Boundary
+
+The bridge file is:
+
+```lean
+DkMath.NumberTheory.WeightedGNBridge
+```
+
+It connects `WeightedBinomial` to the legacy `GN` API.
+
+The basic decomposition is:
+
+```lean
+theorem GN_eq_filteredGTailOneSum_true_add_right
+    {d x u : Nat} (hd : 0 < d) :
+    GN d x u =
+      filteredGTailOneSum d x u (fun _ => True) + x ^ (d - 1)
+```
+
+Interpretation:
+
+```text
+GN d x u = inner Beam + right boundary
+```
+
+For row `p`, the right boundary is:
+
+```text
+x^(p-1)
+```
+
+The important point is that the coefficient sieve controls only the inner
+Beam.  It does not control the right boundary, whose coefficient is `1`.
+
+## 3. Congruence to the Boundary
+
+Since the prime row kills the inner Beam modulo `p`, `GN` is congruent to the
+right boundary:
+
+```lean
+theorem prime_GN_modEq_rightBoundary
+    {p x u : Nat} (hp : p.Prime) :
+    GN p x u ≡ x ^ (p - 1) [MOD p]
+```
+
+There is also a divisibility form:
+
+```lean
+theorem prime_GN_sub_rightBoundary_dvd
+    {p x u : Nat} (hp : p.Prime) :
+    p ∣ GN p x u - x ^ (p - 1)
+```
+
+And a quotient-witness form:
+
+```lean
+theorem prime_exists_GN_eq_mul_add_rightBoundary
+    {p x u : Nat} (hp : p.Prime) :
+    ∃ B, GN p x u = p * B + x ^ (p - 1)
+```
+
+This witness form is often easier to use when later arguments want an explicit
+Beam quotient.
+
+## 4. Fermat's Little Theorem Reads The Boundary
+
+If `p` is prime and `p` does not divide `x`, Fermat's little theorem says:
+
+```text
+x^(p-1) == 1 [MOD p]
+```
+
+In Lean this is supplied by Mathlib:
+
+```lean
+Nat.ModEq.pow_card_sub_one_eq_one
+```
+
+The DkMath bridge theorem is:
+
+```lean
+theorem prime_GN_modEq_one_of_not_dvd_x
+    {p x u : Nat} (hp : p.Prime) (hx : ¬ p ∣ x) :
+    GN p x u ≡ 1 [MOD p]
+```
+
+This theorem is the first clean endpoint where the Beam observation and
+Fermat's little theorem meet.
+
+## 5. Non-Divisibility Of GN
+
+The congruence `GN p x u ≡ 1 [MOD p]` immediately forbids divisibility by `p`:
+
+```lean
+theorem prime_not_dvd_GN_of_not_dvd_x
+    {p x u : Nat} (hp : p.Prime) (hx : ¬ p ∣ x) :
+    ¬ p ∣ GN p x u
+```
+
+Conceptually:
+
+```text
+if p does not divide x,
+then p does not divide GN p x u.
+```
+
+This is exactly the kind of statement needed for later gcd control:
+
+```text
+boundary x
+  and
+GN p x u
+```
+
+do not automatically share the row prime `p`.
+
+## 6. Why This Matters For Primitive / Zsigmondy Work
+
+The primitive-prime layer often reads divisibility through:
+
+```text
+a^d - b^d = (a - b) * GN d (a - b) b
+```
+
+For prime row `p`, set:
+
+```text
+x = a - b
+u = b
+```
+
+Then the new bridge gives:
+
+```text
+if p does not divide a - b,
+then p does not divide GN p (a - b) b.
+```
+
+This separates two sources of divisibility:
+
+```text
+row prime p
+primitive prime q
+```
+
+The row prime `p` is detected by Pascal-row Beam divisibility, but Fermat's
+little theorem shows that it does not necessarily enter the full `GN` factor
+when the boundary axis is a `p`-unit.
+
+This is a useful guardrail for Zsigmondy-style arguments: primitive factors
+should be tracked separately from the row-prime Beam cancellation.
+
+## Implemented Files
+
+Core implementation:
+
+```text
+DkMath.NumberTheory.WeightedBinomial
+DkMath.NumberTheory.WeightedGNBridge
+```
+
+Public import:
+
+```text
+DkMath
+```
+
+Verified commands:
+
+```text
+lake build DkMath.NumberTheory.WeightedGNBridge
+lake build DkMath
+git diff --check
+```
diff --git a/lean/dk_math/docs/dev/das-p2l-260607/History.md b/lean/dk_math/docs/dev/das-p2l-260607/History.md
index 02d7e3a9..5ae59dad 100644
--- a/lean/dk_math/docs/dev/das-p2l-260607/History.md
+++ b/lean/dk_math/docs/dev/das-p2l-260607/History.md
@@ -1124,3 +1124,58 @@ git diff --check
 ```

 いずれも成功。今回追加分に `sorry` はありません。
+
+---
+
+フェルマーの小定理へと繋がる。
+
+prime_GN_modEq_one_of_not_dvd_x
+{p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
+  GN p x u ≡ 1 [MOD p]
+
+prime_not_dvd_GN_of_not_dvd_x
+
+prime_exists_GN_eq_mul_add_rightBoundary
+→ Fermat 小定理で right boundary を読む
+→ p ∤ x なら p ∤ GN
+→ primitive / Zsigmondy 側の gcd 制御へ接続
+
+### 2026/06/09 19:26
+
+入りました。[WeightedGNBridge.lean](/lean/dk_math/DkMath/NumberTheory/WeightedGNBridge.lean) に追加しています。
+
+```lean
+theorem prime_GN_modEq_one_of_not_dvd_x
+    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
+    GN p x u ≡ 1 [MOD p]
+
+theorem prime_not_dvd_GN_of_not_dvd_x
+    {p x u : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) :
+    ¬ p ∣ GN p x u
+```
+
+流れはその通りです。
+
+```txt
+prime_GN_modEq_rightBoundary
+  GN p x u ≡ x^(p-1) [MOD p]
+
+Fermat 小定理
+  p ∤ x → x^(p-1) ≡ 1 [MOD p]
+
+合成
+  GN p x u ≡ 1 [MOD p]
+
+よって
+  p ∤ GN p x u
+```
+
+確認済みです。
+
+```txt
+lake build DkMath.NumberTheory.WeightedGNBridge
+lake build DkMath
+git diff --check
+```
+
+今回追加分に `sorry` はありません。
````
`````

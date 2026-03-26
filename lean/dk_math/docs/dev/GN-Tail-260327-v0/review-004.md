# Review: GN 理論の valuation から obstruction への進展

かなり良い。
これはもう **GN 理論の枝** ではなく、 **CosmicFormula 層の中で squarefree obstruction が一本閉じた** 状況じゃ。`body_not_perfect_pow_of_squarefree_GN` が立ったことで、

$$
\text{squarefree } GN
;\Longrightarrow;
\text{Body 差分は } d\text{ 乗完全冪でない}
$$

が、構想段階ではなく **実名の theorem** になった。しかも履歴どおり、`CosmicFormula` 層から上に逃げず、その場で閉じておるのがとても良い。

## 1. 何が達成されたか

今回立った定理は

$$
\texttt{body\_not\_perfect\_pow\_of\_squarefree\_GN}
$$

で、仮定は

$$
1<d,\quad 1<GN(d,x,u),\quad \gcd(x,GN(d,x,u))=1,\quad \mathrm{Squarefree}(GN(d,x,u))
$$

結論は

$$
\neg \exists t>0,\ (x+u)^d-u^d=t^d
$$

じゃ。
つまり **GN kernel が平方自由で、境界因子 (x) と互いに素なら、Body 差分は完全冪になれぬ** と言っておる。これはかなり本丸に近い。

## 2. 証明方針が美しい

証明の流れが良いのぅ。

まず (N:=GN(d,x,u)) と置いて、平方自由かつ (N>1) だから素因子 (q) を 1 本取る。
互いに素仮定で

$$
q \mid N,\qquad q \nmid x
$$

を確保する。
そこから private helper

$$
\texttt{padicValNat\_eq\_one\_of\_prime\_dvd\_of\_squarefree}
$$

で

$$
v_q(N)=1
$$

を出す。さらに

$$
(x+u)^d-u^d = x\cdot GN(d,x,u)=xN
$$

なので

$$
v_q((x+u)^d-u^d)=v_q(x)+v_q(N)=0+1=1
$$

となる。
最後に、もしこれが (t^d) なら

$$
d \mid v_q(t^d)
$$

であるべきだが、実際は (1)。ゆえに (d\mid 1) となって矛盾。
実に素直で、無理がない。

## 3. 重要なのは exact valuation とは別ルートで閉じたこと

履歴にもある通り、今回は

$$
p \mid x
$$

を仮定する head-unit exactness をそのまま使ったのではなく、逆に

$$
q \mid GN,\qquad q \nmid x
$$

の側から obstruction を作っておる。
この切り分けがとても良い。つまりいま GN 理論には少なくとも 2 本の valuation 路線がある。

### A. boundary-prime route

$$
p \mid x,\quad p \nmid \text{head}
\Rightarrow
v_p((x+u)^d-u^d)=v_p(x)
$$

### B. kernel-prime route

$$
q \mid GN,\quad q \nmid x,\quad \mathrm{Squarefree}(GN)
\Rightarrow
v_q((x+u)^d-u^d)=1
$$

今回の定理は B の完成版じゃ。
これで GN 理論は、 **boundary 側からも kernel 側からも完全冪を折れる** ようになってきた。

## 4. いまの到達点の意味

これは、わっちの見立てでは次の一文で要約できる。

$$
\boxed{
\text{GN kernel の平方自由性が、
Body の完全冪性を直接妨げる}
}
$$

これが theorem 名つきで `CosmicFormulaBinom.lean` に入った意味は大きい。
なぜなら、今後 `NumberTheory` 側から squarefree を供給するだけで、`CosmicFormula` 側ではもう結果を受け取れるからじゃ。層の責務が綺麗に分離された。

## 5. 今の実装で特に良い点

### 5.1. helper を private にした

`padicValNat_eq_one_of_prime_dvd_of_squarefree` は有用じゃが、今の時点では局所補題として扱うのが自然じゃ。汎用 API 化はあとで必要になったらでよい。いまは責務が明確。

### 5.2. `Body = x * GN` を正面から使った

これは宇宙式の (x) を **境界因子** として扱う、先ほどの見立てと完全に一致する。とてもよい。

### 5.3. `CosmicFormula` 層で閉じた

依存方向が汚れておらぬ。ここは将来効く。

## 6. 次に打つとよい手

履歴の「次の課題」も筋が良い。わっちも同意じゃ。

### A. coprime wrapper

いま仮定に

$$
\gcd(x,GN(d,x,u))=1
$$

を直接置いておるが、実運用ではこれを毎回手で渡したくない。
なので

$$
\mathrm{Coprime}(x+u,u)
$$

や、より宇宙式らしい差分条件から `Nat.Coprime x (GN d x u)` を供給する薄い wrapper は欲しい。

候補名はたとえば

* `coprime_GN_of_coprime_add_right`
* `coprime_boundary_GN_of_coprime_body_gap`
* `body_not_perfect_pow_of_squarefree_GN_of_coprime_add`

あたりじゃな。

### B. primitive-prime 版

これは自然な次手じゃ。

* `body_not_perfect_pow_of_primitive_prime_factor`

今回の squarefree 版と naming layer を揃えるのはとても良い。

### C. helper の一般化

もし今後また使うなら

* `padicValNat_eq_one_of_prime_dvd_of_squarefree`
* あるいは公開版 `padicValNat_eq_one_of_dvd_of_squarefree`

として ABC 側や NumberTheory 側にも再利用できる形へ引き上げてもよい。

## 7. 総評

率直に言って、かなり良い節目じゃ。

* `GTail` 一般論
* `GN` exact valuation
* `squarefree GN` obstruction

が、いま三本の柱として並んだ。
そして今回の追加で、

$$
\text{GN} \to \text{squarefree} \to \text{Body 非完全冪}
$$

という読める一本線ができた。これは研究ノート上でも、実装上でも、見通しをかなり良くする。

いまの状況を短く言うなら、

$$
\boxed{
\text{GN 理論は「valuation 理論」から
「非完全冪 obstruction 理論」へ進んだ}
}
$$

じゃよ。
よく育っておる。

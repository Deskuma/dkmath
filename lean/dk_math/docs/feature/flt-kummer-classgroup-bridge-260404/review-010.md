# FLT-Kummer-ClassGroup-Bridge-260404 Review-010

## 1. 状況分析

いまの状況は、かなり良いところまで澄んでおる。
直近の差分で、最上流の open kernel は

$$
\texttt{cyclotomicGenericFactorizationIdentity\_overCommSemiring}
$$

にまで押し戻された。つまり Stage 1a の上流はもう

$$
\text{generic algebraic factorization identity}\\
\to
\text{equation-only identity}\\
\to
\text{prime specialization}\\
\to
\text{abstract identity}\\
\to
\text{counterexample specialization}\\
\to
\text{pure factorization identity}\\
\to
\text{gap-divisible specialization}\\
\to
\text{ideal equation}\\
\to
\text{ideal product}\\
\to
\text{class witness}
$$

の 10 層で見えておる、ということじゃ。ここまで薄くなれば、どこが本当に未解決かはほぼ露出しきったと言ってよい。

さらに重要なのは、`Polynomial.cyclotomic_prime_mul_X_sub_one` を receiver として直結しようとした試行が、数学内容ではなく **target 粒度と universe の噛み合わせ** で崩れた、と判明したことじゃ。これは失敗というより、良い診断結果じゃよ。つまり、いま止まっておる本当の原因は「定理が足りない」より **インターフェイス設計が粗い** ところにある。

## 2. 重要な方向転換

そして、ぬしの今回の注意点――
**「DkMath は将来的に Mathlib と切り離す。無理に依存する必要はない」**
これは極めて重要じゃ。わっちの見立てでは、ここで方針を少し切り替えるべきじゃ。

いままでは「Mathlib にある receiver をどう受けるか」が前景に出ておった。
だが今後の本筋は逆じゃ。

$$
\text{DkMath 側で最小の代数的核を自前で定義し}
$$
$$
\text{Mathlib 側は必要なら後から adapter を付ける}
$$

この向きに切り替えるのがよい。
今回の universe 崩れは、まさにその必要性を示しておる。Mathlib theorem を core に据えるのではなく、 **DkMath-native な局所 target** を core に据えるべきじゃ。

## 3. 解説

いま最上流 kernel とされている `cyclotomicGenericFactorizationIdentity_overCommSemiring` は、抽象としては美しいが、少し広すぎる可能性が高い。
`CommSemiring` 一般まで上げると、受けたい concrete theorem はたいていもっと局所的な文脈、たとえば

* 特定の (p) 乗根 (\zeta) がある
* (\zeta) が primitive である
* 幾何級数和が 0 になる
* 対象が多項式環か、あるいはその評価先である

といった条件を持っておる。
この「局所的に自然な仮定」を一度 DkMath 側で structure 化してしまえば、上流 kernel はかなり書きやすくなるはずじゃ。

つまり、いま必要なのは「もっと上へ抽象化」ではなく、

$$
\text{抽象すぎる target}
\quad\to\quad
\text{自前の最小局所コンテキスト}
$$

への **適正化** じゃ。
Mathlib から切り離す方針なら、なおさらこれが筋じゃよ。

## 4. 次の一手の推論

わっちの推論ははっきりしておる。
次の一手は、Mathlib の concrete receiver を無理に直結することではない。
また、これ以上 generic target を上流へ増やすことでもない。

次にやるべきは、

$$
\boxed{
\text{DkMath-native な局所 ring-parameterized target を新設する}
}
$$

ことじゃ。

具体的には、`cyclotomicGenericFactorizationIdentity_overCommSemiring` をいきなり埋めようとするのでなく、その手前に例えば

$$
\texttt{CyclotomicFactorizationContext}
$$

のような構造、あるいは target を置く。
そこには、Mathlib の名前に依らず、DkMath が本当に必要とする最小条件だけを入れる。

たとえば概念としては、

* 可換半環 (R)
* 自然数 (p)
* 元 (\zeta \in R)
* (\zeta^p = 1)
* (\zeta \neq 1) または primitive 性に相当する条件
* 幾何級数和
  [
  \sum_{i=0}^{p-1} \zeta^i = 0
  ]
  に相当する性質
* 必要なら ((X^p-1)) の factorization に対応する局所補題

こうしたものじゃ。

そして core theorem は

$$
\text{この context があれば factorization identity が出る}
$$

という形で DkMath 内に置く。
そのあとで必要なら

$$
\text{Mathlib の } \texttt{Polynomial.cyclotomic\_prime\_mul\_X\_sub\_one}
\Rightarrow
\texttt{CyclotomicFactorizationContext}
$$

という adapter を別ファイルに作ればよい。
core と adapter を分離するのじゃ。

## 5. 提案

わっちなら次を提案する。

### 5.1. 第一手

`CyclotomicGenericFactorizationIdentity_overCommSemiring` を、いったん core theorem として追うのをやめる。
その代わりに、より狭い DkMath-native な局所 target を 1 つ新設する。

仮名で言えば、

$$
\texttt{CyclotomicLocalFactorizationTarget}
$$

あるいは context 構造でもよい。
ここでは「何を仮定すれば factorization identity が言えるか」を、DkMath の言葉で固定する。

### 5.2. 第二手

その local target から、現在の

$$
\texttt{cyclotomicEquationFactorizationIdentity\_of\_genericIdentity}
$$

や、その下流の specialization 群へ落とす bridge を作る。
すると current chain は保ったまま、最上流 kernel だけが「自前の最小核」へ置き換わる。

### 5.3. 第三手

そのあとで初めて、Mathlib adapter を optional に作る。
つまり

* `DkMath.FLT.Kummer.CyclotomicCore`
  DkMath-native core
* `DkMath.FLT.Kummer.CyclotomicMathlibAdapter`
  Mathlib から core への橋

という二層に分けるのじゃ。
こうしておけば、将来 Mathlib と切り離しても core は傷まぬ。

## 6. 実際の設計上の利点

このやり方の利点は 3 つある。

第一に、universe や polymorphic receiver の噛み合わせ問題を core から追い出せる。
問題は adapter 側へ閉じ込められる。

第二に、DkMath が将来独立するとき、依存の中心が theorem 名ではなく **数学内容の最小核** になる。
これは非常に強い。

第三に、今後の proof search もやりやすい。
`geom_sum₂_mul` や `zeta_spec` や cyclotomic polynomial 補題を、直接 global theorem に押し込むのでなく、まず local context の補題群として整理できるからじゃ。

## 7. 最終提案

結論を一言でまとめるぞい。

$$
\boxed{
\begin{array}{l}
\text{次の一手は、Mathlib receiver 直結ではなく、}\\
\text{DkMath-native な局所 factorization context / target を新設すること}
\end{array}
}
$$

そして順番はこうじゃ。

1. 最上流 kernel を `CommSemiring` 全体から **自前の局所 context** へ落とす
2. その context から current specialization chain へ bridge を作る
3. Mathlib は core ではなく **adapter 側** に追い出す

ぬしの「将来切り離す」という方針を本気で活かすなら、ここでその向きへ舵を切るのが最善じゃ。
いまの詰まりは数学そのものより、core と receiver の境界の取り方にある。ならば、境界を DkMath 側の都合で作り直すべきじゃよ。

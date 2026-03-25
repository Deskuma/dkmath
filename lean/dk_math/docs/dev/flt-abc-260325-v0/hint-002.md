# Hint 002: normal form refuter の数学核を見立てる

## 3. いま残っている数学核

もう残りははっきりしておる。
`PrimeGe5BranchANormalFormRefuterTarget` の仕事は、

\[
z-y = p^{p-1} t^p,\qquad
GN, p,(z-y), y = p s^p,\qquad
x = p(ts)
\]

を、pack の局所条件へ衝突させて `False` を返すことだけじゃ。

ここでわっちの見立てでは、第一候補はやはり **gcd exactness** じゃな。
狙うべき核はたとえば

\[
\gcd\bigl(p^{p-1}t^p,\ p s^p\bigr) =
p \cdot \gcd(t,s)^p
\]

あるいは少なくとも

\[
\gcd\bigl(z-y,\ GN, p,(z-y),y\bigr) =
p \cdot \gcd(t,s)^p
\]

型じゃ。
これが出れば、既存の「(\gcd(gap,GN)) は (p) しか持てぬ」型の制御と衝突させて

\[
\gcd(t,s)=1
\]

を強制できる可能性が高い。そこから (x=p(ts)) と coprime 条件を噛ませるのが最短じゃろう。
履歴にも次課題として gcd exactness と valuation dictionary の二本柱が明記されており、見立ては一致しておる。

## 4. 次に切ると良い補題

わっちなら、次はこの順で切る。

### 4.1. gcd exactness の下半身

まず equality 全体を狙わず、割り切りから始めるのがよい。

\[
\gcd(t,s)^p \mid \gcd(z-y,\ GN, p,(z-y),y)
\]

と

\[
\gcd(z-y,\ GN, p,(z-y),y) \mid p \cdot \gcd(t,s)^p
\]

の 2 本じゃ。
normal form を代入してから `Nat.gcd_mul_left`, `Nat.gcd_mul_right` 系へ流すと、Lean 的にも崩れにくい。

### 4.2. ( \gcd(t,s)=1 ) の抽出

上の補題と既存の gap/GN の共有因子制御を合成して

\[
\gcd(t,s)=1
\]

を独立補題にする。
これが入ると normal form refuter の難度が一段下がる。

### 4.3. valuation dictionary

必要なら並行して

\[
\nu_q(x)=\nu_q(t)+\nu_q(s)\quad (q\neq p),\qquad
\nu_p(x)=1+\nu_p(t)+\nu_p(s)
\]

を作る。
これは最終矛盾そのものではなく、kernel の「観測辞書」じゃ。gcd だけで落ちなければ、ここから pack の互いに素条件へ噛ませられる。

## 5. 今回の差分への短い総評

結論として、これは **かなり勝っている差分** じゃ。
`via_FLT` の依存を「広い霧」から「一点の refuter」へ圧縮した。
しかもその一点は、もう abstract な配線問題ではなく、

\[
(p^{p-1}t^p,\ p s^p,\ pts)
\]

という concrete normal form をどう潰すか、という純局所問題になった。
ここまで来れば、後は数学核を削るだけじゃ。実装設計としてはとても健全じゃよ。

次は、その `normal-form refuter` 用に **gcd exactness 補題の skeleton** を 2〜3 本、Lean 署名の形で切るのがちょうど良い段階じゃ。

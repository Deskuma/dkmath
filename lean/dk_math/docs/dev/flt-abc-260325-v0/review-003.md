# Review 003: normal form refuter の clean 化

うむ、**かなり良い形** になったのぅ。
これはもう

\[
\text{normal form 全体} \to \text{局所算術 kernel} \to \mathrm{False}
\]

という責務分解が、設計図ではなく **Lean の形そのもの** になっておる。`gcd(gap,GN)=p`、`t \perp s`、`t \perp y`、`s \perp y`、`p \nmid s` を先に no-sorry で抽出し、`primeGe5BranchANormalFormRefuter_default` を単なる配線に落としたのは大きい前進じゃ。未完核が `PrimeGe5BranchANormalFormArithmeticKernelTarget` 1 本へ局所化された、という認識でよい。

特に効いているのは次の 3 点じゃ。

## 1. `gcd(gap, GN) = p` まで exact に戻したこと

前は

\[
\gcd(gap,GN)\mid p
\]

で止まっておった。
今回は `p ∣ gap` と `p ∣ GN` を合わせて

\[
\gcd(gap,GN)=p
\]

まで戻しておる。これで「共有因子は **ちょうど** (p) だけ」という剛い拘束になった。ここは arithmetic kernel の中心柱じゃ。

## 2. `x = p(ts)` から右側 coprime を分配したこと

`hxy` と `x = p*(t*s)` から

\[
(t s) \perp y,\qquad t \perp y,\qquad s \perp y
\]

を引き出したのは筋が良い。
これで kernel は「normal form そのもの」ではなく、**互いに素の情報だけを入力とする純算術問題** に近づいた。

## 3. `p \nmid s` を独立抽出したこと

`GN = p s^p` と `p^2 \nmid GN` から

\[
p \nmid s
\]

を出したので、今後は `Nat.Coprime p s` を 1 行 helper で昇格できる。
これは valuation 的な気配を残しつつも、kernel 側では gcd 言語で戦える、ちょうど良い位置取りじゃ。

わっちの見立てでは、次に切るべきものはもうかなり明確じゃ。

## 2. 次の最短 helper

まず 2 本、ほぼ自動的に生える。

```lean
theorem primeGe5BranchANormalForm_coprime_p_s_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_not_dvd_s : ¬ p ∣ s) :
    Nat.Coprime p s := by
  exact Nat.prime.coprime_iff_not_dvd.mpr hpack.hp hp_not_dvd_s
```

```lean
theorem primeGe5BranchANormalForm_prime_not_dvd_y_default
    {p x y z t s : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hsx : x = p * (t * s)) :
    ¬ p ∣ y := by
  have hcop_y_pts : Nat.Coprime y (p * (t * s)) := by
    simpa [Nat.coprime_comm, hsx] using hpack.hxy
  have hparts : Nat.Coprime y p ∧ Nat.Coprime y (t * s) :=
    (Nat.coprime_mul_iff_right).1 hcop_y_pts
  have hcop_py : Nat.Coprime p y := by
    simpa [Nat.coprime_comm] using hparts.1
  exact Nat.prime.not_dvd_of_coprime hpack.hp hcop_py
```

この 2 本が入ると kernel の入力は実質

\[
\gcd(gap,GN)=p,\quad
t\perp s,\quad t\perp y,\quad s\perp y,\quad p\perp s,\quad p\nmid y
\]

まで整理される。

## 3. arithmetic kernel の first candidate

そのうえで第一候補は、やはり **局所 gcd 衝突** じゃな。

狙いはこういう形じゃ。

\[
gcd(gap,GN)=p
\]

と

\[
gap = p^{p-1} t^p,\qquad GN = p s^p,\qquad t\perp s
\]

から、逆に

\[
\gcd(p^{p-1} t^p,\ p s^p)=p
\]

が完全一致することを再確認する。
ここまでは既に実質できておる。問題はその先で、これを `y` との互いに素条件へどう噛ませるかじゃ。

わっちなら次の順で詰める。

1. `p ∤ y`
2. `Nat.Coprime p s`
3. 必要なら `Nat.Coprime (p * s) y`
4. そこから `GN = p*s^p` が `y` とどう振る舞うかを補題化

このあたりで `GN p (z-y) y` 側の既存補題に、「(GN) は (y) と完全に独立ではない」型の情報があれば衝突が起きる。
もしそこがまだ弱ければ、そこで初めて valuation dictionary を足すのがよい。

## 4. いまの段階の総評

率直に言うと、これは **かなり勝っている整理** じゃ。
前までは「normal form refuter が未完」という見え方だった。
今は違う。

\[
\text{未完なのは refuter ではなく arithmetic kernel}
\]

と、対象がはっきりした。しかもその kernel はもはや normal form 全体を受け取らず、抽出済み算術事実だけを受け取る。これは clean 化として理想的じゃ。

次はもう、`PrimeGe5BranchANormalFormArithmeticKernel_default` の中に直接突っ込むより、まず

* `Nat.Coprime p s`
* `¬ p ∣ y`

の 2 本を helper 化してから局所衝突を詰めるのが最短じゃ。

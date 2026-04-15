# Review 004: normal form refuter の線形因子 exactness 化

うむ、これは **かなり良い前進** じゃ。
いまや未完核は本当に

\[
\texttt{PrimeGe5BranchANormalFormGNLinearFactorKernelTarget}
\]

1 本へ落ちておる。しかも、それ以外の `GNFactorKernel` / `GNRightKernel` / `LocalCoprimeKernel` / `ArithmeticKernel` が全部 thin bridge 化した、というのが決定的じゃ。これは「穴が減った」ではなく、**証明責務の局所化が完了した** という意味を持つ。

今回の差分の強さは、factor-level 辞書をさらに **linear-factor 辞書** まで降ろしたことじゃな。
追加した

\[
\mathrm{Coprime}(p,\ s^p),\qquad \mathrm{Coprime}(p \cdot s,\ y)
\]

は、どちらも見た目は小粒じゃが、最後の kernel では非常に効く。
前者は (p) と冪因子の独立、後者は線形因子 (p * s) と右変数 (y) の独立を直接使える形にした。これにより、最後の `sorry` は「GN 全体」ではなく **線形因子 (p*s)** と **冪因子 (s^p)** をどう読むか、というはっきりした局所問題になった。

わっちの見立てでは、次の first candidate はお主の書いておる通り、

\[
\mathrm{Coprime}(p \cdot s,\ y)
\quad\text{と}\quad
x = p \cdot ( t \cdot s )
\]

を軸にした **線形因子 exactness** じゃ。
この方向は筋が良い。なぜなら、もう `GN = p*s^p` のような大きい塊で読むより、

\[
x = t \cdot (p \cdot s)
\]

と見て、`hxy : \mathrm{Coprime}(x,y)` を線形因子へ分配した方が、Lean 的にも factorization 的にも扱いやすいからじゃ。

ここで次に切るとよい helper は、わっちならこの 2 本じゃ。

```lean
theorem primeGe5BranchANormalForm_coprime_t_ps_default
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (_hsx : x = p * (t * s))
    (hcop_ty : Nat.Coprime t y)
    (hcop_psy : Nat.Coprime (p * s) y) :
    Nat.Coprime (t * (p * s)) y := by
  exact Nat.Coprime.mul_left hcop_ty hcop_psy
```

```lean
theorem primeGe5BranchANormalForm_x_eq_t_mul_ps
    {p x y z t s : ℕ}
    (_hpack : PrimeGe5CounterexamplePack p x y z)
    (_hp_dvd_gap : p ∣ (z - y))
    (_hgap : z - y = p ^ (p - 1) * t ^ p)
    (_hsGN : GN p (z - y) y = p * s ^ p)
    (hsx : x = p * (t * s)) :
    x = t * (p * s) := by
  calc
    x = p * (t * s) := hsx
    _ = t * (p * s) := by ring
```

これで

\[
x = t \cdot (p \cdot s),\qquad t \perp y,\qquad (p \cdot s)\perp y
\]

が揃う。
つまり `x` を **線形因子 2 個の積** として完全に見られるようになる。ここまでくると、最後の kernel は「(x) 側の線形分解」と「(GN) 側の冪分解」をどう突き合わせるか、にかなり絞られる。

ただし、注意点もある。
いまの仮定群だけだと

\[
\mathrm{Coprime}(p \cdot s,\ y)
\]

と

\[
x = t \cdot (p \cdot s)
\]

自体は整合的で、**それだけではまだ矛盾にならぬ**。
だから、この線形因子辞書を使う目的は「すぐ False を出す」ことではなく、最終的に

* `Nat.Coprime t (p * s)`
* `Nat.Coprime (p * s) (s ^ p)`

のような **因子間の独立辞書** を揃え、そこから exactness を読むことじゃろう。お主が履歴に書いた次課題は、まさにそこを射抜いておる。

総評すると、戦況はこうじゃ。

* 未完核は **本当に 1 点**
* しかもその 1 点は、もはや「GN 全体」ではなく **linear-factor kernel**
* 上位層は全部配線になった
* 次の一手も、`Nat.Coprime (p * s) y` と `x = p * (t * s)` を合わせる方向で明確

つまり、いまは **終盤の読み合い** じゃな。
大軍同士の戦ではなく、最後の鍵穴に合う歯を一本ずつ削っておる段じゃ。これは実に美しい終盤じゃよ。

次は、その `GNLinearFactorKernel_default` に入る **線形因子 exactness 用の lemma skeleton** を 2〜3 本、Lean の署名で切るのがちょうどよさそうじゃ。

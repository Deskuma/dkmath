# review: missing kernel の proof skeleton を入れた

うむ、これはかなり良い進展じゃ。
今回の差分で、状況はもう一段はっきりした。**named kernel の本文構図が Lean 上で固定された** のが本質じゃ。

## 1. 今回なにが進んだか

追加されたのは

$$
\texttt{exceptional_right_boundary_core_prime_of_wieferich_of_split}
$$

じゃな。
これは単に theorem が 1 本増えた、という話ではない。

この定理でやっていることは明快で、

1. `primeGe5BranchAExceptionalBoundaryData_default` で pack 由来の入力を一括抽出する
2. その抽出結果を `CFBRCBoundaryCorePrimeExistenceOnSplitTarget` の right branch にそのまま流す

という **proof skeleton の canonical 形** を固定したのじゃ。
つまり、named kernel

$$
\texttt{ExceptionalRightBoundaryCorePrimeOfWieferichTarget}
$$

の本文は、少なくとも骨格レベルでは

$$
\text{pack bundle 抽出} \to \text{split reference の right branch}
$$

で書けばよい、と Lean の形で確定したわけじゃ。

## 2. これがなぜ重要か

前までは「どの target を直接埋めるか」「どういう順で仮定を並べるか」がまだ設計寄りの問題として残っておった。
じゃが今は違う。

今回の skeleton によって、named kernel の本文は実質

```lean
intro ...
rcases boundaryData_default ... with ...
exact hSplit ... (Or.inr ⟨..., ...⟩)
```

という流れで進むのが定まった。
これはつまり、**証明の外形は完成した** ということじゃ。

外形が完成した以上、残る問題はただ一つ、

$$
\texttt{hSplit : CFBRCBoundaryCorePrimeExistenceOnSplitTarget}
$$

を **どう concrete に供給するか** だけに縮んだ。
履歴でも、その点へさらに集約されたとはっきり書かれておる。

## 3. いまの状況分析

いまの証明地形を整理すると、こうじゃ。

### 3.1. すでに固まったもの

* proof file の canonical 置き場
* mainline target
* pack-local target
* named kernel
* named kernel と mainline / pack-local の橋
* named kernel の skeleton
* `boundaryData_default` を入口にする入力整理法

ここまでは、ほぼ揺れが止まった。
つまり **証明を書くための器** はもう出来ておる。

### 3.2. まだ未実装の核

残る核は一つじゃ。

$$
\texttt{CFBRCBoundaryCorePrimeExistenceOnSplitTarget}
$$

の right branch を、**Branch A exceptional 専用の concrete theorem でどう供給するか**。

言い換えると、いま不足しているのは theorem の形ではなく、
**`hSplit` の供給源** じゃ。

### 3.3. ordinary reference theorem との差分

今回の骨格によって、ordinary reference theorem との差分もかなり見えやすくなった。

ordinary 側は

$$
\neg p \mid (z-y)
$$

で進む。
exceptional 側は

$$
p \mid (z-y),\qquad y^{p-1}\equiv 1 \pmod{p^2}
$$

を持って right branch に入る。

だが skeleton 自体は、pack から bundle を引いて `hSplit` に流す、という意味でかなり平行になった。
だから本当の差分は、もう

$$
\text{right branch の split existence を exceptional 用にどう供給するか}
$$

そこだけじゃ。

## 4. いま何が言えるか

一言で言えば、

$$
\text{missing kernel の本文構図は完成}
$$

$$
\text{残課題は } hSplit \text{ の concrete 供給のみ}
$$

じゃ。

これはとてもよい状態じゃよ。
研究実装では、本文の形が定まらぬ時期が長いことが多い。
だが今は、本文の形はもう Lean コードとして出ておる。
だから以後は、その中身を支える局所補題に集中できる。

## 5. 次にやること

次の一手はかなり明確じゃ。

### 5.1. `hSplit` の right branch 専用供給補題を切る

たとえば方針としては、こういう theorem を 1 本置くのが自然じゃ。

```lean
theorem exceptional_split_right_branch_supply
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right p (z - y) y ∧
      ¬ q ∣ (z - y)
```

実質は named kernel と同じ見た目じゃが、意識としては
**`hSplit` を局所的に供給する right branch 専用補題** として切るのがよい。

### 5.2. `boundaryData_default` を入口に固定し続ける

これは正しい。
毎回 `hpack.hp`, `hpack.hp5`, `hpack.gap_pos` と散らさず、一度 bundle で受けると、どこが未供給かが Lean 上で見えやすい。
今回の skeleton は、その意味でも筋がよい。

### 5.3. `hSplit` を global に作ろうとしすぎない

ここは留意点じゃ。
前にも global 側へ上げようとして型不整合が出た流れがあった。
だから今は、proof file の責務どおり **pack-local / right branch 専用** にさらに薄く切る方が安全じゃ。

## 6. 賢狼の総括

今回の差分を総括すると、

**証明の「型」はもう迷っておらぬ。
迷っているのは、そこへ入れる concrete な存在定理の供給だけじゃ。**

これはかなり健全な後半戦の姿じゃよ。
設計が固まり、橋も揃い、本文 skeleton も出来た。
残るのは、right branch exceptional 用の局所核をどう切るか、その一点じゃ。

必要なら次で、その **`hSplit` 供給用の次補題候補** を、ordinary theorem との差分が見える形で整理して書くぞい。

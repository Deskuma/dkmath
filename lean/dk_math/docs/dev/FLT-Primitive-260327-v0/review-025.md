# TriominoCosmicBranchAExceptional.lean の主目標を pack-local 形に固定したことの価値と今後の展望

うむ、今回はかなり本質的な前進じゃ。
結論から言うと、**証明すべき主目標が finally 固定された**。これが一番大きい。

## 1. 何が起きたか

今回の差分で新しく入った中心は、

$$
\texttt{PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget}
$$

じゃ。
これは proof file で concrete に埋めるべき目標を、抽象的な `cyclotomicPrimeCore` 側ではなく、

$$
\texttt{boundaryCyclotomicPrimeCore .right p (z-y) y}
$$

を直接結論に持つ **pack-local right branch 形** として固定したものじゃ。

しかも今回はそれだけではなく、

$$
\texttt{PrimeGe5BranchAExceptionalExistenceMainlineTarget}
$$

との間に

* `primeGe5BranchAExceptionalExistenceMainline_of_packLocalBoundary`
* `primeGe5BranchAExceptionalExistenceMainline_iff_packLocalBoundary`

を置いて、**両者が同値** だと proof file 内で明示した。

つまりいまや、このファイルで考えるべきことは実質

$$
\text{mainline target を証明すること}
$$

ではなく、

$$
\text{pack-local right branch existence を証明すること}
$$

と読み替えてよい、という状態になったわけじゃ。

## 2. 今回の進展の本質

今回の本質は、ただ theorem が 2 本増えたことではない。
**探索空間が一段縮んだ** ことじゃ。

以前は

* local mainline
* split target
* pack-local existence
* global exceptional existence

が少しずつずれていて、どこを直接埋めるのが一番自然かを探っておった。
だが今回、その迷いがほぼ消えた。

proof file で今後直接埋めるべき statement は

$$
\texttt{PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget}
$$

だと固定されたからじゃ。

これは証明実装では極めて大きい。
なぜなら「どの theorem 名を最終目標に置くか」で毎回視点がぶれなくなったからの。

## 3. どうして pack-local 化が正しかったか

履歴にある通り、一度

$$
\texttt{CFBRCExceptionalBoundaryCorePrimeExistenceOnWieferichTarget}
$$

のような global target へ直接上げようとして、`PrimeGe5CounterexamplePack` を要求しない型との不整合で build error が出た。
これを pack-local statement に戻したことで、その不整合が解消した。

ここが重要じゃ。

つまり今の proof file の責務は、**一般理論を公開 API 形で証明すること** ではなく、
まず

$$
\text{counterexample pack を固定した上で right branch existence を作る}
$$

ことなのじゃ。
その責務に theorem の型を合わせたので、ようやく証明対象と証明場所の整合が取れたわけじゃな。
これは設計判断としてかなり健全じゃ。

## 4. いまの状況分析

いまの状況を、構造として言い換えるとこうじゃ。

## 4.1. すでに出来ているもの

* proof file の canonical 置き場
* mainline target
* mainline から packet descent へ流す wrapper
* ordinary reference theorem
* split theorem を pack-local right branch へ評価する橋
* mainline target と pack-local target の同値橋

ここまで来ておる。

つまり、**橋と責務分離はかなり完成** しておる。

## 4.2. まだ出来ていないもの

残っている核は、ほぼ一つじゃ。

$$
\texttt{PrimeGe5BranchAExceptionalPackLocalBoundaryExistenceTarget}
$$

を直接返す concrete 補題じゃ。
履歴でも、次の課題として

$$
\texttt{exceptional_right_boundary_core_prime_of_wieferich}
$$

相当を切る、と明言されておる。

これはつまり、

$$
p \mid (z-y),\qquad y^{p-1}\equiv 1 \pmod{p^2}
$$

から

$$
\exists q,\ \mathrm{Prime}(q)\land
q \mid \texttt{boundaryCyclotomicPrimeCore .right p (z-y) y}
\land q \nmid (z-y)
$$

を作る局所定理を起こす、ということじゃ。

## 4.3. いま詰まっているのは「橋」ではない

ここが大事じゃ。
もう詰まっているのは設計の橋ではない。
mainline へ戻す橋も、split から落とす橋も、すでにある。

したがって、残課題は純粋に **right branch existence をどう生むか** 、そこだけになった。
これは前進じゃよ。問題が finally 一点に収束したからの。

## 5. 今回の差分の価値を一言で

一言で言えば、

**「何を証明すれば勝ちか」が fixed された**

これじゃ。

前は「mainline を直接埋めるのか」「global target を埋めるのか」「pack-local を一時的に使うのか」がまだ揺れておった。
いまは違う。

$$
\text{まず pack-local boundary existence を埋める}
$$

$$
\text{mainline へは thin bridge で戻す}
$$

この戦略が定理として固定された。

## 6. 次に何をするべきか

次の一手は、もうかなり明確じゃ。

### 6.1. 直接切るべき theorem

次に置くべき本命は、やはりこれじゃ。

```lean
lemma exceptional_right_boundary_core_prime_of_wieferich
    {p x y z : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hWieferich : y ^ (p - 1) ≡ 1 [MOD p ^ 2]) :
    ∃ q : ℕ, Nat.Prime q ∧
      q ∣ DkMath.CFBRC.boundaryCyclotomicPrimeCore .right p (z - y) y ∧
      ¬ q ∣ (z - y)
```

実際には theorem 名は多少変わってもよいが、中身はこれじゃ。
これを証明できれば、今回置いた同値橋で mainline target は直ちに埋まる。

### 6.2. その前にやるとよいこと

`primeGe5BranchAExceptionalBoundaryData_default` を入口で呼んで、

* `hpack.hp`
* `hpack.hp5`
* `hpack.gap_pos`
* `hpack.y_pos`
* `hpack.gap_coprime_right`

を一括で取り出す流れにするのがよい。
これは前の差分で既に整えてあるので、今度は本格的に使う番じゃ。

### 6.3. ordinary skeleton を真似る

履歴にもある通り、ordinary reference theorem の proof skeleton を模した pack-local 補助補題を追加するのが自然じゃ。

つまり、

* ordinary 側で使っている「境界 core に primitive prime がいる」流れ
* exceptional 側ではどの箇所だけ Wieferich 情報に差し替えるか

を 1 対 1 で対応させるのじゃ。

## 7. 賢狼の見立て

いまの局面は、かなり良い。
なぜなら、設計上の迷いが減り、**新しい数学補題 1 本に火力を集中できる形** になったからじゃ。

言い換えると、

$$
\text{橋の時代はほぼ終わり、核補題の時代に入った}
$$

ということじゃな。
これは研究実装では、とても健全な段階じゃよ。

必要なら次で、その **pack-local target を直接埋める theorem の Lean 骨格** を、`intro` や `rcases` の流れまで含めて起こすぞい。

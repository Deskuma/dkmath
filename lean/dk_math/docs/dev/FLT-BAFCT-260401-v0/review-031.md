# Review 031: SuperWieferichCongruenceTarget の分割

うむ、**これでよい**。
しかも今回の変更は、単なる整理ではなく、**戦況認識を正した** という意味でかなり良い一手じゃ。`WeakSuperWieferichCongruenceTarget` と `StrongSuperWieferichCongruenceTarget` を分離し、既存の `superWieferichCongruence_concrete` を弱い版へ退避し、`Strong ⇒ Weak` の橋を別定理で置いたのは、まさに今やるべき設計じゃ。

## 1. なぜ「これでよい」のか

前の `SuperWieferichCongruenceTarget` は、実は

$$
q \nmid y \Rightarrow y \text{ が } ZMod(q^p)\text{ で可逆}
$$

だけで

$$
z = R y
$$

と書けてしまう、**弱すぎる型** じゃった。
つまり「Hensel lift を取れた」ことを表すつもりの target が、実際には「比 (z/y) を書けた」だけでも通ってしまっておった。これは前回の concrete 証明で露出した弱点じゃ。

今回そこを受けて、

* weak 版
  [
  \exists R,\ z = R y \pmod{q^p}
  ]
* strong 版
  [
  R \bmod q = \omega^j,\qquad \sum_{i=0}^{p-1} R^i = 0,\qquad z = R y
  ]

を分けた。
これは **「達成済みの trivial 層」と「まだ殴るべき本命」を型で分離した** ということじゃ。ここが非常に良い。

## 2. いま何が closed で、何が open か

今回の変更で、状況はかなり見やすくなった。

### 2.1. closed なもの

* `QAdicResidue` の入口層
* weak SuperWieferich
* `Strong ⇒ Weak` の論理橋

ここまではもう Lean 上で安定したと言ってよい。

### 2.2. open なもの

* strong SuperWieferich の concrete 証明
* そのための Hensel step 専用補題
* さらにその先の `QAdicDescentExistenceTarget`

つまり今回の変更で、**Level 1 の本丸がようやく見える名前を持った** のじゃ。
これは戦況整理として非常に正しい。

## 3. ただし、まだ一歩だけ注意が要る

「Strong 版」は前よりずっと良いが、まだ少しだけ設計上の留意点がある。

今の strong 条件は

$$
(R.val : ZMod q) = \omega^j
\quad\text{と}\quad
\sum_{i=0}^{p-1} R^i = 0 \text{ in } ZMod(q^p)
$$

になっておる。
これは方向として正しい。
ただ、将来 Hensel step を本当に回すなら、場合によっては

* `R mod q = ω^j`
* `Φ_p(R) = 0 mod q^n`
* 次の段で `R' ≡ R mod q^n`

のように、**持ち上げの段数 (n)** を明示した中間 target が欲しくなるかもしれぬ。
いきなり (q^p) 完成形だけを strong target に置くのは悪くないが、実装途中では 1-step 版の補題が別に要る可能性が高いの。
とはいえ、これは「今の設計が悪い」という意味ではない。**次の分割点が見えている** というだけじゃ。

## 4. 今回の変更の本当の価値

わっちが一番高く評価するのはここじゃ。

今回の変更で、

> weak が証明できた
> だから Level 1 が済んだ

という誤読を **型システムの側で禁止した**。

これが大きい。
研究では、この種の「弱い達成を本命と見誤る」ことがよくある。
ぬしは今回、その誤読を構文レベルで潰した。
つまり今後は、誰が見ても

* weak はただの可逆性由来
* strong が Hensel 本丸

と分かる。これはとても健全じゃ。

## 5. 結論

**はい、これでよい。むしろこの分離は必要だった。**
今の戦況は

$$
\text{Level 0} ; \checkmark
$$

$$
\text{Level 1 weak} ; \checkmark
$$

$$
\text{Level 1 strong} ; \text{本命}
$$

$$
\text{Level 2} ; \text{真の open kernel}
$$

という形に、ようやく整った。

次に進むなら、わっちはそのまま **Strong 用の 1-step Hensel 補題** を起こすのを勧める。
そこで初めて Level 1 が本当に動き始めるぞい。

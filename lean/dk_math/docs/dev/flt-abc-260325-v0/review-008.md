# `NeP` route の前進と、support separation の確定

おやおや、これは **かなり決定的な変化** じゃ。
今の状況は、もはや「最後の `sorry` をどう埋めるか」ではなく、

$$
\text{そもそも今の comparison-based refuter は、まだ新情報を持っておるのか？}
$$

を **最終確認している段** じゃな。これはとても健全な進み方じゃよ。

## 1. いま起きた本質

今回の差分で、`NePSpine_default` が実際には何を使っていたかを、さらに正直な target へ切り出した。
つまり active 残核はもう

$$
\texttt{PrimeGe5BranchANormalFormNePSupportKernelTarget}
$$

ただ 1 本で、その中身は

* `Nat.Coprime t s`
* (q \neq p) で `q ∣ t → ¬ q ∣ s`
* (q \neq p) で `q ∣ s → ¬ q ∣ t`

だけじゃ。
これは非常に重要での。
なぜなら、これによって

$$
x^p,\quad (z-y)GN,\quad \text{factorization exactness},\quad \text{comparison spine}
$$

の大半は、**最終核では実は使っていない** とコード上で明示されたからじゃ。

## 2. いまの見立て

率直に言うと、賢狼の第一印象はこうじゃ。

$$
\text{この support separation は、かなり高い確率で } Nat.Coprime, t, s \text{ の焼き直し}
$$

じゃ。

というのも、自然数については

$$
\mathrm{Coprime}(t,s)
$$

であれば、任意の素数 (q) について

$$
q \mid t \Rightarrow q \nmid s,
\qquad
q \mid s \Rightarrow q \nmid t
$$

はほぼ自動で出る。
しかも今回の separation は (q \neq p) に限定されておるから、`Coprime t s` より **弱い条件** に見える。
ならば、support separation 単独から `False` が出る見込みはかなり薄い。

## 3. つまり何が分かったか

ここが一番大事じゃ。

今回の差分は、「最後の核が縮んだ」のではなく、

$$
\text{NeP comparison route が本当に新情報を持っているかどうか}
$$

を判定する **final checkpoint** を作った、という意味を持つ。
履歴の書き方もまさにそうなっておる。
これは後退ではなく、設計として非常に賢い。
無理に `sorry` を埋めようとして、既に持っている情報の焼き直しを何段も積み重ねるのが一番危ないからの。

## 4. 戦況を一言で

いまの戦況は、

$$
\text{最後の敵が、実は幻影かもしれないと判明した}
$$

という局面じゃ。
つまり残っている `sorry` は「倒すべきラスボス」ではなく、

$$
\text{この route はここで終わりか？}
$$

を判定する検査門になっておる。
これはかなり本質に近いところまで来た証拠じゃよ。

## 5. 次の判断

次にやるべきことは、履歴どおりほぼ 1 つじゃ。

### A. `NePSupportKernelTarget` が `Nat.Coprime t s` の焼き直しかを証明する

もし

$$
\mathrm{Coprime}(t,s)
\Rightarrow
\text{NePSupportKernel の separation 条件}
$$

が薄い helper で全部出るなら、
その時点で

$$
\text{NeP comparison route 単独では } False \text{ を出せない}
$$

とかなり強く判断できる。

### B. その場合は設計転換

履歴にもある通り、次は

* descent
* minimality
* 別 arithmetic kernel

のどれへ切り替えるかを決める番じゃな。

## 6. 賢狼の結論

いまの状況は **悪くない。むしろ非常に良い**。
なぜなら、残り 1 個の `sorry` が

$$
\text{証明を閉じる穴}
$$

から

$$
\text{この route を続行すべきか打ち切るべきかを判定する穴}
$$

へ変わったからじゃ。
これは設計の成熟じゃよ。

なので、わっちの見立てはこうじゃ。

$$
\textbf{NeP route は、ほぼ「ここで終わりかどうか」を見極める段階に入った}
$$

そして、おそらく次の一手は
**`Coprime t s` から separation が全部出ることを薄い補題で示して、comparison route の限界を確定する**
ことじゃな。
それが通れば、もう迷いなく次の kernel へ進める。

---

焼き直しならば、その証明をして、閉じれば良い。その道の行き止まりを確定してしまえばいいということだね。
そして、その証明が別で活きる可能性は？例えば何か、新しい視点、視座を得られるとか？

---

うむ、**その通り** じゃ。

$$
\text{「焼き直しなら、焼き直しであることを証明して閉じる」}
$$

これはとても良い判断じゃよ。
証明探索では、

* 倒す
* 使う
* 打ち切る

の 3 つが同じくらい大事じゃ。
特に今みたいに最終核が細くなった局面では、

$$
\text{この route は新情報を出していない}
$$

と **定理として確定** してしまうのは、立派な前進じゃ。

## 1. 何を証明すればよいか

今の文脈なら、狙いはだいたいこうじゃな。

### A. 片方向

$$
\mathrm{Coprime}(t,s)
;\Longrightarrow;
\text{NePSupportKernel の条件}
$$

これはかなり素直じゃ。
自然数の互いに素より、任意の素数 (q) について

$$
q \mid t \Rightarrow q \nmid s,\qquad
q \mid s \Rightarrow q \nmid t
$$

が出るからの。
しかも kernel 側は (q \neq p) に制限しておるので、これはむしろ弱い版じゃ。

### B. できれば逆向きも調べる

$$
\text{NePSupportKernel の条件}
;\Longrightarrow;
\mathrm{Coprime}(t,s)
$$

これは少し注意が要る。
`q ≠ p` しか見ていないなら、(p) が両方に立つ可能性を排除できぬ。
じゃが、前段で既に

$$
p \nmid s
$$

や、場合によっては

$$
p \nmid t
$$

まで持っているなら、逆向きも閉じるかもしれぬ。

つまり理想形は、

$$
\text{NeP support separation}
\quad+\quad
p\text{-side の局所条件}
\iff
\mathrm{Coprime}(t,s)
$$

という **同値定理** じゃな。

これが取れれば、もうはっきり

$$
\text{NeP route は新情報ではなく、既知の } t\perp s \text{ の再包装}
$$

と宣言できる。

---

## 2. それを証明する価値

大いにある。
しかも価値は 2 種類ある。

## 2.1. 実務上の価値

これはまず明白じゃ。

* comparison-based refuter の限界を確定できる
* 無駄な `sorry` 追跡を打ち切れる
* 次の kernel へ安心して移れる

つまり

$$
\text{探索木の枝刈り}
$$

として非常に価値がある。

Lean では特に、
「この方向は既知命題の言い換えに過ぎぬ」
を theorem にしておくと、後から同じ沼に落ちにくい。
これは研究でも実装でも強い。

---

## 2.2. 理論上の価値

ここが面白いところじゃ。

もし

$$
\text{NeP support separation}
\iff
\mathrm{Coprime}(t,s)
$$

あるいはそれに近い定理が出ると、これは単なる「失敗報告」ではない。
むしろ

$$
\text{comparison route の情報量は、support の分離までしかない}
$$

という **情報論的な境界** を与える。

これは新しい視座になる。

---

## 3. 得られる新しい視座

わっちの目には、少なくとも 3 つある。

## 3.1. 「指数比較」と「support 比較」は違う

今回の route が support separation までしか出さないなら、それは

$$
\text{prime support の分離}
$$

は見えるが、

$$
\text{valuation の深さ}
$$

までは見えていない、ということじゃ。

つまり

* support は分かる
* exponent は分からない

という境界が見える。
これはかなり大きい。

Branch A の最後で本当に要るのが valuation 的情報なら、
support-only の route では勝てぬ、と分かるからの。

---

## 3.2. `GN` 比較は「構造」ではなく「影」かもしれぬ

今の comparison route は

$$
x^p = (z-y),GN
$$

を prime support で眺め直しておる。
もしそれが結局 `Coprime t s` の焼き直しなら、
この route が見ているのは本体ではなく

$$
\text{既存構造の影}
$$

に過ぎぬということになる。

これは重要じゃ。
つまり `GN` の使い方として、

* support 比較では浅い
* valuation / descent / minimality と組むと深い

という **道具の適正配置** が見える。

---

## 3.3. “何が新情報か” の判定基準になる

今後、新しい kernel を試すときに、

$$
\text{これは本当に新しい制約か？}
$$

を判定する基準が得られる。

たとえば今後は、

* 互いに素の再包装にすぎないのか
* valuation を 1 段深く読めているのか
* minimality を導入して縮小が起きるのか

を見分けやすくなる。

これは研究の目としてとても大事じゃよ。

---

## 4. 論文・設計書での言い方

これはちゃんとした主張になる。たとえばこんな趣旨じゃ。

> Branch A の (q \neq p) comparison spine から得られる局所分離条件は、既知の (\mathrm{Coprime}(t,s)) 条件の再表現にとどまる。
> したがって、この route 単独では新たな矛盾を生まず、最終 refuter には valuation・descent・minimality のいずれか追加情報が必要である。

これは「失敗」ではなく、

$$
\text{この方法の到達限界を定理として記述した}
$$

という成果じゃ。

---

## 5. 実際の次の一手

わっちなら、次はこうする。

### 1

まず薄い補題として

$$
\mathrm{Coprime}(t,s)
\Rightarrow
\forall q\neq p,\ q\mid t \Rightarrow q\nmid s
$$

とその対称版を証明。

### 2

必要なら `p` 側条件を足して、

$$
\text{support kernel} \iff \mathrm{Coprime}(t,s)
$$

まで持っていく。

### 3

その上で

```lean
theorem primeGe5BranchANormalFormNePSupportKernel_is_repackaged_coprime ...
```

のような名前で、
「この route は既知情報の再包装である」と明示する。

これが通れば、その `sorry` は「埋める」のではなく

$$
\text{この kernel は閉じるが、新情報は出さない}
$$

という形で **綺麗に終われる**。

---

## 6. 結論

そうじゃ。
その道が行き止まりなら、

$$
\text{行き止まりであることを証明して地図に描く}
$$

のが正しい。
しかもその証明は、ただの墓標ではない。

$$
\text{何が新情報で、何が再包装か}
$$

を判定する **新しい視座** をくれる。
これは後の設計、特に

* valuation を足すべきか
* descent を入れるべきか
* minimality が必要か

を見極めるうえで、とても役に立つ。

つまり一言で言えば、

$$
\textbf{その証明は「終わりの印」ではなく、「次へ進むための座標軸」になる}
$$

のじゃ。

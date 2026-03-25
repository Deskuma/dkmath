# Branch A の NeP comparison route の限界を定理化した

うむ、これは **かなり良い収穫物** じゃ。
しかも「未完を 1 個減らした」というだけでなく、**比較 route の情報量そのものを測定した** という意味で価値が高い。

今回の差分の芯は、次の 3 層に分けて見るとよく分かる。

## 1. 何を証明したのか

まず generic に

$$
\neg, p \mid s
$$

のもとで、

$$
\mathrm{Coprime}(t,s)
$$

と

$$
\forall q\text{ prime},\ q\neq p,\ q\mid t \Rightarrow q\nmid s
\quad\text{かつ}\quad
\forall q\text{ prime},\ q\neq p,\ q\mid s \Rightarrow q\nmid t
$$

が同値だと示した。
これが

$$
\texttt{coprime_iff_ne_p_support_separation_of_not_dvd_right}
$$

じゃな。

この定理の意味は単純で、
**(q\neq p) に限った support separation は、本質的には coprime の言い換えである**
ということじゃ。

しかも Branch A specialization として

$$
\texttt{primeGe5BranchANormalForm_neP_support_separation_iff_coprime}
$$

を置いたことで、これは単なる一般補題でなく、**今の Branch A 文脈そのものに刺さる辞書** になった。

---

## 2. なぜこれが重要か

ここが今回いちばん大事なところじゃ。

もともと `NeP` comparison route では、

$$
q\neq p
$$

側の factorization / no-shared / support separation を最後の obstruction 候補として追っておった。
じゃが今回の iff によって、

$$
\text{その separation は新情報ではなく、既知の } \mathrm{Coprime}(t,s) \text{ の再包装}
$$

だとはっきり分かった。

つまり comparison route は、最終的に

$$
x^p = (z-y),GN
$$

を細かく分解して見ても、(q\neq p) 側では **新しい prime support 制約を生んでいない**、ということじゃ。

これは証明探索として非常に大きい。
なぜなら、ここで初めて

$$
\text{「この route はもう掘っても同じ石しか出ない」}
$$

と数学的に言えるからじゃ。

---

## 3. 実装設計として何が起きたか

この知見を、そのまま target 分解に落としたのが上手い。

前は active 残核が

$$
\texttt{PrimeGe5BranchANormalFormNePSupportKernelTarget}
$$

だった。
しかし今回、

$$
\texttt{PrimeGe5BranchANormalFormNePCoprimeKernelTarget}
$$

を導入し、

$$
\texttt{NePSupportKernel_of_coprimeKernel}
$$

で support kernel を **coprime-only checkpoint** に reduce した。

これはとても良い設計じゃ。
なぜなら今の `sorry` は、もはや

$$
\text{NeP comparison の穴}
$$

ではなく、

$$
\text{Coprime}(t,s) \text{ だけではまだ } False \text{ に届かない}
$$

という **設計判断の checkpoint** に変わったからじゃ。

この変化は決定的じゃよ。
以前の `sorry` は「まだ補題が足りぬかもしれぬ穴」だった。
今の `sorry` は「この route を打ち切るかどうかを判断する門」になっておる。

---

## 4. generic 定理の中身の読み方

generic 定理

$$
\texttt{coprime_iff_ne_p_support_separation_of_not_dvd_right}
$$

は、数学的にはこう読める。

### 4.1. 順方向

$$
\mathrm{Coprime}(t,s)
\Rightarrow
q\mid t \Rightarrow q\nmid s
$$

は、互いに素の定義そのものじゃ。
ここは素直じゃな。

### 4.2. 逆方向

逆向きで効いているのが

$$
\neg, p\mid s
$$

じゃ。
support separation は (q\neq p) しか見ておらぬので、普通なら (q=p) の共有を排除できぬ。
そこを

$$
p \nmid s
$$

で塞いで、結局 gcd に素因子が立たぬことを示している。

ここが実に美しい。
つまりこの定理は、

$$
\text{「(p) 以外の support separation」}
+
\text{「右側に (p) が立たない」}
$$

を合体させて、完全な coprime に戻しておる。

これは Branch A で得た局所情報を、かなりきれいに圧縮した形じゃ。

---

## 5. この収穫物から得られる新しい視座

お主が聞いていた「これが別で活きるか？」に対しては、答えは **かなり活きる** じゃ。

## 5.1. 情報量の境界が見えた

今回の結果で、

$$
q\neq p \text{ の support をいくら眺めても、結局 coprime に戻る}
$$

と分かった。
つまり **support-level の比較は浅い**。
真に新しい obstruction を出すには、

* valuation の深さ
* minimality
* descent
* 別の arithmetic kernel

のどれかが要る、という境界が見えた。

これは理論的にかなり大きい。

## 5.2. `GN` の使い方の適正配置が見えた

`GN` comparison は useless だった、という話ではない。
むしろ

$$
\text{GN は support 分離までは出せるが、それ以上の新 obstruction は別 mechanism が要る}
$$

と分かった。
これは道具の性質を理解した、ということじゃ。

つまり `GN` は

* shape を作る
* factorization spine を作る
* no-shared を出す

ところでは強い。
しかし最後の contradiction は、それだけでは出ないかもしれぬ。
この理解は、今後の route 設計で非常に効く。

## 5.3. comparison route の「到達限界」を記述できた

これは論文や設計メモに書けるレベルの知見じゃ。

たとえば趣旨としてはこうじゃ。

> Branch A における (q\neq p) comparison spine から得られる support separation は、既知の (\mathrm{Coprime}(t,s)) 条件と同値であり、新しい obstruction を与えない。したがって、最終 refuter には comparison 以外の追加構造が必要である。

これは負け筋の記録ではない。
**方法の限界定理** に近いものじゃ。

---

## 6. 今後どう使えるか

この成果は、少なくとも 3 方向で再利用できる。

### A. 枝刈り

今後 `q\neq p` の support 比較を見て「何か新しいのでは」と思ったとき、
すぐこの iff に戻って「いや、これは coprime の再包装じゃ」と判定できる。

### B. 設計基準

新しい kernel を試すとき、

$$
\text{これは support の再包装か？ valuation の新情報か？}
$$

を見極める基準になる。

### C. lower layer の独立辞書

generic 定理は Branch A 専用に見えて、実は

$$
\neg, p \mid \text{右側}
$$

のもとでの **support separation ↔ coprime** 辞書として独立に使える。
これは他の normal form や別 route でも流用可能じゃ。

---

## 7. 今の `sorry` の意味

これで今の `sorry` は、かなり明確にこう読める。

$$
\texttt{primeGe5BranchANormalFormNePCoprimeKernel_default}
$$

は、

$$
\text{Coprime}(t,s)
$$

だけを受けて `False` を返す kernel じゃ。
しかし既に分かった通り、comparison route で得られる active 情報は実質そこまでしか残っておらぬ。

だからこの `sorry` は、

* まだ補題が足りない穴

ではなく、

* **comparison route をここで終えるか**
* **coprime に加えて何を最小追加入力にするか**

を決める判断点じゃ。

ここまで来ると、証明の霧はかなり晴れておる。

---

## 8. 総評

今回の収穫物を一言で言えば、

$$
\textbf{「NeP comparison route の限界を、定理として固定した」}
$$

じゃ。

これは大きい。
しかも generic 定理まで上げておるから、単なる一回限りの観測ではなく、**再利用可能な辞書** になっておる。

賢狼の見立てでは、今回の差分は

* 実装上は `sorry` を 1 個残したまま
* 理論上は **一つの route をほぼ完走して限界を確定した**

という、とても価値の高い前進じゃよ。

次に深掘るなら、ちょうど 2 方向じゃな。

## 1

この iff を使って
「NeP route は新 obstruction を生まない」
をもう一段明示的な meta 補題にする。

## 2

そのうえで
「では最小追加入力は何か？」
を設計する。候補はやはり

$$
\text{minimality},\quad \text{descent},\quad \text{valuation-depth}
$$

のどれかじゃ。

ここ、実に面白いところまで来たの。

# consider-049: `PrimeGe5BranchAPrimitiveQAdicGapReductionGlobalTarget` を新設し、`2m-core` をさらに `2m-local` と `2m-global` に分けたことの意味

その通りじゃ。
前の返しは **「本丸が `2m-global` にある」** までは言えたが、 **そこから何をどう裂くか** は、まだ具体化し切れておらなんだ。
ぬしの指摘は正しい。いま必要なのは **名前の更新ではなく、次の 1 手が数式で見えること** じゃ。

なので、ここでは曖昧さを捨てて、 **今ほんとうに見えている具体ルート** だけを書くぞい。

---

## 1. いま本当に残っている未知量は何か

`2m-global` の定義を見れば、残っているのは本質的にこれじゃ。

$$
\text{pack} + \text{strong q-adic witness } R
;\Longrightarrow;
\exists g' \in \mathbb{N},\quad g' , GN(p,g',y)=(x/q)^p
$$

つまり、**未知量は \(g'\)** じゃ。
そして witness 側から見て自然に出てくる候補は、ほぼ 1 つしかない。

$$
z \equiv R,y \pmod{q^p}
$$

なら、reduced 側でも

$$
z' = g'+y
$$

が同じ branch に乗ると期待するのが自然じゃから、

$$
g' + y \equiv R,y \pmod{q^p}
$$

すなわち

$$
\boxed{
g' \equiv (R-1),y \pmod{q^p}
}
$$

これじゃ。
わっちが前回まだ明示できておらなんだ「次の具体物」は、これじゃよ。

---

## 2. だから次に切るべき核は `2m-global` ではなく、その中の **anchored 版** じゃ

いまの `2m-global` はまだ広い。
witness \(R\) を仮定に持ちながら、結論の \(g'\) が **\(R\) とどう関係するか** を何も言っておらぬ。
これでは、strong witness を本当に使う mechanism が見えぬ。

だから次の新 target は、まずこれじゃ。

$$
\boxed{
\text{AnchoredGapReductionTarget: }
\exists g' \in \mathbb{N},\
g' GN(p,g',y)=(x/q)^p
\ \land
(g' : ZMod(q^p)) = (R-1),y
}
$$

あるいは等価に

$$
(g'+y : ZMod(q^p)) = R,y
$$

じゃな。

これが通れば、今の `2m-global` は即座に従う。
しかもこれは **本当に witness を使っている** target じゃ。
今の `2m-global` の弱さは、ここが無いことじゃよ。

---

## 3. さらにその anchored 版を 2 つに裂く

ここまで来ると、次はかなり具体的じゃ。

### 3.1. 局所整合

まず

$$
F_y(g):=g,GN(p,g,y)=(g+y)^p-y^p
$$

と置く。
すると目標は

$$
F_y(g')=(x/q)^p
$$

じゃ。
Anchored congruence を仮定すると、まず必要なのは

$$
\boxed{
F_y(g') \equiv (x/q)^p \pmod{q^p}
}
$$

が local に整合することじゃ。
これは witness (R) から期待される最初の合同条件じゃ。

### 3.2. 整数化

だが合同だけでは足りぬ。
次に必要なのは、その residue class の中に **本当に整数解があるか** じゃ。

つまり

$$
g' \equiv (R-1)y \pmod{q^p}
$$

を満たす整数 \(g'\) が存在して、しかも

$$
F_y(g')=(x/q)^p
$$

を厳密に満たすか。
ここが genuinely global な部分じゃ。

---

## 4. なので、次のロードマップはこう書き換えるべきじゃ

いまの `2m-global` をそのまま殴るのではなく、こうじゃ。

## A. `2m-global-anchored` を新設する

strong witness \(R\) と reduced gap \(g'\) の congruence を target に入れる。

$$
g' \equiv (R-1)y \pmod{q^p}
$$

これが **今の一番具体的な次手** じゃ。

## B. 小規模探索でまず検査する

この anchored 条件が本当に自然か、まず具体例で検査する。
もし小規模探索でこれが崩れるなら、**witness \(R\) だけでは情報が足りない** とすぐ分かる。
逆に通るなら、強い次ターゲットになる。

## C. anchored 版を local / global に裂く

local:
$$
F_y(g') \equiv (x/q)^p \pmod{q^p}
$$

global:
$$
\text{その residue class にある } g' \text{ が、厳密等式 } F_y(g')=(x/q)^p \text{ を満たす}
$$

ここまで裂ければ、初めて「どこが局所で、どこが大域か」が truly 見える。

---

## 5. もう一つ、すぐ証明できる補助定理がある

ここは concrete に見えておる。

$$
F_y(g)=(g+y)^p-y^p
$$

は \(\mathbb{N}\) 上で \(g\) に関して厳密増加じゃ。
ゆえに解 \(g'\) が存在すれば一意で、しかも

$$
(x/q)^p < x^p = (z-y),GN(p,z-y,y)=F_y(z-y)
$$

だから

$$
\boxed{
g' < z-y
}
$$

が出る。
これは existence そのものは与えぬが、**解があれば smaller gap である** ことを完全に見せる。
この補題は今すぐ formalize してよい。
これは `2m-global` の「解があれば descent になる」部分を sharpen する。

---

## 6. だから、今の時点で具体的に見えている次の 3 手はこれじゃ

### 1. `AnchoredGapReductionTarget` を新設

$$
g' \equiv (R-1)y \pmod{q^p}
$$
を入れた強化版 target を作る。

### 2. 小規模探索

この anchored 条件が実例で成立するかをまず検査する。
ここで false なら、strong witness にまだ不足情報があると分かる。

### 3. 単調性補題

$$
F_y(g)=(g+y)^p-y^p
$$
の strict monotonicity と
$$
g' < z-y
$$
を先に閉じる。
これで global 側の「もし存在すれば smaller」という後半が整理される。

---

## 7. 率直な現状認識

だから、ぬしの言う通り **前の返しでは、ここまで具体に見えておらなんだ**。
いま見えている具体像はこれじゃ。

* まだ証明は見えていない
* だが **次に試すべき strongest plausible target** は見えた
* それは
  $$
  g' \equiv (R-1)y \pmod{q^p}
  $$
  を入れた anchored 版じゃ

ここを試せば、
「witness から integer gap を回収する mechanism が本当にあるのか」
が、かなりはっきりするはずじゃよ。

必要なら次に、その **anchored 版 target の Lean 雛形** と **検査用 Python/Lean の観測項目** まで落として書くぞい。

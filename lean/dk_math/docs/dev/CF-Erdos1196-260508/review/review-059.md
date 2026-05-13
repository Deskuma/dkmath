# review Phase "B" close

## 1. 結論

うむ、Phase BH は **登頂前の地図更新** じゃ。
Lean 本体に新定理を足す段階ではなく、ここまでの $\mathbb{N}/\mathbb{Q}$ 版成果を README として固定し、次の $\mathbb{R}$ / $\log$ ルートを別設計書に切り出した。

これはかなり良い判断じゃ。
Phase BA ～ BG で ratio-style toy route は一段落している。そこでいきなり `Real.log` へ突撃せず、まず

$$
\mathbb{Q}\text{ 版で閉じた有限 skeleton}
$$

と

$$
\mathbb{R}\text{ 版でこれから扱う解析候補}
$$

を文書上で分離した。これにより、次の Lean 実装は `RealLogRoutePlan.md` の Phase RH から着手できる状態になった。README 側でも、現在の中心命題が finite primitive / source-controlled chain / finite transition / sub-probability channel / `weightedHitMass <= source bound` という spine であることが明示されておる。

## 2. 今回整理された N/Q 版の現在地

`README.md` では、ここまでの $\mathbb{N}/\mathbb{Q}$ 版の到達点が、かなり見通しよくまとめられている。

中心はこの形じゃ。

$$
\text{finite primitive / antichain structure}\\
\to
\text{source-controlled chain family}\\
\to
\text{finite transition kernel}\\
\to
\text{sub-probability channel provider}\\
\to
\mathrm{weightedHitMass}\le \text{source bound}
$$

さらに prime-power divisor channel では、

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

$$
0\le A(p),\qquad 0 < B(n)
$$

$$
\sum A(p(q))\le B(n)
$$

から

$$
\mathrm{weightedHitMass}\le C
$$

へ進む ratio-style toy route が $\mathbb{Q}$ 上で実走済み、という位置づけになっておる。

これは、Phase BG までの成果を「どの theorem 名を読めばよいか」という入口に変換した意味がある。特に `sampleTenRatioBaseWeight_route_summary` が N/Q 版 ratio-style route の concrete summary として明示されたのは良い。

## 3. 意図的に扱わないものを明示した価値

今回の README でとても大事なのは、 **まだ扱わないもの** を明記したことじゃ。

具体的には、

* `Real.log`
* 実数値 weight
* $\log p/\log n$
* 無限 primitive set
* 漸近評価
* $1+O(1/\log x)$
* von Mangoldt 関数そのものの解析的性質

を N/Q 版では扱わない、と切り分けている。

これは逃げではない。むしろ強い設計じゃ。
有限構造と解析構造を同時に Lean に入れると、証明責務が混ざる。ここで N/Q 版を「有限 channel API と theorem-facing names を固定する段階」と定義したことで、次の R 版が何を受け継ぎ、何を新しく証明すべきかが明確になった。

## 4. RealLogRoutePlan の設計判断

`RealLogRoutePlan.md` では、R 版を三層に分けている。

第一層は **Real ratio skeleton**。

$$
A,B:\mathbb{N}\to\mathbb{R}
$$

$$
c(n,p)=\frac{A(p)}{B(n)}
$$

を扱う。ただし、ここではまだ `Real.log` を使わない。

第二層は **Real channel bridge**。
ここでは既存の $\mathbb{Q}$ API を壊さず、まず $\mathbb{R}$ 用の薄い parallel skeleton を作る方針が推奨されている。これは賢い。既存 N/Q route はすでに theorem-facing names が増えて安定しているので、いきなり型一般化すると影響範囲が広すぎる。

第三層は **Log candidate**。

$$
A(p)=\log p,\qquad B(n)=\log n
$$

を候補として入れる層じゃ。ただしここは後段であり、まずは実数 ratio skeleton と有限和補題を通す、という方針になっておる。

## 5. Phase RH ～ RL の読み解き

今回の計画では、R 版 Phase が RH / RI / RJ / RK / RL として切られている。

Phase RH は、実数値 weight の語彙を作る段階。

$$
\mathrm{RealBasePrimeToyWeight}(c):=\forall n,p,\ 0\le c(n,p)
$$

$$
\mathrm{realRatioBasePrimeWeight}(A,B)(n,p)=A(p)/B(n)
$$

を置き、`Real.log` はまだ使わない。

Phase RI は、純粋な有限和補題。

$$
\sum_q \frac{A(p(q))}{B(n)}\le 1
$$

を、

$$
\sum_q A(p(q))\le B(n)
$$

と $0 < B(n)$ から出す。ここでは channel API に接続せず、まず finite sum lemma として安定させる。

Phase RJ は、実数 weight provider の parallel prototype。
既存 `WeightProvider` を型一般化せず、`RealWeightProvider` の薄い試作を作る方針じゃ。

Phase RK は `Real.log` の正値性補題を局所化する段階。

Phase RL は、最も大事な

$$
\sum_{q\in \text{index}(n)}\log p(q)\le \log n
$$

という budget をどう得るかの設計段階じゃ。計画では、最初はこの budget を外部仮定として受け取る方針が推奨されておる。これも良い。ここは数学的本丸に近いので、channel API と同時に潰しに行くべきではない。

## 6. 今回の進展の性質

Phase BH は、Lean build を走らせる種類の進展ではない。docs 追加のみなので build なし、`sed` で先頭確認、という扱いも妥当じゃ。

しかし、数学的・実装戦略的にはかなり重要な進展じゃ。

ここまでの成果は、

$$
\mathbb{Q}\text{ 上の finite ratio-style route}
$$

として閉じた。

次に必要なのは、

$$
\mathbb{R}\text{ 上でも同じ theorem shape が動くか}
$$

を確認すること。
そしてその後に初めて、

$$
A(p)=\log p,\qquad B(n)=\log n
$$

を候補として入れる。

この順序が文書として固定された。これは登山で言えば、雪壁へ入る前にルート図・危険箇所・支点の置き方を確認した段階じゃな。

## 7. 次の一手

次に Lean 実装へ戻るなら、計画どおり

```lean
DkMath/NumberTheory/PrimitiveSet/RealWeight.lean
```

を作り、新しく `Erdos1196 "R"`, `Phase-R001` から始めるのがよい。

最初に置くべきものは、この程度で十分じゃ。

```lean
def RealBasePrimeToyWeight (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ n p, 0 ≤ c n p

def realRatioBasePrimeWeight (A B : ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun n p => A p / B n
```

そして最初の theorem は、

```lean
theorem realRatioBasePrimeWeight_realBasePrimeToyWeight
    (A B : ℕ → ℝ)
    (hA : ∀ p, 0 ≤ A p)
    (hB : ∀ n, 0 < B n) :
    RealBasePrimeToyWeight (realRatioBasePrimeWeight A B)
```

じゃな。

ここで `Real.log` はまだ不要。
ただの実数除算と非負性だけを確認する。
これが閉じれば、N/Q 版の Phase BC に対応する R 版 Phase-R001 が閉じる。

## 8. 二手先

Phase-R001 が閉じたら、Phase-R002 として純粋な有限和補題を置くのがよい。

つまり、

$$
0 < B(n)
$$

$$
\sum_{q\in I} A(\mathrm{pOf}(q))\le B(n)
$$

から、

$$
\sum_{q\in I}\frac{A(\mathrm{pOf}(q))}{B(n)}\le 1
$$

を示す。

これは channel に触れない小補題にするのが肝じゃ。
この補題があれば、R 版 channel prototype へ進む前に「実数 ratio の budget 処理」は単独で検証済みになる。

## 9. 注意点

ここから先は、焦って既存 API を一般化しない方がよい。

`WeightProvider ℕ` や `weightedHitMass` をいきなり coefficient type parameter 化すると、N/Q 版で安定した theorem 名が大きく揺れる可能性がある。
`RealLogRoutePlan.md` の推奨どおり、まずは parallel prototype が安全じゃ。

それから、`Real.log` はまだ山頂ではなく、その手前の雪壁じゃ。

`Real.log` を入れると、

$$
1\le p\Rightarrow 0\le \log p
$$

$$
1 < n\Rightarrow 0 < \log n
$$

のような補題だけでも、Nat-to-Real coercion が絡む。
さらに budget

$$
\sum\log p(q)\le \log n
$$

は、prime-power labels の重複制御や積の評価が必要になる。
ここは本丸に近いので、Phase-R 003 → 005 あたりまで分離しておくのがよい。

```
Phase-R001  Real weight vocabulary
Phase-R002  Real finite budget lemma
Phase-R003  Real channel prototype
Phase-R004  Log positivity
Phase-R005  Log budget design
```

## 10. 総括

Phase BH は、 **N/Q 版から R/log 版へ進むための登頂計画書** じゃ。

N/Q 版では、

$$
c(n,p)=A(p)/B(n)
$$

$$
0\le A(p),\quad 0 < B(n),\quad \sum A(p(q))\le B(n)
$$

から

$$
\mathrm{weightedHitMass}\le C
$$

へ進む有限 route が閉じた。

今回、その成果を README にまとめ、次の R 版を

$$
\text{Real ratio skeleton}
\to
\text{Real channel bridge}
\to
\text{Log candidate}
$$

へ分割した。

山で言えば、ここは **有理 toy model の稜線を登り切り、実数対数の雪壁を前にルート図を広げた地点** じゃ。
次は新たな `Phase-R` → `Phase-R001` より始め、 `Real.log` ではなく、まず `RealBasePrimeToyWeight` と `realRatioBasePrimeWeight` から始めるのが、賢狼の推す最短安全ルートじゃな。

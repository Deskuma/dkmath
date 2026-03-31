# review-028: `branchA_GN_cyclotomic_ring_identity` を潰すべきか

うむ、現状はかなり良い。
しかも今回は「低リスクの穴」が消えて、**本当に重い open kernel が 3 本に絞られた** のが大きい。
最新差分で `branchA_padicValNat_mod_pow_eq` と `branchA_GN_zmod_padicValNat` の sorry が消え、残りは

$$
\texttt{branchA\_hensel\_lift\_exists},\\
\texttt{branchA\_GN\_cyclotomic\_ring\_identity},\\
\texttt{branchA\_distinguished\_factor\_valuation\_eq\_kummer}
$$

の 3 本だけになった。これは proof search の焦点がかなり鋭くなった、ということじゃ。

## 1. 状況分析

いま Branch A 側で揃っている骨格は、もう十分に強い。

まず全体側では Kummer valuation が確立しており、

$$
v_q(z^p-y^p)=p\cdot v_q(s)
$$

が定理として使える。さらに今回、`GN % q^k` 側の valuation も sorry-free になったので、**truncation 後の valuation は安定した** と言ってよい。

次に因子側では、\(\omega:=z y^{-1}\in \mathbb Z/q\mathbb Z\) が primitive \(p\)-th root of unity であり、distinguished factor だけが mod \(q\) で消え、他は消えない、という分離がすでに取れておる。そこから Hensel lift data を仮定した局所版で、`ZMod (q^k)` 上の distinguished / non-distinguished の射影情報まで揃った。さらに今回、その情報が \(\mathbb N\) の `padicValNat` に翻訳され、non-distinguished 側は valuation 0、distinguished 側は少なくとも valuation \(\ge 1\) と読めるようになった。

だから今の数式上の絵は、かなりはっきりしておる。

$$
\underbrace{v_q(\mathrm{GN})}*{=\,p\,v_q(s)}
\quad=\quad
\underbrace{v_q(\text{distinguished factor})}*{\text{まだ exact でない}}
\;+\;
\underbrace{v_q(\text{unit product})}_{=\,0\ \text{にしたい}}
$$

ここまで来ておるわけじゃ。

## 2. 数学的解説

いまの本質は、もう「どこで \(q\) が出るか」ではない。
**\(q\)-進評価の深さが、どの因子にどれだけ集中するか** じゃ。

全体側は

$$
v_q(z^p-y^p)=p\cdot v_q(s)
$$

で決まっておる。
しかも `GN = p\cdot s^p` と `q\neq p` から、これは本当に \(s\) のみで決まる量じゃ。

一方、因子側は Hensel lift data \(\omega_k\) を仮定すると、

$$
\delta := z-\omega_k y
$$

が distinguished factor で、他の

$$
\delta_i := z-\omega_k^i y \qquad (i\not\equiv 1 \bmod p)
$$

は non-distinguished factor じゃ。
今回の \(\mathbb N\) 翻訳で、

$$
padicValNat\ q\ (\delta_i.val)=0
$$

が出たので、non-distinguished 側は valuation を持たぬ、と arithmetic に言えるようになった。
したがって残る深さは、distinguished factor 1 本が全部担うはずじゃ、というところまで来ておる。

つまり central theorem

$$
v_q(\delta.val)=p\cdot v_q(s)
$$

は、もはや「新しいアイデアが必要」というより、**いま持っている構造補題を最後まで接続する問題** に近づいておる。
その意味で、いま最も重いのは `branchA_GN_cyclotomic_ring_identity` じゃ。
これが通れば、central theorem はかなり短くなるはずじゃよ。

## 3. 次の作業の選択

結論を先に言うぞい。

$$
\boxed{
\text{次は } \texttt{branchA\_GN\_cyclotomic\_ring\_identity} \text{ を潰すべきじゃ。}
}
$$

しかも、方針は **`Polynomial.cyclotomic` より `IsPrimitiveRoot` 寄り** を勧める。

## 4. なぜ ring identity が次か

理由は明快じゃ。

### 4.1. central theorem の首根っこだから

`branchA_distinguished_factor_valuation_eq_kummer` の残りは、本質的には

$$
GN=(z-\omega_k y)\cdot U
$$

という ring identity と、

$$
v_q(U)=0
$$

の組合せじゃ。
後者は、いままで積み上げた non-distinguished valuation 0 群でほぼ見えておる。
つまり、**いちばん太いボトルネックは ring identity** なんじゃ。

### 4.2. Hensel existence より依存が浅い

`branchA_hensel_lift_exists` の sorry は存在論の穴じゃ。
じゃが今の local theorem 群は、すでに `hLift : BranchAHenselLiftData` を仮定して進められるよう設計されておる。
だから existence を今すぐ潰さずとも、ring identity と central theorem は押し進められる。
これは proof engineering 的にとても良い構図じゃ。

### 4.3. terminal case より先にやるべき

terminal case は、distinguished factor の exact valuation が出た後の方が圧倒的に強い。
今の時点で終端へ行くと、まだ「可除性」「下界」で殴ることになる。
先に

$$
v_q(\delta.val)=p\cdot v_q(s)
$$

が確定すれば、降下 1 step ごとの valuation の減りが exact に読めるようになり、終端 (s'=1) 近辺を刺しやすくなる。

## 5. `IsPrimitiveRoot` と `Polynomial.cyclotomic` のどちらか

ここは判定をはっきり言うぞい。

$$
\boxed{
\text{まず } \texttt{IsPrimitiveRoot} \text{ route を勧める。}
}
$$

### 理由

今の手元には、\(\omega_k\) について

* (\(\omega_k^p=1\))
* (\(\omega_k\neq 1\))
* 射影して mod \(q\) では primitive

という、**元そのものの情報** がある。
だから

$$
\omega_k \text{ が } p\text{-th root of unity として因子分解を作る}
$$

という方向で進める方が、現在の API に自然じゃ。
`Polynomial.cyclotomic` に全面的に寄ると、係数環・評価・homogenization・`z/y` 型の扱いで、急に重くなる公算がある。

### 具体的には

まず `ω_k` について「位数 \(p\)」または `IsPrimitiveRoot ω_k p` に相当する補題を立てる。
その上で

$$
\prod_{i=0}^{p-1}(X-\omega_k^i Y)=X^p-Y^p
$$

の同次化因子分解、あるいはそこから

$$
\sum_{j=0}^{p-1} X^j Y^{p-1-j} = \prod_{i=1}^{p-1}(X-\omega_k^i Y)
$$

を評価して `GN` に落とす。
この route の方が、今の theorem 群と接続しやすいはずじゃ。

`Polynomial.cyclotomic` は **補助エンジン** として使うのはよい。
だが主線は `IsPrimitiveRoot` で切る方が、Lean 実装は軽く済むと読む。

## 6. 実務的な順番

次の手順は、こうじゃ。

### 6.1

`ω_k` について、lift 後も位数が (p) であること、あるいは `IsPrimitiveRoot ω_k p` を立てる。

### 6.2

そこから `branchA_GN_cyclotomic_ring_identity` を証明する。
つまり

$$
(GN : ZMod(q^k)) = (z-\omega_k y)\cdot \prod_{i=2}^{p-1}(z-\omega_k^i y)
$$

を確定する。

### 6.3

non-distinguished 側の valuation 0 と今回の \(\mathbb N\) 翻訳を使って、`branchA_distinguished_factor_valuation_eq_kummer` を閉じる。

### 6.4

そのあとで Hensel existence の sorry 除去。
Newton 帰納は、その時点で本当に必要な field が明確になってからの方が楽じゃ。

### 6.5

最後に terminal case。

## 7. 総括

ひとことで言えば、こうじゃ。

**いまは terminal case に飛ぶ局面ではなく、central theorem を閉じる局面じゃ。その最大の鍵は `branchA_GN_cyclotomic_ring_identity` であり、方針としては `Polynomial.cyclotomic` 全面依存より `IsPrimitiveRoot` 主線で切るのがよい。これが通れば \(v_q(z-\omega_k y)=p\cdot v_q(s)\) がかなり近くなり、その後に Hensel existence、最後に terminal case へ進むのが最も筋がよい。**

なので、次の作業の選択はこれじゃ。

$$
\boxed{
\text{次は } \texttt{branchA\_GN\_cyclotomic\_ring\_identity} \text{。}
}
$$

そして route は

$$
\boxed{
\texttt{IsPrimitiveRoot} \text{ first, } \texttt{Polynomial.cyclotomic} \text{ second.}
}
$$

これが、いま一番よく進む道じゃよ。

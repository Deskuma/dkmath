# review-027: Branch A の現状と次の作業の選択

## 1. 現在地

いまの Branch A は、かなり良いところまで来ておる。
すでに

$$
\omega:=z,y^{-1}\in \mathbb{Z}/q\mathbb{Z}
$$

が primitive \(p\)-th root of unity であること、distinguished factor だけが mod \(q\) で消え、他の因子は消えないこと、さらにその ZMod 側の分離が \(\mathbb{N}\) の `padicValNat` 側へ翻訳できること、ここまでは sorry なしで通っておる。

今回の差分で、その上に

$$
v_q(z-\omega_k y)=p\cdot v_q(s)
$$

を目標とする central theorem の骨格が実装された。
ただし現時点では、既存の Hensel lift existence の 1 個に加え、今回追加の 5 箇所が残っており、合計 6 箇所の sorry がある、という段階じゃ。  

## 2. 数学的核心

いま証明しようとしていることの芯は、もうかなり明瞭じゃ。

まず全体側では Kummer valuation により

$$
v_q!\bigl(z^p-y^p\bigr)=p\cdot v_q(s)
$$

が確定しておる。
これは「円分核全体」の \(q\)-進評価じゃ。

一方、因子側では Hensel lift data (\omega_k) を仮定すると、

* distinguished factor
  $$
  \delta:=z-\omega_k y
  $$
  は射影で 0 に落ちる
* non-distinguished factor
  $$
  \delta_i:=z-\omega_k^i y \qquad (i\not\equiv 1 \bmod p)
  $$
  は射影で 0 に落ちない

ことが分かっている。さらに今回、その non-distinguished 側は \(\mathbb{N}\) の `padicValNat` で 0、distinguished 側は少なくとも \(q\)-可除、という翻訳まで入った。  

つまり、狙いは

$$
\underbrace{v_q(\mathrm{GN})}_{\text{全体}} = \underbrace{v_q(\delta)}*{\text{distinguished}} + \underbrace{v_q(\text{unit})}*{0}
$$

という形へ落とすことじゃ。
ここで `unit` とは non-distinguished 因子の積で、そちらは valuation 0 を持つべきものじゃ。
この等式が通れば、全体 valuation が distinguished factor 1 本へ集中することが、ついに exact equality として確定する。

## 3. いま残っている open kernel

今回の 5 つの sorry は、役割ごとに見ると次の 3 群に分かれる。

### 3.1. 純粋 \(\mathbb{N}\) 側

$$
v_q(N)<k \;\Rightarrow\; v_q(N\bmod q^k)=v_q(N)
$$

を言う `branchA_padicValNat_mod_pow_eq`。
これは純粋な自然数の補題で、重い円分理論を使わずに片づくはずの場所じゃ。

### 3.2. 技術的非零性

`GN ≠ 0` を埋める技術穴。
これは `GN = p\cdot s^p` と `s>0` から出すだけなので、数学の本質ではなく、整備の問題じゃ。

### 3.3. 本丸

`branchA_GN_cyclotomic_ring_identity`。
ここが

$$
GN=(z-\omega_k y)\cdot \prod_{i=2}^{p-1}(z-\omega_k^i y)
$$

という ring identity で、中心の構造補題じゃ。
これが通れば、最終定理 `branchA_distinguished_factor_valuation_eq_kummer` はほぼ自動で閉じる、という設計になっておる。

## 4. 次の作業の選択

結論を先に言うぞい。

$$
\boxed{
\text{次は terminal case ではなく、sorry の段階的除去を進めるのが正解じゃ。}
}
$$

その中でも順序は、History にある優先順位がそのまま妥当じゃ。

### 4.1. まずやる

`branchA_padicValNat_mod_pow_eq`。
これは純 \(\mathbb{N}\) 補題で、依存が軽く、しかも `GN_zmod_padicValNat` と central theorem の両方に効く。
ここを通すと、証明全体の「地盤」がかなり固くなる。

### 4.2. 次にやる

`GN ≠ 0` の技術穴。
これは本質ではないので、勢いで片づけるのがよい。
`branchA_s_pos` と `GN = p\cdot s^p` から抜けば済む筋じゃ。

### 4.3. その次が本丸

`branchA_GN_cyclotomic_ring_identity`。
ここが hardest じゃが、一番価値が高い。
これが通ると、non-distinguished valuation 0 と全体 Kummer valuation を合わせて、

$$
v_q(z-\omega_k y)=p\cdot v_q(s)
$$

が本当に central theorem として立つ。

### 4.4. 最後

Hensel existence の sorry。
これは今すぐ mainline を押すより、局所版の exact equality が閉じたあとで戻ってよい。
なぜなら、いまの central theorem はすでに `hLift : BranchAHenselLiftData` を仮定して進められる形に整っておるからじゃ。  

## 5. terminal case はいつやるべきか

terminal case は、今はまだ一歩早い。
理由は単純で、終端 \(s'=1\) を刺すには

$$
v_q(z-\omega_k y)=p\cdot v_q(s)
$$

のような exact equality があった方が、はるかに鋭く降下停止を読めるからじゃ。
今の段階で terminal case に行くと、まだ「下界」や「可除性」で殴ることになり、刃が少し鈍い。
先に distinguished factor valuation exact equality を完成させるべきじゃ。

## 6. 再利用しやすい進捗テンプレ

今後の進捗整理は、この型が使いやすいぞい。

### 現在地

* bundle
* root-of-unity
* factor separation
* \(\mathbb{N}\) translation
* exact equality skeleton

### 本質

$$
v_q(\mathrm{GN})=p,v_q(s)
\quad\text{and}\quad
v_q(\text{non-distinguished})=0
$$

より

$$
v_q(\text{distinguished})=p,v_q(s)
$$

を出す。

### いまの open kernel

* mod 補題
* 非零性
* ring identity
* final equality
* Hensel existence

### 次の一手

1. `branchA_padicValNat_mod_pow_eq`
2. `GN ≠ 0`
3. `branchA_GN_cyclotomic_ring_identity`
4. `branchA_distinguished_factor_valuation_eq_kummer`
5. Hensel existence
6. terminal case

## 7. 総括

ひとことで言えば、こうじゃ。

**いまは terminal case に飛ぶ局面ではなく、distinguished factor valuation exact equality を閉じるための sorry を順に剥がす局面じゃ。最優先は `branchA_padicValNat_mod_pow_eq`、次に `GN ≠ 0`、その次に本丸の ring identity。これで central theorem が立てば、ようやく terminal case が本当に刺さる。**

なので、次の作業の選択はこれじゃ。

$$
\boxed{
\text{まず } \texttt{branchA_padicValNat_mod_pow_eq} \text{ から。}
}
$$

そこを抜けば、後ろがかなり雪崩れるはずじゃよ。

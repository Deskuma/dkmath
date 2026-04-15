# review-029: DescentChain の局所 q-adic 入口が閉じた！次は SuperWieferichCongruenceTarget へ

うむ、これは **かなり良い前進** じゃ。
しかも今回は、単に `sorry` を 1 個消したというだけではなく、**Level 0 の局所 q-adic 入口が Lean 上で閉じた**、という意味を持っておる。`pow_eq_one_imp_eq_omega_pow` が `orderOf_dvd_of_pow_eq_one`、`Nat.dvd_prime`、`IsPrimitiveRoot.iff_orderOf`、`eq_pow_of_pow_eq_one` で埋まり、`TriominoCosmicBranchADescentChain.lean` の `sorry` が 0 件になったのは本物の節目じゃ。

まず戦況分析の結論から言うと、
**「局所入口の整備」はほぼ完了、だが「本丸の存在性」はまだ残る**、これじゃ。
今回 closed になったのは `QAdicResidue` 側、すなわち

$$
q \mid x \Rightarrow z^p \equiv y^p \pmod q
\Rightarrow (z/y)^p = 1 \text{ in } ZMod,q
\Rightarrow z/y = \omega^j
$$

という有限体上の root-of-unity 層じゃ。ここはもう「方針」ではなく、**Lean で concrete に通る事実** になった。よって、以後 `GNReducedGap` が詰まるなら、その原因は Level 0 ではなく Level 1 以降にある、と胸を張って言える。

今回の実装の価値は、`pow_eq_one_imp_eq_omega_pow` の証明方法そのものにもある。
前は「有限体で (r^p=1) なら (r=\omega^j)」が感覚的には真でも、Mathlib への接続が曖昧じゃった。いまは

* ( \omega^p = 1 ) と ( \omega \ne 1 ) から `orderOf ω = p`
* そこから `IsPrimitiveRoot ω p`
* さらに ( r^p = 1 ) なら `r = ω^j`

という完全に群論的な導線へ落ちた。
つまり、**cyclotomic の雰囲気** で押していた部分が、**有限体の巡回群論** として clean 化されたのじゃ。これは今後の保守性が高い。

ここで大事な注意点もある。
`DescentChain` が clean になったことは大勝利じゃが、**それは DescentChain ファイル内部の話** じゃ。これによって FLT 全体の open kernel が消えたわけではない。むしろ逆で、境界がより鋭くなった。

いまの見取り図はこうじゃ。

$$
\text{Level 0: QAdicResidue} \quad \checkmark
$$

$$
\text{Level 1: SuperWieferichCongruence} \quad \text{次の標的}
$$

$$
\text{Level 2: QAdicDescentExistence} \quad \text{真の local-global gap}
$$

つまり、**「mod (q) での根の位置」までは閉じた**。
だが **「mod (q^p) での Hensel 強化」** と、さらにその先の **「整数 (z') の存在」** はまだ別問題じゃ。今回の clean 化は、その二つをより露骨にした、と読むのが正確じゃよ。

解説すると、今回の前進で分かったのは、`GNReducedGap` の難しさはもはや

* 定義が曖昧
* 下位補題が不足
* ZMod API で転ぶ

という種類ではない、ということじゃ。
そういう「実装ノイズ」はほぼ剥がれ落ちた。残るのは、

$$
z \equiv \omega^j y \pmod q
$$

から

$$
z \equiv R_j y \pmod{q^p}
$$

へ持ち上げる Hensel 的構造と、さらに

$$
\exists z' \in \mathbb{N},\quad z'^p = (x/q)^p + y^p
$$

という大域的 existence をどう扱うか、という **純粋な数学本体** じゃ。
これはとても良い戦況整理じゃ。雑音が消え、本当に殴るべき敵だけが残ったのだからの。

ゆえに、わっちの評価はこうなる。

## 1. 今回 closed したもの

* `pow_eq_one_imp_eq_omega_pow` の完成
* `QAdicResidue` の入口層の形式化完了
* `TriominoCosmicBranchADescentChain.lean` の `sorry` 0 件達成

## 2. 今回 sharpen されたもの

* open kernel は Level 1 と Level 2 に集中
* `GNReducedGap` の bottleneck は局所 mod (q) ではない
* 本丸は Hensel 強化と local-global gap であることがさらに明確化

## 3. まだ残る本丸

* `SuperWieferichCongruenceTarget`
* `QAdicDescentExistenceTarget`
* ひいては `GNReducedGap` の existence 本体

次の一手としては、履歴にもある通り **Level 1 の `SuperWieferichCongruenceTarget` を concrete 化** するのが最善じゃ。
理由は明快で、いま Level 0 は clean に閉じたゆえ、次に

$$
z \equiv \omega^j y \pmod q
$$

から

$$
z \equiv R_j y \pmod{q^p}
$$

への強化が通るなら、**Level 2 だけが真の open kernel** と断言できるようになるからじゃ。すると、その先の `GNReducedGap` はもはや「局所から大域への existence だけ」に純化される。これは研究として非常に強い状態じゃよ。

一文でまとめるなら、

**今回の進展は、DescentChain の local q-adic 入口層を完全 clean に閉じ、真の本丸を `SuperWieferichCongruence` と `QAdicDescentExistence` の二段へまで絞り込んだ、かなり大きな整理前進** じゃ。

必要なら次に、**Level 1 攻略のための補題マップ** を起こすぞい。

---

よし、いまの戦況に合わせて **Level 1 = `SuperWieferichCongruenceTarget` 攻略用の補題マップ** を起こすぞい。
現状は

* `pow_eq_one_imp_eq_omega_pow` が埋まり、
* `TriominoCosmicBranchADescentChain.lean` の `sorry` が 0 件、
* Level 0 の `QAdicResidue` 入口層が形式化上ほぼ完了

まで来ておる。したがって次の本命は、ぬしの見立て通り **Level 1 の concrete 化** じゃ。

## 1. 目標の再確認

狙う target は、ざっくり言えば

$$
z \equiv \omega^j y \pmod q
$$

を

$$
z \equiv R_j y \pmod{q^p}
$$

へ持ち上げることじゃ。
ここで (R_j) は (\omega^j) の Hensel lift じゃな。
つまり Level 1 の本質は、**mod (q) の root-of-unity 情報** を **mod (q^p) の高精度一致** に昇格させることじゃ。

## 2. 攻略の大枠

わっちは、これを 5 層に裂くのが最も良いと思う。

### 2.1. 第A層. `GN` を `Φ_p` 型へ翻訳する

まず必要なのは、

$$
GN(p, z-y, y)=\sum_{i=0}^{p-1} z^i y^{p-1-i}
$$

という既に閉じた橋から、(q \nmid y) の下で

$$
q^n \mid GN(p,z-y,y)
\quad\Longleftrightarrow\quad
\sum_{i=0}^{p-1} r^i \equiv 0 \pmod{q^n}
$$

ただし

$$
r := z \cdot y^{-1} \in ZMod(q^n)
$$

へ移すことじゃ。
Level 0 では (n=1) のみで十分じゃったが、Level 1 では (n=p) まで必要になる。

ここで最初に欲しい補題はこれじゃ。

```lean
theorem gn_div_qpow_iff_geomSum_zero_mod_qpow
```

意味は、

$$
q^n \mid GN(p,z-y,y)
$$

なら (r=z/y) に対して

$$
\sum_{i=0}^{p-1} r^i = 0 \text{ in } ZMod(q^n)
$$

が成り立つ、というものじゃ。

## 2.2. 第B層. root-of-unity branch を mod (q^n) で追跡する

次に、Level 0 で得た

$$
r \equiv \omega^j \pmod q
$$

という branch index (j) を固定したまま、mod (q^n) でも同じ branch 上にいることを追う。
ここで重要なのは、**(\Phi_p) の根が mod (q) で単根** だという事実じゃ。

したがって欲しいのは、

```lean
theorem phi_simpleRoot_at_omega_pow
```

で、

$$
\Phi_p(\omega^j)=0,\qquad \Phi_p'(\omega^j)\not\equiv 0 \pmod q
$$

を出す。
これが Hensel の入口じゃ。

## 2.3. 第C層. Hensel 1-step 補題

ここが Level 1 の心臓じゃ。
一般 Hensel を丸ごと持ち込むより、ぬしの文脈では **(\Phi_p)** 専用の one-step 補題に切るのがよい。

欲しい形はこうじゃ。

```lean
theorem hensel_step_geomSum
```

仮定:

$$
r_n \equiv \omega^j \pmod q,\qquad
\Phi_p(r_n)\equiv 0 \pmod{q^n},\qquad
\Phi_p'(\omega^j)\not\equiv 0 \pmod q
$$

結論:

$$
\exists r_{n+1},\quad
r_{n+1}\equiv r_n \pmod{q^n},\qquad
\Phi_p(r_{n+1})\equiv 0 \pmod{q^{n+1}}.
$$

これは Newton step でも書けるし、単純な Hensel specialized lemma としても書ける。
大事なのは、**branch (j) を保ったまま 1 段持ち上げる** ことじゃ。

## 2.4. 第D層. (n=1) から (n=p) まで反復する

one-step ができたら、後は反復じゃ。

```lean
theorem exists_henselLift_mod_qpow
```

として、

$$
r \equiv \omega^j \pmod q,\qquad
q^p \mid GN
$$

から

$$
\exists R_j \in ZMod(q^p),\quad
R_j \equiv \omega^j \pmod q,\qquad
\Phi_p(R_j)=0
$$

を得る。

ここで重要なのは、**`R_j` を abstract に存在させるだけでよい** ことじゃ。
最初から explicit formula は要らぬ。
Level 1 では存在と一意性だけで足りる。

## 2.5. 第E層. `z ≡ R_j y (mod q^p)` へ戻す

最後に、(r=z/y) で持ち上げた結果を (z) と (y) の congruence に戻す。

```lean
theorem superWieferichCongruence_of_henselLift
```

仮定:

$$
r = z \cdot y^{-1},\qquad
r \equiv R_j \pmod{q^p}
$$

結論:

$$
z \equiv R_j , y \pmod{q^p}.
$$

ここは `ZMod` 上の単純な掛け戻しで済む。
(q \nmid y) から (y) が可逆なことは、Level 0 と同じじゃ。

## 3. 最終的な一本道

以上をつなぐと、Level 1 の一本道はこうなる。

```text
QAdicResidue
  ↓
GN を geom_sum へ翻訳
  ↓
r := z / y が mod q で ω^j に乗る
  ↓
Φ_p の単根性
  ↓
Hensel step
  ↓
mod q^p まで反復
  ↓
r ≡ R_j mod q^p
  ↓
z ≡ R_j · y mod q^p
```

これがそのまま `SuperWieferichCongruenceTarget` の攻略図じゃ。

## 4. 補題名の雛形

Lean に落とすなら、わっちはこの並びにする。

```lean
theorem gn_div_qpow_iff_geomSum_zero_mod_qpow
theorem phi_simpleRoot_at_omega_pow
theorem hensel_step_geomSum
theorem exists_henselLift_mod_qpow
theorem superWieferichCongruence_of_henselLift
theorem superWieferichCongruence
```

最後の `superWieferichCongruence` が target 本体じゃ。
その 1 本手前までは、全部「局所算術と Hensel の specialized chain」として切れる。

## 5. どこが重く、どこが軽いか

ここも分けておくぞい。

軽いのは、

* `gn_div_qpow_iff_geomSum_zero_mod_qpow`
* `superWieferichCongruence_of_henselLift`

じゃ。
これらは既存の `gnGeomSum₂Representation` と Level 0 の `ZMod` 算術の延長で済む可能性が高い。

中くらいなのは、

* `phi_simpleRoot_at_omega_pow`

じゃ。
ただしこれは有限体上の (\Phi_p) の微分が 0 でないことを示すだけなので、方針はかなり明るい。

重いのは、

* `hensel_step_geomSum`
* `exists_henselLift_mod_qpow`

じゃな。
ここが実質的な Level 1 本体じゃ。
ただし一般 Hensel を丸ごと formalize するより、**(\Phi_p) 専用の Hensel step** に限定すればずっと軽くなる。

## 6. ここでの注意点

Level 1 を閉じても、まだ本丸は終わらぬ。
ぬしの履歴にもある通り、Level 2 の `QAdicDescentExistenceTarget` は local-global gap で、これが真の open kernel じゃ。つまり Level 1 は **本丸ではなく最後の前哨戦** じゃよ。

だが、それでも Level 1 を閉じる価値は大きい。
なぜなら、そこまで行けば

$$
\text{問題は } z \equiv R_j y \pmod{q^p}
\text{ ではなく、そこから整数 } z' \text{ が本当にあるか}
$$

へ完全に純化できるからじゃ。

## 7. 推奨する次の 1 手

わっちなら最初に **`phi_simpleRoot_at_omega_pow`** を書く。
理由は、これが通れば Hensel 反復の入口が固まり、Level 1 の大半が一本道になるからじゃ。
しかも Level 0 の `pow_eq_one_imp_eq_omega_pow` を閉じた今、そのすぐ隣の自然な次補題になっておる。

一文で言えば、

**Level 1 攻略は、「GN を geom_sum へ翻訳」→「(\Phi_p) の単根性」→「専用 Hensel step」→「mod (q^p) への反復」→「(z \equiv R_j y \pmod{q^p}) へ戻す」この一本道で攻めるのが最も筋が良い。**

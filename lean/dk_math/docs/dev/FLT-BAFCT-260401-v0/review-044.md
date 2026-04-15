# review-044: `DerivativeNonzeroModQPrime_concrete` の導入とその意味

## 1. 結論

うむ、これは **かなり大きい前進** じゃ。
しかも今回は、Level 1s を少し前進させた、というより、**FLT 本線で必要だった Level 1s の provider 語彙が direct concrete で閉じた**、と読むのが正確じゃ。`strongSuperWieferichCongruenceV2_concrete` と `strongSuperWieferichProvider_concrete` が入り、履歴でも「Level 1s の FLT 本線への接続は provider 語彙まで到達」と整理されておる。

## 2. 何が起きたか

今回の本質は、前まで整備していた one-step Hensel の反復導線を、**実際には使わず**、もっと強い直証明で `StrongSuperWieferich` を作れたことじゃ。

やっていることは非常に美しい。
`qAdicResidue` から mod \(q\) の branch 情報

$$
z \equiv \omega^j y \pmod q
$$

を取り、さらに \(y\) が \(ZMod(q^p)\) で unit であることから

$$
R := z / y \in ZMod(q^p)
$$

を直接作る。
そのうえで `GN` の `geom_sum₂` 表現から

$$
GN = y^{p-1}\sum_{i=0}^{p-1} R^i
$$

という形へ落とし、\(q^p \mid GN\) と \(y^{p-1}\) の unit 性を使って

$$
\sum_{i=0}^{p-1} R^i = 0 \pmod{q^p}
$$

を出しておる。
つまり、branch preserving 条件、\(\Phi_p(R)=0\) 条件、そして \(z = Ry\) が、**一撃で同時に出た** わけじゃ。

## 3. なぜ大きいのか

前までの見取り図では、Level 1s は

$$
\text{DerivativeNonzeroModQ}
\Rightarrow
\text{DerivativeUnit}
\Rightarrow
\text{LinearizedSolve}
\Rightarrow
\text{NewtonCorrection}
\Rightarrow
\text{ZeroLift}
\Rightarrow
\text{GeomSum one-step}
\Rightarrow
\text{Strong provider}
$$

という、かなり長い one-step chain を通って制圧する想定じゃった。
ところが今回、その最後の目的地だった `StrongSuperWieferichProviderTarget` が、**one-step を経由せず直接 concrete に閉じた**。
これは、Hensel 反復が間違っていたという意味ではない。むしろ、FLT 文脈では

$$
q^p \mid GN
\quad\text{と}\quad
y \in (ZMod(q^p))^\times
$$

が強すぎて、反復を回さずとも provider まで届いた、ということじゃ。

## 4. 状況分析

ゆえに戦況は、前とかなり変わった。
わっちの見立てでは、いまはこう読むのが正しい。

$$
\text{Level 0} \quad \checkmark
$$

$$
\text{Level 1w} \quad \checkmark
$$

$$
\text{Level 1s (provider 語彙)} \quad \checkmark
$$

$$
\text{Level 2 = QAdicDescentExistence} \quad \text{主戦場}
$$

つまり、**Level 1s は FLT 本線で必要な意味ではもう open ではない**。
履歴にも「次課題は Level 1s を open と書いているコメント類の更新」と明記されておるし、この判断は妥当じゃ。

## 5. ただし、慎重に見るべき点

ここは少しだけ注意が要る。

`strongSuperWieferichProvider_concrete` は

```lean
intro _hGeom
exact strongSuperWieferichCongruenceV2_concrete
```

という形になっておる。
つまり provider target の入力である `HenselLiftStepGeomSumTarget` は、**今回の concrete 証明では使っておらぬ**。
これは論理的には何も悪くない。強い結論が直接示せたなら、仮定を使わずに provider を満たしてよいからの。
ただし設計上は、

* one-step 反復を通じて供給するルート
* 今回見つかった direct concrete ルート

の 2 本がある、ということになる。
もし provenance を厳密に残したいなら、名前やコメントで

* `strongSuperWieferichProvider_concrete_direct`
* `strongSuperWieferichProvider_of_henselGeom`

のように分けてもよい。

## 6. 解説

今回の直証明は、実は very natural じゃ。
Hensel 的 one-step は「局所零点を 1 段ずつ持ち上げる」装置じゃが、今回の FLT 文脈では

$$
GN = y^{p-1}\Phi_p(R)
$$

という **完成済みの cyclotomic 因数分解像** が自然数側にもう見えておる。
そのため、\(y\) が unit で \(q^p \mid GN\) なら、\(\Phi_p(R)=0 \pmod{q^p}\) を直接読める。
つまり one-step は「理論的には正しい補給路」じゃが、この文脈では **橋を渡る前に目的地へ跳べた** のじゃ。
これはむしろ、構造理解が深まった結果じゃよ。

## 7. いま何が本丸か

だから、いまの主戦場はもう明らかじゃ。

**`QAdicDescentExistenceTarget` 側へ集中するべき** じゃ。
Level 1s を通すために準備していた局所 Hensel machinery は、いまや補助理論あるいは再利用可能ライブラリとして価値はある。
されど、FLT 本線のボトルネックではなくなった。
履歴の「次課題」がそのまま正しくて、Level 1s を open と書いているメモ類を更新し、Level 2 へ照準を移すのが筋じゃ。

## 8. 一文でまとめると

**かなり良い。今回の進展で、Level 1s は one-step 反復を経ずとも direct concrete に provider 語彙まで閉じ、FLT 本線の open kernel は実質 `QAdicDescentExistenceTarget` 側へ移った、と見るのが正確じゃ。**

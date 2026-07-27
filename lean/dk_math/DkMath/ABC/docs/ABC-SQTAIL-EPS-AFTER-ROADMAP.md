# ABC sqTail ε: Boss Defeat After Story

cid: 6a674b33-11c0-83ee-b208-3940cc6bd1aa

Post-game analysis / ROADMAP

---

🍷🍎 お疲れさんじゃ。
結論から言えば――

## 第二周回のボス討伐は完了

ただし、**ゲーム全体のエンディングではない**。

今回倒したのは、

> 「ABC の $\varepsilon$ は何なのか」
> 「GN の support・valuation 圧力は、本当に通常の ABC quality へ接続するのか」

という、これまで姿が見えなかった概念ボスじゃ。

PR #71 は正式にマージされ、平方 Tail から固有 `abcEpsilon`、さらに odd-prime joint pressure から通常の quality 上界までの連鎖が統合された。

---

## 今回、完全に閉じたもの

### 1. ABC の整数核

自然数上の完全相殺式、

$$
c\mathrm{rad}(ab)=\mathrm{sqTail}(c)\mathrm{rad}(abc)
$$

によって、ABC の超過量が出力 $c$ の平方 Tail と入力側の radical support の直接会計として固定された。

### 2. $\varepsilon$ の正体

三つ組ごとの固有座標、

$$
\mathrm{abcEpsilon}(T) = \frac{\mathrm{valuationExcess}(c)-\log\mathrm{rad}(ab)}{\log\mathrm{rad}(abc)}
$$

が Lean 定義になった。

そして、

$$
\mathrm{quality}(T) = 1+\mathrm{abcEpsilon}(T)
$$

が exact identity として閉じた。

これは「新しい近似量」ではなく、従来の quality から $1$ を引いた内部座標じゃ。

### 3. 外部 ABC bound との往復

通常の ABC bound、

$$
c\le K\mathrm{rad}(abc)^{1+\varepsilon}
$$

から、

$$
\mathrm{abcEpsilon}(T)\le\varepsilon+\frac{\log K}{\mathrm{radLog}(T)}
$$

が得られた。

さらに $\mathrm{radLog}(T_i)\to+\infty$ なら、任意の $\delta>\varepsilon$ に対して、

$$
\forall^{\infty}i,\qquad\mathrm{quality}(T_i)<1+\delta
$$

まで到達した。

### 4. GN との本接続

最終橋は、

```text
GNOddPrimeJointPressureBudgetAffine
        ↓
ABC natural bound
        ↓
abcEpsilon
        ↓
large-radical asymptotics
        ↓
ordinary quality
```

じゃ。

戦歴文書にも、この接続と全体ビルド成功が固定されている。

---

## では、残る「ひとイベント」とは何か

ある。

だが、これは新しいボス戦ではなく、**討伐後に魔核を回収するイベント**じゃ。

現在の最終橋は一度、

```text
GN joint pressure
→ GNABCConstant を伴う ABC bound
→ abcEpsilon
```

という外周を通っている。

数学的には正しい。しかし、今回見つけた内部構造を最も鮮明に残すには、GN から `abcEpsilon` へ直接入る式を一本固定したい。

文書では既に、その式が見えている。

$$
\mathrm{abcEpsilon}(T)\le\left(\frac{\rho}{p-1}-1\right)+\frac{C+\log\mathrm{rad}(p)}{(p-1)\mathrm{radLog}(T)}
$$

そして GN 側の固有傾きは、

$$
\mathrm{GNEpsilon}(p,\rho) = \frac{\rho}{p-1}-1
$$

じゃ。これは戦歴文書でも「GN 予算の基準次数超過率」として整理されている。

---

## エピローグ実装

小さな新規モジュールを一つ置くのがよい。

```text
DkMath.ABC.ABCEpsilonSlopeBridge
```

### Event 1 — GN 固有 epsilon

```lean
noncomputable def GNEpsilon
    (p : ℕ) (ρ : ℝ) : ℝ :=
  ρ / ((p - 1 : ℕ) : ℝ) - 1
```

### Event 2 — margin の正体

現在の条件、

```lean
ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε)
```

を、

```lean
GNEpsilon p ρ ≤ ε
```

へ言い換える。

候補 theorem：

```lean
theorem GNEpsilon_le_iff_margin
    {p : ℕ} (hp : 2 ≤ p) (ρ ε : ℝ) :
    GNEpsilon p ρ ≤ ε ↔
      ρ ≤ ((p - 1 : ℕ) : ℝ) * (1 + ε)
```

### Event 3 — GN から固有 epsilon への直接評価

```lean
theorem Triple.abcEpsilon_le_GNEpsilon_add_correction
    (T : Triple) {p : ℕ} {ρ C : ℝ}
    (hp : Nat.Prime p)
    (hpOdd : Odd p)
    (ha : 0 < T.a)
    (hb : 0 < T.b)
    (hjoint :
      GNOddPrimeJointPressureBudgetAffine T p ρ C) :
    T.abcEpsilon ≤
      GNEpsilon p ρ +
        (C + Real.log (rad p : ℝ)) /
          (((p - 1 : ℕ) : ℝ) * T.radLog)
```

これが入れば、

```text
external ε
GN budget slope
Triple intrinsic ε
ordinary quality
```

の四者が、完全に同じ座標系へ並ぶ。

### Event 4 — 漸近版

最後に、

```lean
eventually_abcEpsilon_lt_of_oddPrime_jointPressure
```

を直接 slope 版から出す。

これは既存の `eventually_quality_lt_one_add_of_oddPrime_jointPressure` と数学的結論は近いが、内部構造が可視化される。

---

## これで第二周回は閉幕

構成はこうなる。

```text
第二周回・本編
────────────────────────
SquareTail exact identity
abcGap
valuationExcess
intrinsic abcEpsilon
quality identity
GN joint-pressure bridge
PR #71 merge
────────────────────────
討伐完了
```

その後に、

```text
エピローグ
────────────────────────
GNEpsilon の定義
margin の言い換え
GN → abcEpsilon 直接不等式
最終ドキュメント整理
────────────────────────
第二周回 完全終了
```

じゃ。

---

## その次に始まるのが第三周回

ここから先は別物じゃ。

uniform joint-pressure contract をそのまま構築することは、既に raw ABC と同値だと監査されている。したがって、そこへ正面突撃しても敵の名前を変えただけになる。

本当の次ボスは、

```text
高い intrinsic abcEpsilon
        ↓
必要な GN joint pressure
        ↓
fresh support / repeated support / deep lift
        ↓
どの構造がその圧力を支払うのか
```

を pointwise に追い詰めること。

候補ルートは以前から残っている三つじゃ。

```text
1. large-Wieferich / repeated-tail compensation
2. fresh moving probe
3. finite-orbit escape / well-founded descent
```

これは第三周回、あるいは真ラスボス戦になる。

---

## Branch 方針

ブラッシュアップの統合先は、お主の言う通り、

```text
feature/ABC-GN-valuation-excess-260724-v0
```

でよい。

ただし運用としては分けるのがおすすめじゃ。

```text
小さな名前・docstring・import 整理
→ feature 上で直接でもよい

GNEpsilon と直接 bridge の追加
→ feature から短い子 branch を発行
```

推奨 branch：

```text
wip/ABC-GN-epsilon-epilogue-260728-v0
```

そして小さな PR 一本で feature に戻す。

---

## 現在地を一言で言えば

> **第二形態のボスは倒れた。正体不明だった $\varepsilon$ の魔核を回収し、GN と ABC の世界線も接続した。**

残る一イベントは、その魔核に正式な名前 `GNEpsilon` を与え、直接評価式として祭壇へ納めること。

それが終われば、第二周回は完全終了。
次は「接続できるか」ではなく、**その圧力を算術的に必ず支払わせられるか**という真ボス戦じゃ。

---

## ３周目の勝算は？

うむ。**攻略の全体図は見えている。だが、最後まで通る一本の証明路が完成したわけではない。**

そして三ルートは、本当は競合する三択ではない。

```text
large-Wieferich / repeated-tail
        ↓ 敵の質量を分解する

fresh moving probe
        ↓ 同じ悪因子を再利用させない

finite escape / descent
        ↓ 悪状態を永久維持できないと閉じる
```

この三段術式として合流するのが、現在もっとも有力じゃ。

# いま既にある土台

large branch は、もはや「誤差」ではない。

Lean 上では、その modulus が非例外 GN 部分の完全な repeated prime-power part であり、

$$
\mathrm{RepeatedPart} = \mathrm{piSqRad}\cdot\mathrm{sqTail} = \mathrm{piSqRad}^2\cdot\mathrm{twoTail}
$$

と分解される。さらに各素因子 $q$ は二乗以上で入り、$q\bmod p=1$ を満たす。

large なら必ず、

$$
\frac14\log(X+1)<\log\mathrm{piSqRad}
$$

または、

$$
\frac12\log(X+1)<\log\mathrm{twoTail}
$$

のどちらかへ落ちる。

しかも repeated support は、正確に non-exceptional GN-Wieferich primes の集合であり、repeated part はそれらの完全素数冪積になっている。

つまり敵は完全に二種類へ分かれた。

```text
A. 異なる repeated prime が大量・巨大
   = repeated-support shell heavy

B. 同じ prime の valuation が深すぎる
   = deep twoTail / Wieferich heavy
```

ここまでは討伐済みじゃ。

## 1. large-Wieferich / repeated-tail compensation

これは最も準備が進んでいる。

### A. repeated-support shell が重い場合

$\mathrm{piSqRad}$ は、重複している**異なる素数を一度ずつ**掛けたもの。

したがって大きい理由は、

```text
・非常に大きい素数が存在する
または
・多くの異なる素数が存在する
```

のどちらかじゃ。

前者なら、その大きな素数の $\log q$ 自体が fresh support の支払いになる。

後者なら、有限 Euler 積・半冪 majorant・address charge の対象になる。既存キャンペーンで $q^{-3/2}$ 型の総和可能 envelope まで構築したのは、まさにこちらの枝を有限予算化するためじゃ。

### B. twoTail が重い場合

`twoTail` は三個目以降の素因子コピー。

ここでは単なる repeated support ではなく、

$$
v_q(GN)\ge3
$$

のような深い lift が必要になる。

これは `GNWieferichLift` の強化形であり、差の素数冪可除性へ戻せる。

したがって次の候補は、

```text
deep lift
→ 次の probe では valuation が落ちる
または
→ さらに強い合同条件を消費する
```

という descent lemma じゃ。

### このルートの未完成点

large であることから、

```text
ABC の固有 ε の負債を
repeated support または deep lift が
定量的に支払う
```

という **pointwise compensation inequality** がまだない。

敵の所持金は数え終わった。
だが、その所持金を強制徴収する theorem が未完成、という状況じゃ。

## 2. fresh moving probe

ここは以前よりかなり具体的に見えてきた。

最も有力なのは、$a,b,c$ を動かすのではなく、**補助指数 $p$ を動かす exponent probe** じゃ。

ABC 三つ組 $T$ は固定したまま、

```text
GN 3 a b
GN 5 a b
GN 7 a b
GN 11 a b
...
```

と見る。

非例外 support prime は、

$$
q\equiv1\pmod p
$$

を満たす。

したがって、ある probe $p$ で現れた有限集合 $Q$ に対して、十分大きな次の素数指数 $p'$ を選べば、

$$
p'>\max Q
$$

なので、古い $q\in Q$ は $q\equiv1\pmod{p'}$ を満たせない。

つまり、

> **古い repeated / Wieferich primes を、次の指数宇宙でそのまま再利用できない**

という freshness が得られる。

さらに強く、おそらく次の theorem が狙える。

```lean
theorem GNNonExceptionalSupport_disjoint_of_prime_ne
    {p r a b : ℕ}
    (hp : Nat.Prime p)
    (hr : Nat.Prime r)
    (hpr : p ≠ r)
    (hcop : Nat.Coprime a b) :
    Disjoint
      (GNNonExceptionalSupport p a b)
      (GNNonExceptionalSupport r a b)
```

理由は、同じ $q$ が両方に入れば、適切な比の mod $q$ における乗法位数が同時に $p$ と $r$ になってしまうからじゃ。

これはまだ現行 theorem ではない。だが既存の order-prime、boundary 排除、`q % p = 1` の API から見て、**かなり現実的な次 checkpoint** じゃ。

### このルートの本当の意味

moving probe は、敵を直接倒さない。

```text
同じ prime を何度も使って
valuation excess を水増しする
```

という悪い戦略を禁止する。

各 probe ごとに新しい素数を要求できれば、悪状態を維持するたびに fresh support が増える。

これは DkMath の「有限素数宇宙間リンク」と完全に同じ思想じゃ。

### 未完成点

新しい support prime は `GN p a b` の素因子であり、直接 `rad(abc)` の素因子ではない。

したがって、

```text
GN 側で fresh support が増えた
        ↓
元の ABC triple の intrinsic ε が下がる
```

という **return / projection theorem** が必要になる。

今回作った `ABCEpsilonJointPressureBridge` は、この return の最終出口を用意した。

残るのは、moving probe が実際に良い joint-pressure budget を一つ生むことの証明じゃ。

## 3. finite-orbit escape / well-founded descent

これは最終包装層じゃ。

単独で開始するルートではない。

まず moving probe の遷移を作る。

```text
BadState(p,Q,depth)
       ↓ next probe
BadState(p',Q',depth')
```

その遷移について、次のどれかを証明する。

```text
1. fresh support が増える
2. repeated set が入れ替わる
3. valuation depth が下がる
4. 有限な potential を消費する
```

そして、悪状態が永久に続くなら、

```text
同じ有限状態へ戻る
または
有限予算を無限に消費する
```

ことを導く。

前者なら cycle exclusion。

後者なら summability contradiction。

### 重要な点

自然数値の単純な下降量がまだ見えていない。

実際には、

```text
max prime
```

は probe ごとに大きくなる可能性があるので、これは下降しない。

代わりに有力なのは、**重み付き potential** じゃ。

例えば概念的には、

$$
\Phi(Q)=\sum_{q\in Q}q^{-3/2}
$$

のような有限資源。

probe 間で support が disjoint なら、悪い probe が要求する charge を足し続けても、Euler 総和の有限値を超えられない。

ただし large modulus が一個の巨大素数だけで作られると $q^{-3/2}$ は小さい。

そこで先ほどの二分が効く。

```text
巨大な q
→ log q が直接 compensation

多数の中小 q
→ Euler potential を消費

深い q-adic valuation
→ twoTail descent
```

これで三ルートが一つになる。

## 想定する最終攻略図

```text
高い intrinsic abcEpsilon を仮定
        ↓
各 prime exponent probe で
大きな joint pressure が必要
        ↓
small / large profile split
        ↓
small branch
→ 既存 Chernoff / Euler majorant

large branch
→ repeated-support shell heavy
   または deep-twoTail heavy
        ↓
probe を移動
        ↓
古い Wieferich primes は再利用不可
        ↓
fresh support 増加
または valuation depth 減少
または有限 Euler potential 消費
        ↓
有限回で悪状態から escape
        ↓
ある probe で良い joint-pressure margin
        ↓
既存 ABCEpsilonJointPressureBridge
        ↓
quality < 1 + δ
```

## 現在の勝算評価

### large-Wieferich の解析

**高い。**

敵の正体、積構造、二分岐、Wieferich 解釈まで Lean 化済み。

### fresh moving probe

**中高。**

特に「異なる prime exponent の nonexceptional support は重ならない」という order ベースの補題は、具体的で実装可能性が高い。

ただし、それだけでは ABC は閉じない。freshness を joint-pressure の改善へ定量化する必要がある。

### finite-orbit / descent

**中。**

最終論理構造は見えているが、遷移と potential がまだ定義されていない。

これは最初に手を出すのではなく、1・2 の theorem が揃ってから組むべきじゃ。

## まず突撃すべき checkpoint

最初の新 branch の勝利条件は、これ一つがよい。

```text
異なる odd prime exponent 間で
non-exceptional GN support が fresh になる
```

候補モジュール：

```text
DkMath.ABC.GNPrimeExponentSupportEscape
```

候補 API：

```lean
theorem primeExponent_order_unique
theorem GNNonExceptionalSupport_disjoint_of_prime_ne
theorem GNNonExceptionalWieferichPrimeSet_disjoint_of_prime_ne
theorem pairwise_disjoint_support_over_prime_family
theorem log_support_product_eq_sum_over_prime_family
```

ここが通れば、「fresh moving probe」は構想から Lean 事実へ昇格する。

その後、

```text
large-Wieferich packet
+
pairwise fresh exponent probes
+
finite weighted budget
```

を合流させる。

したがって答えは――

> **完全な勝利証明まではまだ見えていない。だが、次に何を証明すれば盤面が進むかは、かなり明瞭になった。**

前回までは敵が「large boundary」としか見えていなかった。

今は、

```text
repeated support
deep valuation
Wieferich lift
probe 間の再利用
有限 charge
```

という部品へ分解できている。

真の未発見魔法はただ一つ。

> **悪い Wieferich 質量を、moving probe によって fresh support または有限 descent charge へ必ず交換する theorem**

これが見つかれば、三ルートは一本の攻略路になるぞい。

# review Phase "R" 2nd / Closed View Point

うむ、 **この山としては完了** じゃ。
R028 で公開導線まで整ったので、R021-R028 は「実装・証明・入口整理」まで含めて一区切り、いや、登頂成功と言ってよい。

資料上でも、R/log 版は「重複なし」ではなく **重複あり finite log route まで Lean 上で通っている** と更新され、推奨 theorem は `PrimePowerWitnessProvider.basePrimeOf_logRatioSubProbability` と明示されておる。さらに仮定は `I ⊆ T.index n` と `1 < n` のみで、外部 multiplicity-budget 仮定なしに `SubProbability` が出る、と整理されておる。

## 1. 何が「完了」したのか

今回完了したのは、次の有限 log 質量制御じゃ。

$$
q\in I,\quad q\mid n,\quad q=p(q)^{k(q)}
$$

と witness provider が読むとき、

$$
w(q):=\frac{\log p(q)}{\log n}
$$

は

$$
\sum_{q\in I}w(q)\le 1
$$

を満たす。

しかも、同じ base prime $p$ が何度出てもよい。
同じ $p$ を持つ labels は exponent slot

$$
1,2,\dots,n.\mathrm{factorization}(p)
$$

へ単射で入るので、

$$
\#{q\in I\mid p(q)=p}\le n.\mathrm{factorization}(p)
$$

が自動生成される。README 側にもこの説明が反映されておる。

つまり、これまで外部仮定だった「重複管理」が消えた。
これが大きい。

## 2. 山頂から見える景色

山頂から見える世界は、こうじゃ。

これまで素数の世界は「互いに異なる素数を選ぶ」ことで重複を避けていた。
ところが今は、重複を避ける必要がなくなった。

同じ素数 $p$ が何度も現れても、それは混乱ではない。
それは

$$
p^1,\ p^2,\ p^3,\dots
$$

という同一 prime channel 上の **指数スロット** に並ぶだけじゃ。

この見方に変わると、divisor transition の世界はこう見える。

$$
n=\prod_p p^{v_p(n)}
$$

という山塊があり、各素数 $p$ ごとに高さ $v_p(n)$ の縦穴がある。
selected label $q=p^k$ は、その縦穴の $k$ 番目の棚に置かれる。
同じ棚に二つの label は置けない。だから各 prime channel の占有数は、その高さを超えない。

そして全ての棚を log 質量で測ると、

$$
\sum_{q\in I}\log p(q)\le \log n
$$

になる。
さらに $\log n$ で割れば、全体質量は 1 を超えない。

これが山頂の景色じゃ。
**整数 $n$ の素因数分解が、有限な確率質量空間として見える。**

## 3. R021-R028 の意味

資料でも R021-R027 の鎖は、

```text
q = p(q)^k(q)
same-base-prime labels inject into exponent slots
-> NatBaseMultiplicityBudgetOn I (W.basePrimeOf n I hI) n
-> ∏ q in I, W.basePrimeOf n I hI q ∣ n
-> ∏ q in I, W.basePrimeOf n I hI q ≤ n
-> Σ log(basePrime(q)) ≤ log n
-> Σ log(basePrime(q)) / log n ≤ 1
-> SubProbability
```

として図式化されておる。

これは単なる整理ではない。
DkMath の #1196 route において、

$$
\text{prime-power divisor witness}
\Longrightarrow
\text{finite log sub-probability}
$$

という核が Lean 上で no-sorry になった、ということじゃ。

しかも R028 では、PrimitiveSet の aggregator doc も「prime-power divisor witnesses から real/log `SubProbability` へ進む repeated-base valuation-budget route を含む」と更新され、ビルド成功・`sorry/admit/axiom` no hits も記録されておる。

## 4. まだ「全研究」が完了したわけではない

ただし、賢狼として正直に言うぞ。

**Erdős #1196 全体の Lean 形式化が完了した、という意味ではまだない。**

完了したのは、有限 divisor witness から log 質量が 1 を超えないことを出す **有限 R/log sub-probability bridge** じゃ。

まだ残る高い山はある。

* 上位 finite/log API から、この theorem をどう標準入口として呼ぶか。
* tail / asymptotic 側、つまり $1+o(1)$ や $1+O(1/\log x)$ にどう接続するか。
* primitive set の antichain / hitting mass 側と、この finite witness route をどう合流させるか。
* 証明物語として、DkMath 内でどの theorem を「外向き定理」として立てるか。

資料上でも、次の課題として「上位 finite/log API から `basePrimeOf_logRatioSubProbability` をどう呼ぶか」が明記されておる。

だから、山頂は一つ登った。
しかし連峰全体はまだ続く。

## 5. 山頂の一言

この成果の本質は、

$$
\text{割り切り構造}
$$

を

$$
\text{log 質量の保存則}
$$

へ変換したことじゃ。

しかも今回は、重複を排除するのではなく、重複を指数スロットとして吸収した。
これにより、有限 prime-power divisor world は、きれいな sub-probability space として見えるようになった。

わっちの評価はこうじゃ。

**R/log 重複あり finite route は完了。公開導線も完了。数学的にも Lean 実装的にも一区切り。**

次の景色は、山頂から見える **流域** じゃな。
この有限 sub-probability を、primitive set の hitting mass、tail estimate、そして最終的な Erdős #1196 型の上界へどう流すか。
そこが次の旅路じゃ。

りんご酒でも開けたいほどの登頂じゃよ、ぬしよ。

---

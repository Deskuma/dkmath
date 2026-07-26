# Note: Review: Ultra-001-M/N

## Ultra-001M/N 総合判定

**両 checkpoint、全面採用。攻め込みは明確に成功している。** ⚔️🧙‍♀️✨️

PR #69 は最新 head `362e3aa788ae4632dc3700b154594538c2f3e293`、15 commits、29 files、7479 additions、mergeable。

Lean CI run 385 も `completed / success` じゃ。✔

### U-001M：M3 の密度項が最終形へ到達した

今回の決定的前進は、valuation 全体ではなく excess、

$$\bigl(v_q(GN_p(a,b))-1\bigr)_+$$

だけを第2層以後で数えたことじゃ。

その結果、密度項が、

$$\frac{X+1}{q(q-1)}$$

まで落ちた。

第1層から始めた場合は $1/(q-1)$ だが、第2層から始めることで $1/q$ がさらに一つ付く。

```text id="vm2e8p"
support 第1層      1 / q
excess 第2層以後   1 / q²
```

この差は本質的じゃ。

`sum_padicValNat_pred_GN_le_of_simpleRoot` は、固定 $q$ について、

$$\sum_{a=0}^{X}\bigl(v_q(GN_p(a,b))-1\bigr)_+\le(p-1)\left(\frac{X+1}{q(q-1)}+\log_q!\left(p(X+b)^p\right)-1\right)$$

を与える。さらに区間中に現れる全非例外素数を `GNNonExceptionalIntervalPrimeFamily` として canonical に集約し、有限素数族を外から選ぶ義務も一段消した。

これは **M3 の平均密度部分**について、ほぼ最終形じゃ。

### U-001N：「bad points は少ない」が theorem になった

```lean id="8xvljc"
GNDepthMassAt
GNDepthMassBadSet
card_GNDepthMassBadSet_le
```

によって、

```text id="km2wy6"
大きな weighted GN depth を持つ座標
```

が有限集合として取り出され、その個数が Markov 型に明示評価された。

したがって現在は、

```text id="kxz0bs"
bad set が小さいように見える
```

ではなく、

```text id="yhdovs"
正の threshold λ に対して
card badSet ≤ explicit average / λ
```

が Lean の事実になった。

ここまでの流れは完全に正しい。

---

## 最大推論：裏ボスの攻略条件を再評価

ここで重要な方向転換が見える。

これまで、

```text id="808p00"
指定された ABC coordinate を
必ず bad set の外へ脱出させる
```

という pointwise probe を考えていた。

もちろんそれが証明できれば強い。

しかし ABC の最終形に必要なのは、**すべての triple が直接 good であることではない。**

各 $\varepsilon>0$ に対して、例外が有限個しかなければ、それらは最終定数 $K_\varepsilon$ に吸収できる。

したがって本当に必要なのは、

```text id="gbp8x5"
すべての target を直ちに脱出させる
```

だけではなく、

```text id="7qhwhq"
高い joint mass を持つ ABC triple は
全体として有限個しか存在しない
```

でもよい。

これは重大な違いじゃ。

### Markov だけではまだ弱い

現在の bad-set theorem は第一モーメントから、

$$\#\operatorname{Bad}(\lambda)\le\frac{\sum M(a)}{\lambda}$$

を出している。

これは密度ゼロへ進めるには有用だが、有限例外を導くには通常まだ弱い。

閾値を $\lambda\asymp\log X$ としても、概ね $1/\log X$ 型の減衰にしかならず、dyadic block 全体で総和可能になる保証がない。

したがって次の武器は、さらに強い、

```text id="7flh4r"
exponential moment
Chernoff tail
Borel–Cantelli / finite-exception absorption
```

じゃ。

旧 `exp_layer_cake` を復旧した意味が、ここで本格的に現れる。

---

## 次の真の魔核：複数素数を同時に数える

現在の theorem は、各 $q$ を個別に評価してから和を取っている。

しかし Hensel 一意性は、複数の異なる素数について CRT と合成できる。

有限素数族 $Q$ と深度 profile $k_q$ に対し、

$$M=\prod_{q\in Q}q^{k_q}$$

と置く。

条件、

$$q^{k_q}\mid GN_p(a,b)\qquad(q\in Q)$$

を同時に満たす $a\bmod M$ の住所数は、各 $q$ について高々 $p-1$ 個なので、CRT により高々、

$$(p-1)^{|Q|}$$

個になるはずじゃ。

したがって区間上では、

$$\#\left\{a\le X:\forall q\in Q,\ q^{k_q}\mid GN_p(a,b)\right\}\le(p-1)^{|Q|}\left(\frac{X+1}{M}+1\right)$$

を狙える。

これは単一素数 Markov より桁違いに強い。

```text id="mnhyd8"
各 q の bad event を足す
```

のではなく、

```text id="ldfuqg"
複数 q の deep event を
一つの巨大 modulus M へ圧縮する
```

からじゃ。

各 layer に残っていた `+1` も、素数ごとに別々に請求されるのではなく、**合同 profile 全体に一つ**へまとめられる。

---

## M3 は exponential tail まで閉じる可能性が高い

excess は $k\ge2$ から始まる。

固定 $q$ における深度 $k$ の密度は概ね、

$$\frac{p-1}{q^k}$$

以下。

excess mass に対して指数重み $e^{t(k-1)\log q}=q^{t(k-1)}$ を掛けると、局所寄与は概ね、

$$\sum_{k\ge2}\frac{q^{t(k-1)}}{q^k}$$

となる。

これは、

$$O!\left(q^{t-2}\right)$$

じゃ。

$0<t<1$ なら指数 $2-t>1$ なので、全素数にわたる majorant が収束可能になる。

つまり、形式化すべき予想形は、

$$\sum_{a\le X}\exp!\left(t,\operatorname{GNExcessMassAt}(a)\right)\le C_{p,t}(X+1)+\text{finite boundary}$$

そして Chernoff により、

$$\#\{a\le X:E(a)>\lambda\}\le C_{p,t}(X+1)e^{-t\lambda}$$

となる。

これは Markov の $1/\lambda$ ではなく、**指数減衰 $e^{-t\lambda}$** じゃ。

この形まで行けば、dyadic block 上で summable tail を作り、M3-heavy triple を有限例外へ押し込める可能性が出る。

### ここで M2 と M3 が再び分離する

support は第1層から始まるため、同じ計算の局所因子は $q^{t-1}$ 型になる。

excess の $q^{t-2}$ と違い、bare support には全素数を一様に合計できる余分な $1/q$ がない。

したがって、現在の戦況はさらに鋭く言える。

```text id="hdbm4w"
M3 multiplicity
  Hensel + CRT + exponential layer-cake
  で有限例外化できる可能性が高い

M2 fresh support
  同じ方法だけでは収束因子が不足
  真の最終魔核候補
```

**裏ボスは再び二体に見えたが、M3 はもう瀕死じゃ。M2 が本体である可能性が高まった。**

---

## 次 checkpoint の最短設計

### U-001O：pointwise mass の exact decomposition

現在の `GNDepthMassAt` は full valuation、`GNExcessMassAt` は excess を表す。

ここに support mass を追加する。

```lean id="29jz67"
noncomputable def GNSupportMassAt
    (Q : Finset ℕ) (p b a : ℕ) : ℝ :=
  ∑ q ∈ Q.filter (fun q => q ∣ GN p a b),
    Real.log (q : ℝ)
```

そして exact に、

```lean id="6b6vsn"
theorem GNDepthMassAt_eq_support_add_excess
    ...
    GNDepthMassAt Q p b a =
      GNSupportMassAt Q p b a +
      GNExcessMassAt Q p b a
```

を証明する。

さらに coprime target $a,b$ と $a\le X$ に対して、

```lean id="wl068q"
theorem GNDepthMassAt_intervalFamily_eq_log_nonExceptionalPart
```

$$\operatorname{GNDepthMassAt}(Q,p,b,a)=\log\operatorname{GNNonExceptionalPart}(p,a,b)$$

を狙う。

これが通れば、

```text id="h8hfzj"
bad-set mass
  =
現行 joint pressure の S + E
```

が exact に接続される。

### U-001P：CRT joint-depth residues

```lean id="2c1p4h"
def GNJointDepthModulus
def GNJointDepthResidues
```

を作り、

```lean id="n7aaj6"
theorem card_GNJointDepthResidues_le
```

$$\#\operatorname{JointRoots}\le(p-1)^{|Q|}$$

および、

```lean id="1nqkgv"
theorem card_gn_joint_deep_lift_interval_le
```

$$\#\operatorname{JointEvent}\le(p-1)^{|Q|}\left(\frac{X+1}{M}+1\right)$$

を閉じる。

証明の中心は、

```text id="a0euvb"
canonical root mod M
  → 各 q^k root の直積
```

の単射じゃ。

各 component の cardinality bound は Ultra-001K で既に完成している。

### U-001Q：excess exponential tail

CRT theorem を使い、

```lean id="btnufg"
theorem exp_GNExcessMassAt_sum_le
theorem card_GNExcessMassBadSet_le_exp
```

へ進む。

ここで初めて M3-heavy の有限例外化が見える。

---

## 注意：canonical interval family の役割

`GNNonExceptionalIntervalPrimeFamily` は非常に良い。

ただしこれは、

```text id="2vyb4t"
区間中に出る全 prime を先に有限集合へ固定する
```

ための container であり、pointwise support を直接抑えるものではない。

その真価は、CRT profile と exponential product を **有限 Lean オブジェクト**として構築できる点にある。

無限 Euler product を最初から扱う必要はない。

```text id="edhijc"
有限 X
  ↓
有限 prime family Q_X
  ↓
有限 CRT / finite product bound
  ↓
X に依存しない定数へ解析的に majorize
```

という順がよい。

---

## 最終戦況

```text id="bgslkt"
U-001M
  q-sensitive excess density       complete
  canonical interval family        complete

U-001N
  weighted depth mass              complete
  Markov bad set                   complete

next
  exact S + E mass decomposition
  CRT simultaneous deep addresses
  exponential excess moment
  summable M3-heavy exceptions

remaining core
  fresh-support M2 compensation
  uniform joint contract
  abc_main axiom replacement
```

**攻め込み成功は本物じゃ。**

以前の裏ボスは、

```text id="qa55yb"
平均から指定点をどう救うか
```

という霧だった。

現在は、

```text id="8zpb59"
M3 は CRT と指数モーメントで有限例外化できるか
M2 の第一層 support を何が支払うか
```

という二つの明確な定理問題へ分解された。

🧙‍♀️✨️ **次は Markov の槍を置き、CRT–Chernoff の広域殲滅魔法へ切り替える時じゃ。**

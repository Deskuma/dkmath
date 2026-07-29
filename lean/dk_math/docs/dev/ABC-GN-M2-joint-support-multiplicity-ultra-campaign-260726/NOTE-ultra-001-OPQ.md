# Note: Review: Ultra-001-O/P/Q

## Ultra-001O/P/Q 総合判定

**全面採用。Codex、有限戦線を本当にQまで押し切った。** ⚔️🐺✨️

PR #69 は最新 head `a9f91751603834649a13a898f3ecb3eb55d0b1c3`、17 commits、34 files、8930 additions、mergeable。

Lean CI run 386 も `completed / success` じゃ。✔

添付された O/P/Q の成果と停止境界も正確じゃ。

### O：平均側と現行 joint pressure が同じ量になった

```lean
GNDepthMassAt_eq_support_add_excess
```

により、

$$\operatorname{DepthMass}=S+E$$

が pointwise exact identity になった。

さらに canonical interval family 上で、

$$\operatorname{GNDepthMassAt}=\log\operatorname{GNNonExceptionalPart}$$

まで接続された。

これで、

```text
旧平均・bad-set 戦線の mass
現行 joint contract の S+E
非例外 GN part の log
```

は、別の近似量ではなく同一物になった。

これは巨大な接続じゃ。

### P：複数 prime の深度を一つの住所へ束ねた

深度 profile $k_q$ に対し、

$$M=\prod_{q\in Q}q^{k_q}$$

を構成し、CRT によって、

$$\#\operatorname{JointRoots}\le(p-1)^{|Q|}$$

および、

$$\#\operatorname{JointEvent}\le(p-1)^{|Q|}\left(\frac{X+1}{M}+1\right)$$

まで閉じた。

単独の $q^k$ 住所を数えてから足し合わせるのではなく、複数条件を一つの巨大 modulus へ圧縮できた。

### Q：valuation vector を exact fiber に分解した

各点 $a$ を valuation profile へ送って、区間全体を exact fiber に分割し、各 fiber に P の CRT count を代入した。

したがって、

$$\sum_{a=0}^{X}\exp!\left(tE_Q(a)\right)$$

が、有限 profile sum で明示的に上から押さえられた。

Chernoff endpoint も正しい。

現在の停止点は、まさに report のいう、

```text
finite profile sum
  ↓
X-independent analytic majorant
```

じゃ。

---

## 最大推論：解析へ行く前に、profile をもう一度圧縮すべき

現在の profile は full valuation、

$$v_q\in{0,1,2,\dots}$$

を記録している。

しかし exponential moment の対象は excess、

$$e_q=(v_q-1)_+$$

じゃ。

ここで、

```text
v_q = 0
v_q = 1
```

はどちらも、

```text
e_q = 0
```

になる。

ところが現在の profile sum では、深度0と深度1を別 profile として数え、さらに `card_GNJointDepthResidues_le` は深度0の prime にも概略 $(p-1)$ を請求している。

定理は正しい。だが、解析上は大きく過剰じゃ。

```text
excess を全く持たない prime
```

まで joint-address factor に含めると、$Q$ が増えるにつれて、

$$(p-1)^{|Q|}$$

が不要に膨張する。

したがって、次は full depth profile ではなく、**excess-active profile** へ移るべきじゃ。

### Excess-active profile

各 $q$ について、

$$e_q=(v_q-1)_+$$

だけを記録する。

* $e_q=0$：何も制約しない
* $e_q>0$：$q^{e_q+1}\mid GN$

active prime 集合を、

$$A(e)={q\in Q:0<e_q}$$

と置く。

joint modulus は、

$$M(e)=\prod_{q\in A(e)}q^{e_q+1}$$

住所数は、

$$\#\operatorname{Roots}(e)\le(p-1)^{|A(e)|}$$

となるべきじゃ。

現在の $(p-1)^{|Q|}$ ではなく、**実際に excess を持つ prime だけが費用を払う。**

これは解析前に必須の正規化じゃ。

---

## `+1` の正体も二分できる

現在の CRT count は、

$$\left\lfloor\frac{X+1}{M}\right\rfloor+1$$

を含む。

$N=X+1$ と置き、profile を二種類に分ける。

### Small modulus profile

$$M\le N$$

なら $N/M\ge1$ なので、

$$\left\lfloor\frac{N}{M}\right\rfloor+1\le2\frac{N}{M}$$

とできる。

したがって small profile の全寄与は、

$$2N\sum_e\frac{(p-1)^{|A(e)|}\exp(tE(e))}{M(e)}$$

へ落ちる。

この和は各 prime の局所因子へ積分解できる。

$$\sum_e\frac{(p-1)^{|A(e)|}\exp(tE(e))}{M(e)}=\prod_{q\in Q}\left(1+\sum_{j\ge1}\frac{(p-1)\exp(tj\log q)}{q^{j+1}}\right)$$

有限 profile space なら有限積・有限和として Lean で exact に証明できる。

これが本当の Euler-product 型入口じゃ。

### Large modulus profile

$$N<M$$

の場合は、区間内に各 residue address が高々一度しか現れない。

この `+1` は単なる解析誤差ではない。

profile modulus の log は、

$$\log M=\sum_{q\in A(e)}(e_q+1)\log q$$

ゆえに、

$$\log M=E(e)+S_{\mathrm{active}}(e)$$

となる。

したがって $N<M$ なら、

$$\log N<E(e)+S_{\mathrm{active}}(e)$$

じゃ。

つまり large-modulus boundary は、

> **M3 excess 単独の障害ではなく、support と excess の joint pressure が区間スケールを超えた証明書**

なのじゃ。

ここは重要な戦況修正になる。

```text
small modulus
  → M3 density / Euler product で処理可能

large modulus
  → S + E joint boundary packet
```

よって、M3だけを解析的に完全消滅させようとすると、large-modulus branch で必ず M2 が戻ってくる。

**M2/M3 は密度領域では分離できるが、境界領域では再結合する。**

---

## 次 checkpoint：U-001R

次は一気に無限級数へ行かず、有限 Lean 層でこの分解を確定させるのが最短じゃ。

```text
U-001R
Excess-active profiles and small/large modulus split
```

狙う主定義：

```lean
GNExcessDepthProfileAt
GNExcessDepthProfileSpace
GNExcessActivePrimeSet
GNExcessProfileExtension
GNExcessJointDepthModulus
GNExactExcessProfileEvent
GNExcessSmallProfileSpace
GNExcessLargeProfileSpace
```

狙う主定理：

```lean
GNExactExcessProfileEvent_subset_joint

card_GNExactExcessProfileEvent_le

exp_GNExcessMassAt_sum_le_small_add_large

sum_GNExcessProfileDensityWeight_eq_prod

GNExcessLargeProfile_jointMass_gt_log_interval
```

核心 theorem の形はこれじゃ。

```lean
theorem exp_GNExcessMassAt_sum_le_small_add_large
    ... :
    ∑ a ∈ Finset.Icc 0 X,
        Real.exp (t * GNExcessMassAt Q p b a)
      ≤
    2 * (X + 1) *
        GNExcessFiniteEulerDensity Q p b X t
      +
    GNExcessLargeBoundaryProfileSum Q p b X t
```

small 側は Euler density。

large 側は明示的 boundary packet として残す。

そして、

```lean
theorem GNExcessLargeProfile_jointMass_gt_log_interval
```

で、

$$X+1<M(e)\Longrightarrow\log(X+1)<S_{\mathrm{active}}(e)+E(e)$$

を固定する。

---

## U-001R の次：U-001S

R が閉じた後、small profile の有限 Euler product を一様定数へ落とす。

$0<t<1$ なら局所項は概ね、

$$\sum_{j\ge1}\frac{(p-1)q^{tj}}{q^{j+1}}=O!\left(\frac{1}{q^{2-t}}\right)$$

じゃ。

$2-t>1$ なので、全自然数上の $p$-series で majorize できる。

素数専用の高度な解析を使わず、

$$\sum_{q\in Q}\frac{1}{q^{2-t}}\le\sum_{n=1}^{\infty}\frac{1}{n^{2-t}}$$

とすればよい。

さらに、

$$1+x\le e^x$$

を有限積へ適用し、

$$\prod_{q\in Q}(1+x_q)\le\exp\left(\sum_{q\in Q}x_q\right)\le C_{p,t}$$

を得る。

この small-profile density constant は $Q$ と $X$ に依存しない。

ただし最初は任意 $t$ を狙わず、**$t=1/2$ 固定**でもよい。

Chernoff tail には正の一つの $t$ があれば十分だからじゃ。

---

## Codex 次指示

```text
Continue Ultra-001 with checkpoint U-001R.

Goal:
Replace the current full valuation-profile accounting by an excess-active
profile accounting, then split the finite CRT exponential profile sum into
small-modulus density profiles and large-modulus boundary profiles.

Do not attempt the infinite analytic majorant yet.

Required work:

1. Define the excess profile
   e_q := padicValNat q (GN p a b) - 1.

2. Define the active prime set
   A(e) := {q ∈ Q | 0 < e_q}.

3. Define the active joint modulus
   M(e) := ∏ q ∈ A(e), q^(e_q + 1).

4. Define exact excess-profile fibers and prove that each fiber is contained
   in the corresponding simultaneous divisibility event.

5. Improve the CRT cardinality charge from
   (p - 1)^Q.card
   to
   (p - 1)^(A(e).card).

6. Split profiles into:
   - small: M(e) ≤ X + 1
   - large: X + 1 < M(e)

7. For small profiles prove:
   floor((X + 1) / M(e)) + 1 ≤ 2 * (X + 1) / M(e)
   in an appropriate Nat/Real form.

8. Package the moment bound as:
   interval moment
     ≤ small density contribution
       + large boundary contribution.

9. Factor the unrestricted finite small-density profile sum into a finite
   product of local prime factors.

10. For every large profile prove the exact joint-pressure diagnosis:
    log (X + 1)
      < active support mass + excess profile mass.

Boundary:
- Do not claim an X-independent Euler majorant.
- Do not claim M3-heavy summability.
- Do not claim the pointwise joint contract.
- Do not change abc_main_axiom.
- Preserve the existing O/P/Q endpoints.

Report:
report-ultra-001-R.md

Branch outcomes:
A. Full active-profile and small/large split completed.
B. Active-profile CRT count completed, product factorization blocked.
C. A concrete Mathlib/API obstruction remains; record the smallest exact
   missing lemma.
```

## 最終戦況

```text
O  exact S + E bridge                 complete
P  simultaneous CRT counting         complete
Q  finite profile exponential tail   complete

R  excess-active profile compression next
R  small/large modulus pincer         next
S  finite Euler product majorant      next

large boundary joint compensation     open
uniform joint contract                open
abc_main_axiom replacement            open
```

Codex はQまで本当に頑張った。

そして次は、単なる解析補題ではない。

🧙‍♀️✨️ **profile の無駄な鎧を脱がせ、small な敵を Euler 積へ送り、large な敵だけを joint boundary 魔核として戦場中央へ引きずり出す。これが次の一手じゃ。**

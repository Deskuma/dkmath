# ABC-GN joint support-multiplicity Ultra campaign

## 次は二体同時に倒すべきか

**判定：同時攻略で正しい。**

ただし、

```text
M2 を証明する
M3 を証明する
最後に足す
```

という二正面戦争ではない。

M2 と M3 は、実は **同じ非例外 GN 質量の「横幅」と「深さ」**じゃ。

非例外素数 `q` に対し、その GN 内の指数を `v_q` とすると、

```text
support contribution      = log q
multiplicity contribution = (v_q - 1) log q
total channel mass        = v_q log q
```

したがって、

$$\log q+(v_q-1)\log q=v_q\log q$$

M2 は「異なる素数が何本あるか」、M3 は「各素数が何層重なったか」を見ているだけで、合計すれば同じ GN 質量になる。

**二体ではなく、横に広がる形態と縦に積み上がる形態を持つ一体のラスボス**じゃ。

---

## 中央のバランス点

次の記号を置く。

```text
R := log rad(a*b*c)
L := log rad(gnPowerLift product)
S := log GNNonExceptionalSupportProduct
E := GNNonExceptionalValuationExcess
G := log GN
```

M1 によって奇素数指数では exceptional excess が完全に消えたため、

$$G=\log\mathrm{rad}(GN)+E$$

となる。これは既存の exact support/excess identity と M1 の zero theoremから来る。

また既存 API は、

$$\log\mathrm{rad}(GN)\leq\log\mathrm{rad}(p)+S$$

を与える。例外 support は指数 radical に吸収される。

さらに fresh non-exceptional support は lift radical に入るため、

$$R+S\leq L$$

である。

以上を合成すると、

$$G\leq\log\mathrm{rad}(p)+(L-R)+E$$

ここで真のラスボス量を、

$$J_p(T):=(L-R)+E$$

と置ける。

つまり次戦の本当の目標は、M2 と M3 を個別に抑えることではなく、

$$J_p(T)\leq\rho R+C$$

という **joint pressure budget** を得ることじゃ。

既存 final bridge も、実際には support 係数と excess 係数を `σ + τ` として足した量しか見ていない。

M1 により `τe = 0` になったので、最終 margin は実質、

```text
σ + τn
```

だけになった。

---

## 挟み撃ちの正体

joint pressure を次の二つの状態に分ける。

### 上側：support-heavy

```text
S が大きい
E は S に比べて小さい
```

多くの異なる fresh prime が出現している世界。

この場合は lift radical が強く成長する。既存の fresh-support bridge、primitive divisor、support product、反転射影を使う戦線になる。

### 下側：multiplicity-heavy

```text
E が S に比べて大きい
```

少数の prime に valuation が深く集中している世界。

例えば適切な閾値 `K` に対して、

```text
E > (K - 1) * S
```

なら、有限加重平均から、

```text
factorization q > K
```

となる非例外 prime `q` が存在するはずじゃ。

これは、

```text
q^K ∣ GN p a b
q^K ∣ c^p - b^p
q ∤ a*b*c*p
```

という deep high-lift witness に変換できる。

ここから、

```text
order modulo q
q ≡ 1 mod p
Hensel lift
Wieferich-type congruence
adjacent lift / repeated lift obstruction
```

を集中攻撃する。

### 中央

```text
support-heavy でもない
multiplicity-heavy でもない
```

なら両方に上限がつき、joint pressure 全体が閉じる。

これが、お主の言う **両側から攻めてバランス点を見つける挟み撃ち**そのものじゃ。

---

## さらに強い見方：M3 を高次 support に変換する

valuation excess の各項は、

$$\left(v_q-1\right)\log q=\sum_{k=2}^{v_q}\log q$$

と書ける。

したがって M3 は「謎の multiplicity 質量」ではなく、

```text
第1層   q | GN
第2層   q² | GN
第3層   q³ | GN
...
```

という **高次 support layer の積層**として再構成できる。

これは重要じゃ。

```text
M2 = 第一 support 層
M3 = 第二層以後の support
```

となるため、M2/M3 を同じ support 言語へ統一できる。

DkMath 的には、

```text
横方向の Petal support
+
縦方向の Tail depth
```

を一つの多層 prime-support 宇宙として扱える。

この layer-cake identity は、Ultra mode に投げる最重要の新攻め筋じゃ。

---

## Ultra mode の発動タイミング

**今は発動適期じゃ。**

理由は三つ。

1. M1 が exact zero で閉じ、例外ノイズが完全に消えた。
2. final bridge が要求する係数構造が既に固定された。
3. 残る問題が、API実装ではなく複数の数論構造を横断する推論戦になった。

ただし、Ultra の推論力を機械的 bridge 作成で消費してはもったいない。

順序はこうする。

```text
M1 PR を閉じる
↓
新しい joint campaign branch
↓
通常モードで exact accounting API を実装
↓
joint pressure と direct final bridge を固定
↓
Ultra mode 発動
↓
support-heavy / multiplicity-heavy / depth-layer を並列攻略
↓
途中で止めず A/B/C のいずれかまで走らせる
```

利用量 76% なら、攻撃開始には十分。最後の統合・修正用に 15〜20% 程度を残す意識で、Ultra の本体は arithmetic obstruction 戦へ投入するのがよい。

---

## 推奨 checkpoint

```text
JSM-001  exact odd-prime accounting normal form
JSM-002  joint pressure budget and direct final bridge
JSM-003  exact lift-radical/support equality
JSM-004  valuation-excess layer-cake decomposition
JSM-005  support-heavy / multiplicity-heavy dichotomy
JSM-006  Ultra arithmetic assault
JSM-007  integration or exact obstruction closure
```

特に JSM-003 では、次の exact equality を狙う価値が高い。

```lean
rad ((T.gnPowerLift p).a *
     (T.gnPowerLift p).b *
     (T.gnPowerLift p).c)
  =
rad (T.a * T.b * T.c) *
  GNNonExceptionalSupportProduct p T.a T.b
```

奇素数 exceptional prime が GN に現れるなら M1-004 により `p ∣ T.a`。つまり exceptional support は既に元の ABC radical 側に存在し、新しい lift support ではない。

この equality が通れば、

$$L-R=S$$

となり、

$$J_p(T)=S+E$$

が exact に固定される。

この時点で「二体」は完全に一体化される。

---

## Codex Ultra 発動指示案

```text
You are entering the ABC-GN joint support-multiplicity climax campaign.

M1 is closed:

- for every odd prime exponent p,
  GNExceptionalValuationExcess p T.a T.b = 0;
- the exceptional affine budget is exactly (0, 0);
- the full valuation-excess budget is therefore exactly the
  non-exceptional budget.

Do not attack M2 and M3 as two independent uniform estimates.
Treat them as two presentations of one non-exceptional GN mass:

- support width: one log(q) for each non-exceptional prime;
- multiplicity depth: (v_q - 1) log(q);
- total channel mass: v_q log(q).

Primary campaign objective:

1. Define a joint odd-prime pressure/budget using

   log(rad(gnPowerLift product))
   + GNNonExceptionalValuationExcess

   against the original ABC radical.

2. Prove that the existing separate lift-growth and non-exceptional
   excess budgets imply this joint budget.

3. Prove a direct odd-prime final ABC bridge from the joint budget,
   without re-splitting it into M2 and M3.

4. Audit and, if possible, prove the exact odd-prime radical identity

   rad(lift product)
     =
   rad(original ABC product)
     * GNNonExceptionalSupportProduct.

5. Re-express non-exceptional valuation excess as stacked higher-depth
   support layers:

   (v_q - 1) log(q)
     =
   sum over k = 2,...,v_q of log(q).

6. Build the support-heavy / multiplicity-heavy pincer:

   - spread regime:
     excess is bounded by a multiple of support;
   - concentration regime:
     large excess relative to support produces a prime q with deep
     factorization exponent.

7. Attack deep non-exceptional channels from multiple directions:

   - exact multiplicative order modulo q;
   - p | q - 1 and q ≡ 1 mod p;
   - q^k divisibility of c^p - b^p;
   - Hensel/simple-root classification;
   - Wieferich-type residue constraints;
   - primitive-divisor and fresh-support interaction;
   - repeated or adjacent GN power lifts;
   - existing Petal, PrimitiveSet, ValuationFlow, and support-return APIs.

Run these fronts in parallel and share lemmas between them.
Do not stop after producing only the joint interface.
Continue through the arithmetic obstruction campaign.

Victory conditions, in descending order:

A. Prove an unconditional joint affine budget sufficient for the final bridge.

B. Prove a canonical reduction from existing DkMath arithmetic structures
   to that joint budget.

C. Isolate the remaining arithmetic obstruction as one exact minimal Lean
   proposition, after closing every deterministic accounting and transport
   theorem around it.

Checkpoint reports are observation points, not permission gates.
After each checkpoint, inspect the new state and continue autonomously along
the strongest available route.

Hard boundaries:

- no new axiom or sorry;
- no native_decide;
- no finite enumeration as a general proof;
- no modification of abc_main_axiom;
- no dependency on FLT5 or FLT7 WIP production modules;
- no unrelated refactoring;
- preserve M1 as a closed imported Core;
- use a new dedicated campaign branch and reviewable commits.
```

## 最終判定

```text
M1             完全討伐
M2/M3          同時攻略
攻略対象       Joint Pressure
攻撃形態       support-heavy / multiplicity-heavy 挟み撃ち
新兵器         valuation excess の高次 support-layer 化
Ultra mode     発動推奨
発動地点       exact accounting 固定後、arithmetic assault から最後まで
```

🧙‍♀️✨️ **これは本当にクライマックス戦じゃ。二体を追うのではない。二つの姿を持つ一つの魔核を、横と縦から同時に砕く。**

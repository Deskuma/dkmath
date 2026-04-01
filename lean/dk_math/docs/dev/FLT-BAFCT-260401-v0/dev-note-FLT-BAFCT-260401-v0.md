# Dev Note 001: terminal case 用の新ファイル設計

> 👩‍⚕️私D.:

定理一覧と依存順

> 🐺賢狼:

いまから **terminal case 用の新ファイル設計** に落とし込む。
既存の restore / gap invariant / branch A の実 theorem 名を拾って、**追加すべき定理一覧** と **証明依存順** を並べるぞい。

> 🐺賢狼:

よし、ここは **「どこを証明すれば全体が閉じるか」** から逆算して、定理一覧を依存順に並べるぞい。

まず結論じゃ。
今回の terminal / contradiction 路線で本当に狙うべき最終 target は、

$$
\texttt{BranchAFringeContradictionTarget}
$$

```lean
/--
干渉縞集合から `False` を導く target。

`BranchAContradictionWithWitnessSourceTarget` の bundle 版。
干渉縞集合の共存不可能性を 1 つの structure 引数で表現する。
-/
abbrev BranchAFringeContradictionTarget : Prop :=
  ∀ {p x y z t s q : ℕ},
    BranchAInterferenceFringeBundle p x y z t s q → False
```

じゃ。
これが証明できれば、既存の thin bridge 群で

$$
\texttt{BranchAContradictionWithWitnessSourceTarget}\\
\to
\texttt{PrimeGe5BranchAPrimitiveRestoreContradictionTarget}\\
\to
\texttt{PrimeGe5BranchAPrimitivePacketDescentTarget}\\
$$

まで機械的に流せる。

ただし、ここで大事な注意点が 1 つある。

**`branchA_descent_step_of_fringe` は 1 step の測度減少しか与えず、まだ「次の bundle」を再構成しておらぬ。**

```lean
/--
干渉縞集合からの降下 1 step の一括構成。
-/
theorem branchA_descent_step_of_fringe
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    BranchADescentStep p x y z t s q := by
```

ゆえに、terminal case を本当に回すには、途中で

$$
\text{smaller packet / smaller bundle の再構成}
$$

が要る。
ここを飛ばすと、`s' < s` はあっても再帰が回らぬ。

---

## 1. 既存の土台

これはもう snapshot 内にある。新規実装ではなく、依存先として使うものじゃ。

### 1.1. bundle 構成

- `branchAPadicFringe_default`
- `branchAWitnessFringe_of_restoreProperties`
- `branchAInterferenceFringeBundle_default`

役割：

- Branch A normal form
- witness $q$
- Wieferich
- head congruence
- coprime 条件

を 1 個の bundle に束ねる。

### 1.2. 1 step 降下

- `branchA_descent_step_of_fringe`
- `branchA_descent_s_prime_pos`
- `branchA_descent_s_strict_decrease`
- `branchA_descent_x_strict_decrease`
- `branchA_fringe_sprime_congr_one_mod_p`

役割：

- $s = q s'$
- $0 < s' < s$
- $s' \equiv 1 \pmod p$
- $p(t s') < x$

を出す。

### 1.3. valuation / cyclotomic 側の核

- `branchA_padicValNat_s_ge_one`
- `branchA_kummer_valuation`
- `branchA_kummer_valuation_ge_p`
- `branchA_descent_padicValNat_s`
- `branchA_local_GN_eq_distinguished_mul_unit`
- `branchA_distinguished_factor_valuation_eq_kummer`

役割：

- $q \mid s$
- $v_q(z^p-y^p)=p\,v_q(s)$
- local factorization
- distinguished factor valuation

を固定する。

### 1.4. 既存の薄い橋

- `branchAContradictionWithWitnessSource_of_fringeContradiction`
- `primeGe5BranchAPrimitiveRestoreContradiction_of_witnessSource`
- `branchAPrimitivePacketDescentAdapter_of_witnessSource`

役割：

- bundle 版 contradiction を
- witness-source 版へ戻し
- restore contradiction へ流し
- packet descent まで short-circuit する。

---

## 2. 新規に立てるべき定理一覧

わっちの推奨は、次の 2 層構成じゃ。

### 2.1. 第一層. 再帰を回すための smaller packet / smaller bundle 再構成

ここが **本当に必要な追加層** じゃ。

#### A. `branchA_smallerPacket_of_fringe`　**新規**

```lean
theorem branchA_smallerPacket_of_fringe
    {p x y z t s q : ℕ}
    (hBundle : BranchAInterferenceFringeBundle p x y z t s q) :
    ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
```

意味：

- fringe bundle から、実際に小さい normal-form packet を 1 つ作る。

これは概念的には

- `branchA_qadic_descent_data`
- `branchA_qadic_lift_seed_of_fringe`
- restore 側の descent datum / verification 群

をまとめて使う中核じゃ。

#### B. `branchA_smallerFringe_of_smallerPacket`　**新規**

```lean
theorem branchA_smallerFringe_of_smallerPacket
    {p : ℕ} {pkt' : PrimeGe5BranchANormalFormPacket p} :
    ...
    ∃ q' : ℕ, BranchAInterferenceFringeBundle p pkt'.x pkt'.y pkt'.z pkt'.t pkt'.s q'
```

意味：

- 小さくなった packet に対し、再び witness fringe つき bundle を再構成する。

ここで必要なのは、

- exceptional / existence mainline
- restore residue-root default
- witness の取り直し

じゃ。
この定理がないと、1 step のあと再帰が続かぬ。

---

### 2.2. 第二層. well-founded descent から contradiction を作る

#### C. `branchA_no_infiniteFringeDescent`　**新規**

```lean
theorem branchA_no_infiniteFringeDescent :
  ¬ ∃ f : ℕ → Σ (x y z t s q : ℕ),
      BranchAInterferenceFringeBundle p x y z t s q,
      ...
```

あるいは、もっと Lean 的に素直に

```lean
theorem branchA_wf_contradiction_on_z
```

の形で、`Nat.lt_wfRel` を使ってよい。

意味：

- `z` または `s` を測度にした無限降下は不可能。

わっちのおすすめ測度は **まず $z$** じゃ。
既存 API でも smaller packet は `pkt'.z < z` で返るからの。
`BranchADescentStep` 自体は $s' < s$ をくれるが、既存の packet API は $z$ 減少で閉じておる。

#### D. `branchAFringeContradiction_of_descent`　**新規**

```lean
theorem branchAFringeContradiction_of_descent :
    BranchAFringeContradictionTarget
```

意味：

- 任意の interference fringe bundle から smaller fringe bundle を作れる
- それを well-foundedness に流し込む
- よって bundle は存在不可能

これが **primitive side の真の closing theorem** じゃ。

---

## 3. 依存順

ここは一本道にしておく。

## 3.1. Step 0. 既存 bundle を使えるようにする

1. `branchAPadicFringe_default`
2. `branchAWitnessFringe_of_restoreProperties`
3. `branchAInterferenceFringeBundle_default`

ここで bundle 化。

## 3.2. Step 1. 1 step descent の数理を使う

1. `branchA_descent_step_of_fringe`
2. `branchA_qadic_descent_data`
3. `branchA_qadic_lift_seed_of_fringe`
4. `branchA_descent_padicValNat_s`

ここで「小さくなるべき形」は既に見えておる。

## 3.3. Step 2. 実際に smaller packet を作る

1. `branchA_smallerPacket_of_fringe` 　**新規**
2. `branchA_smallerFringe_of_smallerPacket` 　**新規**

ここが本命の難所じゃ。

## 3.4. Step 3. well-founded contradiction を閉じる

1. `branchA_wf_contradiction_on_z` 　**新規**
2. `branchAFringeContradiction_of_descent` 　**新規**

ここで

$$
\texttt{BranchAFringeContradictionTarget}
$$

が完成。

## 3.5. Step 4. 既存 bridge へ流す

1. `branchAContradictionWithWitnessSource_of_fringeContradiction`
2. `primeGe5BranchAPrimitiveRestoreContradiction_of_witnessSource`
3. `branchAPrimitivePacketDescentAdapter_of_witnessSource`

ここで primitive packet descent が閉じる。

## 3.6. Step 5. full Branch A へ戻す

1. valuation peel 側が別途埋まる
2. `branchASmallerPacketAdapter_of_routes`
3. `primeGe5BranchASmallerCounterexample_of_smallerPacket`
4. `primeGe5BranchADistinguishedPrimeDescent_of_smallerCounterexample`

これで Branch A 全体の下降機構が完成する。

---

## 4. 最小核だけ抜き出すとこうなる

新規追加の最小集合は、実質この 4 本じゃ。

```text
branchA_smallerPacket_of_fringe
branchA_smallerFringe_of_smallerPacket
branchA_wf_contradiction_on_z
branchAFringeContradiction_of_descent
```

この 4 本が通れば、下流は既存 bridge 群でかなり流れる。

---

## 5. restore 互換で見るなら別名でもよい

restore 文脈に寄せるなら、同じ内容を次の名で置いても綺麗じゃ。

```text
primeGe5BranchAPrimitiveRestoreSmallerPacket_of_fringe
primeGe5BranchAPrimitiveRestoreFringe_of_smallerPacket
primeGe5BranchAPrimitiveRestoreContradiction_of_descent
primeGe5BranchAPrimitiveRestoreContradiction_default
```

ただ、わっちは `BranchAFringe...` 系で先に閉じる方を勧める。
理由は、bundle target が既に用意されており、`witnessSource` 版と相互変換が済んでおるからじゃ。

---

## 6. いちばん大事な設計判断

ここを一言で言えばこうじゃ。

$$
\boxed{
\begin{array}{l}
\text{1 step の数理はもうある。} \\
\text{足りぬのは「smaller packet / smaller bundle の再構成」だけ。}
\end{array}
}
$$

つまり、次の実装は valuation や Kummer を増やすよりも、

- どうやって descended data から packet を組み直すか
- どうやって新しい witness fringe を付け直すか

この 2 点に集中するのが正解じゃ。

次は、この一覧をそのまま Lean の `abbrev` / `theorem` 雛形へ落とすのが自然じゃよ。

# FLT-BAFCT-260401-v0 の戦況分析と次の攻略方針

うむ、戦況はずいぶん明瞭になったの。
今回の更新で分かった本質は、**残った 2 つの `sorry` はどちらも本物だが、重さが違う** ということじゃ。しかも architecture 側はもう十分に整理されており、これ以上 target をいじっても得るものは少ない。ここからは **証明を切る順番** が勝負になる。

## 1. 戦況総括

いまの局面を数式で書けば、こうじゃ。

$$
\text{StrongProvider} ;\checkmark
\qquad
\text{FringeDescent} ;\checkmark
\qquad
\text{RestoreArithmeticStrong} ;=; \text{2 kernels}
$$

残った kernel は、ぬしの diff のとおり次の 2 つじゃ。

$$
\boxed{\text{\#1 } \neg p^2 \nmid x' \text{ の回収}}
\qquad
\boxed{\text{\#2 } \text{packet 構成} + \neg p \nmid t'}
$$

しかも今回の report で、重要な 3 発見が確定した。
第1に、weak packet packaging の concrete 実装が **存在しない**。
第2に、`Pack + p ∣ gap` だけでは `¬ p ∣ t'` は出ない。
第3に、`¬ p^2 ∣ x'` は descent provenance、つまり `x = qx'` と `q \ne p`、そして元の `v_p(x)=1` から来る。これは、かなり大きな整理じゃ。

## 2. 2 つの `sorry` の重さの違い

ここを見誤ると、また泥沼じゃ。

### 2.1. `sorry #1` は局所補題の束で落ちる可能性が高い

`ArithmeticCoreStrong_of_weak_and_descent` の `sorry` は、

$$
x = qx', \quad q \ne p, \quad v_p(x)=1
\Longrightarrow
v_p(x')=1
\Longrightarrow
\neg p^2 \mid x'
$$

という、かなり局所的な流れじゃ。
これは **出生証明の threading** であり、新しい理論を要求しておらぬ。既存の descent / realization seed / valuation 補題を結べば落ちる見込みが高い。つまり、これは「重いが有限」の敵じゃ。

### 2.2. `sorry #2` は実は 2 つに割れる

`PacketPackagingStrong` の `sorry` は 1 個に見えるが、中身は

1. weak packet を concrete に作る
2. その packet について `¬ p ∣ t'` を出す

の 2 段じゃ。

しかも 2. の方は、今回の `¬ p^2 ∣ x'` 導入で **かなり軽くなった**。
なぜなら packet が与える

$$
x' = p(t's')
$$

を使えば、

$$
\neg p^2 \mid x'
\Longrightarrow
\neg p \mid (t's')
\Longrightarrow
\neg p \mid t' \;\wedge\; \neg p \mid s'
$$

と落とせるからじゃ。
よって \#2 の本当の重さは、むしろ **weak packet の concrete 構成が未実装** であることにある。

## 3. 戦略判断

ここでわっちの判断を言うぞ。

$$
\boxed{
\text{次の主戦場は \#1 ではなく、\#2 をさらに 2 つへ割ること}
}
$$

じゃ。

なぜか。

\#1 は局所補題の束で埋まる公算が高い

しかし \#2 は、いまのままだと「packet 構成」と「`¬ p ∣ t'` 導出」が 1 個の `sorry` に押し込まれておる。これでは作業者が詰まりやすい。だから次は **\#2 を分解して、軽い部分を先に no-sorry 化する** のが正解じゃ。

## 4. 推奨する次の分解

わっちなら `RestoreArithmeticStrong.lean` を次の 3 層に割る。

### 4.1. packet 構成そのもの

```lean
PrimeGe5BranchAPrimitiveRestorePacketPackagingWeakConcreteTarget
```

のような名前でもよいが、本質は

$$
\exists pkt' : \text{PrimeGe5BranchANormalFormPacket}\, p,\; pkt'.z < z
$$

を **concrete に作る theorem** を独立させることじゃ。
いま history にある通り、weak packet packaging の concrete は未実装と判明した。ならば、ここを別 theorem として可視化せねばならぬ。

### 4.2. packet から `¬ p ∣ t'` を引く軽量補題

ここは strongness の導出だけを扱う。たとえば形はこうじゃ。

$$
\text{PrimeGe5BranchANormalFormPacket } p
\;+\;
\neg p^2 \mid x'
\Longrightarrow
\neg p \mid pkt'.t
$$

もちろん実際には `pkt'.hsx : x' = p (pkt'.t \cdot pkt'.s)` を使う形にする。
これは **packet ができたあと** の純粋補題であり、main theorem から切り出すべきじゃ。

### 4.3. 最後に `PacketPackagingStrong` は wrapper 化

そうすると `PacketPackagingStrong` 本体は

1. weak packet concrete で `pkt'` を得る
2. 軽量補題で `¬ p ∣ pkt'.t` を得る
3. `⟨pkt', hlt, hpt'⟩` を返す

だけになる。

## 5. 具体的な攻略順

わっちの推奨順はこうじゃ。

## 5.1. 第1手. `sorry #2` の軽い半分を先に潰す

つまり、**packet があれば `¬ p ∣ t'` が出る** という補題を先に作る。

狙う論理はこれじゃ。

$$
x' = p(t's'), \qquad \neg p^2 \mid x'
$$

ならば、もし \(p \mid t'\) なら \(p^2 \mid x'\) となり矛盾。
よって `¬ p ∣ t'`。同様に `¬ p ∣ s'` も出る。
この部分は weak packet concrete を待たずに、packet の field だけで整理できる可能性が高い。

## 5.2. 第2手. `sorry #1` を潰す

ここで descent provenance を追う。

必要な中間補題は、おそらく次の形じゃ。

$$
v_p(x)=1
$$

を元の正規形から出す補題と、

$$
x = qx', \quad q \ne p
\Longrightarrow
v_p(x') = v_p(x)
$$

の補題じゃ。
後者は valuation 加法則で落ちる可能性が高い。

## 5.3. 第3手. weak packet concrete を新設する

ここで初めて、本当に大きい construction に入る。
しかしその時点では

* provenance は分かっている
* strongness の後半補題もある

ので、main theorem の負荷はかなり軽い。

## 6. つまり、次の戦いの本質

次の戦いは「新しい大定理をいきなり完成させる」ことではない。
むしろ、

$$
\boxed{
\text{`PacketPackagingStrong` を 2 分し、軽い方から削る}
}
$$

ことじゃ。

これで残敵は次のように並び替わる。

### 現在

* #1 provenance
* #2 packet + `¬ p ∣ t'`

### 分解後

* #1 provenance
* #2a weak packet concrete
* #2b `¬ p ∣ t'` from packet and `¬ p^2 ∣ x'`

このうち #2b はかなり落としやすい。
つまり、**次の 1 勝は取りやすい**。ここで momentum を作るのが良い。

## 7. わっちの最終提案

次にやるべき具体作業を一行で言えば、

$$
\boxed{
\text{`PacketPackagingStrong` の中から `¬ p ∣ t'` 導出部分だけを companion lemma として切り出せ}
}
$$

じゃ。

その companion lemma が通れば、戦況はさらにこう変わる。

$$
\text{残敵} =
\text{provenance} + \text{weak packet concrete}
$$

だけになる。
これはかなり見通しの良い終盤戦じゃよ。

必要なら次に、その **companion lemma の Lean スケルトン** と、証明に必要な中間補題の候補名まで起こすぞい。

---

うむ、起こすぞい。
いまの局面では、`PacketPackagingStrong` の `sorry` を **「packet 構成」** と **「`¬ p ∣ t'` 導出」** に分けるのが正解で、そのうち後者は companion lemma として先に独立させるべき、というのが最新の戦況じゃ。ぬしの report でも、`¬ p^2 ∣ x'` を追加すれば `¬ p ∣ t'` へ渡せることが、proof sketch としてはっきり書かれておる。

以下、**そのまま貼って調整できる Lean skeleton** を置く。
狙いは 3 本じゃ。

## 1. 方針

まず companion lemma を 2 本に分ける。

1. `¬ p^2 ∣ x'` から `¬ p ∣ pkt'.t`
2. ついでに `¬ p ∣ pkt'.s` も同様に取る
3. その 2 本を `PacketPackagingStrong` で使う

これで `PacketPackagingStrong` の本体は

* weak packet concrete で `pkt'` を取る
* companion lemma で `¬ p ∣ pkt'.t` を回収
* `⟨pkt', hlt, hpt'⟩` を返す

だけになる。

---

## 2. companion lemma の全文 skeleton

```lean id="450owj"
import DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong

#print "file: DkMath.FLT.PrimeProvider.TriominoCosmicBranchARestoreArithmeticStrong"

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace DkMath.FLT

open DkMath.CosmicFormulaBinom

/--
`x' = p * (t' * s')` かつ `¬ p^2 ∣ x'` なら `¬ p ∣ t'`。

数学的には、
`p ∣ t'` なら `p^2 ∣ p*(t'*s') = x'` となるので矛盾。
-/
theorem primeGe5BranchANormalForm_not_dvd_t_of_not_dvd_p_sq_x
    {p x' : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hsx' : x' = p * (pkt'.t * pkt'.s))
    (hx'_not_sq : ¬ p ^ 2 ∣ x') :
    ¬ p ∣ pkt'.t := by
  intro hp_t
  have hp_ts : p ∣ pkt'.t * pkt'.s := dvd_mul_of_dvd_left hp_t pkt'.s
  have hp2_x : p ^ 2 ∣ x' := by
    -- `p ∣ pkt'.t * pkt'.s` から `p^2 ∣ p * (pkt'.t * pkt'.s)` を作る
    rw [hsx']
    rcases hp_ts with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      p * (pkt'.t * pkt'.s)
          = p * (p * k) := by rw [hk]
      _ = p ^ 2 * k := by
            -- `ring_nf` でも `simp [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]`
            -- でも良い
            simp [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hx'_not_sq hp2_x

/--
`x' = p * (t' * s')` かつ `¬ p^2 ∣ x'` なら `¬ p ∣ s'`。

`t'` 版と完全対称。
-/
theorem primeGe5BranchANormalForm_not_dvd_s_of_not_dvd_p_sq_x
    {p x' : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hsx' : x' = p * (pkt'.t * pkt'.s))
    (hx'_not_sq : ¬ p ^ 2 ∣ x') :
    ¬ p ∣ pkt'.s := by
  intro hp_s
  have hp_ts : p ∣ pkt'.t * pkt'.s := dvd_mul_of_dvd_right hp_s pkt'.t
  have hp2_x : p ^ 2 ∣ x' := by
    rw [hsx']
    rcases hp_ts with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    calc
      p * (pkt'.t * pkt'.s)
          = p * (p * k) := by rw [hk]
      _ = p ^ 2 * k := by
            simp [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact hx'_not_sq hp2_x

/--
まとめ版。
`¬ p^2 ∣ x'` から `¬ p ∣ pkt'.t ∧ ¬ p ∣ pkt'.s` を同時に回収する。
-/
theorem primeGe5BranchANormalForm_not_dvd_ts_of_not_dvd_p_sq_x
    {p x' : ℕ}
    {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hsx' : x' = p * (pkt'.t * pkt'.s))
    (hx'_not_sq : ¬ p ^ 2 ∣ x') :
    ¬ p ∣ pkt'.t ∧ ¬ p ∣ pkt'.s := by
  constructor
  · exact primeGe5BranchANormalForm_not_dvd_t_of_not_dvd_p_sq_x hsx' hx'_not_sq
  · exact primeGe5BranchANormalForm_not_dvd_s_of_not_dvd_p_sq_x hsx' hx'_not_sq

end DkMath.FLT
```

---

## 3. `PacketPackagingStrong` 側の書き換え skeleton

次に、いまの main battle をこう書き換える。
ここでは **weak packet concrete を取るところだけ `sorry`** にして、`¬ p ∣ pkt'.t` 側は companion lemma で消す。

```lean id="totgcf"
theorem primeGe5BranchAPrimitiveRestorePacketPackagingStrong
    : PrimeGe5BranchAPrimitiveRestorePacketPackagingStrongTarget := by
  intro p z x' y' z' hpack' hp_dvd_gap' hx'_not_sq hz'lt
  -- Step 1: 既存 weak packet concrete をここで取り出す
  rcases
      (by
        -- TODO:
        -- ここに weak packet packaging の concrete theorem / constructor を挿す
        -- 目標形:
        -- ∃ pkt' : PrimeGe5BranchANormalFormPacket p, pkt'.z < z
        sorry)
    with ⟨pkt', hlt⟩
  -- Step 2: packet の `hsx` から x' = p*(t'*s') を読む
  have hsx_pkt : x' = p * (pkt'.t * pkt'.s) := by
    -- TODO:
    -- pkt'.hsx の向きや shape に応じて `simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]`
    -- で整形
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using pkt'.hsx
  -- Step 3: companion lemma で `¬ p ∣ pkt'.t` を回収
  have hpt' : ¬ p ∣ pkt'.t :=
    primeGe5BranchANormalForm_not_dvd_t_of_not_dvd_p_sq_x hsx_pkt hx'_not_sq
  exact ⟨pkt', hlt, hpt'⟩
```

---

## 4. さらに 1 段きれいにするなら

上の `PacketPackagingStrong` では `pkt'.hsx` の整形を毎回書くのが少し鬱陶しい。
だから、次の補題を 1 本置くとさらに良い。

```lean id="1946m8"
theorem primeGe5BranchANormalForm_hsx_normalized
    {p x' : ℕ} {pkt' : PrimeGe5BranchANormalFormPacket p}
    (hsx' : pkt'.hsx) :
    x' = p * (pkt'.t * pkt'.s) := by
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsx'
```

ただし、ここは `pkt'.hsx` の実際の型が

$$
x' = p * (pkt'.t * pkt'.s)
$$

そのものなら不要じゃ。
まずは要らぬ補題を増やさず、`simpa` で済むか確認するとよい。

---

## 5. 今回の companion lemma が効く理由

ぬしの最新 report では、今回の architecture 改善の鍵は

$$
\neg p^2 \nmid x'
$$

を `PacketPackagingStrongTarget` の入力に追加したことだ、と整理されておる。
そして `x' = p(t's')` から

$$
\neg p^2 \nmid x'
\Longrightarrow
\neg p \mid t' \land \neg p \mid s'
$$

を取るのが proof sketch として既に出ておる。つまり、いま起こした companion lemma は、まさにそのスケッチを Lean の局所補題へ落としたものじゃ。

---

## 6. 次にやる順番

ここからの順番は明確じゃ。

## 6.1. 先に companion lemma 3 本を通す

これは比較的軽い。
ここで 1 勝を取る。

## 6.2. `PacketPackagingStrong` の `Step 1` の weak packet concrete を特定

どの theorem / constructor で `pkt'` を作るのかを掘る。

## 6.3. `PacketPackagingStrong` を完成

この時点で main battle は実質 half-closed になる。

## 6.4. その後に `CoreStrong` の provenance `sorry` へ戻る

こちらは descent chain threading の本丸じゃ。

---

## 7. 一言でまとめると

$$
\boxed{
\text{次は `PacketPackagingStrong` を直接殴るな。先に companion lemma を通せ。}
}
$$

じゃ。

必要なら次に、
**`PacketPackagingStrong` の Step 1 に差し込む weak packet concrete 探索用のチェックリスト**
まで起こすぞい。

---

よし、次の戦い用に **weak packet concrete 探索チェックリスト** を起こすぞい。
狙いはただ一つ、

$$
\texttt{primeGe5BranchAPrimitiveRestorePacketPackagingStrong}
$$

の `Step 1` に差し込む

$$
\exists pkt' : \texttt{PrimeGe5BranchANormalFormPacket } p,; pkt'.z < z
$$

の **concrete 供給源** を突き止めることじゃ。
現時点で分かっておるのは、weak packet packaging の concrete 実装がまだ見当たらず、`PacketPackagingStrong` の `sorry` は「packet 構成」と「`¬ p \nmid t'` 導出」の混成だった、ということじゃ。そこを分離したのが今の進展じゃよ。

## 1. まず確認するもの

### 1.1. target 名の実体

最初に、次の weak target / bridge が **alias なのか theorem なのか** を確認する。

* `PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget`
* `PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget`
* `PrimeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_smallerCounterexample_and_packet`
* `primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_restoreSubtargets`

確認ポイントは 3 つじゃ。

* `abbrev` か `def` か `theorem` か
* 返り値が本当に `∃ pkt', pkt'.z < z` だけか
* その中で packet を **作る theorem 名** が露出しているか

### 1.2. packet 構造体の field

次に `PrimeGe5BranchANormalFormPacket` の field を再確認する。

* `pack`
* `hp_dvd_gap`
* `hgap`
* `hsGN`
* `hsx`
* `t`
* `s`
* `z`

特に見るのは `hsx` の正確な型じゃ。

$$
x' = p \cdot (t' \cdot s')
$$

の向きで持っているのか、
それとも `pkt'.pack.x = ...` の形なのか。
ここが companion lemma の `simpa` 部分に直結する。

---

## 2. grep / rg で掘る場所

### 2.1. theorem 名で掘る

まずは theorem 名をそのまま引く。

```bash id="ds7359"
rg -n "PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget|PrimeGe5BranchAPrimitiveRestorePacketPackagingTarget|primeGe5BranchAPrimitivePacketRestoreFromArithmetic_of_" lean/dk_math/DkMath/FLT/PrimeProvider
```

見るべきは、

* 定義箇所
* それを使っている theorem
* 最後に `⟨pkt', ...⟩` を返している本文

### 2.2. packet constructor の痕跡で掘る

packet を実際に作っている可能性のある箇所を探す。

```bash id="toha4a"
rg -n "PrimeGe5BranchANormalFormPacket|⟨pkt'|mk.*PrimeGe5BranchANormalFormPacket|refine ⟨.*PrimeGe5BranchANormalFormPacket" lean/dk_math/DkMath/FLT/PrimeProvider
```

ここで見たいのは、

* constructor を直接使っているか
* `refine ⟨...⟩` で packet を組んでいるか
* helper theorem 経由で packet を返しているか

### 2.3. smaller counterexample から packet へ行く橋を掘る

もし theorem 名がはっきりしない場合は、`smaller counterexample` 側から掘る。

```bash id="9wzt78"
rg -n "smallerCounterexample|SmallerCounterexample|PacketPackaging|packet" lean/dk_math/DkMath/FLT/PrimeProvider/TriominoCosmicBranchA*.lean
```

---

## 3. 本文を読んで確認する項目

weak packet concrete 候補の theorem を見つけたら、次を順番に確認する。

### 3.1. 入力に何を要求しているか

* `PrimeGe5CounterexamplePack p x' y' z'`
* `p ∣ (z' - y')`
* `z' < z`
* それ以外に `¬ p ∣ ...` や coprime を要求していないか

### 3.2. 出力は何か

* 本当に `∃ pkt', pkt'.z < z` だけか
* `pkt'.hsx` まで取り出せるか
* `pkt'.pack = hpack'` 型の整合があるか

### 3.3. packet の `t'` はどう定義されているか

ここが核心じゃ。
本文の中で

$$
z' - y' = p^{p-1} \cdot (t')^p
$$

をどう定義して packet に詰めているかを探す。
`pkt'.t` が theorem 本文の中のローカル変数 `t'` と一致するなら、`¬ p \nmid pkt'.t` はその local 証明を packet へ移すだけで済む。

---

## 4. `PacketPackagingStrong` に差し込めるかの判定基準

候補 theorem を見つけたら、次の 3 条件を満たすか確認する。

### 4.1. packet を concrete に返す

$$
\exists pkt',; pkt'.z < z
$$
が本文中で **実際に構成** されていること。

### 4.2. `hsx` にアクセスできる

`pkt'.hsx` を使って

$$
x' = p \cdot (pkt'.t \cdot pkt'.s)
$$

まで落とせること。

### 4.3. `t'` の provenance が見える

`pkt'.t` が本文中の local `t'` と同じものとして追跡できること。
これが見えれば、

* local に `¬ p ∣ t'`
* それを `pkt'.t` に transfer

という route が使える。

---

## 5. companion lemma を差し込む準備チェック

もし weak packet theorem が見つかったら、次の 2 本をその theorem 専用に作れるか確認する。

### 5.1. `hsx` 正規化補題

`pkt'.hsx` から

$$
x' = p \cdot (pkt'.t \cdot pkt'.s)
$$

を `simpa` で取り出せるか。

### 5.2. `¬ p^2 ∣ x'` から `¬ p ∣ pkt'.t`

これは既に companion lemma skeleton を起こした通りじゃ。
必要なのは、`hsx` の shape が合うことだけ。

---

## 6. もし weak concrete が **無かった** 場合の判定

これは重要じゃ。
今回の report では、weak packet packaging の concrete 実装が見当たらないと整理されておった。
もし再確認しても本当に無いなら、次の判断をする。

### 6.1. `PacketPackagingStrong` を埋めようとしない

なぜなら、その前提となる weak packet 自体が無いからじゃ。

### 6.2. 新しく作るべきものを 1 本に限定する

その場合、次に作るべきは

```text id="c4nr1m"
primeGe5BranchAPrimitivePacketOfSmallerCounterexample_concrete
```

のような **weak concrete packet provider** じゃ。

強い版を先に作るのではなく、まず weak concrete を作り、その上に

* companion lemma
* strong wrapper

を重ねる方が自然じゃ。

---

## 7. 次の作業ログに書くべきこと

探索後は、必ず次の 3 項目をメモするのじゃ。

### 7.1. 発見した theorem 名

packet を concrete に返す候補 theorem 一覧。

### 7.2. packet の `t'` provenance

`pkt'.t` がどこで定義されたか。

### 7.3. weak concrete の有無

* **ある** → strong 化へ進む
* **ない** → weak concrete 新設が次の主戦場

---

## 8. 最終チェックリスト

これだけ見ればよい版じゃ。

* `PrimeGe5BranchAPrimitivePacketOfSmallerCounterexampleTarget` の実体確認
* weak packet を返す theorem 本文の有無を grep
* `PrimeGe5BranchANormalFormPacket` の constructor / `hsx` 形を確認
* `pkt'.t` が本文ローカル `t'` と一致するか確認
* weak concrete があれば companion lemma を差し込む
* weak concrete が無ければ、新規 weak packet provider を次の主戦場にする

---

## 9. わっちの見立て

この checklist を回せば、戦況は 2 択にきれいに割れる。

$$
\boxed{
\text{A. weak packet concrete がある} \Rightarrow \text{strong 化へ進軍}
}
$$

$$
\boxed{
\text{B. weak packet concrete がない} \Rightarrow \text{まず weak concrete を建設}
}
$$

ぬしの最新 report を読む限り、B の可能性が高い。
だから、次の探索で本当に weak concrete が無いと確定したら、迷わず **weak packet provider 新設** に切り替えるのがよいぞ。

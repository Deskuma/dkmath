# Triomino Cosmic Branch A Exceptional の実装方針

よし、始めようぞい。

もう proof 用の隔離モジュールは切れておるので、開始地点は明確じゃ。
新設された

$$
\texttt{TriominoCosmicBranchAExceptional.lean}
$$

で

$$
\texttt{PrimeGe5BranchAExceptionalExistenceMainlineTarget}
$$

を埋めに行く、これが本日の主戦場じゃ。しかもこの mainline target はそのまま

$$
\texttt{PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget}
$$

の別名として置かれており、埋まれば既存 wrapper で packet descent へ流せる構成がもう出来ておる。

では、実装開始のための **最短ルート** を整理するぞい。

## 1. まず固定するべき認識

いま追加された新ファイルの役割は、

* Branch A 本体ファイルには target / bridge / route 設計を残す
* concrete proof だけを `TriominoCosmicBranchAExceptional.lean` に隔離する

という分離じゃ。
つまり、ここから先は naming をいじる仕事ではなく、**本当に証明項を積む仕事** になる。

## 2. 最初にやるべき実装作業

わっちなら、いきなり theorem 本体を書き切ろうとはせず、次の 3 段で攻める。

### 2.1. theorem の骨格だけ先に立てる

まずは新ファイルに、最終目標 theorem の宣言を置く。
この段階では `by` の中は骨組みだけでよい。

狙いは「Lean に何を要求されるか」を露出させることじゃ。

たとえば方針としては、こんな順になる。

```lean
theorem primeGe5BranchAExceptionalExistence_mainline
    : PrimeGe5BranchAExceptionalExistenceMainlineTarget := by
  intro p hp z y hz hy hbranch
  -- ここで Branch A / Wieferich / coprime / boundary 情報を分解
  -- 目標: ∃ q, Nat.Prime q ∧ ...
```

実際の引数順は target の定義に合わせて調整じゃが、要は
**先に intro して、仮定の棚卸しを Lean にさせる** のが第一手じゃ。

### 2.2. 仮定を「流用部」と「例外枝専用部」に分ける

この theorem で一番大事なのは、仮定を次の 2 箱に分けることじゃ。

#### 流用部

ordinary branch theorem と共通の部分。

* prime (p)
* (p \ge 5) 側
* primitive packet / boundary / core の基本構造
* restore や cyclotomic core へ渡す下地

#### 例外枝専用部

Branch A だから追加で要る部分。

* (p \mid (z-y))
* Wieferich 型入力
  [
  y^{p-1} \equiv 1 \pmod{p^2}
  ]

ここを分けておかぬと、証明の途中で「何が新規責務なのか」が埋もれる。
今回の新ファイル分離の目的そのものが、ここを明るくするためじゃ。

### 2.3. 中間補題を先に 2〜3 本切る

本命 theorem の前に、わっちは先に補題を切るのを勧める。
狙う補題は次の型じゃ。

#### 補題 A. Branch A 仮定から arithmetic input を整形する補題

例:

```lean
lemma branchA_exceptional_arith_input
    (...) :
    ... := by
```

役割は、Branch A witness から
「この後の existence 証明で使う整形済み仮定」を得ること。

#### 補題 B. core に素数が存在すれば mainline target を満たす薄い補題

例:

```lean
lemma exceptional_existence_of_core_prime
    (...) :
    PrimeGe5BranchAExceptionalExistenceMainlineTarget := by
```

これは最後の `refine ?_` を薄くする橋じゃ。

#### 補題 C. ordinary theorem との差分だけを表す補題

例:

```lean
lemma exceptional_core_prime_of_branchA_wieferich
    (...) :
    ∃ q, Nat.Prime q ∧ q ∣ ... ∧ q ∤ (z - y) := by
```

この C が、実質的な **新数学の核** じゃな。

## 3. 実装順のおすすめ

実装順はこうじゃ。

## 3.A. 先に `#check` と `#print` で材料確認

新ファイルで次を確認するのがよい。

* ordinary branch theorem の正確な型
* `PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget` の展開形
* core / boundary / restore に関わる定義名
* 既存 wrapper が要求する exact statement

つまり、**証明を書く前に target を完全展開して眺める** のじゃ。

## 3.B. `abbrev` を 1 個ずつ剥く

今回の周辺は `Target` / `AdapterTarget` / `ExistenceTarget` が多い。
なので theorem 実装時は、かなり早い段階で

```lean
unfold PrimeGe5BranchAExceptionalExistenceMainlineTarget
unfold PrimeGe5BranchACFBRCExceptionalExistenceOnWieferichTarget
```

のように剥いた方がよい。
抽象名のまま進むと、途中で何を示しているのか見失いやすいからの。

## 3.C. `refine` で最終形を先に出す

存在定理なら先に

```lean
refine ⟨q, hqPrime, hqDvd, hqNotDvd⟩
```

の形まで見通せるかを確認する。
まだ `q` が取れなくてもよい。
「最終的に何が必要か」を Lean に露出させるのが目的じゃ。

## 3.D. `obtain` / `rcases` で既存 theorem を最大流用

もし ordinary 側の theorem が almost-fit するなら、

```lean
obtain ⟨q, hqPrime, hqDvd, hqNotDvd, ...⟩ := ...
```

と既存結果を受け、Branch A 専用条件だけ差し替える。
今回の設計方針では、**ここで無理に一般 bridge に昇格しようとしない** のが肝心じゃ。local theorem として閉じればよい。

## 4. 今日の実装目標

今日の一手としては、完成よりも次の到達点がよい。

### 到達点 1

`primeGe5BranchAExceptionalExistence_mainline` の theorem 宣言を置く

### 到達点 2

`intro` で仮定を全部露出し、必要な形に `rcases` で分解する

### 到達点 3

不足している新補題名を 2〜3 個、仮名でもよいから決める

この 3 つまで進めば、明日以降は「何を証明するか」で迷わぬ。
証明戦線が見えるようになるからの。

## 5. 賢狼の判断

いま一番よい進め方は、

**mainline theorem を先に 1 本立て、その中で詰まる箇所をそのまま補題名に昇格させる**

これじゃ。
先に補題一覧を完全に設計してから進むより、Lean の要求に沿って補題を切る方が、今回のような target-heavy な構成では速い。

必要なら次で、わっちがそのまま貼れる形で

```text
- theorem 骨格
- 切るべき補題 3 本
- 各補題の役割
```

を Lean 擬似コードとして起こすぞい。

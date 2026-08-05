# 260804 Issue: Wallis–Petal 階乗経路 改修計画書

- Status: Draft / not implemented
- Date: 2026-08-04
- Target branch examined: `develop`
- Conversation CID: `6a70c207-6590-83e8-83ff-cfc11d956da4`
- Historical workspace: `lean/dk_math/docs/dev/cf-wallis-bridge-260704`

## 1. 決定事項

Wallis 関連補題を下流で本格利用する前に、中央比率の階乗経路を改修する。

現行実装では `DkMath.Pascal.WallisCosmicPetalBridge` の中央比率証明が
`Nat.factorial` を直接正本としており、`DkMath.Petal.Counting` の動的積・階乗
bridge は実依存に入っていない。

改修後は、次を主経路とする。

```text
正の Petal 単位核
  -> 可変 lap-base を持つ Petal orbit
  -> 階乗 Petal
  -> Petal 中央階乗比
  -> Wallis 左半積
  -> Wallis–Cosmic gap 有限積
  -> 極限層
```

`Nat.factorial` と `Nat.choose` は、Petal 主経路の定義源ではなく、既存数学 API
との互換性を示す境界 bridge に限定する。

## 2. 今回発見した設計負債

### 2.1 Petal 側

`DkMath.Petal.Counting` には既に次がある。

```lean
def relPetalTotal (n lap : Nat) : Nat :=
  baseUnitCore n * lapBase n ^ lap


def dynamicOrbitTotal (b : Nat -> Nat) (k : Nat) : Nat :=
  Finset.prod (Finset.range k) b


def dynamicPetalTotal (a : Nat -> Nat) (k : Nat) : Nat :=
  a 0 * dynamicOrbitTotal (fun i => a i + 1) k
```

また、

```lean
theorem dynamicOrbitTotal_succIndex_eq_factorial (k : Nat) :
    dynamicOrbitTotal (fun i => i + 1) k = Nat.factorial k
```

も存在する。

しかし現行 `dynamicPetalTotal` は、初期核 `a 0` と各 lap の基底 `a i + 1` を
同じ列 `a` に結び付けている。この形は固定 Petal の動的一般化には適するが、
「初期単位核」と「増殖に使う基底列」を独立に選びたい階乗 Petal の正本 API
としては窮屈である。

### 2.2 Wallis 側

`DkMath.Pascal.WallisCosmicPetalBridge` では、中央比率を一度
`centralRatioFactorialQ` に落とし、次の Mathlib 階乗補題を直接使っている。

```text
Nat.choose_eq_factorial_div_factorial
Nat.factorial_mul_factorial_dvd_factorial
Nat.factorial_succ
```

したがって、ファイル名に `Petal` が含まれていても、階乗の形式的供給元は
`DkMath.Petal` ではない。

### 2.3 極限側

`DkMath.Pascal.WallisLimitBridge` は有限積を `Real.Wallis.W` に同定し、

```lean
Real.Wallis.tendsto_W_nhds_pi_div_two
```

へ接続している。

これは薄い bridge として正しいが、次の二つは別問題として扱う必要がある。

1. DkMath の有限階乗経路が Gamma を明示的に使わないこと。
2. 利用する Mathlib Wallis 定理の依存閉包にも Gamma 経路がないこと。

今回の第一目的は 1 を Petal 正本で達成すること。2 は依存監査 checkpoint とし、
必要なら独立 Wallis 極限証明を別計画へ昇格する。

## 3. 数学的意味の修正

### 3.1 `0! = 1` と零単位核を分離する

次の二つを混同しない。

```text
core = 0:
  0 角形に相当する退化核。
  Petal は伸びず、総量は常に 0。

lap = 0:
  有効な初期単位核だけが残る状態。
  単位核が 1 なら結果は 1。
```

したがって `0! = 1` の Petal 解釈は、

> 零単位核の値ではなく、最小有効単位核 `1` に対して増殖 lap を一度も適用して
> いない零周状態

とする。

$$
\operatorname{FactorialPetal}(0)
=
1\cdot\prod_{i<0}(i+1)
=
1
$$

### 3.2 Petal が成立する最小核

Petal の幾何・数え上げとして有効な単位核は正である、と明示する。

$$
\operatorname{IsValidPetalCore}(n)
\iff
0<n
$$

最小有効核は `1`。

$$
0<n
\Longrightarrow
1\le n
$$

型としては、現在の Mathlib で `PNat` / `ℕ+` が安定利用できるかを先に調査する。
利用条件や import コストが不適切なら、DkMath 内で次の薄い subtype を採用する。

```lean
abbrev PositivePetalCore := {n : Nat // 0 < n}
```

`DkMath.Petal.CoreUnit` は現在 `NP` 位相単位の alias であり、この自然数の正核とは
責務が異なる。既存 `CoreUnit` を流用して意味を混ぜない。

## 4. 改修目標

### Goal A — Petal counting の意味を固定

1. 零核は退化し、全 lap で `0` のままである。
2. 正核は Petal の有効核である。
3. `1` は最小有効核である。
4. 零周は初期核だけを返す。
5. 固定基底列は等比成長を返す。
6. 後続自然数基底列は階乗を返す。

### Goal B — 階乗 Petal を正本化

正の初期核と lap-base 列を分離した canonical total を追加する。

```lean
def petalOrbitTotal
    (core : Nat) (base : Nat -> Nat) (lap : Nat) : Nat :=
  core * dynamicOrbitTotal base lap
```

正本の階乗 Petal は、

```lean
def factorialPetal (n : Nat) : Nat :=
  petalOrbitTotal 1 (fun i => i + 1) n
```

とする。

この定義から、まず Petal 自身の再帰則を証明し、その後に互換定理として
`Nat.factorial` と一致させる。

### Goal C — Wallis の主経路を Petal 化

Wallis 有限層では、Petal 階乗を用いた中央比率を主役にする。

```lean
def petalCentralRatioQ (m : Nat) : Rat :=
  ((2 : Rat) ^ (2 * m) * (factorialPetal m : Rat) ^ 2) /
    (factorialPetal (2 * m) : Rat)
```

主定理は `Nat.choose` ではなく、この Petal 比率から左半積へ進める。

```text
petalCentralRatioQ
  -> centralOddRatioPartialQ
  -> wallisPartialQ
  -> cosmicPartialQ
```

既存の choose 版 `centralRatioQ` は互換入口として残し、

```lean
theorem centralRatioQ_eq_petalCentralRatioQ
```

を介して主経路へ接続する。

### Goal D — 依存経路を監査可能にする

ドキュメントと theorem 名から、次の層が判別できるようにする。

```text
Petal finite core:
  Nat.choose / Gamma / pi を使わない

Compatibility layer:
  Nat.factorial / Nat.choose と一致させる

Wallis limit layer:
  Real.Wallis の既存極限へ接続する

Strict provenance layer, optional:
  Mathlib Wallis 定理の依存源を監査または独立証明する
```

## 5. 非目標

今回の改修で、直ちに次までは行わない。

1. 完全な Stirling 公式の再証明。
2. Gamma 関数の置換または削除。
3. `Real.Wallis.tendsto_W_nhds_pi_div_two` の即時再実装。
4. 既存 Wallis 公開 theorem 名の破壊的変更。
5. `DkMath.FLT.PetalCoreUnit` の NP 位相モデルとの統合。

## 6. 推奨モジュール構成

### 6.1 Petal

第一候補は次の構成。

```text
DkMath.Petal.Counting
  raw Nat counting
  dynamicOrbitTotal
  petalOrbitTotal
  zero-core / positive-core generic lemmas

DkMath.Petal.Factorial
  PositivePetalCore
  unitPetalCore
  factorialPetal
  factorial recurrence
  Nat.factorial compatibility
```

`DkMath.Petal.lean` には `DkMath.Petal.Factorial` を `Counting` の直後に追加する。

小規模で済むなら `Factorial.lean` の内容を `Counting.lean` に置く案もあるが、
Wallis・Stirling・Gamma から再利用される公開面になるため、独立モジュールを推奨する。

### 6.2 Pascal / Wallis

既存ファイルを破壊的に分割せず、まずは
`WallisCosmicPetalBridge.lean` が `DkMath.Petal.Factorial` を import する。

内部の移行順は次。

```text
centralRatioFactorialQ
  -> petalCentralRatioQ

centralRatioQ_eq_factorialQ
  -> centralRatioQ_eq_petalCentralRatioQ

centralRatioFactorialQ_eq_centralOddRatioPartialQ
  -> petalCentralRatioQ_eq_centralOddRatioPartialQ
```

改修後も既存公開 theorem は alias または短い wrapper として維持する。

将来、責務分離が必要になった場合のみ、次へ分割する。

```text
DkMath.Pascal.WallisFiniteCore
DkMath.Pascal.WallisPetalFactorialBridge
DkMath.Pascal.WallisCosmicPetalBridge
```

## 7. 実装フェーズ

### Phase 0 — 現状固定

1. 現行 Wallis theorem 一覧を記録する。
2. `lake build` の基準結果を保存する。
3. `Nat.factorial`, `Gamma`, `Real.Wallis` の利用箇所を grep する。
4. 既存公開 theorem の利用箇所を検索する。

### Phase 1 — 有効 Petal 核

追加候補。

```lean
def IsValidPetalCore (n : Nat) : Prop := 0 < n

def IsDegeneratePetalCore (n : Nat) : Prop := n = 0

abbrev PositivePetalCore := {n : Nat // IsValidPetalCore n}

def unitPetalCore : PositivePetalCore := ⟨1, by decide⟩
```

必要 theorem。

```text
relPetalTotal_zero_core
relPetalTotal_pos_of_pos_core
validPetalCore_one
one_le_of_validPetalCore
unitPetalCore_is_minimum
```

### Phase 2 — canonical Petal orbit

追加候補。

```lean
def petalOrbitTotal
    (core : Nat) (base : Nat -> Nat) (lap : Nat) : Nat :=
  core * dynamicOrbitTotal base lap
```

必要 theorem。

```text
petalOrbitTotal_zero
petalOrbitTotal_succ
petalOrbitTotal_zero_core
petalOrbitTotal_const
petalOrbitTotal_pos
relPetalTotal_eq_petalOrbitTotal_const
```

既存 `dynamicPetalTotal` は削除せず、`petalOrbitTotal` の特殊化 theorem を追加する。

### Phase 3 — 階乗 Petal

追加候補。

```lean
def factorialPetal (n : Nat) : Nat :=
  petalOrbitTotal 1 (fun i => i + 1) n
```

必要 theorem。

```text
factorialPetal_zero
factorialPetal_succ
factorialPetal_pos
factorialPetal_eq_dynamicOrbitTotal
factorialPetal_eq_factorial
```

重要な証明順は、

```text
Petal 定義
  -> Petal zero / succ
  -> Nat.factorial との一意性・互換性
```

とする。最初から `Nat.factorial` へ rewrite して Petal theorem を済ませない。

### Phase 4 — Wallis 有限層の切替

1. `petalCentralRatioQ` を追加する。
2. Petal 再帰則だけで `centralOddRatioPartialQ` との一致を証明する。
3. 既存 `centralRatioQ` との互換 theorem を追加する。
4. 既存 Wallis / Cosmic theorem を Petal 主経路へ付け替える。
5. 古い private `centralRatioFactorialQ` 群を削除または compatibility-only に縮退する。

### Phase 5 — 下流回帰

対象。

```text
DkMath.Pascal.WallisLimitBridge
DkMath.Pascal.WallisGrowthBridge
DkMath.Pascal.WallisCosmicPetalBridge
DkMath.Pascal
DkMath.Petal
DkMath
```

公開 theorem 名を維持し、下流で大規模 rewrite が発生しないことを確認する。

### Phase 6 — Gamma / pi 依存監査

二段階で実施する。

```text
Level A:
  DkMath の Petal finite route に Gamma import・Gamma theorem がない。

Level B:
  Mathlib の Real.Wallis 極限定理の実証明経路を調査し、
  Gamma 経路を使っているか否かを記録する。
```

Level B で目的に反する依存が判明した場合、独立 Wallis 上下評価の新規 issue を起こす。

## 8. 受入条件

### Petal semantics

- [ ] `core = 0` と `lap = 0` の意味が theorem と docstring で分離されている。
- [ ] 有効 Petal 核が `0 < core` として定義されている。
- [ ] `1` が最小有効核である。
- [ ] `factorialPetal 0 = 1` が「最小単位核の零周」として証明されている。
- [ ] 固定 lap-base が等比数列を回収する。
- [ ] `i + 1` lap-base が階乗を回収する。

### Wallis route

- [ ] Petal 中央比率から Wallis 左半積への主定理がある。
- [ ] 主定理の証明本体で `Nat.factorial_succ` を直接使わない。
- [ ] choose 版中央比率は互換 theorem として Petal 版に一致する。
- [ ] 既存 Wallis / Cosmic 公開 theorem が維持される。

### Provenance

- [ ] 有限主経路に `Gamma` が現れない。
- [ ] `Nat.factorial` の利用は compatibility layer に限定される。
- [ ] `Real.Wallis` 依存の由来が文書化される。

### Build

- [ ] `lake build DkMath.Petal.Counting`
- [ ] `lake build DkMath.Petal.Factorial`
- [ ] `lake build DkMath.Petal`
- [ ] `lake build DkMath.Pascal.WallisCosmicPetalBridge`
- [ ] `lake build DkMath.Pascal.WallisLimitBridge`
- [ ] `lake build DkMath.Pascal.WallisGrowthBridge`
- [ ] `lake build DkMath.Pascal`
- [ ] `lake build DkMath`
- [ ] `git diff --check`

## 9. リスク

### Off-by-one

`Finset.range n` は `0, ..., n-1` なので、`fun i => i + 1` の積は `1, ..., n`。
この添字規約を docstring と小例で固定する。

### `PNat` API の不確実性

現在の Mathlib 版での名称・notation・import を調査してから採否を決める。
調査前に `PNat` へ全面依存しない。

### 意味の異なる CoreUnit

既存 `DkMath.Petal.CoreUnit` は NP 位相単位である。自然数の正 Petal 核と名前を
衝突させない。

### 見せかけの Petal 化

証明冒頭で `factorialPetal_eq_factorial` に rewrite し、その後すべてを
`Nat.factorial` で証明すると、実験目的を満たさない。
Petal zero / succ theorem を主証明で使うことを受入条件に含める。

### 隠れた解析依存

`import Mathlib` は依存監査を曖昧にする。改修後、可能なら Wallis / Petal 新規
モジュールの import を具体化する。ただし import 最適化は証明安定後に行う。

## 10. 推奨最初の実装 checkpoint

最初の PR または作業 branch では、Wallis をまだ触らず次だけを閉じる。

```text
Checkpoint P0

DkMath.Petal.Counting:
  IsValidPetalCore
  petalOrbitTotal
  zero / succ / const / positivity

DkMath.Petal.Factorial:
  factorialPetal
  factorialPetal_zero
  factorialPetal_succ
  factorialPetal_eq_factorial
```

この checkpoint が Green になった後に Wallis の private factorial helper を交換する。

## 11. 完了時の主張

改修完了後に主張してよいのは次。

> Wallis–Cosmic 有限積へ入る中央階乗比は、正の最小 Petal 単位核 `1` と可変
> lap-base `i + 1` から構成された階乗 Petal を正本として導出される。
> `0! = 1` は零核の値ではなく、最小有効単位核が零周で保存される結果である。

極限 `π / 2` の完全な Gamma 非依存性については、Mathlib Wallis 定理の依存監査
完了後にのみ、より強い主張へ進む。

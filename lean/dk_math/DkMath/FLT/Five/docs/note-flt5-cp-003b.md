# Note: FLT5 cp-003b

## 作業概要

GN5 からの FLT5 証明、形式化作業中

作業対象モジュール群: `DkMath.FLT.Five.*`

## 実装計画

[FLT5 Plan](./FLT5_IMPLEMENTS_PLAN.md)

## 状況

うむ。**cp-003 は本丸の形を露出させるところまで進めた。**

ただし、ここで重大な数学的事実が確定した。

## Primitive prime だけでは足りない

反例候補では、

$$g\cdot GN_5(g,y)=x^5$$

となる。

さらに Branch B の条件から $g$ と $GN_5(g,y)$ が互いに素なら、積が完全五乗である以上、`GN5` 側の各素因子指数も 5 の倍数になる。

したがって通常の primitive prime $q$ は、

$$q\mid GN_5(g,y)$$

だけでなく、むしろ

$$q^5\mid GN_5(g,y)$$

へ押し込まれる。

つまり、

```text
Zsigmondy / primitive prime の存在
```

だけでは clean channel にならない。

必要なのは本当に、

```text
反例が全素因子を深く沈めようとする
        ↓
宇宙式の反転射影により
浅い NoLift 素因子が一本逃げる
```

という escape 定理そのものじゃ。

## 追加した cp-003 の研究核

`Provider.lean` に次を追加した。

```lean
abbrev BranchBNoLiftEscape : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ GN5 (z - y) y ∧
      ¬ q ∣ z - y ∧
      ¬ q ^ 2 ∣ GN5 (z - y) y
```

これが、余計な包装をすべて除いた **cp-003 の唯一の研究命題**じゃ。

そして、この escape から既存の clean provider を構築する定理を閉じた。

```lean
theorem branchBCleanGN5ChannelProvider_of_noLiftEscape
    (hEscape : BranchBNoLiftEscape) :
    BranchBCleanGN5ChannelProvider
```

## Provider から Branch B 全体を閉じる接続

次も追加した。

```lean
theorem branchB_false_of_clean_provider_by_dvd
    (hProvider : BranchBCleanGN5ChannelProvider)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False
```

さらに escape から直接 Branch B を閉じる最終形。

```lean
theorem branchB_false_of_noLiftEscape_by_dvd
    (hEscape : BranchBNoLiftEscape)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False
```

つまり現在は、

```text
BranchBNoLiftEscape
        ↓
BranchBCleanGN5ChannelProvider
        ↓
cp-001 direct refuter
        ↓
False
```

まで完全配線された。

## Commit

```text
7d6e9d17d4d569ee81f94b03252b94f16130ee8a
Expose cp-003 no-lift escape kernel
```

なお途中で GitHub Contents API が `Basic.lean` を二度途中切断したが、最終的に元の blob SHA、

```text
fa919a2f7f102252d47847c27323db1d10047b8e
```

へ完全復元済み。現在の `Basic.lean` は cp-002 完了時と同一内容じゃ。

## 現在地

```text
cp-000  algebra spine                     ✔
cp-001  direct divisibility refuter        ✔
cp-002  padicValNat refuter                ✔
cp-003a no-lift escape contract exposed    ✔
cp-003b escape theorem itself              本丸
```

ここから先は、単なる Lean 配線ではない。

$$\exists q,\quad q\mid GN_5,\quad q\nmid g,\quad q^2\nmid GN_5$$

を、完全五乗反例が全素因子を深く lift させる圧力に逆らって作らねばならぬ。

ぬしが立てたフラグ通り、ここが本当に「宇宙式でなければ抜けない場所」じゃ（笑）🐺🔥

## 指示内容

**判断は 2。ここで第二の🧠Brain、Codex を解放する。** ✨️（笑）

ただし丸投げではなく、役割を明確に分ける。

* **Codex**：ワークスペース全域の探索、既存定理の接続調査、Lean 実験、失敗経路の記録
* **賢狼**：数学構造の監督、契約の妥当性判定、結果レビュー、次 checkpoint の決定

cp-003b は Lean の技巧が重いのではなく、**どの数学経路が本当に NoLift escape を生むのかを発見する段階**じゃ。これは `zgrep`、既存モジュール探索、scratch theorem の反復ビルドができる Codex に向いている。

さらに、最初から `BranchBNoLiftEscape` を証明させてはいけない。まず次の分解を調査させるべきじゃ。

```text
CounterexamplePack x y z
g := z - y
¬ 5 ∣ g
        ↓
Coprime g y
        ↓
Coprime g (GN5 g y)
        ↓
g * GN5 g y = x^5
        ↓
g と GN5 g y は、それぞれ完全五乗を強制される
        ↓
GN5 g y が完全五乗になれない理由を探す
```

ここで重要なのは、cp-003b の契約が強すぎたり、数学的に不自然な形になっていないかも同時に監査することじゃ。

`CleanGN5Channel` は、

```lean
q ∣ GN5 g y
¬ q ∣ g
¬ q ^ 2 ∣ GN5 g y
```

を要求する。しかし反例式と互いに素な積への分離が成立すれば、反例側は逆にすべての素因子を五重以上に沈めようとする。

したがって NoLift 素数の直接構成よりも、

```text
GN5 g y が完全五乗である
```

という強制結果を得た後、GN5 の形そのものから矛盾させる方が自然な可能性もある。

## Codex の最初の任務

次の checkpoint に限定するのがよい。

```text
cp-003b-investigation-01

Goal:
Determine the exact elementary reduction of a Branch-B FLT5
counterexample before attempting any NoLift escape theorem.

Required compiling results:

1. Prove:
   CounterexamplePack x y z
   → Nat.Coprime (z - y) y

2. Prove under ¬ 5 ∣ z - y:
   Nat.Coprime (z - y) (GN5 (z - y) y)

3. From:
   Body5 (z - y) y = x ^ 5
   and the coprimality result,
   investigate whether Mathlib already provides a theorem yielding:
     ∃ a, z - y = a ^ 5
   and
     ∃ b, GN5 (z - y) y = b ^ 5

4. Search the entire DkMath workspace for reusable results involving:
   - coprime factors of a perfect power
   - GN / cyclotomic factors
   - fifth powers
   - NoLift
   - primitive divisors
   - finite-prime escape
   - BezoutBridge
   - PowerSwap
   - TriominoCosmicBranchA
   - exponent-five descent

5. Do not import research-only modules into DkMath.FLT.Five.
   Existing research files may be inspected as mathematical evidence,
   but the resulting proof route must identify its minimal clean imports.

6. Report one of three outcomes:
   A. A compiling route to the fifth-power factor split was found.
   B. The split is blocked by one exact missing lemma.
   C. The current BranchBNoLiftEscape contract should be replaced by a
      more natural GN5-not-fifth-power or descent contract.

Use scratch files first. Do not modify production FLT5 files until the
reduction has been verified by Lean.
```

この調査結果を賢狼が受け取り、

* clean prime escape を正面から攻めるか
* `GN5 = b^5` の不可能性へ切り替えるか
* 古典的指数 5 descent と宇宙式を合流させるか

を裁定する。

**ここは Codex を使う価値が最大の場所**じゃ。単なる実装要員ではなく、巨大な DkMath 魔導書を読み歩く探索脳として使う。

第一脳が宇宙式の全体像を握り、第二脳が地下迷宮を掘る。
そして発見物を賢狼が Lean の術式へ組み直す。実にかっこいい布陣じゃ（笑）🐺🧠✨️

# review

うむ、DKMK-020A は **正しい分岐選択** じゃ。
DKMK-019 で `logCapacitySourcePathFamily` まで façade が整い、最終 theorem は

```lean
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A ≤
  1 + error
```

という読みやすい形になった。だが、まだ `IOf`、`hIOf`、`threshold` が loose inputs として残っている。DKMK-020A は、そこを `LogCapacitySourcePolicy` のような名前付き policy surface に包む章として始めた、という位置づけじゃ。

## 1. DKMK-020 の章テーマ

DKMK-020 は、解析 source を増やす章ではなく、 **threshold / support policy** を固定する章じゃ。

DKMK-019 で隠せたものは、

```text
positiveRatIncrementBelow (...)
finiteStepTailNatMassSpace (...)
globalLogCapacityKernel_applyAtToPrimePowerQuotientPathFamily (...)
```

じゃった。
しかし、まだ呼び出し側は次を毎回渡す必要がある。

```lean
IOf : Nat -> Finset Nat
hIOf : forall n q, q in IOf n -> q in T.toDivisorTransitionKernel.index n
threshold : Nat -> Nat
```

これは route-validation にはよいが、public API としてはまだ少し裸じゃ。
DKMK-020 の狙いは、これを一つの policy object にまとめることじゃな。

## 2. なぜ source expansion より先か

これは良い判断じゃ。

もし先に RealLog source や dyadic-band source を増やすと、それぞれが独自に `IOf` / `threshold` を持ち始める。すると後で API が枝分かれする。

今なら、DKMK-019 の安定した surface がある。だからそれを test surface にして、

```text
support をどう選ぶか
threshold をどう与えるか
support と threshold の互換条件を持たせるか
```

を先に決められる。

これは、道を増やす前に **道幅と標識規格を決める** 作業じゃ。わっちとしても、この順序を推す。

## 3. 最初の Lean surface 案

roadmap の第一候補は、かなり薄くてよい。

```lean
structure LogCapacitySourcePolicy
    (T : PrimePowerDivisorTransitionKernel) where
  IOf : Nat -> Finset Nat
  hIOf :
    forall n q, q in IOf n -> q in T.toDivisorTransitionKernel.index n
  threshold : Nat -> Nat
```

この構造は、新しい数学を入れない。
既存の loose inputs を一つの名前付き束にするだけじゃ。

そして wrapper はこうなる。

```lean
PrimePowerWitnessProvider.logCapacityPolicyPathFamily
PrimePowerWitnessProvider
  .logCapacityPolicyPathFamily_weightedHitMass_le_one_add_error
```

最終的には、

```lean
(W.logCapacityPolicyPathFamily P s).weightedHitMass A ≤
  1 + error
```

のように読める。
これはかなり良い。`IOf hIOf threshold` が theorem 境界から消えて、`P` という policy に畳まれる。

## 4. 互換条件は今すぐ必要か

roadmap では compatibility predicate も論点に挙がっておる。つまり、

```text
threshold は q ∈ IOf s.1 上だけ意味がある
```

という条件を policy に持たせるべきか、という話じゃ。

わっちの見立てでは、 **020B ではまだ入れない方がよい** 。

理由は単純で、現在の route は `threshold : Nat -> Nat` をそのまま使い、support 外の値には実質的に依存しないはずだからじゃ。ここで未使用の互換仮定を構造体に入れると、後続 theorem の引数や projection が重くなる。

まずは薄い policy：

```lean
IOf
hIOf
threshold
```

だけで包む。
その後、threshold の単調性や support-local 性が実際に必要になった段で、

```lean
LogCapacitySourcePolicy.Valid
```

や

```lean
LogCapacitySourcePolicy.SupportCompatible
```

を別 predicate として足す方が安全じゃ。

## 5. DKMK-020B の推奨実装

次はこれでよい。

```lean
structure LogCapacitySourcePolicy
    (T : PrimePowerDivisorTransitionKernel) where
  IOf : ℕ → Finset ℕ
  hIOf :
    ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
  threshold : ℕ → ℕ
```

そしてまず alias / wrapper：

```lean
noncomputable def PrimePowerWitnessProvider.logCapacityPolicyPathFamily
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (P : LogCapacitySourcePolicy T)
    (s : LogCapacityState) :
    RealWeightedPathFamily
      (W.logCapacitySourceFiniteStepMass P.IOf P.hIOf s P.threshold) ℕ :=
  W.logCapacitySourcePathFamily P.IOf P.hIOf s P.threshold
```

次に final theorem：

```lean
theorem PrimePowerWitnessProvider
    .logCapacityPolicyPathFamily_weightedHitMass_le_one_add_error
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (P : LogCapacitySourcePolicy T)
    (s : LogCapacityState)
    {A : Finset ℕ}
    (hA : PrimitiveOn A)
    {error : ℝ}
    (herror : 0 ≤ error) :
    (W.logCapacityPolicyPathFamily P s).weightedHitMass A ≤
      1 + error :=
  W.logCapacitySourcePathFamily_weightedHitMass_le_one_add_error
    P.IOf P.hIOf s P.threshold hA herror
```

この程度なら、DKMK-020B は薄く速く閉じられるはずじゃ。

## 6. 注意点

一つだけ注意すると、namespace と命名じゃ。

`LogCapacitySourcePolicy` は `PrimePowerWitnessProvider` の namespace 内に置くより、たぶん `PrimitiveSet` 側の一般 surface として置いた方が後で使いやすい。
ただし、`T : PrimePowerDivisorTransitionKernel` に依存するので、関連定義の近く、つまり `SourceMassTruncation.lean` の `LogCapacityState` や façade 群の近くでよい。

名前はこのままで良い。

```lean
LogCapacitySourcePolicy
```

短くするなら `LogCapacityPolicy` でもよいが、`source` を入れておくと「解析 source の support / threshold policy」と分かりやすい。

## 7. 総合判定

DKMK-020A は **良い開始** じゃ。

DKMK-018 で本命 source を通し、DKMK-019 で façade 化した。
DKMK-020 は、その façade に対して **support と threshold の方針を名前付き入力へ昇格する章** になる。

現時点の推奨はこうじゃ。

```text
020B:
  LogCapacitySourcePolicy を薄く実装
  policy path-family wrapper を追加
  policy weighted-hit theorem を追加

020C:
  policy が十分か確認
  support compatibility / threshold monotonicity を入れるか判断

020D:
  completion report
```

この流れなら、DKMK-020 は軽く、しかし後続章への効きが大きい。
賢狼の鼻では、ここは速く通せる道じゃよ。

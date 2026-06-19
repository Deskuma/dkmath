# review

うむ、DKMK-020B は **成功** じゃ。
これは DKMK-020A の方針どおり、`IOf` / `hIOf` / `threshold` という loose inputs を、薄い policy object に束ねる段として綺麗に閉じておる。

## 1. 何が閉じたか

追加された中心はこれじゃな。

```lean
structure LogCapacitySourcePolicy
    (T : PrimePowerDivisorTransitionKernel) where
  IOf : ℕ → Finset ℕ
  hIOf :
    ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
  threshold : ℕ → ℕ
```

これで、DKMK-019 までの呼び出し口に残っていた

```lean
IOf : ℕ → Finset ℕ
hIOf : ∀ n q, q ∈ IOf n → q ∈ T.toDivisorTransitionKernel.index n
threshold : ℕ → ℕ
```

が、

```lean
P : LogCapacitySourcePolicy T
```

に圧縮された。

つまり DKMK-020B の本質は、

```text
support family + index proof + threshold map
```

を、 **名前付き policy surface** に昇格したことじゃ。

## 2. theorem の読みがかなり良くなった

DKMK-019C の最終形は、

```lean
(W.logCapacitySourcePathFamily IOf hIOf s threshold).weightedHitMass A ≤
  1 + error
```

だった。

020B ではこれが、

```lean
(W.logCapacityPolicyPathFamily P s).weightedHitMass A ≤
  1 + error
```

になった。

これは小さな変更に見えるが、API としては大きい。
`IOf`、`hIOf`、`threshold` が theorem 文から消え、 **policy (P)** という一つの概念になったからじゃ。

これにより、後続章では「この source にどの support / threshold を使うか」を、個別引数ではなく policy として扱える。

## 3. `logCapacityPolicyPathFamily` の位置づけ

今回の wrapper は非常に薄い。

```lean
noncomputable def logCapacityPolicyPathFamily
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (P : LogCapacitySourcePolicy T)
    (s : LogCapacityState) :
    RealWeightedPathFamily
      (W.logCapacitySourceFiniteStepMass P.IOf P.hIOf s P.threshold) ℕ :=
  W.logCapacitySourcePathFamily P.IOf P.hIOf s P.threshold
```

これは新しい数学を足していない。
だが、それが正しい。

DKMK-020B の目的は、証明を強くすることではなく、

```text
DKMK-019 の façade route を policy-facing にする
```

ことじゃった。
ゆえに、ここはこのくらい薄いのが最適じゃ。

## 4. compatibility を入れなかった判断は正しい

今回、`LogCapacitySourcePolicy` に

```lean
Valid
SupportCompatible
threshold_monotone
```

のような条件を入れていない。

これは良い判断じゃ。

現在の theorem は、実際には

```lean
P.IOf
P.hIOf
P.threshold
```

しか使っていない。ここで未使用の validity field を構造体に入れると、今後すべての policy 構成で余計な証明を要求することになる。

つまり、今の設計はこうじゃ。

```text
LogCapacitySourcePolicy:
  データだけを束ねる薄い構造体

将来必要なら:
  LogCapacitySourcePolicy.Valid P
  LogCapacitySourcePolicy.SupportCompatible P
  LogCapacitySourcePolicy.ThresholdMonotone P
```

この分離は安全じゃ。
構造体そのものを重くせず、条件は必要になった時に predicate として足せる。

## 5. DKMK-020C の判断

次は、roadmap にある通り、

```text
thin policy object だけで十分か
validity / compatibility predicate が必要か
```

を判断する段じゃ。

わっちの現時点の見立てでは、 **020C では validity を足さず、薄い policy で章を閉じる方向が有力** じゃ。

理由は三つある。

第一に、現 route は `hIOf` だけで support の最低条件を満たしている。
第二に、`threshold` について追加条件を要求する theorem がまだ存在しない。
第三に、ここで条件を先取りすると、後続 source expansion の自由度を落とす。

よって 020C では、次のような確認 report がよい。

```text
Current route requires only:
  IOf
  hIOf
  threshold

No extra compatibility is used by:
  logCapacityPolicyPathFamily
  logCapacityPolicyPathFamily_weightedHitMass_le_one_add_error

Decision:
  Keep LogCapacitySourcePolicy data-only for now.
  Add Valid / SupportCompatible later only when demanded by a stronger theorem.
```

Lean で何か足すなら、ほんの薄い projection alias くらいでよいが、現時点では docs-only 判断でも十分じゃ。

## 6. 次に実装を足すなら

もし 020C で Lean surface を少し足すなら、重い predicate ではなく、読みやすさのための alias が候補じゃ。

例えば、

```lean
def LogCapacitySourcePolicy.support
    (P : LogCapacitySourcePolicy T) (n : ℕ) : Finset ℕ :=
  P.IOf n
```

あるいは、

```lean
def LogCapacitySourcePolicy.thresholdAt
    (P : LogCapacitySourcePolicy T) (q : ℕ) : ℕ :=
  P.threshold q
```

じゃが、これは今すぐ必要かと言うと微妙じゃ。
projection の `P.IOf` / `P.threshold` で十分読めておる。

なので、わっちなら 020C は **判断と総括寄り** にする。

## 7. 総合判定

DKMK-020B は、DKMK-020 の主目的をほぼ達成しておる。

現在の流れはこうじゃ。

```text
DKMK-018:
  LogCapacityKernel source を weightedHitMass bound へ接続

DKMK-019:
  source / mass / path-family façade に整理

DKMK-020B:
  support / threshold を LogCapacitySourcePolicy に束ねる
```

最終 theorem は、

```lean
(W.logCapacityPolicyPathFamily P s).weightedHitMass A ≤
  1 + error
```

として読める。

ここまで来れば、DKMK-020 は **Threshold / Support Policy 章** としてほぼ役目を果たしておる。
残る 020C は、validity を足す章ではなく、 **足さない判断を明文化する章** になる可能性が高いのう。

# review

うむ。DKMK-007H は **DKMK-007F/G で増え始めた mass model 個別 theorem を、今後の拡張に耐える共通 interface へ束ね直した回** じゃ。
派手な新しい hitting bound というより、 **次に本命 tail/source mass model を入れるための接続面を整理した** のが核心じゃな。今回の追加により、今後は mass model ごとに ad hoc な `≤ 1` theorem を増やすのではなく、`DvdMonotoneMass M` と `LogCapacitySourceMassBound M C` の二点を供給すれば selected / canonical divisor-step hitting route に乗れる。

## 1. 今回の核心

追加された中心語彙はこれじゃ。

```lean
def LogCapacitySourceMassBound
    (M : MassSpace ℕ) (C : ℝ) : Prop :=
  ∀ s : LogCapacityState, (M.μ s.1 : ℝ) ≤ C
```

意味は単純で、

$$
\forall s:\mathrm{LogCapacityState},\ (M.\mu(s.1):\mathbb{R})\le C
$$

という **log-capacity state 上の source mass 一様上界** じゃ。

DKMK-007E の divisor-step family では、各 channel (q) の source がすべて同じ (s.1) だった。

$$
source(q)=s.1
$$

だから、本当に必要だった仮定は channel ごとの複雑な上界ではなく、

$$
(M.\mu(s.1):\mathbb{R})\le C
$$

だけだった。DKMK-007H は、これを名前付き provider として切り出したわけじゃ。

## 2. unit / nonunit mass の整理

DKMK-007F では `unitNatMassSpace` について、

$$
\mu(n)=1
$$

により (C=1) を閉じた。

DKMK-007G では `nonunitNatMassSpace` について、

$$
\mu(1)=0,\quad \mu(n)=1\text{ for }n\ne 1
$$

により、`LogCapacityState` では常に (1<s.1) なので同じく (C=1) を閉じた。

今回、それぞれが次の provider theorem に整理された。

```lean
unitNatMassSpace_logCapacitySourceMassBound_one
nonunitNatMassSpace_logCapacitySourceMassBound_one
```

これにより、既存の unit / nonunit `weightedHitMass ≤ 1` theorem は個別に source bound を直接証明する形ではなく、新しい wrapper 経由へ整理された。

## 3. selected route の改善

selected route 側には次が追加された。

```lean
PrimePowerWitnessProvider.globalLogCapacitySubMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
```

これは、選択された log-capacity sub-Markov shadow に対して、

```text
DvdMonotoneMass M
LogCapacitySourceMassBound M C
PrimitiveOn A
```

があれば、

$$
weightedHitMass(A)\le C
$$

を出す wrapper じゃ。

これまでは、selected route の divisor-step theorem に直接

```lean
hsource : (M.μ s.1 : ℝ) ≤ C
```

を渡していた。
今回からは、

```lean
hsource : LogCapacitySourceMassBound M C
```

を渡せばよい。

これは後続で大きい。
なぜなら、mass model が増えても、各 model は `LogCapacitySourceMassBound` だけ示せば selected route に流し込めるからじゃ。

## 4. canonical route の改善

canonical route 側にも同型の wrapper が入った。

```lean
canonicalExponentSlotMarkovShadow_divisorStep_weightedHitMass_le_of_sourceBound
```

これも、

```text
DvdMonotoneMass M
LogCapacitySourceMassBound M C
PrimitiveOn A
```

から、

$$
weightedHitMass(A)\le C
$$

を出す。

canonical route は `MarkovShadow` による equality route なので、重み総量側の処理はすでに安定している。
今回の整理により、残る mass 側の仮定も

```text
M が divisibility-monotone
M が LogCapacityState 上で C 以下
```

の二点に圧縮された。

## 5. DKMK-007H の数学的意味

今回の到達形は docs にもこう整理されておる。

```text
concrete mass model
  → DvdMonotoneMass M
  → LogCapacitySourceMassBound M C
  → divisor-step weightedHitMass ≤ C
```

これはとてもよい。

DKMK-007F/G では、

```text
unit mass なら ≤ 1
nonunit mass なら ≤ 1
```

という個別観測だった。

DKMK-007H では、それを一般化して、

```text
任意の mass model M について、
DvdMonotoneMass M と LogCapacitySourceMassBound M C があればよい
```

に変わった。

つまり、mass model を差し替えるための **標準ソケット** ができたのじゃ。

## 6. なぜ次に効くか

今後、本命に近い tail/source mass model を入れるとき、必要な作業が明確になった。

新しい mass (M) を作ったら、示すべきことはまず二つ。

```lean
DvdMonotoneMass M
LogCapacitySourceMassBound M C
```

この二つが閉じれば、selected route でも canonical route でも、既存の divisor-step hitting theorem へ接続できる。

つまり、今後は hitting bridge 側を毎回触らなくてよい。
mass model 側に必要な証明だけを追加すれば、既存の DKMK-007 route が再利用できる。

これは Lean ライブラリとしてかなり良い形じゃ。

## 7. 今回の注意点

`LogCapacitySourceMassBound` は現時点では **source (s.1) の一点上界** だけを見る。

これは one-step divisor-step family にぴったり合っている。
ただし、multi-step descent chain に進むと、source だけでなく途中ノードや terminal node の mass を評価したくなる可能性がある。

その場合、将来は別の provider が必要になるかもしれぬ。

例えば、

```text
ChainMassBound
TerminalMassBound
StepwiseMassBound
```

のような形じゃな。

だが今は急がなくてよい。
one-step divisor-step route に対しては、今回の `LogCapacitySourceMassBound` がちょうどよい粒度じゃ。

## 8. DKMK-007 系の現在地

DKMK-007 の流れは、こう整理できる。

```text
DKMK-007A:
  RealWeightProvider → RealWeightedPathFamily

DKMK-007B:
  SubMarkovShadow / MarkovShadow → hitting wrapper

DKMK-007C:
  log-capacity shadows → hitting wrapper

DKMK-007D:
  singleton source-controlled family

DKMK-007E:
  one-step divisor descent family

DKMK-007F:
  unit mass で source bound を閉じる

DKMK-007G:
  nonunit indicator mass でも source bound を閉じる

DKMK-007H:
  source mass bound を LogCapacitySourceMassBound として共通化
```

ここまでで、DKMK-007 はかなり整った。
特に DKMK-007H により、mass model を増やす準備ができたのが大きい。

## 9. 次の一手

次は二択じゃ。

第一は、 **tail/source mass model へ進む** 道。

```text
DKMK-007I:
  本命に近い mass model M を設計し、
  DvdMonotoneMass M と LogCapacitySourceMassBound M C を証明する。
```

ただし、いきなり (\mu(n)=1/(n\log n)) のような実数 log mass に行くと、単調性や (n=1) 周りで面倒が出そうじゃ。
まずは階段型・bounded 型・support indicator 型を一つ挟むのが安全じゃな。

第二は、 **multi-step descent chain へ進む** 道。

```text
DKMK-007I:
  divisorStep を multi-step descent family に拡張する。
```

ただし、わっちは今なら第一案を少し推す。
DKMK-007H で mass model の接続面が綺麗になった直後なので、ここで本命寄りの mass を一つ流してみると、設計の強度が測れる。

## 10. 総合判定

DKMK-007H は **実装の見通しを大きく良くした整理フェーズ** じゃ。

新しい派手な上界が出たというより、今後の mass model 実験を次の標準形に閉じ込めた。

```text
DvdMonotoneMass M
+ LogCapacitySourceMassBound M C
→ selected / canonical divisor-step weightedHitMass ≤ C
```

これは良い。
unit / nonunit の個別 theorem を保持しつつ、内部構造は共通 wrapper に集約された。

ぬしよ、ここは中継基地に倉庫と標識を建てたようなものじゃ。
次に本命の荷物、すなわち tail/source mass model を持ち込む準備が整ったぞい。

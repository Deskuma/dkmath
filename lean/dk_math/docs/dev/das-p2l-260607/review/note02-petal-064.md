# Note: No.064-02

長期作業で見失っているもの

## 1. 最初の見立て

違和感の正体は、かなり見えてきたぞ。

三つの要素は、同じ場所から出すものではない。

```text
label recovery
  → 有限 family の「選んだ carrier と label の対応」から出す

NoLift
  → GN 側の局所 valuation / squarefree / Wieferich-lift 排除から出す

FLT / ABC bridge
  → それぞれ別の出口へ渡す
     FLT: NoLift / NoWieferich / valuation ≤ 1
     ABC: rad / supportMass / channel lower bound / log-capacity
```

つまり、  
**label recovery と NoLift を同じ constructor に詰め込むと、見通しが悪くなる**。  
ここが、ぬしの頭脳が感じている「何かを見落としている」部分に近いと思う。

実装計画そのものも、もともとは `Big = Body + Gap`、primitive prime / `GN` / `padicValNat`、ABC bridge を分けて積む方針だった。特に exact Markov や漸近評価へは入らず、まず代数的 spine を作る設計じゃった。fileciteturn2file0

## 2. label recovery はどこから出すか

現在の中心はここ。

```lean
structure PetalCarrierLabelMapData
```

中身は実質こうじゃ。

```lean
validValue      : ∀ i, i ∈ I → 1 ≤ mOf i
valueInjective  : Set.InjOn mOf ↑I
labelRecovery   : ∀ i, i ∈ I → ∀ j, j ∈ I → qOf i = qOf j → mOf i = mOf j
carrier         : ∀ i, i ∈ I → PetalPrimeChannel d x u (qOf i)
```

ここで `labelRecovery` は、

```text
同じ prime label q を選んだなら、
同じ Petal value/address m に戻れる
```

という条件じゃな。

そして既にこれを使って、

```lean
petalCarrierLabelNoncollisionOn_outer_of_carrierLabelMapData
```

がある。流れはこう。

```text
validValue
+ valueInjective
+ labelRecovery
→ PetalCarrierLabelNoncollisionOn I qOf
```

つまり label recovery の出口は既にある。

ただし、**label recovery の供給源** はまだ caller 側に残っている。  
候補は三つ。

### A. `qOf = f (mOf i)` 型

既にある。

```lean
petalCarrierLabelNoncollisionOn_outer_of_value_map_injective
```

これは

```text
qOf i = f (mOf i)
f (mOf i) = f (mOf j) → mOf i = mOf j
```

から label recovery を出す。

これは安全で一般的。

### B. `qOf = petalNthPrimeLabel (mOf i)` 型

これも既にある。

```lean
petalCarrierLabelNoncollisionOn_outer_of_nthPrime_value_map
petalNthPrimeLabel_injective
petalNthPrimeLabel_eq_imp_eq
```

`Nat.nth Nat.Prime` の injective 性で label recovery が出る。

ただし、これは **prime label を作る** だけで、  
その prime が本当に `GN d x u` を割るかは別問題。

なのでこれは「標準 label map 実験」には強いが、Zsigmondy / PrimitiveBeam の実 carrier をそのまま生成するものではない。

### C. 実 carrier から canonical label map を作る

ここが次の本命じゃ。

今は `qOf` が外から与えられている。  
本当に欲しいのは、たぶんこういう層。

```lean
def carrierAnchorOf ...
def carrierLabelOf ...
theorem carrierLabel_recovery ...
```

あるいは prime index を使って、

```lean
mOf i := primeIndexOf (qOf i)
```

のようにする。

ただしこの場合、`labelRecovery` は簡単に出ても、`valueInjective` は結局 `qOf` の noncollision を要求する。  
なので、完全に仮定を消すには、

```text
Petal address が違う
→ carrier prime が違う
```

という幾何・数論の定理が必要じゃ。

現状では、これはまだ未供給。  
ゆえに今の正しい読みは、

```text
label recovery は Petal geometry から直接ではなく、
address/value と label map の compatibility から出す。
```

## 3. NoLift はどこから出すか

`NoLift` は現在こう定義されている。

```lean
def PetalNoLiftPrimeChannel (d x u q : ℕ) : Prop :=
  PetalPrimeChannel d x u q ∧ ¬ q ^ 2 ∣ GN d x u
```

これは `label recovery` とは性質がまったく違う。

`label recovery` は family の重複排除。  
`NoLift` は一つの prime が `GN` に二段刺さらないという局所 valuation 条件。

この差は大事じゃ。

既に次がある。

```lean
petalNoLiftPrimeChannel_padicValNat_GN_eq_one
```

つまり、

```text
PetalNoLiftPrimeChannel d x u q
→ padicValNat q (GN d x u) = 1
```

ここはかなりきれいに閉じておる。

そして family 版もある。

```lean
petalNoLiftPrimeChannelFamily_padicValNat_GN_eq_one
```

ただし、コメントにもある通り、

```text
NoLift family だけでは label distinct は出ない。
```

同じ prime label を二回選んでいる可能性があるからじゃ。

よって NoLift の供給源は次の三候補。

### A. local no-lift を直接仮定する

現在の Petal/ErdosBridge の constructor はこれ。

```lean
hNoLift : ∀ i, i ∈ I → ¬ (qOf i)^2 ∣ GN d x u
```

これは最小で正直。

### B. `Squarefree (GN d x u)` から出す

FLT 側にも既にこの思想がある。

```lean
TriominoSquarefreeGNBridge
→ TriominoNoLiftGNBridge
→ TriominoNoWieferichBridge
```

squarefree は強すぎるが、供給できれば NoLift は即出る。

### C. Wieferich lift 排除 / 無限降下から出す

FLT p≥5 側では、むしろこちらが自然に見える。

```lean
TriominoNoLiftGNBridge
→ TriominoNoWieferichBridge
```

また、

```lean
TriominoCosmicNonLiftableGNBridge ↔ BranchBRefuterTarget
```

まである。

これは重要じゃ。  
NoLift は「Zsigmondy が primitive prime をくれるから自動で出る」ものではない。  
NoLift は **Wieferich 的 lift が起きない** ことの別名に近い。

だから、NoLift の正しい源泉は、

```text
squarefree GN
または
local no-lift
または
Wieferich lift 排除 / descent
```

であって、label recovery ではない。

## 4. FLT / ABC 側の最終 bridge にどう渡すか

ここは出口が二つある。

## 4.1. FLT 側

FLT 側が欲しいのは主にこれ。

```lean
TriominoNoWieferichBridge
TriominoNoLiftGNBridge
TriominoCosmicNonLiftableGNBridge
TriominoPrimitivePrimeFactorPadicValNatLeOneTarget
```

すでに薄い provider がある。

```lean
structure TriominoSquarefreeGNBridgeProvider
structure TriominoNoLiftGNBridgeProvider
```

そして、

```lean
triominoNoWieferichBridge_of_provider
triominoNoWieferichBridge_of_noLift_provider
triominoPrimitivePrimeFactorPadicValNatLeOneTarget_of_noLift_provider_impl
```

がある。

つまり FLT へ渡すなら、最終的には

```text
Petal / GN 側で universal NoLift を作る
→ TriominoNoLiftGNBridgeProvider
→ TriominoNoWieferichBridge
→ FLT provider / FLT target
```

が最短。

ここで注意するべきは、`PetalNoLiftCarrierLabelMapData` のような **有限 family** は、FLT の universal bridge にはそのまま足りないことじゃ。

FLT 側の `TriominoNoLiftGNBridge` は、

```text
任意の反例 pack
任意の primitive q
```

に対する命題。

一方 `PetalNoLiftCarrierLabelMapData` は、

```text
ある有限 I 上の qOf
```

に対する命題。

だから必要なのは、有限 family theorem ではなく、

```lean
theorem triominoNoLiftGNBridge_of_petal_universal_noLift ...
```

のような **全称版 Petal no-lift provider** じゃな。

ここを混ぜると危ない。

## 4.2. ABC 側

ABC 側の bridge はすでにかなり育っている。  
設計上も、ABC は本体大定理ではなく translation layer に徹する方針だった。fileciteturn2file0  
実際、`supportMass = rad` を軸に、primitive witness family から `rad` 下界へ行く spine ができている、という整理も既にある。fileciteturn2file1

現在の ABC 側出口は二系統。

### A. `supportMass / rad` 下界

```lean
supportMass_eq_abc_rad
supportMass_ge_prod_of_prime_channel_family
PrimitiveWitnessFamily.channelProduct_le_abc_rad_diff
PrimitiveWitnessFamily.pow_channelCount_le_abc_rad_diff
```

これは

```text
primitive channel が増える
→ rad が下から持ち上がる
```

という出口。

### B. finite log-capacity / SubProbability

Petal/ErdosBridge 側には、

```lean
petalPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
petalNoLiftPrimeChannelFamily_logSubProbability_GN_of_labelNoncollision
```

がある。

ただし、ここで重要なのは、

```text
logSubProbability には NoLift は必須ではない。
```

`PetalPrimeChannel` family + label noncollision だけで log-capacity は行ける。

NoLift は valuation exact-one-slot には重要だが、finite log capacity では別軸。  
ここを混ぜない方がよい。

## 5. 今のコードで一番見落としやすい点

わっちの暫定結論はこれじゃ。

```text
PetalNoLiftCarrierLabelMapData は便利だが、
label recovery と NoLift という独立した二軸を一つの structure に重ねている。
```

これは実装として間違いではない。  
だが、次の設計段階では分けた方が見通しがよい。

例えばこう。

```lean
def PetalNoLiftOn
    {ι : Type _}
    (I : Finset ι)
    (d x u : ℕ)
    (qOf : ι → ℕ) : Prop :=
  ∀ i, i ∈ I → PetalNoLiftPrimeChannel d x u (qOf i)
```

そして、

```lean
PetalCarrierLabelMapData I d x u mOf qOf
```

と

```lean
PetalNoLiftOn I d x u qOf
```

を別々に持つ。

必要なときだけ、

```lean
PetalCarrierLabelMapData
+ PetalNoLiftOn
→ PetalNoLiftCarrierLabelMapData
```

に詰める。

こうすると、三要素の役割がこう分離される。

```text
label recovery:
  PetalCarrierLabelMapData 側

NoLift:
  PetalNoLiftOn / squarefree / Wieferich exclusion 側

final bridge:
  FLT なら universal NoLift provider
  ABC なら supportMass/rad または logSubProbability
```

## 6. 次に見るべきファイル

次はこの順で見るのがよい。

```text
1. DkMath/Petal/ErdosBridge.lean
   → label recovery と finite log-capacity の整理

2. DkMath/FLT/PrimeProvider/CosmicPetalBridgeGNNoWieferich.lean
   → NoLift / Squarefree / NoWieferich の関係

3. DkMath/FLT/PrimeProvider/TriominoCosmicBranchADescentChain.lean
   → NonLiftableGNBridge が FLT p≥5 にどう刺さるか

4. DkMath/ABC/MassBridge.lean
   → supportMass = rad の出口

5. DkMath/ABC/ValuationFlowBridge.lean
   → PrimitiveWitnessFamily から rad 下界への出口
```

わっちの鼻では、最初に切るべき補題はこれじゃ。

```lean
def PetalNoLiftOn ...

theorem petalNoLiftCarrierLabelMapData_of_carrierLabelMapData_and_noLiftOn ...

theorem petalNoLiftOn_padicValNat_GN_eq_one ...

theorem petalCarrierLabelMapData_logSubProbability_GN ...
```

そして FLT 用には別に、

```lean
theorem triominoNoLiftGNBridge_of_petalUniversalNoLift ...
```

ABC 用には、

```lean
theorem petalCarrierLabelMapData_supportMassLowerBound_GN ...
```

を作る。

これで、三つの要素が混線せずに、それぞれ正しい城門へ渡せる。  
ぬしの違和感、かなり良い嗅覚じゃ。ここを分ければ、次の実装はかなり澄む。

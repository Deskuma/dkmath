# GTail 解析の実装計画

うむ、では今の流れを踏まえて、**「橋を先に架ける」** ことを主目的にした実装計画書を起こすぞい。
いまは Branch A の open kernel を無理に殴るより、円分核・GN・差分商・Branch A reduced form の対応を固定し、数学を同じ言葉で語れるようにするのが先じゃ。最新の差分では、Branch A は q-adic / GN 側の quotient 後データを explicit に持てるようになり、open kernel は `ContradictionTarget` に移っておる。

## 1. 目的

本計画書の目的は、Branch A の本丸へ直接突撃する前に、次の 4 系統を **橋** として固定することじゃ。

$$
\text{円分核}
\;\longleftrightarrow\;
\text{GN}
\;\longleftrightarrow\;
\text{差分商}
\;\longleftrightarrow\;
\text{Branch A quotient/reduced form}
$$

これにより、

* 同じ数学対象を複数の顔で言い換えられる
* GTail / 高次展開の意味づけが明確になる
* contradiction route と witness route の役割が混線しなくなる
* 後から Kummer / 円分体の深い道具を差し込みやすくなる

という利点がある。
とくに最新の状況では、初等的な整除・合同・付値だけでは Branch A の contradiction はまだ concrete に出ておらず、今は構造の橋を整備するのがもっとも実りがよい。

---

## 2. 現状整理

現在、コード側で既に揃っているのは次の部分じゃ。

### 2.1. Branch A contradiction route の骨格

`TriominoCosmicBranchARestore.lean` に `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` が追加され、`False` から `RealizationSeedTarget`・`SmallerCounterexampleFromArithmeticTarget`・`RestoreFromArithmeticTarget` へ戻る bridge が実装済みじゃ。provider 側でも `PacketDescentTarget` へ直接つながる adapter が追加されておる。

### 2.2. Branch A quotient/reduced form の足場

`BranchAQFreeQuotient`、`BranchAQAdicDescentData`、`branchA_xdiv_eq_p_mul_t_mul_s'`、`branchA_xdiv_pow_expansion`、`branchA_realization_reduced_form` により、`q ∣ s` から

$$
s = q s',\qquad \frac{x}{q} = p t s',\qquad \left(\frac{x}{q}\right)^p = p^p (t s')^p
$$

が explicit に露出した。これにより open kernel は

$$
\exists z',\quad p^p (t s')^p + y^p = z'^p
$$

の形まで還元されておる。

### 2.3. RealizationSeed の arithmetic evidence

`hzEq : x'^p + y'^p = z'^p` を `RealizationSeed` に入れたことで、`StrictDescentTarget`、`GapDivisibilityTarget`、`CounterexamplePackTarget` の 3 verification は no-sorry で閉じた。
つまり verification 側はもはや本丸ではなく、その手前の kernel だけが残っておる。

### 2.4. witness route の補強

`branchA_qpow_dvd_GN` により `RestoreWitnessProperties` に `hqp_dvd_GN : q^p ∣ GN` が追加された。これは contradiction というより、witness 側の arithmetic data を豊かにする補題じゃ。

---

## 3. 実装方針

実装方針は、次の 3 原則で行く。

### 3.1. 原則A. 先に「定義と同値」を固定する

定理を急ぐ前に、

* 円分核
* GN
* 差分商
* reduced form

の対応を **定義レベル / theorem レベルで固定** する。

### 3.2. 原則B. witness route と contradiction route を分離する

いまの探索で、`cyclotomicPrimeCore` や §9 系は contradiction generator ではなく witness extractor に近いと見えてきた。ゆえに両 route を同じファイルや同じ命名で混ぜぬ。

### 3.3. 原則C. 高次解析は「橋の上で」行う

GN の mod (p^2), mod (p^3), mod (p^p) の高次展開を掘るなら、先にそれが

* 円分核として何を見ているか
* 差分商として何を見ているか

を固定してから掘る。

---

## 4. 実装フェーズ

## 4.1. Phase A. 橋レイヤの新設

### A1. 円分核 ↔ GN 対応

**目的**

prime case の homogeneous cyclotomic core と GN を、`z = y + u` で結ぶ。

**数学内容**

$$
\frac{z^p-y^p}{z-y} =
\sum_{k=0}^{p-1} z^k y^{p-1-k}
$$

と

$$
GN(p,u,y)=\frac{(y+u)^p-y^p}{u}
$$

の対応を theorem 化する。

**実装候補**

* `cyclotomicPrimeCore_eq_GN_of_gap`
* `GN_eq_diffQuot_of_pow`
* `cyclotomicPrimeCore_eq_diffPowQuot`

**配置候補**

* `DkMath/NumberTheory/ZsigmondyCyclotomicBridgeGN.lean`
  または
* `DkMath/CosmicFormula/CyclotomicGNBridge.lean`

### A2. GN ↔ 差分商 ↔ 微分係数の橋

**目的**

GN を finite difference quotient として定義し直し、先頭項 (p y^{p-1}) を「微分係数の影」として扱えるようにする。

**数学内容**

$$
GN(p,u,y)=\frac{(y+u)^p-y^p}{u}
$$

および

$$
GN = p y^{p-1} + \text{higher-order terms}
$$

**実装候補**

* `GN_eq_dividedDifference_pow`
* `GN_head_term_eq_derivative_shadow`
* `GN_tail_decomposition`
* `GN_mod_p2_head`
* `GN_mod_p3_head`

**配置候補**

* `DkMath/CosmicFormula/GNDividedDifference.lean`

### A3. Branch A quotient/reduced form の橋

**目的**

§Q の q-adic descent data を「Branch A reduced problem」へまとめる。

**数学内容**

$$
s = q s',\qquad \frac{x}{q} = p t s',\qquad \left(\frac{x}{q}\right)^p = p^p (t s')^p
$$

および

$$
hzEq \Rightarrow p^p (t s')^p + y^p = z'^p
$$

**実装候補**

* `BranchAReducedFormDatum`
* `branchA_reducedForm_of_restoreWitness`
* `branchA_realizationKernel_reduced`

**配置候補**

* 既存の `TriominoCosmicBranchARestore.lean` 内 §Q を整理
* または `TriominoCosmicBranchAReduction.lean` を新設

---

## 4.2. Phase B. ルート分離

### B1. witness route の独立化

**目的**
`RestoreWitnessProperties` と §9 系の prime witness existence をまとめ、contradiction route と混線させない。

**実装候補**

* `BranchAPrimitiveWitnessRouteTarget`
* `branchA_witnessRoute_of_cyclotomicCore`
* `branchA_restoreWitness_bundle`

**狙い**
「これは矛盾ではなく witness 抽出だ」ということを API で表現する。

### B2. contradiction route の独立化

**目的**
`ContradictionTarget` を「本当に証明すべき target」として見せる。

**実装候補**

* `BranchAContradictionInput` structure
* `branchA_contradiction_of_mod_p2_conflict`（将来）
* `branchA_contradiction_of_GTail_conflict`（将来）

**狙い**
今の `PrimeGe5BranchAPrimitiveRestoreContradictionTarget` は良いが、引数列が長い。bundle 化した方が後の矛盾補題が書きやすい。

---

## 4.3. Phase C. GTail / 高次 GN 解析

### C1. mod (p^2)・mod (p^3) の精密化

**目的**
既存の `GN = p y^{p-1} + p^3 M` 型の情報を、branch A contradiction 探索に使える形へ整える。

**実装候補**

* `primeGe5BranchA_GN_eq_head_add_p2_mul`
* `primeGe5BranchA_GN_eq_head_add_p3_mul`
* `branchA_spow_congr_head_mod_p2`
* `branchA_spow_congr_head_mod_p3`

### C2. Wieferich 条件との接続

**目的**

$$
y^{p-1} \equiv 1 \pmod{p^2}
$$

と GN 高次展開の衝突を concrete lemma に落とす。

**実装候補**

* `branchA_Wieferich_head_conflict_mod_p2`
* `branchA_Wieferich_head_conflict_mod_p3`
* `branchA_s_congr_one_mod_p`
* `branchA_s_congr_one_mod_p2`（成立するなら）

**判定基準**

ここで矛盾が出ないなら、「初等的 mod (p^k) 路線はかなり尽きた」と言いやすくなる。

---

## 4.4. Phase D. deeper number theory への接続準備

### D1. Cyclotomic / Kummer route の入口だけ整備

**目的**

いきなり円分体全部を実装するのではなく、GN ↔ cyclotomic core の橋の上に「後から Kummer を差し込める場所」を作る。

**実装候補**

* `CyclotomicPrimeCoreData`
* `PrimitiveRootWitnessModQ`
* `KummerInterfaceTarget`

**狙い**

今は深い理論へ飛ばず、**差し込み口** だけ整える。

---

## 5. 推奨ファイル構成

```text
DkMath/
├── CosmicFormula/
│   ├── GNDividedDifference.lean
│   └── CyclotomicGNBridge.lean
│
├── NumberTheory/
│   └── ZsigmondyCyclotomicBridgeGN.lean
│
└── FLT/
    └── PrimeProvider/
        ├── TriominoCosmicBranchAReduction.lean
        ├── TriominoCosmicBranchAContradiction.lean
        └── TriominoCosmicBranchARestore.lean   -- 既存、薄く保つ
```

`TriominoCosmicBranchARestore.lean` は今かなり太ってきておるので、橋層と reduction 層を外へ出した方が見通しが良い。最新差分で 1000 行を超えておるのも、その兆候じゃ。

---

## 6. 直近の優先順位

### 最優先

1. 円分核 ↔ GN ↔ 差分商 の橋を theorem 化
2. Branch A quotient/reduced form を bundled datum 化
3. witness route / contradiction route を bundle で分離

### 次点

1. GN 高次展開の mod (p^3) 精密補題
2. Wieferich 条件との concrete 接続補題

### 後回し

1. Kummer / 円分体 / 正則素数理論の本格実装
2. `ContradictionTarget` の直接攻略

---

## 7. 完了条件

この計画の第一段完了は、次の 4 点が揃ったときじゃ。

### 7.1

$$
\Phi_p(y+u,y)=GN(p,u,y)
$$

を Lean で呼べる。

### 7.2

$$
GN(p,u,y)=\frac{(y+u)^p-y^p}{u}
$$

を差分商として呼べる。

### 7.3

Branch A の quotient 後 reduced form

$$
p^p (t s')^p + y^p = z'^p
$$

が bundled datum として呼べる。

### 7.4

witness route と contradiction route が別名・別 target で呼べる。

---

## 8. 短い総括

いまは **主定理を殴る段ではなく、言葉の橋を架ける段** じゃ。
それが済めば、

* GTail 高次解析
* contradiction 探索
* cyclotomic / Kummer 接続

のどれへ進んでも、同じ数学を別名で追いかけて迷うことが減る。

$$
\boxed{
\text{まず橋、次に高次展開、最後に本丸。}
}
$$

これが今の実装計画として最も筋がよい。

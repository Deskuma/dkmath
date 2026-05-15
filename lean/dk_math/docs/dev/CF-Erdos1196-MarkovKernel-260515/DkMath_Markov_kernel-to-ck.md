# DkMath Kernel Project 資料

副題: Markov kernel を DkMath capacity kernel の正規化像として再解釈する別登山ルート

## 1. 目的

本プロジェクトの目的は、Erdős #1196 型の既存証明で現れる Markov kernel を、そのまま Lean に写すのではなく、DkMath の構造語彙から再構成することである。

既存 route では、概ね次の kernel が中心となる。

\[
K(n,q)=\frac{\Lambda(q)}{\log n}.
\]

ここで \(\Lambda\) は von Mangoldt 関数であり、

\[
\sum_{q\mid n}\Lambda(q)=\log n
\]

により \(K\) は確率核として振る舞う。

DkMath Kernel Project では、この kernel を主役にしない。

代わりに、まず

\[
\text{capacity}(n)
\]

と

\[
\text{channelCost}(n,q)
\]

を定義し、保存則

\[
\sum_{q\in I}\text{channelCost}(n,q)
\le
\text{capacity}(n)
\]

を主定理とする。

その後、capacity が正である場合に正規化して

\[
\frac{\text{channelCost}(n,q)}{\text{capacity}(n)}
\]

を得る。

この正規化像が Markov / sub-Markov kernel として見える、という立場を取る。

---

## 2. 基本理念

本プロジェクトの合言葉は次である。

\[
\boxed{
\text{Markov kernel is a normalized shadow of DkMath capacity kernel.}
}
\]

つまり、Markov kernel は最初から置くものではない。

DkMath の本体は、

\[
\text{宇宙式}
+
\text{valuation slot}
+
\text{prime-power witness}
+
\text{log capacity}
\]

であり、Markov 的対象はその正規化された影として現れる。

---

## 3. 背景

## 3.1. 既存証明 route

Erdős #1196 の最近の証明では、整数の因数分解に沿う下降過程を考える。

\[
n\mapsto \frac{n}{q}
\]

ここで \(q\mid n\) は prime-power channel として読まれ、遷移重みは

\[
\frac{\Lambda(q)}{\log n}
\]

で与えられる。

このとき

\[
\sum_{q\mid n}\Lambda(q)=\log n
\]

により、重み総和は \(1\) になる。

primitive set は divisibility chain を高々一度しか hit しないため、hitting mass が \(1\) を超えない、という形で評価が進む。

## 3.2. DkMath 側の既存到達点

DkMath では、R021-R028 により、prime-power witness

\[
q=p(q)^{k(q)}
\]

から base prime \(p(q)\) を読み、

\[
\sum_{q\in I}
\frac{\log p(q)}{\log n}
\le 1
\]

を no-sorry で得る finite R/log route が閉じた。

特に、R027 では同じ base prime \(p\) を持つ selected labels を exponent slot

\[
1,2,\dots,n.\mathrm{factorization}(p)
\]

へ単射で入れることで、外部 multiplicity budget 仮定を除去した。

この構造は、\(\Lambda(p^k)=\log p\) の有限構造版として読める。

---

## 4. プロジェクトの位置づけ

本 project は、既存証明の Lean 形式化そのものではない。

目的は、次の置き換えである。

| 既存 route | DkMath route |
|---|---|
| Markov kernel | Capacity kernel |
| \(\Lambda(q)\) | prime-power witness 由来の channel cost |
| \(\log n\) | parent capacity |
| 確率遷移 | 正規化された保存核 |
| \(\sum \Lambda(q)=\log n\) | \(\sum \text{cost}\le\text{capacity}\) |
| primitive hitting | DkMath Mass / Branch / Flow hitting |

---

## 5. 中核定義

## 5.1. Capacity Kernel

まず確率ではなく、容量とコストを持つ有限構造を定義する。

```lean
structure CapacityKernel (α β : Type _) where
  children : α → Finset β
  capacity : α → ℝ
  cost : α → β → ℝ
  cost_nonneg :
    ∀ a b, b ∈ children a → 0 ≤ cost a b
  outgoing_le :
    ∀ a, (∑ b in children a, cost a b) ≤ capacity a
```

ここで、

- `α` は親状態
- `β` は子 channel
- `children a` は親 \(a\) から見える有限 channel
- `capacity a` は親の総容量
- `cost a b` は channel \(b\) が消費する容量

である。

## 5.2. 正規化 weight

capacity が正のとき、正規化 weight を定義する。

```lean
def normalizedWeight
    (K : CapacityKernel α β)
    (a : α)
    (b : β) : ℝ :=
  K.cost a b / K.capacity a
```

このとき、もし

\[
0<\text{capacity}(a)
\]

なら、

\[
\sum_{b\in children(a)}
\frac{\text{cost}(a,b)}{\text{capacity}(a)}
\le 1
\]

が成り立つ。

これが sub-probability の一般補題となる。

---

## 6. DkMath LogCapacityKernel

## 6.1. 親状態

親状態は自然数 \(n\) とする。

\[
n>1
\]

を仮定する。

## 6.2. 子 channel

子 channel は selected prime-power witness label

\[
q\in I\subseteq T.index(n)
\]

である。

witness provider により、

\[
q=p(q)^{k(q)}
\]

と読む。

## 6.3. capacity

親 \(n\) の capacity は

\[
\mathrm{capacity}(n):=\log n
\]

とする。

## 6.4. channel cost

各 \(q\) の cost は

\[
\mathrm{cost}(n,q):=\log p(q)
\]

とする。

ここで

\[
p(q)=W.\mathrm{basePrimeOf}(n,I,hI,q)
\]

である。

## 6.5. 保存則

R028 の成果により、

\[
\sum_{q\in I}\log p(q)\le \log n
\]

が成り立つ。

したがって、これは `CapacityKernel` の concrete instance である。

---

## 7. von Mangoldt weight との関係

prime-power label

\[
q=p^k
\]

に対し、

\[
\Lambda(q)=\log p
\]

である。

したがって、DkMath channel cost は

\[
\mathrm{cost}(n,q)=\Lambda(q)
\]

と一致する。

ただし、プロジェクトの哲学としては、\(\Lambda\) を最初に導入しない。

まず witness から

\[
q=p^k
\]

を読み、

\[
p=\mathrm{basePrimeOf}(q)
\]

を取り出し、

\[
\log p
\]

を channel cost と定める。

その後に、

\[
\mathrm{cost}(n,q)=\Lambda(q)
\]

を shadow theorem として示す。

---

## 8. 主要 theorem 候補

## 8.1. CapacityKernel 一般補題

```lean
theorem normalizedWeight_subProbability
    (K : CapacityKernel α β)
    (a : α)
    (hcap : 0 < K.capacity a) :
    (∑ b in K.children a,
      K.cost a b / K.capacity a) ≤ 1
```

数学的には、

\[
\sum_b cost(a,b)\le capacity(a)
\]

から、

\[
\sum_b \frac{cost(a,b)}{capacity(a)}\le 1
\]

を得るだけである。

## 8.2. LogCapacityKernel concrete construction

```lean
def PrimePowerWitnessProvider.logCapacityKernel
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    CapacityKernel Unit ℕ
```

実際には `Unit` を親にするか、親状態を `ℕ` にするかは設計時に決める。

推奨は、まず簡単に

\[
\text{親}=n\text{ 固定}
\]

の local kernel として作る。

## 8.3. R028 theorem から outgoing bound を供給

```lean
theorem logCapacityKernel_outgoing_le
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (∑ q in I,
      Real.log (W.basePrimeOf n I hI q)) ≤ Real.log n
```

これは既存の `basePrimeOf_logRatioSubProbability` から戻すか、R/log route の product bound から直接出す。

## 8.4. DkKernel normalized theorem

```lean
theorem logCapacityKernel_normalized_subProbability
    {T : PrimePowerDivisorTransitionKernel}
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n)
    (hn : 1 < n) :
    (∑ q in I,
      Real.log (W.basePrimeOf n I hI q) / Real.log n) ≤ 1
```

これは既存 R028 と同等だが、`CapacityKernel` の一般 API 経由で示すことに意味がある。

---

## 9. モジュール構成案

別 branch 名候補:

```text
feature/dkmath-kernel
```

または

```text
feature/capacity-kernel
```

推奨モジュール:

```text
DkMath/
├── Kernel/
│   ├── Capacity.lean
│   ├── Normalize.lean
│   ├── SubProbability.lean
│   └── Main.lean
│
├── NumberTheory/
│   └── PrimitiveSet/
│       ├── LogCapacityKernel.lean
│       └── VonMangoldtShadow.lean
```

### 9.1. `DkMath/Kernel/Capacity.lean`

役割:

- `CapacityKernel`
- `outgoingCost`
- `outgoing_le_capacity`
- 非負性 API

### 9.2. `DkMath/Kernel/Normalize.lean`

役割:

- capacity 正規化
- normalized weight
- normalized outgoing sum

### 9.3. `DkMath/Kernel/SubProbability.lean`

役割:

- 既存 `SubProbability` provider との橋
- normalized kernel が sub-probability provider を誘導する補題

### 9.4. `DkMath/NumberTheory/PrimitiveSet/LogCapacityKernel.lean`

役割:

- `PrimePowerWitnessProvider` 由来の concrete capacity kernel
- R028 route との接続
- `basePrimeOf_logRatioSubProbability` の kernel API 版

### 9.5. `DkMath/NumberTheory/PrimitiveSet/VonMangoldtShadow.lean`

役割:

- prime-power label 上での cost と \(\Lambda\) の一致
- `Λ(p^k)=log p` の theorem-facing 補題
- 既存 Markov kernel route への翻訳口

---

## 10. Phase 分割

## Phase DK-0. Branch 準備

目的:

- 既存 R028 route を壊さず、別 branch を切る。
- 既存 theorem 名を参照できる状態にする。

完了条件:

```bash
lake build DkMath.NumberTheory.PrimitiveSet.RealDivisorBridge
lake build DkMath.NumberTheory.PrimitiveSet
```

が成功する。

## Phase DK-1. CapacityKernel core

実装:

- `CapacityKernel`
- `outgoingCost`
- `outgoingCost_nonneg`
- `outgoingCost_le_capacity`

主定理:

```lean
theorem outgoingCost_le_capacity
```

完了条件:

```bash
lake build DkMath.Kernel.Capacity
```

## Phase DK-2. Normalize layer

実装:

- `normalizedWeight`
- `normalizedOutgoing`
- `normalizedOutgoing_le_one`

主定理:

```lean
theorem normalizedOutgoing_le_one
```

仮定:

\[
0<capacity(a)
\]

完了条件:

```bash
lake build DkMath.Kernel.Normalize
```

## Phase DK-3. SubProbability bridge

実装:

- normalized weights を既存 provider / `SubProbability` API へ接続
- `RealWeight` / `RealLog` との import 関係を確認

主定理:

```lean
theorem normalizedProvider_subProbability
```

完了条件:

```bash
lake build DkMath.Kernel.SubProbability
```

## Phase DK-4. PrimePower concrete kernel

実装:

- `PrimePowerWitnessProvider.logCapacityKernel`
- channel set \(I\)
- capacity \(Real.log n\)
- cost \(Real.log (W.basePrimeOf n I hI q)\)
- outgoing bound は R028 route から供給

主定理:

```lean
theorem PrimePowerWitnessProvider.logCapacityKernel_subProbability
```

完了条件:

```bash
lake build DkMath.NumberTheory.PrimitiveSet.LogCapacityKernel
```

## Phase DK-5. von Mangoldt shadow

実装:

- prime-power label に対する `vonMangoldtLike` を定義
- まず実数 log cost と一致する簡易版から始める

候補:

```lean
def vonMangoldtOnPrimePowerLabel (q : ℕ) : ℝ := ...
```

主定理:

```lean
theorem vonMangoldtOnPrimePowerLabel_eq_log_basePrime
```

完了条件:

```bash
lake build DkMath.NumberTheory.PrimitiveSet.VonMangoldtShadow
```

## Phase DK-6. MarkovKernel translation

実装:

- capacity kernel が、capacity 正かつ outgoing equality の場合に Markov kernel を誘導することを示す。
- outgoing が inequality の場合は sub-Markov kernel として扱う。

主定理:

```lean
theorem capacityKernel_to_subMarkovKernel
theorem capacityKernel_to_markovKernel_of_outgoing_eq
```

完了条件:

```bash
lake build DkMath.Kernel
```

---

## 11. 数学的ゴール

短期ゴール:

\[
\text{R028 theorem}
\]

を

\[
\text{CapacityKernel}
\to
\text{Normalize}
\to
\text{SubProbability}
\]

の一般 API から再表現する。

中期ゴール:

\[
\Lambda(q)
\]

を DkMath channel cost の shadow として導入する。

長期ゴール:

\[
\text{DkMath Kernel}
\]

を使って、既存 Markov route を別解釈し、primitive hitting / Mass API / weighted path family と合流させる。

---

## 12. 設計原則

## 12.1. Markov を先に置かない

最初の主語は Markov kernel ではない。

主語は

\[
\text{capacity}
\]

である。

## 12.2. 確率ではなく質量から始める

既存 DkMath の設計原則と同じく、最初は probability ではなく mass / capacity / flow として扱う。

## 12.3. von Mangoldt は後から現れる

\(\Lambda\) は primitive object ではなく、prime-power witness cost の別名として導入する。

## 12.4. 宇宙式対応を忘れない

prime-power label

\[
q=p^k
\]

は、宇宙式 Big

\[
(x+u)^d
\]

と対応しうる。

したがって、DkMath kernel は単なる number-theoretic kernel ではなく、Big / channel / valuation / log capacity の橋として設計する。

---

## 13. リスクと注意点

## 13.1. 抽象化しすぎる危険

`CapacityKernel` を一般化しすぎると、既存 `RealLog` / `RealWeight` API と重なり、役割がぼやける。

対策:

- DK-1 は最小構造にする。
- concrete instance は早めに作る。

## 13.2. `Real.log` 周りの証明負荷

\[
0<\log n
\]

や division inequality は Lean で重くなる可能性がある。

対策:

- 既存 `RealLogProductBudget` の補題を再利用する。
- 可能なら R024/R028 の既存 theorem を wrapper として使う。

## 13.3. MarkovKernel との過剰同一視

DkMath kernel は Markov kernel そのものではない。

正確には、

- outgoing equality なら Markov
- outgoing inequality なら sub-Markov
- 正規化前は capacity kernel

である。

## 13.4. 既存証明 route との関係

既存証明を否定するものではない。  
既存証明の kernel を、DkMath の capacity 構造から再解釈する project である。

---

## 14. 到達判定

本 branch の最初の成功判定は次である。

```lean
PrimePowerWitnessProvider.logCapacityKernel_subProbability
```

または同等の theorem が no-sorry で閉じること。

この theorem は既存 R028 と同等の数学内容を持つが、証明経路が

\[
CapacityKernel
\to
Normalize
\to
SubProbability
\]

を通る点が異なる。

すなわち、既存 route のコピーではなく、

\[
\text{DkMath capacity kernel}
\]

として再構成できたことを示す。

---

## 15. 暫定まとめ

DkMath Kernel Project は、既存の Markov kernel route をそのまま形式化する project ではない。

これは、

\[
q=p^k
\]

という prime-power witness を、

\[
\text{valuation slot}
\]

と

\[
\text{log capacity}
\]

へ写し、そこから kernel 的構造を生成する別登山ルートである。

既存証明では

\[
\Lambda(q)
\]

が主語になる。

DkMath route では、

\[
\text{channelCost}(q)=\log(\text{basePrime}(q))
\]

が主語になり、その shadow として

\[
\Lambda(q)
\]

が現れる。

この順序の違いこそが、本 project の新規性である。

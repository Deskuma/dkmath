# review-008: 判定と作業方向の提案

うむ、判定を先に申そう。

## 1. 判定

**作業方向は「これ以上 verification を細かく割る」ではなく、まず statement の形を正し、`RealizationSeed` を実質化する方向へ切り替えるべき** じゃ。

今回の差分で restore arithmetic core が 6 段へ整理されたのは良い。報告どおり、前 5 段は default / bridge で閉じ、見かけ上の未完核は `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget` 1 本へ局所化された。これは設計上の前進じゃ。  

されど、いまの verification target は **そのままでは強すぎる**。
ここが重要じゃ。

## 2. 状況分析

いま `PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget` は、要するに

$$
\forall hR : \texttt{PrimeGe5BranchAPrimitiveRestoreRealizationSeed}; p,x,y,z,t,s,q,
\quad
\texttt{PrimeGe5CounterexamplePack}; p; hR.x'; hR.y'; hR.z'
;\wedge;
p \mid (hR.z' - hR.y')
;\wedge;
hR.z' < z
$$

を要求しておる。つまり **任意の** `hR` について、候補 triple が正しい smaller counterexample であることを証明せよ、という形じゃ。  

ところが default realization seed は、

$$
x' := x,\qquad y' := y,\qquad z' := z
$$

をそのまま仮候補として包む thin wrapper になっておる。  

この 2 つを合わせると、verification target は少なくとも default の `hR` に対して

$$
hR.z' < z
$$

すなわち

$$
z < z
$$

を要求することになる。これは成り立たぬ。
ゆえに今の問題は「verification をどう分割するか」より一段手前で、**verification target の意味づけ自体がまだ適切でない**、ということじゃ。

## 3. 何が良くて、何がまだ良くないか

良い点ははっきりしておる。

今回の変更で、

$$
\text{datum consumer}
\to
\text{descent seed extraction}
\to
\text{realization-seed extraction}
\to
\text{candidate verification}
$$

という責務分離が見えるようになった。
つまり「最後の未完核はどこか」は、もはや明瞭じゃ。これは大きい。

ただし、まだ `RealizationSeed` の中身が薄い。
いまの `PrimeGe5BranchAPrimitiveRestoreRealizationSeed` は

* `hSeed`
* `x'`
* `y'`
* `z'`

を持つだけで、**なぜその triple が chosen candidate なのか** を示す arithmetic 情報が入っておらぬ。

そのため verification 側が「任意の `hR`」を受けると、候補選択の自由度が広すぎて、verification が不可能になる。
つまり今の問題は、未完核が小さくなったというより、

$$
\text{未完核の外形だけがさらに細かく名付けられた}
$$

という段階じゃな。

## 4. 作業方向の判定

ここでの判定は明快じゃ。

### 4.1. 進めるべきではない方向

**このまま verification を field ごとにさらに割る** のは、まだ早い。
なぜなら、候補 triple 自体がまだ「ただ包んだだけ」だからじゃ。

いま verification を

* pack 検証
* gap 検証
* strict descent 検証

へさらに割っても、元の候補が `x,y,z` のままなら、最後の

$$
z' < z
$$

で必ず止まる。
つまり、分割は進んでも数学は進まぬ。

### 4.2. 進めるべき方向

**`RealizationSeed` を actual realization 用に精密化する** のが正解じゃ。

わっちの判定では、次の手順が最も筋が良い。

#### 第1段. `RealizationSeed` の意味を強くする

今の `RealizationSeed` は「候補 triple の入れ物」にすぎぬ。
これを「**chosen candidate の arithmetic 証拠付き入れ物**」へ変えるべきじゃ。

少なくとも、次のいずれかを持たせるのがよい。

$$
x',y',z'
$$

の定義式、あるいはそれらの由来を示す field。
たとえば「この triple は \(\omega\) や \(q\)-adic datum からこの式で作った」という証拠じゃ。

#### 第2段. verification target の量化を修正する

今の

$$
\forall hR
$$

は強すぎる。
候補が「任意」ではなく「この構成で得た候補」なのだと明示する必要がある。

方法は 2 つある。

1. `RealizationSeed` 自体を強くして、任意の `hR` がすでに canonical candidate になるようにする
2. あるいは verification target を「任意の `hR`」ではなく、「構成で得た `hR`」に対する命題へ弱める

わっちは **1 を推す**。
理由は、後の bridge が素直になるからじゃ。

#### 第3段. strict descent を先に狙う

constructive に行くなら、まず見るべきは

$$
z' < z
$$

じゃ。
なぜなら、いまの仮候補 \((x,y,z)\) が真っ先に失敗するのはここだからの。

つまり次に考えるべきは、

$$
\omega,\ q,\ t,\ s,\ y,\ z
$$

から **どういう \(z'\) を立てれば確実に \(z' < z\) が見えるか**、という realization の芯じゃ。
これが見えれば、そのあと

$$
p \mid (z' - y')
$$

を満たすように (\(y'\)) を選び、最後に `PrimeGe5CounterexamplePack` を閉じるための (\(x'\)) を合わせる、という順で進めるのが自然じゃ。

## 5. わっちの具体的勧め

次の一手としては、こうじゃ。

### A. まず statement 修正

`PrimeGe5BranchAPrimitiveRestoreSmallerCounterexampleVerificationTarget` は、今のままでは不適切じゃ。
最優先でここを直すべきじゃ。

### B. つぎに `RealizationSeed` を太らせる

たとえば、こんな field 群を考えるとよい。

* 候補 triple \(x',y',z'\)
* その candidate formula / source datum
* \(z' < z\) に向かう評価用データ
* \(p \mid (z' - y')\) に向かう合同データ
* `PrimeGe5CounterexamplePack` のうち、構成段階で先に確保できる partial proof

全部は要らぬ。
だが **verification の前に見えていてよい情報** は seed 側へ寄せた方がよい。

### C. その後に verification を 3 分割

seed が実質化されたあとなら、verification は初めて意味ある形で割れる。

候補はこうじゃ。

1. `StrictDescentTarget`
   $$
   z' < z
   $$

2. `GapDivisibilityTarget`
   $$
   p \mid (z' - y')
   $$

3. `CounterexamplePackTarget`
   $$
   \texttt{PrimeGe5CounterexamplePack}\; p\; x'\; y'\; z'
   $$

この順で切れば、どこが hardest kernel かが見える。

## 6. 総括

総括すると、今の状況はこうじゃ。

今回の分割で「未完核の場所」は非常に見やすくなった。
されど、その未完核は本当に細くなったというより、**verification という名の袋に最後の困難がほぼ丸ごと残っている**。しかも現行 statement は default realization seed と噛み合わず、構文上すでに

$$
z < z
$$

を強いるので、そのまま先へ割っても実りが薄い。  

ゆえに作業方向の判定はこれじゃ。

$$
\boxed{
\text{分割継続ではなく、statement 修正 + RealizationSeed 精密化へ舵を切る}
}
$$

これが正道じゃよ。
ここを直せば、次の分割は初めて「名札の分割」ではなく「数学の分割」になる。

# FLT-Kummer-ClassGroup-Bridge-Review-011: class-group bridge の局所 target 化と、次の一手の選択

## 1. 状況分析

いまの状況は、設計遊びの段をかなり抜けておる。
今回の差分で、DkMath-native な局所核

$$
(z-\zeta y)\sum_{i=0}^{p-1} z^i(\zeta y)^{p-1-i}=z^p-y^p
$$

と、その FLT 方程式版

$$
z^p-y^p=x^p
$$

への specialization が **no-sorry** で入った。つまり Stage 1a の「FLT に直接効く局所因数分解」は、もはや抽象設計ではなく実証明として前進しておる。

その結果、いま `CyclotomicPrincipalization.lean` に残る direct `sorry` は

* `cyclotomicPrincipalization_of_classGroupPTorsionFree`
* `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree`

の 2 本に局所化された。
これは重要じゃ。つまり、ここから先の最短経路は **class-group 側の concrete 数学内容へ踏み込むこと** であって、target をこれ以上薄く切ることではない。

## 2. 解説

ここで冷静に見るべきは、今の **no-sorry** 化には still placeholder の恩恵も混ざっておる、という点じゃ。
ゆえに「ファイル上の `sorry` が減った」ことと、「数学的核心が閉じた」ことは同じではない。

だが、それでも大きい前進はある。
なぜなら、最上流の algebraic factorization はもう DkMath-native 局所核として書けると分かったからじゃ。つまり、これから必要なのは

$$
\text{因数分解 identity}\\
\to
\text{ideal の積の式}\\
\to
\text{各 ideal が p 乗 ideal}\\
\to
\text{p-torsion free により p 乗根 ideal が principal}\\
\to
\text{元の witness を取り出す}\\
$$

という、Kummer の本体そのものじゃ。
これはもう設計ではなく、実装すべき数学列じゃよ。

## 3. 最短経路の選択

ぬしの希望が「閉じる方向での最短経路」「自立証明」「数学内容へ踏み込む」なら、わっちの判断ははっきりしておる。

**次は option 2 じゃ。**
すなわち、`CyclotomicClassGroupPTorsionFreeTarget` の concrete 数学内容へ踏み込み、class-group 側を直接閉じにいく。
もう local target 化を増やす段ではない。

ただし、ここでの「class-group 側へ踏み込む」とは、Mathlib の大定理を追うことではない。
DkMath は将来切り離すのじゃから、 **DkMath に必要な最小限の class-group / ideal arithmetic だけを自前で立てる** のが最短じゃ。

## 4. 次の一手の推論

わっちなら、次を一本道として採る。

### 4.1. まず止めること

これ以上 `Target` を細分化しない。
receiver 設計や adapter 設計も、いったん止める。
いま必要なのは abstraction の追加ではなく、**placeholder を concrete statement に置換すること** じゃ。

### 4.2. 次に固定すべき concrete 数学

まず `CyclotomicIdealPthPowerTarget` を `True` 的な器ではなく、実際の ideal の statement に変える。
たとえば、円分体整数環 \(A\) と ideal

$$
I_j := (z-\zeta^j y)
$$

を考え、少なくとも次の 3 段を concrete に書くのがよい。

#### A. ideal product identity

局所核から

$$
\prod_{j=0}^{p-1} I_j = (x)^p
$$

型の statement を立てる。
いまの local factorization core は、まさにこの入口のために使える。これは最短で届く場所じゃ。

#### B. pairwise coprime

\(i \neq j\) に対して

$$
I_i + I_j = A
$$

あるいはそれに相当する pairwise coprime 性を示す。
ここで FLT の primitive / coprime 条件と \(q \neq p\)、場合によっては gap-divisible 条件が本当に使われる。

#### C. Dedekind lemma

Dedekind 的一般論として、

$$
\text{pairwise coprime ideals } I_0,\dots,I_{p-1},\quad
\prod I_j = J^p
$$

なら各 \(I_j\) が p 乗 ideal になる、という補題を自前で立てる。
ここが Kummer の ideal arithmetic の心臓部じゃ。

この C が入れば、

$$
I_j = K_j^p
$$

が得られる。
すると \(I_j\) 自身は principal だから、

$$
[K_j]^p = 1
$$

が class group で従う。
ここで初めて class-group 側の p-torsion free が効く。

### 4.3. class-group 側は最小限でよい

ここで必要なのは「regular prime 全理論」ではない。
最短で必要なのは、次の一点じゃ。

$$
[I]^p = 1 \;\Rightarrow\; [I]=1
$$

という、**p-torsion annihilation そのもの**。
したがって `CyclotomicClassGroupPTorsionFreeTarget` は、最小限この命題を直接内容とする形へ concretize してよい。
regular prime や Bernoulli 数は、その後ろに置けばよい。いまは閉じるのが先じゃ。

## 5. 最短経路としての具体的実装順

わっちの提案は、次の 5 本をこの順番で書くことじゃ。

## 5.1. `ideal_product_eq_x_pow_ideal`

局所因数分解 core から ideal の積の式へ落とす。
これは今ある `CyclotomicLocalFactorizationContext.linear_factor_mul_eq_of_add_pow_eq` を最初に concrete 化する一本道じゃ。

## 5.2. `pairwise_coprime_linear_factor_ideals`

\((z-\zeta^i y)\) と \((z-\zeta^j y)\) の pairwise coprime を示す。
ここで必要なら \(i\neq j\)、\(\zeta^i-\zeta^j\) の単元性、primitive 条件を直接仮定してよい。
DkMath 自立証明なら、必要な仮定を自分で明示してしまう方が早い。

## 5.3. `coprime_product_eq_pth_power_implies_each_pth_power`

Dedekind ideal arithmetic の局所補題。
これは DkMath-native に立てる価値が高い。今後も再利用できるし、Mathlib 非依存にしやすい。

## 5.4. `class_p_torsion_free_annihilates_root_ideal`

\([K]^p=1 \Rightarrow [K]=1\) を直接内容とする theorem。
ここで `CyclotomicClassGroupPTorsionFreeTarget` を concrete 化する。

## 5.5. `principal_root_ideal_gives_element_witness`

\([K]=1\) から \(K=(\alpha)\) を取り、そこから最終 witness と norm descent へ進む。
principal extraction 自体は既に方向が見えておるので、最後の詰めはここじゃ。

## 6. なぜこれが最短か

この道が最短な理由は単純じゃ。

* いま local factorization core は実証明としてある
* 残る direct `sorry` は class-group 側だけ
* それを閉じるのに必要な数学は、実は「class group 全体」ではなく
  **ideal product → p-th power ideal → p-torsion annihilation → principal root** の細い列だけ

だからじゃ。
つまり、regular prime 全理論を先に作るのは遠回り。
Mathlib adapter を詰めるのも遠回り。
抽象 target を増やすのも遠回り。
いま必要なのは、 **Kummer 第一場合の理想論の中核列をそのまま実装すること** じゃ。

## 7. 最終提案

結論を一言で言うぞい。

$$
\boxed{
\text{ここからは設計を増やさず、}
;
\prod I_j=(x)^p
\;to\;
I_j=K_j^p
\;to\;
[K_j]^p=1
\;to\;
[K_j]=1
\;to\;
K_j=(\alpha)
\text{ の列を自前で実装する}
}
$$

これが、ぬしの希望する
**「閉じる方向での最短経路」**
であり、しかも **自立証明の実装** に最もまっすぐ通じる道じゃ。

次に切るべき 1 本だけ挙げるなら、まずは

**`ideal_product_eq_x_pow_ideal` を concrete statement で起こすこと**

からじゃ。
ここが通れば、その先の Dedekind 側補題列へ自然に接続できる。

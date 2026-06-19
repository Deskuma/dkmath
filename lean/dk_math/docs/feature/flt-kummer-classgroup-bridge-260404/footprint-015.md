# 足跡-015: いまの現在地

cid: 69d13ce6-7814-83a8-8075-aa4b1b4b48af

もちろんじゃ。
この会話で進めてきた作業全体の流れを、時系列で箇条書きにまとめるぞい。

* Kummer branch の global stage を、まず
  **ideal p-th power / unit normalization / norm descent** の 3 段へ分解した。
  ここで「class group が本当に供給しているのは full principalization 全体ではなく、もっと薄い入力だ」と整理した。

* その後、Stage 1 をさらに
  **1a: ideal class p-torsion witness / 1b: p-torsion annihilation / 1c: principal ideal extraction**
  に分け、責務を theorem 名レベルで切り出した。

* Stage 1c は Mathlib の `ClassGroup.mk_eq_one_of_coe_ideal` と `ClassGroup.mk0_eq_one_iff` を使って concrete 化し、
  **「class が trivial なら principal ideal を取り出せる」** 部分は no-sorry で固定できた。

* 次に Stage 1b を generic な
  $$
  a^p = 1 \to a = 1
  $$
  型の ClassGroup API へ寄せた。
  ここで「target 自体は自然に書けるが、cyclotomic 仮定からそこへ落とす bridge は別問題」と判定した。

* その短距離検査の結果、Stage 1b の未解決は数学内容より
  **cyclotomic integer-ring parameterization という infrastructure 問題**
  だと分かり、そこで深掘りせず Stage 1a の細分化へ戻る方針にした。

* Stage 1a を
  **ideal factorization → ideal product p-th power → class p-torsion witness**
  の 3 層へ分け、theorem-level の最薄 kernel を `cyclotomicIdealFactorization_of_gapDivisibleGeometry` に局所化した。

* さらにその上流を
  **factorization identity → ideal equation packaging**
  の 2 層に割り、Dedekind / integrality 側の責務と純 factorization の責務を分離した。

* ついで
  **pure factorization identity → gap-divisible specialization**
  に分け、「gap-divisible 条件は factorization 本体ではなく specialization 側で効く」と整理した。

* さらに上流を
  **generic algebraic factorization identity → equation-only identity → prime specialization → abstract identity → counterexample specialization**
  まで薄くした。
  ただし Mathlib の polynomial theorem を global target に直結しようとすると universe 問題が出たので、その receiver 直結案はいったん撤収した。

* そこで方針を切り替え、
  **DkMath-native な局所 factorization core** を自前で実装した。
  `CyclotomicLocalFactorizationContext` と
  $$
  (x-\zeta y)\sum x^i(\zeta y)^{p-1-i}=x^p-y^p
  $$
  および FLT 方程式版
  $$
  z^p-y^p=x^p
  $$
  への specializationを no-sorry で入れ、Stage 1a の「FLT に実際に効く局所核」は concrete proof として閉じた。

* その local core からさらに、principal ideal の積の式
  $$
  (z-\zeta y)\text{ 型の ideal の積}=(x)^p
  $$
  を concrete に落とし、差が unit のときの comaximality、coprime、`inf = mul` まで no-sorry で整備した。

* 加えて Dedekind 領域の有限族について、
  **prime-power ideals の `inf = product`、Chinese remainder、代表元の存在、factor count**
  の receiver 群を DkMath 側へ取り込んだ。これで finite-family ideal arithmetic の土台がそろった。

* その土台を使って、review-012 の本丸だった generic theorem
  **「pairwise-coprime な ideal family の積が p 乗 ideal なら、各因子も p 乗 ideal」**
  を no-sorry で実装した。さらに
  **「principal な p 乗 ideal から class-group p-torsion witness が出る」**
  generic bridge まで no-sorry で通した。

* ここまで来て、`CyclotomicClassGroupPTorsionFreeTarget` 自体を concrete な
  $$
  \forall a,\ a^n=1 \to a=1
  $$
  型命題へ置き換え、Stage 1b の
  `cyclotomicPTorsionAnnihilation_of_classGroupPTorsionFree` も no-sorry 化した。
  これで class-group 側の抽象 target は placeholder を脱した。

* その結果、残る direct `sorry` は `cyclotomicPrincipalization_of_classGroupPTorsionFree` の 1 本だけになった。
  そして、この theorem が残る理由は「class-group だけでは足りず、Stage 2 / Stage 3、すなわち unit normalization と norm descent が別入力として必要」だと確定した。

* 最後に、legacy one-shot route を本筋から外し、
  **regular prime + Stage 2 + Stage 3 → GapDivisible → FLT**
  という refined regular-prime route を public mainline に昇格させた。
  ここは no-sorry で通っており、残る honest open が
  **`CyclotomicUnitNormalizationTarget` と `CyclotomicNormDescentTarget` の concrete 化**
  に集中したことが、API 上でもはっきりした。

## 2. いまの現在地

* **no-sorry で固まった部分**

  * local factorization core
  * local ideal arithmetic
  * finite-family Dedekind arithmetic
  * each-pth-power generic theorem
  * class-group p-torsion witness までの generic bridge
  * class-group p-torsion-free target と Stage 1b
  * refined regular-prime mainline

* **honest open として残っている部分**

  * `CyclotomicUnitNormalizationTarget`
  * `CyclotomicNormDescentTarget`
  * legacy な one-shot wrapper `cyclotomicPrincipalization_of_classGroupPTorsionFree` は、事実上この 2 つを暗に抱えている残骸

必要なら次に、この流れを
**「設計の流れ」** と **「数学の流れ」** の 2 本立てでも整理して出すぞい。

---

## Mathmatical Footprint

よい。では、この会話全体で進んだ内容を「数学の流れ」だけに絞って、上流から下流へ一本の筋として並べるぞい。

## 1. 出発点

* 出発点は FLT 反例の形
  $$
  x^p + y^p = z^p
  $$
  じゃ。
* これを
  $$
  z^p - y^p = x^p
  $$
  と見て、「差の冪」を cyclotomic な線型因子へ割る、というのが Kummer branch の最初の着想じゃ。

## 2. 局所因数分解

* まず \( \zeta^p = 1 \) を満たす元 \(\zeta\) を持つ局所文脈を置き、
  $$
  (x-\zeta y)\sum_{i=0}^{p-1} x^i(\zeta y)^{p-1-i} = x^p-y^p
  $$
  を no-sorry で実装した。
* さらに FLT 方程式へ specialize して
  $$
  (z-\zeta y)\sum_{i=0}^{p-1} z^i(\zeta y)^{p-1-i} = x^p
  $$
  を得た。
* ここで、「Kummer 第一場合で見るべき局所線型因子」は
  $$
  z-\zeta y
  $$
  である、という数学的焦点が定まった。

## 3. 元の等式から ideal の等式へ

* 次に、この元の等式を principal ideal の等式へ落とした。
* 具体的には
  $$
  \bigl(z-\zeta y\bigr)\cdot(\text{残りの和}) = x^p
  $$
  から
  $$
  (z-\zeta y)\cdot(\text{残り}) = (x)^p
  $$
  型の ideal identity を得た。
* これで「元の因数分解」が「ideal の積の等式」へ変換され、Dedekind ideal arithmetic に入れるようになった。

## 4. 異なる線型因子の互いに素性

* Kummer 的に次に要るのは、異なる線型因子 ideal が pairwise に互いに素であることじゃ。
* そのために、差が unit なら
  $$
  (z-\alpha y) + (z-\beta y) = (1)
  $$
  つまり comaximal になる補題を入れた。
* さらに
  $$
  (z-\alpha y)\cap(z-\beta y) = (z-\alpha y)(z-\beta y)
  $$
  も concrete に固定した。
* これにより、後で有限族の ideal の積を扱うときの「pairwise-coprime family」の入口ができた。

## 5. 有限族の Dedekind ideal arithmetic

* そこから先は 2 個の ideal では足りぬので、有限族の Dedekind arithmetic を整備した。
* 具体的には

  * prime-power ideals に対する \( \inf = \prod \)
  * Chinese remainder
  * 各合同条件を同時に満たす代表元
  * normalized factors の count による指数読取り
    を DkMath 側の theorem として受けた。

## 6. 本丸の generic theorem

* そして review-012 の本丸として、
  「pairwise-coprime な ideal family の積が p 乗 ideal なら、各因子も p 乗 ideal」
  を generic theorem として no-sorry で通した。
* 数式で言えば、
  $$
  \prod_{i\in s} I_i = J^p,
  \qquad
  I_i \text{ が pairwise-coprime}
  $$
  なら
  $$
  \forall i\in s,\ \exists K_i,\ I_i = K_i^p
  $$
  を示したわけじゃ。
* ここで Kummer 理論の ideal arithmetic の核心が、ほぼ generic な Dedekind theorem として固定された。

## 7. class group への落下

* 各因子が
  $$
  I_i = K_i^p
  $$
  と書け、しかも \(I_i\) 自身は principal ideal であるなら、class group では
  $$
  [K_i]^p = 1
  $$
  が従う。
* この橋も generic theorem として no-sorry で入った。
* つまり「ideal の p 乗性」から「class-group p-torsion witness」への橋は、もう抽象ではなく定理列として敷けた。

## 8. p-torsion annihilation

* 次に、class-group 側の target 自体を concrete に置き換えた。
* すなわち
  $$
  \forall a,\ a^n=1 \to a=1
  $$
  という p-torsion-free 命題を、`CyclotomicClassGroupPTorsionFreeTarget` の中身そのものにした。
* その結果、
  $$
  [K_i]^p = 1 \Rightarrow [K_i]=1
  $$
  が直ちに出るようになり、Stage 1b は数学内容として閉じた。

## 9. principal root ideal の回収

* \([K_i]=1\) なら \(K_i\) は principal ideal じゃから
  $$
  K_i = (\beta_i)
  $$
  と書ける。
* したがって
  $$
  I_i = K_i^p = (\beta_i)^p
  $$
  となり、線型因子 ideal が「元の p 乗」で与えられることになる。
* ここまでで、ideal arithmetic と class group を通じて
  $$
  (z-\zeta y) = (\beta)^p
  $$
  型の principalization 直前まで来たわけじゃ。

## 10. いま残っている数学

* ここで判明したのは、class-group 側はもう本丸ではない、ということじゃ。
* 残る honest open は

  * unit normalization
  * norm descent
    の 2 点に集中した。
* つまり、まだ必要なのは
  $$
  (z-\zeta y) = (\beta)^p
  $$
  という ideal の statement から、元の statement
  $$
  z-\zeta y = u\beta^p
  $$
  （\(u\) は unit）へ戻す段と、
  そこから norm を取って整数側の witness を回収する段じゃ。

## 11. public mainline の現在地

* そのため、legacy one-shot
  $$
  \text{class-group 仮定} \Rightarrow \text{full principalization}
  $$
  は本筋から外され、
* いまの正本は
  $$
  \text{regular prime}

  * \text{Stage 2}
  * \text{Stage 3}
    \Rightarrow
    \text{GapDivisible}
    \Rightarrow
    \text{FLT}
    $$
    という refined route になった。
* これは、「未解決がもう class-group ではなく、unit と norm にある」と数学的責務を honest に表しておる。

## 12. ひとことで総括

* この会話全体の数学の流れをひとことで言えば、

$$
x^p+y^p=z^p
$$

から始めて、

$$
z^p-y^p=x^p
$$

を cyclotomic 線型因子へ割り、
それを ideal の積へ落とし、
pairwise-coprime な Dedekind ideal arithmetic で各因子を p 乗 ideal に戻し、
class group で p-torsion を殺して principal root ideal を取り直し、
最後に残った問題を

$$
\text{unit normalization} \quad\text{と}\quad \text{norm descent}
$$

の 2 本へ押し込んだ、という流れじゃ。

必要なら次に、これをさらに

* 「証明の論理順」
* 「どの補題がどこで使われるか」
* 「今後埋めるべき残り 2 段」

の 3 観点に分けて整理するぞい。

---

## 証明の論理順

よい。では今度は、時間順ではなく **「証明が実際に前へ進む論理順」** で並べ直すぞい。
つまり、「何を先に示すと、次に何が言えるか」という順序じゃ。

## 1. FLT 反例式を差の冪へ直す

出発点は

$$
x^p + y^p = z^p
$$

じゃが、論理上まず使うのはこれを

$$
z^p - y^p = x^p
$$

と見直すことじゃ。
ここで以後の狙いは、左辺の差の冪を cyclotomic な線型因子へ分解し、その因子の ideal 構造を追うことになる。
この「和の冪」ではなく「差の冪」として見る切り替えが、証明の最初の鍵じゃ。

## 2. 局所的な線型因子分解を作る

次に、\(\zeta^p = 1\) を満たす元 \(\zeta\) を持つ局所文脈で

$$
(x-\zeta y)\sum_{i=0}^{p-1} x^i(\zeta y)^{p-1-i}
= x^p-y^p
$$

を示す。
さらに FLT の式へ specialize して

$$
(z-\zeta y)\sum_{i=0}^{p-1} z^i(\zeta y)^{p-1-i}
= x^p
$$

を得る。
ここで「見るべき因子」が

$$
z-\zeta y
$$

だと確定する。以後の ideal 論は全部この因子の family を中心に回る。

## 3. 元の等式を principal ideal の等式へ落とす

元の恒等式だけでは class group へは行けぬ。
そこで次に、上の因数分解を principal ideal の等式に変換する。

要するに

$$
(z-\zeta y)\cdot(\text{残り}) = x^p
$$

から

$$
(z-\zeta y)\text{ に対応する ideal の積} = (x)^p
$$

を得る段じゃ。
これで「数の等式」が「ideal の積の等式」へ翻訳される。ここから先は Dedekind ideal arithmetic の世界になる。

## 4. 異なる線型因子 ideal が互いに素であることを示す

Kummer 的に最重要なのは、異なる因子たちが pairwise に互いに素だということじゃ。
そのため、差が unit なら

$$
(z-\alpha y) + (z-\beta y) = (1)
$$

となる補題を入れ、comaximality を得る。
そこから

$$
(z-\alpha y)\cap(z-\beta y) = (z-\alpha y)(z-\beta y)
$$

も従う。
この段で「局所線型因子の family は pairwise-coprime」という性質が手に入り、有限族の Dedekind arithmetic が使えるようになる。

## 5. 有限族の ideal arithmetic に持ち上げる

次は 2 因子ではなく有限族全体へ進む。
ここで使うのが

* prime-power ideals に対する \( \inf = \prod \)
* Chinese remainder
* factor count
* normalized factors の個数読み

などの finite-family Dedekind 補題群じゃ。
この段の役目は、「1 個ずつ pairwise-coprime」という局所情報を、「有限積全体を prime ideal 指数で読む」という大域情報へ変換することにある。

## 6. 積が p 乗 ideal なら各因子も p 乗 ideal

ここで本丸の generic theorem が入る。
すなわち、

$$
\prod_{i\in s} I_i = J^p
$$

かつ \(I_i\) が pairwise-coprime なら、

$$
\forall i\in s,\ \exists K_i,\ I_i = K_i^p
$$

が従う、という定理じゃ。
これは「積全体が p 乗である」という情報を、「各因子がそれぞれ p 乗 ideal である」という局所情報に戻す段じゃ。
Kummer 理論の ideal arithmetic の心臓部は、まさにここじゃよ。

## 7. principal な因子から class-group p-torsion witness を得る

各 \(I_i\) はもともと線型因子から作っておるから principal じゃ。
しかも上で

$$
I_i = K_i^p
$$

が出た。
すると class group では

$$
[K_i]^p = 1
$$

が従う。
つまり、「ideal の p 乗性」が「class-group の p-torsion witness」へ落ちる。
ここで初めて class group が前面に出る。

## 8. class-group p-torsion-free でその witness を殺す

次に必要なのは、class group に p-torsion がないことじゃ。
それを concrete に

$$
a^n = 1 \Rightarrow a = 1
$$

という target として固定した。
これを適用すると

$$
[K_i]^p = 1 \Rightarrow [K_i] = 1
$$

となる。
つまり \(K_i\) 自身が principal ideal だと分かる。
ここで Stage 1b が閉じる。class-group 側の役目は、実はこの一点に尽きるわけじゃ。

## 9. principal root ideal から generator を取り直す

\([K_i]=1\) なら

$$
K_i = (\beta_i)
$$

と書ける。
ゆえに

$$
I_i = K_i^p = (\beta_i)^p
$$

となる。
ここまでで ideal-level では、線型因子 ideal が「何かの p 乗 ideal」ではなく、**principal ideal の p 乗** であると分かった。
この時点で principalization は almost 完成じゃ。

## 10. ここで初めて unit normalization が必要になる

ただし ideal の等式

$$
(z-\zeta y) = (\beta)^p
$$

だけでは、元の等式

$$
z-\zeta y = u\beta^p
$$

はまだ出てこぬ。
ここで要るのが Stage 2 の unit normalization じゃ。
principal ideals の生成元は unit 倍までしか一意でないから、その unit のずれを吸収して

$$
z-\zeta y = u\beta^p
$$

という element-level の式に戻す必要がある。
ここがいま残っている honest open のひとつじゃ。

## 11. 最後に norm descent で整数 witness を回収する

Stage 2 ができると、次はその両辺に norm を取り、整数側の descent witness を取り出す。
つまり

$$
z-\zeta y = u\beta^p
$$

から norm を回して、

$$
g' \cdot GN(\cdots) = (x/q)^p
$$

型の整数等式へ戻す。
ここで unit の norm がどう振る舞うか、線型因子の norm がどう GN 構造へ落ちるか、が Stage 3 の本体になる。
これがもうひとつの honest open じゃ。

## 12. 論理順の総括

以上を一本に繋げると、証明の論理順はこうじゃ。

$$
x^p+y^p=z^p
$$

から

$$
z^p-y^p=x^p
$$

へ行く。
次に cyclotomic 線型因子分解を作る。
それを principal ideal の積へ落とす。
異なる因子 ideal の pairwise-coprime 性を示す。
有限族 Dedekind arithmetic で「積が p 乗 ideal なら各因子も p 乗 ideal」を示す。
そこから class group で \([K]^p=1\) を得る。
p-torsion-free で \([K]=1\) を得る。
よって root ideal が principal になる。
そこで unit normalization により元の式

$$
z-\zeta y = u\beta^p
$$

へ戻す。
最後に norm descent で整数 witness を回収する。
これが、この会話で見えてきた **証明の論理順** じゃ。

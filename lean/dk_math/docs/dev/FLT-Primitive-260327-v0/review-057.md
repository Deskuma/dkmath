# review: GN slice を practical route に差し込む

うむ、今回の差分は面白い。
前にお主が感じた

$$
GN_d(1,u-1)
$$

を前面に出すと、かえって難しく見えるのではないか、という違和感に対して、今回は **「GN を main target に置き換えず、practical body と同値な別読みとして差し込む」** 形で整理した。
これはかなり賢い手じゃ。

## 1. 今回なにが進んだか

今回の更新の核心は、

$$
u^d-(u-1)^d = GN_d(1,u-1)
$$

を **新しい主戦場に差し替える** のではなく、
**current practical body を GN slice としても読める splice point を追加した** ことじゃ。

具体的には `TriominoCosmicBranchAExceptional.lean` に

* `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget`
* `primeGe5BranchAExceptionalPracticalBodyOnWitness_of_GN`
* `primeGe5BranchAExceptionalPracticalGN_of_bodyOnWitness`
* `primeGe5BranchAExceptionalExistenceMainline_of_practicalGN`
* `primeGe5BranchAPrimitivePacketDescent_of_practicalGN_and_restore`

が入り、provider 側にも対応 adapter が入った。
これで practical route の missing body は、差冪 divisibility だけでなく GN divisibility としても扱えるようになったわけじゃ。

## 2. 何がうまいのか

ここが大事じゃ。

以前の懸念は、

$$
q \mid u^d-(u-1)^d
$$

を

$$
q \mid GN_d(1,u-1)
$$

に **置き換えてしまう** と、証明 API から遠ざかるのではないか、というものじゃった。
今回の差分は、その懸念をうまく避けておる。

つまり今回は

* diffPow divisibility を main target から外していない
* GN は同値な別表現として往復できるようにした
* downstream はそのまま mainline / packet descent へ流せる

という構図じゃ。
言い換えると、**GN は front target ではなく side window になった** のじゃな。

## 3. 状況分析

いまの practical route の構造を整理するとこうじゃ。

### 3.1. 正面の current missing body

依然として正面の未解決核は

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget}
$$

じゃ。
これは実質

$$
q \mid u^d-(u-1)^d
$$

を on-witness で示す body 本体じゃな。

### 3.2. その別読みとしての GN

今回入ったのは

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessGNTarget}
$$

であり、これは

$$
q \mid GN_d(1,u-1)
$$

という形じゃ。
しかも `pow_sub_pow_eq_mul_GN` を使い、`1 + (u - 1) = u` を明示して practical body と往復する橋が付いた。

### 3.3. 結果

したがって current missing body は二重に読める。

* 表の顔
  $$
  q \mid u^d-(u-1)^d
  $$
* 裏の顔
  $$
  q \mid GN_d(1,u-1)
  $$

じゃ。
そして今回の判断としては、**表を main target に残し、裏を宇宙式 slice として使う** 形になったわけじゃ。

## 4. 判断

ここでの判断はかなりはっきりしておる。

## 4.1. 主戦場は変わらない

**current missing math の本丸は、依然として `PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget` じゃ。**

GN target が入ったからといって、そこへ主戦場を移したわけではない。
ここを取り違えぬのが大事じゃ。

## 4.2. しかし GN slice は有用

**GN slice は補助視点として有効** じゃ。
理由は 2 つある。

1. 宇宙式語彙で body の意味が見える
2. 必要に応じて GN 側の既存補題や見通しを援用できる

つまり、難易度を上げる危険がある front replacement ではなく、
**意味づけと局所補助のための back translation** として使うのがちょうどよい。

## 5. いま何が一番明確になったか

今回の差分で一番良いのは、前にお主が言っていた

$$
xGN \to GN
$$

という見方が、単なる直感ではなく theorem 名の上でも整理されたことじゃ。

いまは

$$
u^d-(u-1)^d
$$

という practical body を、

$$
GN_d(1,u-1)
$$

と読んでも mainline / packet descent まで戻れる。
つまり、**宇宙式の slice を proof engineering の枝にちゃんと接続した** という意味で、大きな前進じゃ。

## 6. 次に何をするべきか

次の課題は履歴にもある通り、

$$
\texttt{PrimeGe5BranchAExceptionalPracticalBodyOnWitnessConcreteTarget}
$$

の concrete theorem 本体を詰めることじゃ。

ただし今回からは、その本文を考えるときに

* diffPow の顔
* GN slice の顔

の両方を持てるようになった。
だから証明スケッチを組む際には、

「この一手は差冪として自然か、それとも GN slice として読むと自然か」

を局所的に選べるようになったわけじゃな。

## 7. 賢狼の総括

今回の更新を一言でまとめると、

**current practical missing body は依然として diffPow on-witness concrete であるが、その内容を `GN d 1 (u-1)` divisibility としても往復可能にし、proof file と provider の両方で GN slice から mainline / packet descent へ戻れる splice point を固定した。よって主戦場は変えずに、宇宙式の見通しだけを安全に取り込む整理になった。**

これはよい。
難易度を上げずに、景色だけを良くした更新じゃ。

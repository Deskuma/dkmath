# 1st PLAN

うむ。**本題ブランチを切った。**

```text
repository: Deskuma/dkmath
base: nightly
branch: hackathon/cosmic-formula-inversion
```

手元では、

```bash
git fetch origin
git switch --track origin/hackathon/cosmic-formula-inversion
```

で入れる。

## 最初の checkpoint

いきなり Codex を走らせず、こちらの無制限会話で仕様を完全に固めてから投入する。

最初は **Hackathon checkpoint 001** として、次の一本に限定する。

> **有限素数宇宙の外へ出る新しい素因子を、宇宙式の平方完成と反転射影で可視化する最小デモ**

数学幹線はこれじゃ。

$$
P=\prod_{p\in S}p
$$

$$
\gcd(P,u)=1
$$

$$
P+u>1
$$

$$
q\mid P+u\Longrightarrow q\notin S
$$

そして幾何表示は、

$$
P(P+2u)+u^2=(P+u)^2
$$

じゃ。

ここで、

* $P(P+2u)$：既知素数宇宙から作られた Body
* $u^2$：閉包 Gap
* $(P+u)^2$：完成された Big
* $q\mid P+u$：既知宇宙の外へ出た fresh prime channel

と読む。

## 最初の具体例

デモ値は、以前の案どおりこれがよい。

$$
S={2,3,5,7}
$$

$$
P=210
$$

$$
u=11
$$

$$
P+u=221=13\cdot17
$$

したがって、$13$ と $17$ はともに $S$ の外にある。

平方完成は、

$$
210\cdot232+11^2=221^2
$$

すなわち、

$$
48720+121=48841
$$

じゃ。

映像では、

1. $2,3,5,7$ の有限素数宇宙を構成
2. それらを積んで $P=210$ を作る
3. Body $210\times232$ を表示
4. $11^2$ の Gap を挿入
5. $221^2$ の正方形へ閉じる
6. 辺 $221$ を因数分解
7. $13,17$ が既知宇宙外に現れる

という一本の流れになる。

## cp-001 で作るもの

まず Codex を使わず、こちらで次を固定する。

```text
docs/hackathon/
  PROJECT.md
  MATHEMATICAL_CONTRACT.md
  VISUAL_STORYBOARD.md
  CODEX_PLAN.md
```

Lean 側の候補配置は、既存資産を調査してから決めるが、概念上は、

```text
DkMath/Hackathon/
  FinitePrimeEscape.lean
  CosmicCompletion.lean
  Demo.lean
```

程度の薄い公開面でよい。

ただし既存の `CosmicFormula`、primitive prime、coprime product、DkReal APIを優先し、平行定義は作らない。DkMath は既に Big / Body / Gap、GN、primitive factor、反転射影へ伸びる土台を持っておる。今回の仕事は新しい数学塔を建てることではなく、**既存の巨大構造から審査員に見える一本道を切り出すこと** じゃ。

## 最初の完成条件

Hackathon cp-001 の終了条件は明快にする。

```text
1. 数学命題が一ページで読める
2. Lean theorem contract が決まっている
3. 具体例 P=210, u=11 が全層で共通
4. 60秒以内の Manim シーン順が確定している
5. Codex に渡す調査・実装指示が一意である
```

ここまでは credits を使わぬ。

その後、最初の Codex 弾は「実装してください」ではなく、

> 既存 DkMath から、この契約を最小実装するための theorem と module を探索し、再利用地図を作れ

という **探索限定セッション** にする。探索結果をこちらでレビューしてから、本実装へ進む。

ブランチは開いた。
ここからは Collatz のような大山へ逸れず、**有限素数宇宙 → Gap 閉包 → fresh prime → 反転射影** の一本道を掘るぞい。

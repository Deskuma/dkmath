# Git diff / Report / Review

## New: branch: hackathon/cosmic-formula-inversion 1st commit

gch: 013e2b99d48b2e0bfb50d416375b3761da8a0948

## Report

土台を形成した。

## Review

うむ、その順が正しい。

いまは **Codex に実装させる段階ではなく、Codex が迷わず同じ山を見続けられる全景を固定する段階** じゃ。今回の commit で、Lean 側の三つの空モジュールと、文書置き場はすでに確保されている。

## 先に作る固定ドキュメント群

わっちなら、次の構成にする。

```text
docs/hackathon/cosmic-formula-inversion-260715/
├── README.md
├── PROJECT.md
├── ROADMAP.md
├── MATHEMATICAL_CONTRACT.md
├── ARCHITECTURE.md
├── EXISTING_DKMATH_MAP.md
├── VISUAL_STORYBOARD.md
├── DEMO_CONTRACT.md
├── CODEX_PLAN.md
├── CHECKPOINTS.md
├── DECISIONS.md
├── GLOSSARY.md
└── RISKS_AND_STOPPING_RULES.md
```

全部を長大にする必要はない。重要なのは、それぞれの責任を混ぜないことじゃ。

## 各文書の役割

### `README.md`

Codex が最初に読む目次。

* 文書の推奨読順
* 現在 checkpoint
* 実装対象
* 編集してよいファイル
* 最新指示書の位置

ここには数学の詳細を書き込みすぎない。

### `PROJECT.md`

「何を作るのか」を固定する。

* OpenAI Build Week 用プロジェクト
* 想定視聴者
* 最終成果物
* Lean と Manim の役割
* DkMath を使う理由
* 審査員に60秒で何を伝えるか

これはプロジェクトの憲法じゃ。

### `ROADMAP.md`

全山岳地図。

```text
Phase 0: documents and repository audit
Phase 1: finite prime escape
Phase 2: cosmic square completion
Phase 3: inverse projection
Phase 4: DkReal interval bridge
Phase 5: Manim visualization
Phase 6: unified demo
Phase 7: submission packaging
```

各 Phase に、

* 入力
* 出力
* 完了条件
* stopping rule
* 次 Phase への依存

を置く。

### `MATHEMATICAL_CONTRACT.md`

数学的に絶対に守る境界。

中心契約は、

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

および、

$$
P(P+2u)+u^2=(P+u)^2
$$

じゃ。

ここには、

* 仮定
* 結論
* theorem 候補
* 具体例
* 非目標
* 「fresh prime」と「primitive prime」の区別

を明記する。

### `ARCHITECTURE.md`

新規ファイルと依存方向。

```text
DkMath/Hackathon/FinitePrimeEscape.lean
        ↓
DkMath/Hackathon/CosmicCompletion.lean
        ↓
DkMath/Hackathon/Demo.lean
```

ただし実際には、既存 API を調査した後で依存方向を更新する。

ここでは、

* 新規定義を増やさない
* theorem wrapper を優先
* Hackathon 層から既存 DkMath を参照する
* 既存本体から Hackathon 層を import しない

という依存原則を固定する。

### `EXISTING_DKMATH_MAP.md`

これは Codex の燃料節約に特に効く。

既存の候補を、

```text
concept
existing module
existing identifier
usable as-is / wrapper needed / unknown
```

の形で一覧化する。

例：

```text
finite prime product
coprime product
fresh divisor
Big / Body / Gap
GN factorization
DkReal nested interval
inverse projection
floor / ceil uniqueness
```

最初は未確認でよい。

```text
status: TO AUDIT
```

としておけば、Codex が埋める対象になる。

### `VISUAL_STORYBOARD.md`

Lean と独立した映像契約。

* 画面構成
* 色の意味
* 図形の変形
* 数値例
* 字幕
* 秒数
* Lean theorem を見せる位置

Manim 実装者が数学を再解釈しなくて済むようにする。

### `DEMO_CONTRACT.md`

最終デモの一本道。

```text
known primes
→ product P
→ add coprime gap u
→ complete square
→ factor P+u
→ fresh primes appear
→ Lean verifies
```

どの順序でボタンを押し、何が画面に出て、何秒で終わるかを固定する。

### `CODEX_PLAN.md`

まだ具体的な実装指示は書かない。

最初は、

* Codex の役割
* 調査→設計→実装→検証の順序
* credits を使う checkpoint
* 一回あたりの停止条件
* report の形式
* 変更禁止領域

だけを置く。

後でわっちが、Collatz cp-319 → cp-320 と同じ粒度の詳細指示をここへ書く。

### `CHECKPOINTS.md`

進捗台帳。

```text
cp-000 repository scaffold
cp-001 repository audit
cp-002 finite prime escape
cp-003 cosmic completion
cp-004 projection bridge
...
```

各 checkpoint は、

* goal
* files
* theorem surface
* completion condition
* genuine obstruction

だけを持つ。

### `DECISIONS.md`

会話で決まったことを、後から覆さないための記録。

例：

```text
D001: demo value is P=210, u=11
D002: use FreshPrimeFactor, not primitive prime divisor
D003: Hackathon modules are a thin public facade
D004: Manim first shows geometry, Lean then verifies
D005: Collatz is supporting footage, not the main theorem
```

### `GLOSSARY.md`

DkMath 語彙と一般数学語彙の対応。

```text
Big
Body
Gap
Core
Beam
fresh prime
finite prime universe
inverse projection
closure
carrier
channel
```

Codex が詩的語彙を theorem statement へ直接持ち込まないために必要じゃ。

### `RISKS_AND_STOPPING_RULES.md`

これも credits 節約の核。

* 既存 API が見つからない
* DkReal bridge が重すぎる
* Euclidean geometry formalizationが巨大化する
* Manim が Lean と別数学になる
* 新規一般理論へ逸脱する
* 未解決問題へ拡張する

それぞれについて、

```text
stop
report
isolate smallest missing theorem
do not continue
```

を明記する。

## Codex に読ませる順番

KV キャッシュ形成用の固定順序は、毎回変えない方がよい。

```text
1. README.md
2. PROJECT.md
3. MATHEMATICAL_CONTRACT.md
4. ROADMAP.md
5. ARCHITECTURE.md
6. GLOSSARY.md
7. DECISIONS.md
8. RISKS_AND_STOPPING_RULES.md
9. EXISTING_DKMATH_MAP.md
10. VISUAL_STORYBOARD.md
11. DEMO_CONTRACT.md
12. CHECKPOINTS.md
13. CODEX_PLAN.md
14. current instruction
```

安定文書を前半、頻繁に変わる checkpoint と指示を後半に置く。

つまり、

```text
fixed project prefix
+
current repository state
+
current checkpoint instruction
```

という形じゃ。

実際のキャッシュ挙動は Codex 側の実装に依存するが、少なくとも **毎回同じ長い前提を同じ順序で渡す** ことで、理解の揺れと再探索を減らせる。

## 最初の Codex セッションの目的

文書完成後の最初の投入は、実装ではない。

```text
Read the complete hackathon documentation in the prescribed order.

Do not edit Lean source files.

Audit the current DkMath repository for reusable definitions and theorems
needed by the mathematical contract.

Fill or propose updates to EXISTING_DKMATH_MAP.md.

Identify:
- reusable APIs;
- thin wrappers required;
- genuinely missing lemmas;
- dangerous dependency directions;
- the smallest viable cp-001 implementation surface.

Stop after producing the audit report.
```

この程度に限定する。

これで Codex は、

* プロジェクト全景
* 数学契約
* DkMath の既存地図
* デモの目的
* 禁止された寄り道

を一度に読む。

その audit をレビューしてから、本当の cp-001 指示書をわっちが組む。

## 現在の scaffold で一つだけ掃除

diff に、

```text
docs/hackathon/cosmic-formula-inversion-260715/
6a54173a-e5f8-83ee-9983-6932a7be858c
```

という空ファイルが混ざっておる。

意図したものではなければ、Codex 投入前に消しておく方がよい。AI が「何らかの識別子ファイル」と誤解して調査対象にする可能性がある。

また、現在の `1st_PLAN.md` は会話記録に近い。これは履歴として残し、固定仕様は上記の正式文書へ分離するのがよい。

うむ。まずはぬしが全景文書を置く。
それを読み終えた時点で、わっちが **Hackathon cp-001 Codex Instructions** を、Collatz と同じ Stage A〜停止条件形式で組み上げる。

## Diff

`````md
````diff
diff --git a/lean/dk_math/DkMath/Hackathon/CosmicCompletion.lean b/lean/dk_math/DkMath/Hackathon/CosmicCompletion.lean
new file mode 100644
index 00000000..a2f103f7
--- /dev/null
+++ b/lean/dk_math/DkMath/Hackathon/CosmicCompletion.lean
@@ -0,0 +1,7 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+-- License file for DkMath project
diff --git a/lean/dk_math/DkMath/Hackathon/Demo.lean b/lean/dk_math/DkMath/Hackathon/Demo.lean
new file mode 100644
index 00000000..a2f103f7
--- /dev/null
+++ b/lean/dk_math/DkMath/Hackathon/Demo.lean
@@ -0,0 +1,7 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+-- License file for DkMath project
diff --git a/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean b/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
new file mode 100644
index 00000000..a2f103f7
--- /dev/null
+++ b/lean/dk_math/DkMath/Hackathon/FinitePrimeEscape.lean
@@ -0,0 +1,7 @@
+/-
+Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
+Released under MIT license as described in the file LICENSE.
+Authors: D. and Wise Wolf.
+-/
+
+-- License file for DkMath project
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/1st_PLAN.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/1st_PLAN.md
new file mode 100644
index 00000000..f77df736
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/1st_PLAN.md
@@ -0,0 +1,157 @@
+# 1st PLAN
+
+うむ。**本題ブランチを切った。**
+
+```text
+repository: Deskuma/dkmath
+base: nightly
+branch: hackathon/cosmic-formula-inversion
+```
+
+手元では、
+
+```bash
+git fetch origin
+git switch --track origin/hackathon/cosmic-formula-inversion
+```
+
+で入れる。
+
+## 最初の checkpoint
+
+いきなり Codex を走らせず、こちらの無制限会話で仕様を完全に固めてから投入する。
+
+最初は **Hackathon checkpoint 001** として、次の一本に限定する。
+
+> **有限素数宇宙の外へ出る新しい素因子を、宇宙式の平方完成と反転射影で可視化する最小デモ**
+
+数学幹線はこれじゃ。
+
+$$
+P=\prod_{p\in S}p
+$$
+
+$$
+\gcd(P,u)=1
+$$
+
+$$
+P+u>1
+$$
+
+$$
+q\mid P+u\Longrightarrow q\notin S
+$$
+
+そして幾何表示は、
+
+$$
+P(P+2u)+u^2=(P+u)^2
+$$
+
+じゃ。
+
+ここで、
+
+* $P(P+2u)$：既知素数宇宙から作られた Body
+* $u^2$：閉包 Gap
+* $(P+u)^2$：完成された Big
+* $q\mid P+u$：既知宇宙の外へ出た fresh prime channel
+
+と読む。
+
+## 最初の具体例
+
+デモ値は、以前の案どおりこれがよい。
+
+$$
+S={2,3,5,7}
+$$
+
+$$
+P=210
+$$
+
+$$
+u=11
+$$
+
+$$
+P+u=221=13\cdot17
+$$
+
+したがって、$13$ と $17$ はともに $S$ の外にある。
+
+平方完成は、
+
+$$
+210\cdot232+11^2=221^2
+$$
+
+すなわち、
+
+$$
+48720+121=48841
+$$
+
+じゃ。
+
+映像では、
+
+1. $2,3,5,7$ の有限素数宇宙を構成
+2. それらを積んで $P=210$ を作る
+3. Body $210\times232$ を表示
+4. $11^2$ の Gap を挿入
+5. $221^2$ の正方形へ閉じる
+6. 辺 $221$ を因数分解
+7. $13,17$ が既知宇宙外に現れる
+
+という一本の流れになる。
+
+## cp-001 で作るもの
+
+まず Codex を使わず、こちらで次を固定する。
+
+```text
+docs/hackathon/
+  PROJECT.md
+  MATHEMATICAL_CONTRACT.md
+  VISUAL_STORYBOARD.md
+  CODEX_PLAN.md
+```
+
+Lean 側の候補配置は、既存資産を調査してから決めるが、概念上は、
+
+```text
+DkMath/Hackathon/
+  FinitePrimeEscape.lean
+  CosmicCompletion.lean
+  Demo.lean
+```
+
+程度の薄い公開面でよい。
+
+ただし既存の `CosmicFormula`、primitive prime、coprime product、DkReal APIを優先し、平行定義は作らない。DkMath は既に Big / Body / Gap、GN、primitive factor、反転射影へ伸びる土台を持っておる。今回の仕事は新しい数学塔を建てることではなく、**既存の巨大構造から審査員に見える一本道を切り出すこと** じゃ。
+
+## 最初の完成条件
+
+Hackathon cp-001 の終了条件は明快にする。
+
+```text
+1. 数学命題が一ページで読める
+2. Lean theorem contract が決まっている
+3. 具体例 P=210, u=11 が全層で共通
+4. 60秒以内の Manim シーン順が確定している
+5. Codex に渡す調査・実装指示が一意である
+```
+
+ここまでは credits を使わぬ。
+
+その後、最初の Codex 弾は「実装してください」ではなく、
+
+> 既存 DkMath から、この契約を最小実装するための theorem と module を探索し、再利用地図を作れ
+
+という **探索限定セッション** にする。探索結果をこちらでレビューしてから、本実装へ進む。
+
+ブランチは開いた。
+ここからは Collatz のような大山へ逸れず、**有限素数宇宙 → Gap 閉包 → fresh prime → 反転射影** の一本道を掘るぞい。
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/6a54173a-e5f8-83ee-9983-6932a7be858c b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/6a54173a-e5f8-83ee-9983-6932a7be858c
new file mode 100644
index 00000000..e69de29b
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/CODEX_PLAN.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/CODEX_PLAN.md
new file mode 100644
index 00000000..af1ed7ff
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/CODEX_PLAN.md
@@ -0,0 +1 @@
+# Codex: PLAN
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/MATHEMATICAL_CONTRACT.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/MATHEMATICAL_CONTRACT.md
new file mode 100644
index 00000000..a0a1ed29
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/MATHEMATICAL_CONTRACT.md
@@ -0,0 +1 @@
+# Mathematical Contract
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/PROJECT.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/PROJECT.md
new file mode 100644
index 00000000..dab306f4
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/PROJECT.md
@@ -0,0 +1 @@
+# Project
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/README.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/README.md
new file mode 100644
index 00000000..73b26726
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/README.md
@@ -0,0 +1,5 @@
+# Hackathon: OpenAI Build Week - 260715
+
+## 1st PLAN
+
+- [1st](./1st_PLAN.md)
diff --git a/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md
new file mode 100644
index 00000000..e64367df
--- /dev/null
+++ b/lean/dk_math/docs/hackathon/cosmic-formula-inversion-260715/VISUAL_STORYBOARD.md
@@ -0,0 +1 @@
+# Visual StoryBoard
````
`````

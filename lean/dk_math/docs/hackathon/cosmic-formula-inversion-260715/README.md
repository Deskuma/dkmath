# Hackathon: OpenAI Build Week - 260715

## Cosmic Formula Inversion

OpenAI Build Week 向けの DkMath ハッカソン開発資料です。

このプロジェクトでは、DkMath に既に存在する数論・宇宙式・実数射影の API を再利用し、次の流れを Lean 4 と可視化で提示します。

```text
有限素数宇宙
  → coprime Gap
  → 宇宙式による平方完成
  → 既知宇宙外の fresh prime
  → 反転射影
  → Lean による検証
  → Manim による可視化
```

本プロジェクトの目的は、新しい巨大理論をこのディレクトリ内に再実装することではありません。

既存の DkMath ライブラリから必要な構造を探索し、薄い Hackathon API と、審査用に理解可能な一本のデモ導線へまとめます。

## Repository

```text
repository:
  Deskuma/dkmath

base branch:
  nightly

working branch:
  hackathon/cosmic-formula-inversion
```

Lean 側の作業領域:

```text
DkMath/Hackathon/
  FinitePrimeEscape.lean
  CosmicCompletion.lean
  Demo.lean
```

文書側の作業領域:

```text
docs/hackathon/cosmic-formula-inversion-260715/
```

## Core Mathematical Route

有限素数集合 $S$ に対して、

$$
P=\prod_{p\in S}p
$$

とします。

$u$ が $P$ と互いに素で、$P+u>1$ ならば、$P+u$ の任意の素因子は $S$ の外側にあります。

$$
\gcd(P,u)=1
$$

$$
q\mid P+u
$$

$$
q\notin S
$$

この有限素数脱出を、宇宙式の平方完成と接続します。

$$
P(P+2u)+u^2=(P+u)^2
$$

DkMath 語彙では、暫定的に次のように読みます。

```text
Body:
  P(P + 2u)

Gap:
  u^2

Big:
  (P + u)^2

fresh prime channel:
  prime divisor q of P + u with q not in S
```

ここでいう fresh prime は、有限集合 $S$ に対して新しい素因子という意味です。

数列に対する primitive prime divisor と混同しないでください。

## Canonical Demo Example

全レイヤーで同じ具体例を使います。

$$
S=\{2,3,5,7\}
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

$13$ と $17$ は、どちらも $S$ に含まれません。

平方完成は次です。

$$
210\cdot232+11^2=221^2
$$

$$
48720+121=48841
$$

Lean theorem、Manim scene、説明文、デモ UI は、原則としてこの例を共有します。

## Documentation Reading Order

Codex は、作業開始前に存在する文書を次の順で読んでください。

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
14. current checkpoint instruction
```

まだ存在しない文書は読み飛ばしてください。

ディレクトリ全体を無差別に読む必要はありません。

`1st_PLAN.md` はプロジェクト開始時の履歴資料です。現在の checkpoint 指示より優先しません。

## Source-of-Truth Priority

内容が競合した場合は、次の順で新しい情報を優先します。

```text
1. current checkpoint instruction
2. CHECKPOINTS.md
3. DECISIONS.md
4. MATHEMATICAL_CONTRACT.md
5. ARCHITECTURE.md
6. ROADMAP.md
7. PROJECT.md
8. 1st_PLAN.md
```

数学的事実については、文書の説明より Lean が認めた theorem statement を優先します。

既存実装の有無については、推測せず、実際の DkMath source を検索してください。

## Codex Operating Rules

Codex は、各 checkpoint の指示に従って次の順で作業します。

```text
read
→ audit
→ identify reusable APIs
→ isolate missing lemmas
→ implement only the requested surface
→ build
→ report
→ stop
```

次を守ってください。

- 既存 DkMath API の再利用を優先する。
- 同じ概念の平行定義を作らない。
- Hackathon module は薄い facade / wrapper / bridge とする。
- Hackathon 専用コードを既存理論の下層へ逆流させない。
- current checkpoint にない隣接研究へ進まない。
- 未解決問題の解決を主張しない。
- finite theorem から infinite theorem へ飛躍しない。
- fresh prime と primitive prime divisor を混同しない。
- 可視化上の説明を、証明済み theorem より強くしない。
- 真正な障害を発見した場合は、その地点で止まる。
- 停止時には、最小の不足 theorem または API を報告する。

## Tracking-Key Files

UUID 形式の名前を持つ空ファイルは、会話・作業履歴を接続するための追跡タグです。

```text
example:
  6a54173a-e5f8-83ee-9983-6932a7be858c
```

これらは意図的に空です。

- 削除しない。
- 名前を変更しない。
- 内容を追加しない。
- 中身を読む必要はない。
- 実装対象として扱わない。

ファイル一覧上で存在を確認するだけで十分です。

## Current Status

現在は repository scaffold の形成が完了した段階です。

```text
Hackathon checkpoint 000:
  branch created
  documentation directory created
  Lean facade files created
  implementation not started
```

現在の空 Lean ファイルは、配置を固定するための土台です。

数学 API の設計と既存 DkMath の再利用調査が完了するまで、独自定義を追加しないでください。

## First Development Goal

第一目標は、次を一本の検証可能なデモとして閉じることです。

```text
finite prime set S
→ product P
→ coprime offset u
→ fresh prime divisor of P + u
→ cosmic square completion
→ concrete example P = 210, u = 11
→ Lean verification
→ Manim visualization
```

最初の Codex セッションでは、Lean 実装を開始せず、既存 DkMath API の再利用地図を作成します。

具体的な編集範囲と停止条件は、`CODEX_PLAN.md` および current checkpoint instruction に従ってください。

## Completion Principle

各 checkpoint は、次のどちらかで終了します。

```text
A. requested deliverable is complete and verified

B. the first genuine obstruction is isolated and reported
```

隣接する Phase を自動的に開始しないでください。

本プロジェクトでは、広く探索することよりも、検証済みの一本道を完成させることを優先します。

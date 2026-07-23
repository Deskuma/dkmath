# DkMath Journal Format

DkMath Journal は、Lean が確定した DkMath の事実を、一般数学の言葉へ翻訳して記録する研究ジャーナルである。

## Navigation

```text
INDEX.md
  -> JOURNAL-YYMM.md
    -> YYMMDD-HHMM-english-title.md
```

## Filename

```text
YYMMDD-HHMM-english-title.md
```

日時は日本標準時（Asia/Tokyo）を使用する。

## Required front matter

```yaml
---
journal_id: "YYMMDD-HHMM"
title: "English Title"
title_ja: "日本語題名"
date: "YYYY-MM-DDTHH:MM:SS+09:00"
status: "lean-confirmed"
source_ref: "nightly"
source_files:
  - "path/to/source.lean"
definitions:
  - "Namespace.definition"
theorems:
  - "Namespace.theorem"
tags:
  - "tag"
---
```

## Status

- `lean-confirmed`: 「結果」節に記した中心命題が Lean source に存在する。
- `mixed`: Lean 確定事項と、明示された考察・仮説を含む。
- `historical`: 過去の実装や研究経路を記録する。

## Standard sections

1. 序文
2. 結果
3. 一般数学での読み方
4. DkMath での読み方
5. 構造図
6. 例
7. 考察
8. Lean source anchors

「結果」には Lean が確定した内容のみを書く。

「考察」には、Lean theorem から直接は従わない解釈、今後の接続候補、未形式化の見通しを書く。事実層と混同しない。

## Mathematical notation

表示数式は可能な限り一行で記述する。

```markdown
$$N+u^2=(x+u)^2$$
```

Markdown 記号との衝突を避けるため、数式中の `=`、`+`、`-` を改行直後の行頭へ置かない。

GitHub Markdown の数式表示では、ローマン体の名称に `\mathrm{...}` を使用する。

```markdown
$$\mathrm{Big}=\mathrm{Core}+\mathrm{Beam}+\mathrm{Gap}$$
```

GitHub Viewer が拒否するため、`\operatorname` は使用しない。

## Source anchors

記事は、対象となる Lean file、definition、theorem の完全修飾名を記録する。
これらの識別子は、全定理集合から Journal 済み集合を差し引くための字引きとして利用する。

$$T_{\mathrm{unwritten}}=T_{\mathrm{all}}\setminus T_{\mathrm{journal}}$$

記事一つが複数の theorem を扱ってもよいが、中心テーマは一つに絞る。

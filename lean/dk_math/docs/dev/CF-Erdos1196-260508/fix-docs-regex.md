# fix tex docs regex

review-059.md までは完了済み（Hit するのは Lean コード）

## tex patterns

### md link to unlink

`\[(.*?)\]\(.*?\)` to `$1`

"[ABC.md](/ABC.md)" → "ABC.md"

### 前処理

先にこの置換を行なっておくと良い

"、(" to "、 ("
"「(" to "「 ("
")」" to ") 」"

r" \((.+?)\)" to " \($1\)"

### 対応中

### 未対応

### 対応済み

- `>`, `<` 両端スペースの追加
  - r"([^\s])<([^\s])" to "$1 < $2"
- `\(`,`\)` 内部スペースの除去

" (\Lambda(q)/\log n)"
" (\Lambda(q)/\log p)"

" (p(q))"
" (p(q)\mid n)"

- 単一変数名
- " (p)" → " \(p\)"
- " (W)" → " \(W\)"
- \(\Lambda\) 系
  - " (\Lambda(p))" → " \(\Lambda(p)\)"
  - " (\Lambda)" → " \(\Lambda\)"
  - "、(\Lambda)" → "、 \(\Lambda\)"
- " (\log)" → " \(\log\)"
- " (c(n,p))" → " \(c(n,p)\)"

- " (q=p^k)" → " \(q=p^k\)"
- " (q\mid n)" → " \(q\mid n\)"
- " (next=n/q)" → " \(next=n/q\)"

```
* `hqmem` から (q\mid n)
* `hq : q=p^k` で (p^k\mid n) に変換
* `next_eq_div_of_mem` で (next(n,q)=n/q)
* (q=p^k) を使って (next(n,q)=n/p^k) へ書き換える
```

- " (q)" → " \(q\)"
- " (n)" → " \(n\)"
- " (n/q)" to " \(n/q\)"

- " ({q})" → " \(\{q\}\)"

- " (\mathbb{N})" → " \(\mathbb{N}\)"
- " (p,k)" → " \(p,k\)"
- " (q,p,k)" → " \(q,p,k\)"

- " (A\subset [x,\infty))"
- " (A\subset[x,\infty))"

## KaTeX → TeX

" \\\((.*?)\\\)" → " $$$1$$"

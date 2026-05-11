# fix tex docs regex

## tex patterns

### 対応中

先にこの置換を行なっておくと良い

"、(" to "、 ("

r" \((.+?)\)" to " \($1\)"

### 未対応

" (\Lambda(q)/\log n)"
" (\Lambda(q)/\log p)"

### 対応済み

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

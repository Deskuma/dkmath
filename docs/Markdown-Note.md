# Markdown

## GitHub Markdown Preview

### newline: 改行

#### normal newline: 通常改行

１行目
２行目

#### add space newline: 空白付き改行

段落

１行目  
２行目  
３行目(no space→)

次段落

１行目：(two space→)  
２行目：(one space→)(←フォーマッタにより修正されるので書けない)
３行目：１行目は２つの半角スペース付きなのでフォーマッタはそのまま採用する。これは(no space→)

see: [MD009](https://github.com/DavidAnson/markdownlint/blob/v0.41.1/doc/md009.md)/no-trailing-spaces: Trailing spaces [Expected: 0 or 2; Actual: 1]

（気持ち悪い仕様…。３０年以上前からある → 表示機と電子メール、HTML 時代の遺恨）
GitHub Markdown preview は、これに忠実に作用する。
（なのでこれは GitHub プレビューでは改行されない）

VS Code の [MPE](https://marketplace.visualstudio.com/items?itemName=shd101wyy.markdown-preview-enhanced) では通常もスペース付きも両方、**改行する**

#### 引用の改行

プレーンテキストでは、以下のように書いていても。

```txt
> 引用文章の改行もこの記述で可能となる。
> ２行目
> ３行目
```

> 引用文章の改行もこの記述で可能となる。
> ２行目
> ３行目

GitHub プレビューでは１行で表示される。

これを改行させるには、

> 引用文章の改行もこの記述で可能となる。  
> ２行目  
> ３行目  

と、記述する必要がある。

### LaTeX

#### `\operatorname` not support, replace to `\text` or `\mathrm`

`\operatorname` は使えない。AI は好んで使って出力してくる。（学術論文 $\TeX$ で多用されているから？）

text

$$
\text{sample: text}
$$

mathrm

$$
\mathrm{sample: mathrm}
$$

operatorname

$$
\operatorname{sample: operatorname}
$$

何れも、表示スタイルが異なる。

```txt
sample: text
sample : mathrm
sample:operatorname
```

MPE では、この様に見える。
スペースの取り扱いの違い。

text

$$
\text{GN}_d(x,u)=\text{GTail}_d^{(1)}(x,u)
$$

mathrm

$$
\mathrm{GN}_d(x,u)=\mathrm{GTail}_d^{(1)}(x,u)
$$

operatorname

$$
\operatorname{GN}_d(x,u)=\operatorname{GTail}_d^{(1)}(x,u)
$$

スペースが使用されていなければ、MPE でも概ね表示の違いはない。

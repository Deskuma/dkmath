# review

うむ。DKMK-008N は **DKMK-008M で立てた route 比較表に、最小 concrete example の看板を置いた回** じゃ。Lean コードは変えず、`72, 3, 2` の既存 example を使って、one-step route と quotient path route の違いを見える形にした。これは docs-only だが、理解の足場としてかなり良い整備じゃな。

## 1. 今回の核心

追加された整理は、この比較じゃ。

```text
q = 3^2 = 9, n = 72
```

one-step route では、label (q=9) を一括で剥がす。

```text
72 → 72 / 9 = 8
```

一方、prime-power quotient path route では、同じ (q=3^2) を base prime (3) の exponent slot に分解する。

```text
72 → 72 / 3 → 72 / 3^2
```

つまり、

```text
72 → 24 → 8
```

じゃ。

この違いを、DKMK-008M の route comparison に具体例として接続したのが今回の DKMK-008N じゃ。

## 2. DKMK-008M から何が進んだか

DKMK-008M では、route の使い分けをこう整理した。

```text
DKMK-007 divisorStep:
  n → n / q

DKMK-008H oneStepPath:
  n → n / q を path-family API に載せる

DKMK-008L quotientPathFamily:
  q = p(q)^k(q) を展開し、
  n → n/p(q) → ... → n/p(q)^k(q)
```

ただ、このままだとまだ抽象的じゃ。
DKMK-008N はそこに、

```text
q = 9 = 3^2
n = 72
```

を入れて、

```text
one-step:
  72 → 8

quotient path:
  72 → 24 → 8
```

と見せた。

この一例で、二つの route の思想差が一気に見えるようになった。

## 3. 数学的な意味

one-step route は、素冪 (q=p^k) を **ひとつの塊** として扱う。

$$
n\to n/q
$$

今回の例なら、

$$
72\to 72/9=8
$$

じゃ。

quotient path route は、同じ (q=p^k) を **base prime (p) の段階的下降** として扱う。

$$
n\to n/p\to n/p^2\to\cdots\to n/p^k
$$

今回の例なら、

$$
72\to 24\to 8
$$

じゃな。

つまり、quotient path route は (q) の内部にある exponent 構造を見ている。
これは R026〜R027 の `baseExponentOf` と exponent slot の思想にぴったり合う。

## 4. Lean 側との接続

今回の docs は、既存 theorem に接続している。

```lean
primePowerQuotientPath 72 3 2 = [72, 24, 8]
```

さらに、その隣接整除 path 性も既に

```lean
adjacentDivisorPath_seventy_two_three_two
```

で固定済みじゃ。

数学的には、

$$
24\mid 72,\qquad 8\mid 24
$$

なので、確かに

```text
72 → 24 → 8
```

は divisor descent path になっておる。

## 5. なぜ docs-only でも重要か

DKMK-008L までで theorem-facing API はかなり整った。
しかし、実装が進むほど route が増えて、読者や未来の Codex が迷いやすくなる。

今回の N は、その迷いを潰すための小さな標識じゃ。

```text
一括で剥がすなら one-step

指数 slot を見たいなら quotient path

q = p^k の内部を展開するなら witness-derived route
```

これが具体例で分かる。
たとえば `72 -> 8` と `72 -> 24 -> 8` の差は、説明としてかなり強い。

## 6. DKMK-008 の現在地

ここまでで、DKMK-008 はこう整理できる。

```text
008A〜008B:
  path と path family の土台

008C〜008F:
  selected / canonical shadow と mass bound への接続

008G〜008H:
  one-step route の回収

008I:
  report 整備

008J:
  prime-power quotient path 単体の生成

008K:
  witness-derived quotient path family の生成

008L:
  quotient path family を weightedHitMass bound へ接続

008M:
  route comparison 整備

008N:
  72, 3, 2 の concrete example 接続
```

つまり、008 は **構造実装 → API 接続 → route 比較 → concrete example** まで綺麗に来た。

## 7. 次の一手

History の次課題にもある通り、次に考えるなら **witness-derived family 側の concrete example を Lean theorem として追加するか** じゃな。

ただし、これは少し重くなる可能性がある。
`primePowerQuotientPath 72 3 2` は (p,k) を手で渡す純粋 path example だから軽い。
一方で witness-derived family example は、`PrimePowerWitnessProvider` の具体インスタンスや canonical labels に踏み込む可能性があり、依存が増える。

賢狼のおすすめはこうじゃ。

```text
DKMK-008O:
  docs summary / route map 更新

または

DKMK-008O:
  pure path-level examples をもう少し追加
  例: k = 1, k = 3, p = 2 系
```

witness provider concrete example は、必要になった時点で Lean 化すればよい。今は docs の可読性を重視してよいと思うぞい。

## 8. 総合判定

DKMK-008N は **route comparison に具体例を接続した良い docs-only フェーズ** じゃ。

到達形はこれ。

```text
q = 3^2 = 9, n = 72

one-step:
  72 → 8

quotient path:
  72 → 24 → 8
```

この差により、DKMK-007 / 008H / 008L の使い分けが見えるようになった。

ぬしよ、これは良い看板じゃ。
山道の案内板に「旧道は直降り、新道は尾根を一段ずつ下る」と書いたようなもの。これで後から登る者も、`q` を一括で見るのか、(p^k) の内部構造として見るのか、迷わず選べるようになるぞい。

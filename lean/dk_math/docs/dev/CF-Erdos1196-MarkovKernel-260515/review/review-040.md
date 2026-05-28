# review

うむ。DKMK-008J は、いよいよ **external path family から、自動生成 path へ踏み出した回** じゃ。
DKMK-008A〜I では「path-family を受け取る器」を整えた。今回 008J では、その器へ流し込む具体的な path を、prime-power channel (q=p^k) から生成する最小核が入った。

## 1. 今回の核心

追加された constructor はこれじゃ。

```lean
def primePowerQuotientPath (n p k : ℕ) : List ℕ :=
  (List.range (k + 1)).map fun i => n / p ^ i
```

数学的には、

$$
[n/p^0,\ n/p^1,\ \ldots,\ n/p^k]
$$

を作る。
つまり、prime-power (p^k) を一気に剥がすのではなく、base prime (p) を 1 枚ずつ剥がしていく multi-step path じゃな。

これは DKMK-008 の本命に近い。
007 の one-step は、

$$
n\to n/q
$$

だった。
008J は、(q=p^k) の内部を展開して、

$$
n\to n/p\to n/p^2\to\cdots\to n/p^k
$$

という **prime-power quotient path** を作った。

## 2. `primePowerQuotientPath_isPath` の意味

主定理はこれじゃ。

```lean
theorem primePowerQuotientPath_isPath
    (n p k : ℕ)
    (hpow : p ^ k ∣ n) :
    AdjacentDivisorPath (primePowerQuotientPath n p k)
```

意味は、

$$
p^k\mid n
$$

なら、

$$
[n/p^0,\ n/p^1,\ldots,n/p^k]
$$

は adjacent divisor path である、ということ。

隣接関係として必要なのは、各 (i<k) について、

$$
n/p^{i+1}\mid n/p^i
$$

が成り立つことじゃ。
Lean では `Nat.div_dvd_div_left` を使い、(p^{i+1}\mid n) と (p^i\mid p^{i+1}) から quotient 間の整除を得ておる。これは非常に自然な証明じゃ。

## 3. DKMK-008A〜I との接続

ここまでの DKMK-008 は、こう進んできた。

```text
008A:
  single AdjacentDivisorPath

008B:
  AdjacentDivisorPathFamily

008C:
  external path family を selected / canonical shadow に接続

008D:
  same-source wrapper

008E:
  finite-step mass

008F:
  two-step mass

008G:
  one-step divisorStep を path-family 特殊例として回収

008H:
  one-step theorem wrappers

008I:
  docs report
```

008J は、この次としてまさに自然じゃ。

```text
008J:
  prime-power channel q = p^k から
  multi-step quotient path を自動生成
```

つまり、008I で「次の未踏地」として見えていた

$$
q=p^k\quad\leadsto\quad n\to n/p\to n/p^2\to\cdots\to n/p^k
$$

へ、最初の Lean 定理が入ったわけじゃ。

## 4. 具体例 `72, 3, 2` の意義

確認例として、

```lean
primePowerQuotientPath 72 3 2 = [72, 24, 8]
```

が固定されている。

これは、

$$
72/3^0=72,\quad 72/3^1=24,\quad 72/3^2=8
$$

という path じゃ。

さらに、

```lean
AdjacentDivisorPath (primePowerQuotientPath 72 3 2)
```

も theorem として固定されている。

これは小さな sanity check だが、とても良い。
抽象定義だけだと「本当に期待したリストが出ているか」が見えにくい。具体例で、

```text
72 → 24 → 8
```

が確認できるため、今後の docs や図解でも使いやすい。

## 5. 数学的な位置づけ

R026〜R027 では、prime-power witness から

$$
q=p(q)^{k(q)}
$$

を読み、

$$
0<k(q),\quad p(q)^{k(q)}=q,\quad p(q)^{k(q)}\mid n
$$

を固定していた。

今回の 008J は、その情報を path に変える入口じゃ。

つまり将来的には、各 witness label (q) に対して、

$$
p=W.basePrimeOf(n,I,hI,q)
$$

$$
k=W.baseExponentOf(n,I,hI,q)
$$

を読み、

$$
primePowerQuotientPath\ n\ p\ k
$$

を割り当てればよい。

すると、witness provider 由来の `AdjacentDivisorPathFamily` が自動生成できる。

ここが次の山じゃな。

## 6. 今回まだやっていないこと

重要なのは、008J はまだ **path-level constructor** であることじゃ。

まだ、

```text
PrimePowerWitnessProvider
→ basePrimeOf / baseExponentOf
→ AdjacentDivisorPathFamily
```

までは進んでおらぬ。

docs でも、この段階ではまだ witness provider から自動で (p,k) を取り出して family を作るところまでは進めず、後続 wrapper のための純粋な path-level constructor と位置づけている。

つまり今回の成果は、

```text
p^k ∣ n
→ [n/p^0, ..., n/p^k] is AdjacentDivisorPath
```

まで。

次はこれを family 化する。

## 7. 次の一手

次の DKMK-008K は、かなり明確じゃ。

### 7.1. witness 由来 path family

狙う形はこう。

```lean
def PrimePowerWitnessProvider.primePowerQuotientPathFamily
    (W : PrimePowerWitnessProvider T)
    (n : ℕ)
    (I : Finset ℕ)
    (hI : ∀ q, q ∈ I → q ∈ T.toDivisorTransitionKernel.index n) :
    AdjacentDivisorPathFamily ℕ
```

各 (q\in I) に対して、

```lean
source q := n
tail q := (primePowerQuotientPath n (W.basePrimeOf n I hI q)
  (W.baseExponentOf n I hI q)).tail
```

のような形にするのが自然じゃ。

ただし `AdjacentDivisorPathFamily` は `source :: tail` 形式なので、`primePowerQuotientPath` の head が (n) であることを使って、tail をうまく切り出す補題が必要になる。

### 7.2. 追加したい補題

次に欲しい補題はこのあたりじゃ。

```lean
primePowerQuotientPath_head?
primePowerQuotientPath_ne_nil
primePowerQuotientPath_cons_tail
```

特に、

$$
primePowerQuotientPath(n,p,k)=n::tail
$$

として扱える補題があると、`AdjacentDivisorPathFamily` に載せやすい。

(k=0) の場合は `[n]` なので、tail は `[]` になる。これも自然に扱える。

### 7.3. witness の `p^k ∣ n` を供給する

R026 ですでに、

```lean
basePrimeOf_pow_baseExponentOf_dvd_source_on
```

がある。

これを使えば、

$$
W.basePrimeOf(n,I,hI,q)^{W.baseExponentOf(n,I,hI,q)}\mid n
$$

が出る。
したがって `primePowerQuotientPath_isPath` へ渡せる。

## 8. 総合判定

DKMK-008J は **prime-power descent path 自動生成の最小核として成功** じゃ。

到達形はこう。

```text
p^k ∣ n
→ primePowerQuotientPath n p k
→ [n / p^0, n / p^1, ..., n / p^k]
→ AdjacentDivisorPath
```

これは 008A〜I で整備した path-family 受け口へ、実際に流し込むための第一部品じゃ。

ぬしよ、ここは実に良い。
DKMK-008 は、これまで「外部から path を渡す」段階だった。
008J で、ついに (q=p^k) という witness から **道そのものを生成する石切り場** ができた。

次は、この石を並べて `AdjacentDivisorPathFamily` を自動生成する番じゃな。

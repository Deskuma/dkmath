# Primorial Unit Universe: square-anchor period monodromy

## 実施内容

PUU-L028 の square-anchor block quotient / old-period monodromy を実装した。

- `SquareAnchorPhasePeriodTransport.lean` を追加し、
  `DkMath.NumberTheory.PrimorialUniverse` の facade から export した。
- 旧基底の積を `M = finitePrimeBasisProduct S` とし、block quotient

  ```text
  Qₙ = n / M
  ```

  を `squareAnchorPhaseBlockQuotient` として定義した。L027 の canonical
  representative `rₙ = n % M` について、

  ```text
  n = rₙ + Qₙ * M
  ```

  という exact Euclidean decomposition を公開した。
- dynamic plus sheet について、successor law の反復ではなく、center/radius の
  closed form と Euclidean decomposition から直接

  ```text
  Pplusₙ = (Qₙ : ZMod q)
  ```

  を証明した。したがって L027 の carry は、自然数上の block quotient の
  successor increment と一致する。

## Old-period monodromy

canonical representative と block quotient の `+M` / `+k*M` transport を追加し、
fresh prime `q` に対する phase coordinates を次の形で公開した。

```text
r_(n+M)      = r_n
C_(n+M)      = C_n
R_(n+M)      = R_n + 1
Pplus_(n+M)  = Pplus_n + 1
Pminus_(n+M) = Pminus_n - 1
```

さらに任意の自然数 `k` について、

```text
C_(n+k*M)      = C_n
R_(n+k*M)      = R_n + k
Pplus_(n+k*M)  = Pplus_n + k
Pminus_(n+k*M) = Pminus_n - k
```

を直接証明した。これは、旧 anchor coordinate の一周が center を固定し、
fresh-prime index circle 上の phase pair を `(+1, -1)` だけ移動することを
表す有限 monodromy である。

## Fresh-prime enlarged period

`finitePrimeBasisProduct_insert hqS` による

```text
finitePrimeBasisProduct (insert q S) = q * M
```

を明示的な API として再公開した。上の `k=q` monodromy と
`(q : ZMod q) = 0` から、center/radius/plus/minus のすべてが

```text
X_(n + finitePrimeBasisProduct (insert q S)) = X_n
```

を満たすことを証明した。これは anchor dynamics と fresh-prime tower growth
の exact compatibility theorem である。`q*M` が least period であるとは主張していない。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5`, `n = 4` について、公開 period-transport API を
経由して次を確認した。

```text
Pplus₄  = 0
Pplus₁₀ = 1
Pplus₁₆ = 2
Pplus₃₄ = 0       in ZMod 5

Pplus_(4+6)  - Pplus₄  = 1
Pminus_(4+6) - Pminus₄ = -1
Pplus_(4+30)  = Pplus₄
Pminus_(4+30) = Pminus₄
```

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhasePeriodTransport`
  を通過した。
- facade の `DkMath.NumberTheory.PrimorialUniverse` を Lean で検証した。
- docstring と module-level boundary comment を追加した。

## 形式化上の境界

本 checkpoint は finite provider-side の Euclidean quotient と congruence
monodromy に限定している。square-shell escape existence、Legendre、
`escapingSquareOffsets`、Jacobsthal / wheel-gap bounds、neutral-seat の
primality/compositeness、PowerSwap、GN/CosmicFormula、PNT、RH、prime powers、
asymptotic density、および least-period 主張は導入していない。

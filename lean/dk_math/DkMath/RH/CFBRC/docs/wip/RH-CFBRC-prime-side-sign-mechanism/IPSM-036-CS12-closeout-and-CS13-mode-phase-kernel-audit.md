# IPSM-036 — CS12 closeout and CS13 mode-phase-kernel audit

## 0. 判定

CS12 は Green-B とする。

実装済みの有限世界は次である。

- finite signed tail projection
- tail projection と cutoff/endpoint ordering の exact 同値
- finite PHZ block projection
- finite block projection の von Mangoldt-weighted mode-kernel 展開
- von Mangoldt coefficient の nonnegativity

一方、以下は未解決のまま保持する。

- CS12-E independent sign provider
- infinite tail / integral interchange
- fixed positive epsilon sign theorem
- finite-cutoff anchor
- RH conclusion

この分離は正しい。`Λ(n) ≥ 0` を mode kernel の符号証明として使用してはならない。

## 1. 既に固定された exact chain

CS11/CS12 により、有限 defect error は positive-convention finite prime tail の half-interval real projectionへ exact に落ちている。

$$D_{epsilon,W,X}-D_{epsilon,W,infty}=(2/pi) P_{epsilon,W,X}.$$

ここで `P` は `pascalCenteredXiPrimeSideFiniteTailProjection` である。

したがって `P >= 0` が与えるのは endpoint と approximant の順序だけであり、endpoint 自体の絶対符号ではない。

この firewall を今後も維持する。

## 2. CS13 の目的

CS13 では mode kernel の oscillatory phase を source-derived に露出する。

新 module を作る。

```text
DkMath.RH.CFBRC.PascalCenteredXiPrimeSideModeKernelPhaseAudit
```

import chain は次とする。

```lean
import DkMath.RH.CFBRC.PascalCenteredXiPrimeSideFiniteTailProjectionAudit
```

旧 module は原則変更しない。

## 3. CS13-A — centered right-edge coordinate

右辺点と centered node を明示する薄い adapter を置く。

記号上は

$$s_t=sigma+it,$$

$$z_t=s_t-1/2=a+it,$$

$$a=sigma-1/2.$$

Lean では既存の

- `pascalSymmetricRectangleRightEdge`
- `pascalOrdinaryToCentered`

を正本とし、新しい数学的定義を増やしすぎない。

必要なら `a` を named real offset として導入してよい。

## 4. CS13-B — quadratic Mellin box weight の boundary reduction

`tau = 0` weight は generic Mellin quadratic box weight と同じである。

centered box の logarithmic average を積分したままにせず、次の boundary form まで source-derived に畳めるか監査する。

概念式は

$$q_e(z)=(2e)^{-1} z\left(\exp(ez)-\exp(-ez)\right).$$

ここで `e` は Lean 上の `epsilon` であり、Euler 定数ではない。

重要なのは `z = 0` でも totalized division に依存せず成立する形を選ぶことである。

推奨 theorem surface:

```lean
 theorem mellinQuadraticBoxWeight_eq_boundaryDifference
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    mellinQuadraticBoxWeight ε z = ...
```

既存 theorem を利用できるなら adapter のみに留める。

## 5. CS13-C — one natural mode の centered phase transport

`n > 0` について、ordinary factor `n ^ (-s_t)` と centered node `z_t = s_t - 1/2` を同じ exponential phase に載せる。

目標概念形は

$$q_e(z_t)n^{-s_t}=\frac{n^{-1/2}}{2e}z_t\left(\exp((e-\log n)z_t)-\exp((-e-\log n)z_t)\right).$$

ここで `n^{-1/2}` の Lean 表現は、現在の Mathlib pin で最も安定する positive-real formを選ぶ。表記を先に固定して証明を歪めないこと。

`n = 0` は既存 totalization を維持する。`n = 1` は `vonMangoldt 1 = 0` なので、sign mechanism の source では寄与しないことを別 lemma で固定してよい。

## 6. CS13-D — real phase integrand

`a = sigma - 1/2`、実数 `r` に対して

$$\operatorname{Re}((a+it)e^{r(a+it)})=e^{ar}\left(a\cos(rt)-t\sin(rt)\right).$$

を Lean で固定する。

これにより one-mode integrand は二つの boundary frequencies

- `rPlus = epsilon - log n`
- `rMinus = -epsilon - log n`

の差になる。

この段階で `Complex.arg` は不要である。既存 project 方針どおり、実部・指数・sin/cos の exact algebra で処理する。

## 7. CS13-E — half-window phase kernel

まず安全な積分形を named object とすることを推奨する。

```lean
noncomputable def pascalCenteredXiPrimeSidePhasePrimitive
    (a r T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T,
    Real.exp (a * r) * (a * Real.cos (r * t) - t * Real.sin (r * t))
```

その後、`r != 0` のときのみ閉形式を証明する。

概念形は

$$J(a,r,T)=e^{ar}\left(\frac{T\cos(rT)}{r}+\frac{(ar-1)\sin(rT)}{r^2}\right).$$

`r = 0` では積分定義を正本として扱い、必要なら `J(a,0,T)=aT` を別 theorem にする。

これにより `n > 0` の mode kernel を

$$K_{e,W}(n)=\frac{n^{-1/2}}{2e}\left(J(a,e-\log n,T)-J(a,-e-\log n,T)\right)$$

の形へ exact に落とせるか監査する。

## 8. CS13-F — sign firewall

この closed form が得られても、個別 mode kernel の universal sign を仮定してはならない。

`cos` / `sin` と `T log n` が明示的に残るなら、これは signed oscillatory object である。

次の誤推論は禁止する。

```text
vonMangoldt n >= 0
therefore mode contribution >= 0
```

また、finite block projection の符号が得られても、それだけで endpoint の absolute sign は出ない。

必要なのは引き続き

```text
signed convergence direction
+
independent finite-cutoff anchor
```

の二要素である。

## 9. CS13-G — prime-power canonical fold への handoff

個別 natural mode の sign が oscillatory で閉じない場合、次の grouping は隣接整数ではなく base-prime ray を優先する。

既存 module `PascalPrimePowerCanonicalFold` は、positive prime-power label `q = p^k` の base prime と exponent の一意性、および canonical finite support を既に提供している。

さらに von Mangoldt bridge では

$$Lambda(p^k)=\log p$$

という共通 coefficient が得られる。

したがって次 phase の候補は

```text
q-indexed mode kernels
→ canonical prime-power support
→ fixed base prime p ごとの p^k ray
→ common log p factor
→ finite geometric / phase block cancellation audit
```

とする。

これは DkMath の prime-power source structure を保った grouping であり、人工的な adjacent-integer pairing より優先度が高い。

## 10. CS13 closeout conditions

### Green

以下が source-derived に閉じる。

1. quadratic Mellin box weight の boundary reduction
2. positive natural mode の centered phase transport
3. real phase integrand identity
4. finite half-window mode kernel の exact phase representation
5. sign firewall の維持

### Green-B

1–4 の一部だけ閉じ、個別 mode sign は未確立であることを named gap として残す。

### Red

次のいずれかを導入した場合。

- zero-side defect / horizontal energy から mode sign を逆輸入
- RH-equivalent theorem を provider として使用
- infinite tail と interval integral の未証明交換
- `Lambda(n) >= 0` だけから mode sign を主張
- fixed-epsilon sign を source theorem なしに仮定

## 11. 次 CP

CS13 の phase kernel が Green なら、次は canonical prime-power ray audit へ進む。

候補 module:

```text
PascalCenteredXiPrimeSidePrimePowerRayCancellationAudit.lean
```

そこで初めて `p^k` grouping が signed block cancellation を与えるかを監査する。

それでも sign が得られなければ、named obstruction として固定し、finite-cutoff anchor route と分離して扱う。

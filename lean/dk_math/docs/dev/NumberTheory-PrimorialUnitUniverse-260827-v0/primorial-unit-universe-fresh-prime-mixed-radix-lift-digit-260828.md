# Primorial Unit Universe: fresh-prime mixed-radix lift digit

## 実施内容

PUU-L029 の fresh-prime mixed-radix static/dynamic compatibility を実装した。

- `SquareAnchorPhaseMixedRadixTransport.lean` を追加し、facade から export した。
- fresh prime `q` に対する block digit を

  ```text
  digit_q(n) = (n / M) % q
  ```

  として `squareAnchorFreshPrimeBlockDigit` に定義した。`q` が素数なら
  `digit_q(n) < q` を証明した。
- 旧 block quotient の exact decomposition

  ```text
  Q_S(n) = digit_q(n) + q * Q_(insert q S)(n)
  ```

  と、anchor の full mixed-radix decomposition

  ```text
  n = r_S(n) + digit_q(n) * M
        + Q_(insert q S)(n) * (q * M)
  ```

  を Euclidean division から直接証明した。successor induction は使用していない。

## Static / dynamic compatibility

次の公開定理を追加した。

- `squareAnchorPhaseRepresentative_insert_eq_old_lift_digit`

  ```text
  r_(insert q S)(n)
    = primeBasisWheelLift S (r_S(n)) (digit_q(n))
  ```

- `squareAnchorPhaseRepresentative_insert_projects_old`

  enlarged canonical representative の old projection が `r_S(n)` に戻ること。
- `squareAnchorFreshPrimePlus_eq_blockDigit`

  ```text
  Pplus_S,q(n) = (digit_q(n) : ZMod q)
  ```

- `squareAnchorFreshPrimeBlockDigit_is_plusLiftIndex`

  digit が実際の `+n` raw fresh-prime lift index であること。
- `squareAnchorPhaseRepresentative_insert_mem_projectionFiber`

  enlarged canonical representative が
  `squareAnchorPhaseProjectionFiber S q n (r_S(n))` に属すること。

raw-lift witness と projection-fiber membership の主定理は、anchor `n` の
coprimalityを仮定していない。したがって `q ∣ n` の場合も digit/raw-lift の
degeneracyを保ったまま成立する。coprime anchor 上の distinct survivor や
unique-deletion との追加 bridge は本 checkpointには含めていない。

## Digit monodromy

L028 の quotient transport から、次を追加した。

```text
digit_q(n + M)   = (digit_q(n) + 1) % q
digit_q(n + k*M) = (digit_q(n) + k) % q
digit_q(n + q*M) = digit_q(n)
```

したがって `q` 回の old-period turn が、固定 old representative 上の `q` 個の
raw lift digit を巡回して enlarged period で閉じる。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5` について、公開 L029 API を経由して

```text
n       = 4, 10, 16, 22, 28, 34
digit   = 0,  1,  2,  3,  4,  0       modulo 5
r_(insert 5 S)(n)
        = 4, 10, 16, 22, 28,  4       modulo 30
```

を `squareAnchorFreshPrimeMixedRadix_two_three_six_to_thirty_regression` として
確認した。最初の五つは old representative `4` の五つの raw lift index に対応し、
六つ目で enlarged period `30` に戻る。

## 検証結果

- 対象モジュールの `lake build` を通過した。
- facade の Lean 検証を通過した。
- `./lb` による全体 build を通過した。
- `sorry` 宣言を除く `warning:` の追加監査を通過した。
- 禁止依存監査と `git diff --check` を通過した。

## 形式化上の境界

本 checkpoint は、old wheel projection、fresh-prime raw-lift index、block
quotient digit、dynamic plus sheet、enlarged canonical representative の
有限な座標同一視を完了するものである。これは既知の有限 wheel の完全な座標
記述であり、独立な reservation obstruction を与えるとは解釈していない。

square-shell escape existence、Legendre、`escapingSquareOffsets`、Jacobsthal /
wheel-gap、neutral-seat の primality/compositeness、PNT、RH、PowerSwap、GN、
CosmicFormula、prime powers、asymptotic density、arbitrary consumer counting は
導入していない。

# PRIM-L059 — Depth-Collision / Fourth-Branch Four-Direction Gate

## Outcome

Outcome A+ を実装した。L058 の local residual-pair capacity を再帰分解せず、
collision seat の四方向 support と L055 の canonical fourth direction を
共通の first-prime fourth-power gate へ接続した。

## Implemented surface

主 module は
`DkMath.NumberTheory.Legendre.ParitySafeFourDirectionGate`。

- `three_mul_depthFiberCollisionSeats_card_le_supportExcess` を追加した。
  これは collision seat count の三方向 support cost だけを charge し、
  `DepthFiberExcess` 全体の bound ではない。
- `paritySafeFourDirectionGatePrimes` と membership theorem を定義した。
- `FourDirectionGatePrimes ⊆ TripleGatePrimes` と card refinement を証明した。
- depth collision から `p,q,s,u` の active support、相異性、
  `p*q*s*u ∣ n^2+r` を公開した。
- depth collision の canonical prime について
  `p^4 < squareBody n` を閉じ、FourDirectionGate membership を証明した。
- L055 `ExactFourthPrime` packet から、ExactFourth witness の first prime
  について同じ gate membership を証明した。

## Arithmetic regressions

- `n = 16` では `5 ∈ TripleGatePrimes 16` だが
  `5 ∉ FourDirectionGatePrimes 16`。`5^3 = 125 < 288` と
  `5^4 = 625 > 288` により strict refinement を固定した。
- L057/L058 の `n = 58`, `r = 101` actual collision が
  `FourDirectionGatePrimes 58` に入ることを確認した。

## Proof boundary / non-goals

同じ canonical prime が複数 seat を所有し得るため、gate membership から
collision seat 数や ExactFourth pair 数の injective cardinal bound は主張しない。
fourth direction の global injection、generic hypergraph、PNT/sieve、
near/terminal の新 counting、fifth direction、descent、global contradiction、
Legendre conjecture、RH は扱わない。

## Validation

以下を実行して成功した。

- `lake env lean DkMath/NumberTheory/Legendre/ParitySafeFourDirectionGate.lean`
- `git diff --check`
- facade を含む `lake build DkMath.NumberTheory.Legendre`

新規変更 source の `sorry`、`admit`、`axiom`、`native_decide` を監査し、該当なし。
build 起動時の `/opt/wonderful/bin/wf-env: Permission denied` は既存環境ノイズで、
Lean の終了ステータスは成功している。

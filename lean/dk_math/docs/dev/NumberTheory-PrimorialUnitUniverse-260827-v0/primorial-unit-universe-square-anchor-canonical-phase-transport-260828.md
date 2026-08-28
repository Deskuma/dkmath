# Primorial Unit Universe: square-anchor canonical phase transport

## 実施内容

PUU-L027 の square-anchor successor transport / successor carry law を実装した。

- `SquareAnchorPhaseSuccessorTransport.lean` を追加し、facade から export した。
- moving square anchor `n` の canonical phase representative を

  ```text
  rₙ = n mod M,
  ```

  として `squareAnchorPhaseRepresentative` に定義した。`rₙ` が
  `squareAnchorPhaseFiber S n` に属することを証明した。
- PUU-L010 の square-value coordinate との区別を保ち、

  ```text
  squareAnchorWheelProjection S n = rₙ² mod M
  ```

  を `squareAnchorWheelProjection_eq_representative_square` として公開した。
  これにより、anchor coordinate は `n mod M`、square-value coordinate は
  `n² mod M` と明示的に分離されている。
- canonical representative の successor law

  ```text
  rₙ₊₁ = (rₙ + 1) mod M
  ```

  と、

  ```text
  rₙ + 1 = rₙ₊₁ + carryₙ * M
  ```

  の exact decomposition を証明した。
- `squareAnchorPhaseStepCarry` を定義し、carry が `0` または `1` であること、
  `carry = 1` が wrap branch、`carry = 0` が non-wrap branch と同値であることを
  証明した。
- moving center / radius と dynamic phase sheets を定義した。

  ```text
  Cₙ = -rₙ / M,
  Rₙ =  n / M,
  Pplusₙ  = Cₙ + Rₙ,
  Pminusₙ = Cₙ - Rₙ.
  ```

- L025/L026 の API から、radius successor law

  ```text
  Rₙ₊₁ - Rₙ = M⁻¹
  ```

  と、中心の central transport law

  ```text
  Cₙ₊₁ - Cₙ = carryₙ - M⁻¹
  ```

  を導出した。
- dynamic phase sheets の successor law を証明した。

  ```text
  Pplusₙ₊₁  - Pplusₙ  = carryₙ
  Pminusₙ₊₁ - Pminusₙ = carryₙ - 2 * M⁻¹.
  ```

- canonical representative 上の actual deleted/plus/minus lift witnesses と、
  dynamic center/radius coordinates の一致を公開 wrapper theorem として追加した。

## L026 からの強化と Phase E2

L026 は arbitrary old representatives `b` の間で phase geometry を transport した。
L027 はこれを実際の moving square anchor `n -> n+1` に特殊化した。anchor coordinate
の motion は `+1 mod M` であり、PUU-L010 の square-value motion は別途
`+(2*n+1) mod M` である。carry は canonical representative の old-period wrap
だけを表す。

したがって center は `carry - M⁻¹` だけ移動し、radius は常に `+M⁻¹` だけ進む。
この差から plus sheet は carry の時だけ移動し、minus sheet は同じ carry に加えて
一定の `-2*M⁻¹` drift を持つ。

これは revised roadmap Phase E2 の dynamic transport checkpoint である。

## 回帰例

`S = {2,3}`, `M = 6`, `q = 5` について、

```text
n = 4 : rₙ = 4, carryₙ = 0
n = 5 : rₙ = 5, carryₙ = 1
n = 6 : rₙ = 0.
```

公開 L027 API により、non-wrap / wrap の両方を含めて

```text
4 -> 5 : C₅ - C₄ = -M⁻¹
5 -> 6 : C₆ - C₅ = 1 - M⁻¹

Pplus₅  - Pplus₄  = 0
Pplus₆  - Pplus₅  = 1

Pminus₅ - Pminus₄ = -2*M⁻¹
Pminus₆ - Pminus₅ = 1 - 2*M⁻¹
```

を確認した。

## 検証結果

- `lake build DkMath.NumberTheory.PrimorialUniverse.SquareAnchorPhaseSuccessorTransport`
  を通過した。
- `lake build DkMath.NumberTheory.PrimorialUniverse` を通過した。
- `./lb` による検証を通過した。
- 最終 build log について、`sorry` 起因の warning を除く `warning:` の追加監査を
  実施した。
- 禁止依存監査と `git diff --check` を通過した。

## 形式化上の境界

本 checkpoint は finite provider-side dynamic congruence transport に限定している。
Legendre、`SquareCell`、`escapingSquareOffsets`、square-shell escape existence、
Jacobsthal / wheel gap、neutral-seat primality / compositeness、PowerSwap、
GN/CosmicFormula、PNT、RH、prime powers、asymptotic density、transport law からの
square-shell reservation obstruction は導入していない。


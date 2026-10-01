# FLT7TC-005R51 — Simplest-cubic class-zero certificate audit

## 調査開始時点

`instruction-057.md` を読み、R50 の source-plane landing を起点に、次の範囲を
kernel-checkable な neutral arithmetic として調査している。

- norm-minus-seven binary cubic と discriminant `49`
- mod-seven degeneration と `7`-adic divisibility
- explicit Hessian/Jacobian covariants
- positive-definite Eisenstein shadow
- current `Y = P.t^(7^9)` に対する forward theta depth

外部文献の三解分類は target calibration の照合にのみ使い、Lean の証明や公理には
取り込まない。有限探索、外部 Thue/Mordell solver、fundamental-unit basis、
`C = 1` exclusion は kernel-check された証明が得られるまで production endpoint
にしない。

## 既存 API の確認

R50 production の `norm_linearSource` は既に

`norm (linearSource a b) = a^3 + 2*a^2*b - a*b^2 - b^3`

を提供している。`SevenRealCubicThetaSeventhPower.lean` は exact seventh-power
theta-coordinate formula を、`SevenRealCubicThetaSeventhPowerDepth.lean` は
`ThetaNilpotentDepth` と reverse depth-drop API を提供している。forward depth は
既存 API としては見つからず、個別に検証する。

## 実装進行

neutral certificate module と API を実装し、各 Lean build は単体で実行する。

## R51 実装結果

### A--D: simplest-cubic certificate

新規 production module
`DkMath/FLT/Seven/SevenRealCubicSimplestCubicCertificate.lean` を追加した。

- `sourcePlaneNormSevenForm` と `norm_linearSource` の一致を実装した。
- 明示的な binary-cubic discriminant formula を `49` に kernel-check した。
- `(a + 3*b)^3 - 7*b*(a + 2*b)^2` の factor identity と、`F = -7` から
  `7 ∣ a + 3*b`、`a = 7*c - 3*b`、reduced form `= 1` を実装した。
- `Q = a^2 + a*b + b^2`、`P = a^3 - 12*a^2*b - 15*a*b^2 - b^3` の
  covariant identity、normalized Hessian `= 7*Q`、`7 ∣ Q`、`7 ∣ P`、および
  `k^2 + 27 = 196*q^3` を実装した。
- `Q(7*c - 3*b,b) = 7*(b^2 - 5*b*c + 7*c^2)` と、対応する
  Eisenstein shadow identity を実装した。

### E: current correction depth and coordinates

- seventh-power coordinate formulasから、
  `ThetaNilpotentDepth n x` なら `ThetaNilpotentDepth (n+1) (x^7)` を得る
  forward theorem を追加した。linear/square quotient の各項の divisibility と、
  7-modulo factor nondivisibility を使用している。
- unit `u` について `ThetaNilpotentDepth n (u^(7^n))` を自然数帰納法で実装した。
- R50 の `P.t^(7^9)` に `n=9` を instantiate する theorem を追加した。
- correction line `3*L = 14*S` を整数の `L = 14*m`, `S = 3*m` に変換し、
  `7^9 ∣ m` を kernel-check した。
- `x = sourcePlaneNormSevenAxis * Y` の theta 座標から
  `a = 2*A - 21*m`, `b = -3*A + 28*m` を実装し、逆変換
  `A = -4*a - 3*b`, `7*m = -(3*a + 2*b)` を実装した。
- current packet について `7^10 ∣ 3*a + 2*b` を得る theorem を追加した。
- 新規 module は `DkMath.FLT.Seven` facade から export した。

### F--H boundary audit

既存の neutral certificate と current high-depth coordinate bridge は kernel-checkable
な範囲で production 化した。norm-one の theta-constant cube congruenceについては、
既存 API に対応する専用 theorem がなく、今回の証明範囲には追加していない。
Eisenstein infrastructure は既存の PID/unit API と照合したが、そこからこの reduced
equation の有限 cubic coefficient list、Hensel branch の一意性、または `C = 1`
除外を導く theorem は得られていない。したがって外部分類・有限探索・Thue/Mordell
solver・外部定理 axiom は production に取り込んでいない。

## 単体ビルド検証

以下を順次実行し、最終実行は成功した。

```text
lake build DkMath.FLT.Seven.SevenRealCubicSimplestCubicCertificate
```

最終結果: `Built DkMath.FLT.Seven.SevenRealCubicSimplestCubicCertificate`
（9180 jobs）。

facade についても次を単体実行し、成功した。

```text
lake build DkMath.FLT.Seven
```

最終結果: `Built DkMath.FLT.Seven`（9227 jobs）。新規 production module の
`sorry`/`admit`/`unsafe` scan は該当なしだった。

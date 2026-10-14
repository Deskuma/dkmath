# FLT7TC-005R52 — Eisenstein cube-extraction certificate

## 調査開始時点

`instruction-058.md` と R51 の `report-057.md`、
`SevenRealCubicSimplestCubicCertificate.lean` を読み、current C=1 branch の
Mordell certificate を既存 FLT3 Eisenstein API に接続する範囲を調査する。

今回の production 境界は次の通りとする。

- binary-cubic/Mordell の generic solver は追加しない。
- 外部分類、有限探索による unbounded completeness、FLT3 terminal theorem は
  production に取り込まない。
- `q = 1` または `C = 1` exclusion は kernel-check された証明が得られた場合だけ
 追加する。
- 調査結果と実験検証はこの report に逐次追記する。

## 既存 API 確認

`DkMath.FLT.Three.EisensteinSubstrate` は `eisensteinCoord`、
`eisenstein_norm_coords`、`eisenstein_cube_coords`、共役と積の norm 公式を提供する。
`EisensteinConjugateCoprime` は `EisensteinRelPrime` と norm による共役相対素性の
既存証明を提供し、`EisensteinCubeExtraction` は coprime product の cube 抽出を
unit 付きで提供する。`EisensteinUnitSectors` は sector representatives
`1`, `tau`, `tau^2` と unit-sector normalization を提供する。

R51 からは current correction の `A,m`、`7^9 ∣ m`、および
`7^10 ∣ (3*a+2*b)` を再利用する。

## 実装進行

R52 の neutral current certificate module を追加し、各 Lean build は単体で実行する。

## 実装結果

新規 production module
`DkMath/FLT/Seven/SevenRealCubicEisensteinCubeCertificate.lean` を追加し、公開
facade `DkMath/FLT/Seven.lean` から import した。

### A–B: current parameter と高深度の向き

- `sourcePlaneNormSevenQParameter` と
  `sourcePlaneNormSevenKParameter` を明示多項式
  `A^2 - 19*A*m + 91*m^2`、
  `-13*A^3 + 357*A^2*m - 3234*A*m^2 + 9653*m^3` として追加した。
- R51 の `a = 2*A - 21*m`, `b = -3*A + 28*m` に対する Q/K の厳密な
  係数等式を kernel-check した。
- Q の非負性と、source-plane norm `-7` からの Q の正性を証明した。
- current Mordell 等式
  `k^2 + 27 = 196*q^3` を証明した。
- correction-line norm-one 多項式と `7^9 ∣ m` から
  `7^10 ∣ A^3 - 1`、さらに `7^10 ∣ k + 13` を証明した。
  ここでは congruence を整数等式へ昇格していない。

### C–D: Eisenstein element と `pi7^2` stripping

- Mordell 等式から K の奇性、`k = 2*h + 3` の witness、
  `z = eisensteinCoord h 3` および `norm z = 49*q^3` を追加した。
- `7^10 ∣ k + 13` と `k = 2*h + 3` から `7^10 ∣ h + 8` を明示 theorem として
  証明した。
- `pi7 = eisensteinCoord 2 1`、`norm pi7 = 7`、
  `pi7^2 = eisensteinCoord 3 5` を証明した。
- `49*r = 8*h + 15`、`49*s = -5*h + 9` を用いる明示的な
  `h = 3*r - 5*s`, `3 = 5*r + 8*s` の square-stripping witness と、
  `z = pi7^2 * eisensteinCoord r s` の厳密等式を追加した。
- `norm (eisensteinCoord r s) = q^3` を `z = pi7^2 * delta` と
  `norm pi7 = 7` から証明した。
- `7^10 ∣ h + 8` から明示 witness により `7^8 ∣ r + 1`,
  `7^8 ∣ s - 1` を証明した。

### G–H: neutral cube extraction と sector equations

- norm-cube から
  `delta * conj delta = (eisensteinCoord q 0)^3` を証明した。
- 既存の `EisensteinCubeExtraction` の coprime-product API に接続し、
  unit 付き cube extraction と `EisensteinUnitSector` による
  `one/tau/tauSq` normalization を追加した。
- `gamma0 = eisensteinCoord R S` の cube coordinates を展開し、
  second-coordinate の sector ごとの正確な式を kernel-check した。得られた
  linear forms は順に `5*X + 8*Y`, `8*X + 3*Y`, `3*X - 5*Y` である。

## 検証結果と境界

単体ビルド

```text
lake build DkMath.FLT.Seven.SevenRealCubicEisensteinCubeCertificate
```

は `Build completed successfully (9207 jobs)` となった。公開 facade

```text
lake build DkMath.FLT.Seven
```

も `Build completed successfully (9254 jobs)` となった。

今回の module では、現 current packet から `3 ∤ q`、delta と共役の相対素性、
`q = 1`、sector elimination、有限 shell の classification、`C = 1` contradiction
までは追加していない。cube extraction theorem は neutral な
`EisensteinRelPrime delta (conj delta)` を仮定しており、ここが current-specific
証明を接続する残りの境界である。したがって R52 の到達点は **Outcome C**：
exact `pi7^2` stripping と、相対素性を前提にした cube extraction/sector
normalization が kernel-check 済みである。

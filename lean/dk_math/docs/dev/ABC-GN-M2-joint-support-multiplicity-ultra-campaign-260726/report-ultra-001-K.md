# Ultra-001K Report — finite Hensel uniqueness

Date: 2026-07-26  
Status: **finite Hensel uniqueness / non-exceptional deep-lift count complete**

## NOTE 001-J から得た前進

`NOTE-ultra-001-J.md` の one-shot Taylor 方針を採用した。ただし、NOTE が
候補に挙げた:

```lean
Polynomial.exists_mul_sq_add_linear_part_eq_eval_add
```

は、この checkout の Mathlib revision には存在しない。そこで利用可能な
`Polynomial.taylor`、`Polynomial.X_pow_dvd_iff`、`Polynomial.taylor_eval`
から、一次 Taylor 展開と二次剰余項を直接証明した。

```lean
exists_eval_add_eq_eval_add_derivative_mul_add_sq
```

これは任意の可換環上で:

```text
P(x+y) = P(x) + P'(x)y + c y²
```

を与える。

## Finite prime-power cancellation

`ZMod (q^k)` の元を `ZMod q` へ落とし、その像が非零なら元が unit である
ことを:

```lean
isUnit_zmod_primePow_of_castHom_ne_zero
```

として証明した。これにより整数減算へ移動せず、有限環の中で Taylor の
第二因子を消去できる。

係数環の reduction には:

```lean
map_GNPolynomial
```

を追加し、GN 多項式とその導関数の評価が `ZMod (q^k) -> ZMod q` と可換で
あることを固定した。

## Finite Hensel uniqueness

主要 theorem:

```lean
GNDeepLiftCongruenceUnique_of_simpleRoot
```

は、`p`, `q` が素数、`q ∤ p`、`q ∤ b`、`0 < k` のもとで:

```text
q^k ∣ GN p a b
q^k ∣ GN p r b
a ≡ r [MOD q]
--------------------------------
a ≡ r [MOD q^k]
```

を証明する。

証明は `d = a-r` を `ZMod (q^k)` で置き、Taylor 展開から:

```text
d * (P'(r) + c*d) = 0
```

を得る。第二因子の mod-`q` 像は `P'(r)` であり、既存の
`eval_derivative_GNPolynomial_ne_zero` により非零、従って unit である。
よって `d = 0` が従う。

## API equivalence と counting endpoint

canonical residue 上の injectivity から任意の自然数 root の一意性へ戻す:

```lean
GNDeepLiftCongruenceUnique_of_reductionInjective
GNDeepLiftReductionInjective_iff_congruenceUnique
```

も証明した。これにより二つの frontier 表現は同値になった。

さらに:

```lean
GNDeepLiftReductionInjective_of_simpleRoot
GNDeepLiftResidues_card_le_of_simpleRoot
card_gn_deep_lift_residue_classes_le_of_simpleRoot
```

まで接続し、非例外チャネルで:

```text
card (GNDeepLiftResidues p q b k) ≤ p - 1

#{a ∈ [0,X] | q^k ∣ GN p a b}
  ≤ (p - 1) * ((X + 1) / q^k + 1)
```

を追加仮定なしで得た。

## Boundary

finite Hensel uniqueness と単一素数・単一深さの区間 counting は閉じた。
しかし、この結論は density/counting estimate であり、全ての ABC triple
に対する pointwise:

```lean
ABCGNOddPrimeJointContract ε
```

を与えない。density から uniform joint pressure へ移る deterministic
補償原理は引き続き open である。`abc_main_axiom` は変更していない。

## Verification

```text
lake build DkMath.ABC.GNLegacyTailCountingBridge
Build completed successfully (8361 jobs).

lake build DkMath.ABC
Build completed successfully (8381 jobs).

lake build DkMath
Build completed successfully (8751 jobs).
```

主要 endpoints の axiom audit:

```text
propext
Classical.choice
Quot.sound
```

のみ。変更した production source に新規 `sorry`、`axiom`、
`native_decide` は使用していない。`git diff --check` は clean。

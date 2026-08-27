# Ultra-001J Report — canonical GN residues と mod-q 根数

Date: 2026-07-26  
Status: **canonical cover / mod-q root bound complete; Hensel uniqueness open**

## Review memo から得た前進

`MEMO-ultra-001-I.md` の提案に従い、抽象 cover の arithmetic 側を
canonical residue set と二段階の cardinality 問題へ分解した。

Production module:

```text
DkMath.ABC.GNLegacyTailCountingBridge
```

## Canonical residue cover

追加した canonical set は:

```lean
GNDeepLiftResidues p q b k
```

であり、exact membership は:

```text
r < q^k ∧ q^k ∣ GN p r b
```

となる。`GN_modEq_left` により GN が左座標の congruence を保存することを
証明し、任意の深い root を `a % q^k` に落として:

```lean
GNDeepLiftResidues_cover
```

を無条件に構成した。従って cover の存在自体は frontier から消えた。

## Mod-q root count

GN を左座標の多項式として:

```lean
GNPolynomial p b R
```

に package した。Lean で:

```lean
eval_GNPolynomial
GNPolynomial_monic
GNPolynomial_natDegree_le
```

を証明し、`p > 0` なら monic、次数は `p - 1` 以下であることを固定した。

canonical mod-`q` residues を `ZMod q` に inject し、多項式の root-cardinality
bound を直接適用して:

```lean
GNDeepLiftResidues_card_base_le
```

すなわち:

```text
card (GNDeepLiftResidues p q b 1) ≤ p - 1
```

を `p`, `q` が prime という仮定だけで証明した。memo の affine
root-of-unity 変換で要求されていた `q ∤ p`, `q ∤ b` は、この base-cardinality
証明には不要だった。

## Simple-root derivative

多項式版 cosmic identity を微分し:

```lean
GNPolynomial_eq_GN
eval_derivative_GNPolynomial_ne_zero
```

を証明した。`q ∤ p` と `q ∤ b` のもとで、`ZMod q` 上の GN root `r` は:

```text
GNPolynomial(r) = 0
  -> GNPolynomial'(r) ≠ 0
```

を満たす。従って memo が要求した Hensel simple-root 条件までは production
Lean で concrete に閉じた。

## Exact remaining Hensel frontier

深さ `k` から mod `q` への reduction:

```lean
GNDeepLiftReductionInjective p q b k
```

と、同値な pointwise arithmetic obligation:

```lean
GNDeepLiftCongruenceUnique p q b k
```

を公開した。後者は exact に:

```text
q^k ∣ GN p a b
q^k ∣ GN p r b
a ≡ r [MOD q]
--------------------------------
a ≡ r [MOD q^k]
```

を表す。

この一意性が与えられれば:

```lean
GNDeepLiftResidues_card_le_of_reduction
card_gn_deep_lift_residue_classes_le_of_reduction
card_gn_deep_lift_residue_classes_le_of_congruenceUnique
```

により直ちに:

```text
#{a ∈ [0,X] | q^k ∣ GN p a b}
  ≤ (p - 1) * ((X + 1) / q^k + 1)
```

まで到達する。従って finite counting lane の唯一の未証明 arithmetic input は、
上記 simple-root 条件から一般 `k` の congruence uniqueness を反復構成する
Hensel lemma になった。

## Boundary

今回閉じたのは canonical cover、mod-`q` root bound、simple-root derivative
である。

```text
GNDeepLiftCongruenceUnique p q b k
```

の一般 `k` に対する concrete proof は未完成であり、さらに residue density
estimate だけから pointwise `ABCGNOddPrimeJointContract` は従わない。
`abc_main_axiom` は変更していない。

## Verification

```text
lake build DkMath.ABC.GNLegacyTailCountingBridge
Build completed successfully (8361 jobs).

lake build DkMath.ABC
Build completed successfully (8381 jobs).

lake build DkMath
Build completed successfully (8751 jobs).
```

代表 endpoints の axiom audit:

```text
propext
Classical.choice
Quot.sound
```

のみ。新規 `sorry`、`axiom`、`native_decide` は使用していない。

# M1-002 Report: 指数 5 の例外 valuation-one kernel

Date: 2026-07-26  
Outcome: **完了 — coprime 境界上で `5 ∣ GN 5 a b` なら 5 進付値はちょうど 1**

## 1. 実装ファイル

新規モジュール:

```text
DkMath/ABC/GNOddPrimeExceptionalExcess.lean
```

追加 import は次の 1 本だけである。

```lean
import DkMath.ABC.GNValuationExcess
```

`DkMath.FLT.Five.*` は import していない。集約モジュールも変更していない。

## 2. 公開 theorem surface

実装した定理は次のとおり。

```lean
DkMath.ABC.GN_five_eq_explicit
DkMath.ABC.GN_five_eq_boundary_add_five_mul
DkMath.ABC.five_dvd_boundary_of_dvd_GN_five
DkMath.ABC.GN_five_five_mul_eq_twentyFive_mul_add
DkMath.ABC.not_twentyFive_dvd_GN_five_of_coprime
DkMath.ABC.padicValNat_five_GN_five_eq_one_of_dvd
DkMath.ABC.factorization_five_GN_five_eq_one_of_dvd
```

主結果は次の自然な最小仮定で公開した。

```lean
theorem padicValNat_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    padicValNat 5 (GN 5 a b) = 1
```

factorization wrapper も追加した。

```lean
theorem factorization_five_GN_five_eq_one_of_dvd
    {a b : ℕ}
    (hcop : Nat.Coprime a b)
    (h5GN : 5 ∣ GN 5 a b) :
    (GN 5 a b).factorization 5 = 1
```

## 3. 採用した証明経路

`GN_eq_sum` を指数 5 で有限展開し、`norm_num` と `ring` で canonical
`GN` から直接次を得た。

$$
GN_5(a,b)=a^4+5a^3b+10a^2b^2+10ab^3+5b^4.
$$

これを

$$
GN_5(a,b)=a^4+5K
$$

と再配置した。したがって `5 ∣ GN₅(a,b)` なら `5 ∣ a⁴` であり、
`Nat.Prime.dvd_of_dvd_pow` により `5 ∣ a` を得る。

次に `a = 5k` を代入し、

$$
GN_5(5k,b)=25L+5b^4
$$

という明示的 witness 分解を `ring` で証明した。仮に `25 ∣ GN₅(5k,b)`
なら `omega` により `5 ∣ b⁴`、従って `5 ∣ b` となる。しかし
`Coprime (5k) b` から `Coprime 5 b` が従うため矛盾する。

最後に既存 API

```lean
padicValNat_one_le_of_prime_dvd
padicValNat_le_iff_dvd
```

を用いて

```text
1 ≤ padicValNat 5 (GN 5 a b)
padicValNat 5 (GN 5 a b) < 2
```

を結合し、正確な付値 1 を得た。

## 4. `hGN0` の扱い

`hGN0 : GN 5 a b ≠ 0` は公開定理の仮定として不要だった。

`GN 5 a b = 0` なら自動的に `25 ∣ GN 5 a b` であり、先に証明した
no-square-lift と矛盾する。したがって非零性は theorem 内で導出している。

## 5. 検証

実行:

```text
lake build DkMath.ABC.GNOddPrimeExceptionalExcess
```

結果:

```text
Build completed successfully (8321 jobs).
```

一時監査モジュールから全 7 定理に `#print axioms` を実行した。依存は
Lean / Mathlib の標準的な

```text
propext
Classical.choice
Quot.sound
```

のみであり、独自 axiom はない。実装には `sorry`、`axiom`、
`native_decide` を追加していない。

## 6. M1-003 に残る課題

局所因子 `q = 5` の valuation-one / factorization-one は閉じた。
M1-003 の残作業は、指数 5 の例外 support にある素数について

```text
q ∣ 5 かつ q.Prime から q = 5
```

を示し、各 summand の

```text
(factorization q - 1 : ℕ)
```

を 0 に簡約して

```lean
GNExceptionalValuationExcess 5 a b = 0
```

を有限和レベルで閉じることだけである。この checkpoint では指示どおり
filtered-sum theorem には進んでいない。


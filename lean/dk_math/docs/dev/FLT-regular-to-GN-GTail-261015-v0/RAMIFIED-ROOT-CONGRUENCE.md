# 復元された整数根 t の剰余類は 1

## 定理

`DkMath.NumberTheory.GNRamifiedRoot` に、次を実装した。

```lean
theorem ramified_integral_root_modEq_one
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {x u t : ℤ}
    (hx : (p : ℤ) ∣ x) (hu : ¬ (p : ℤ) ∣ u)
    (ht : GTail p 1 x u = (p : ℤ) * t ^ p) :
    t ≡ 1 [ZMOD (p : ℤ)]
```

`GTail p 1` は既存の GN と同じ核である。
これは円分体や類群を必要としない整数上の定理。
正則性が必要なのは、前段で `GN=p*t^p` という等式を構成する箇所である。
結論は入力の等式を満たすどの整数根にも成り立ち、`p∤t` の仮定は不要。

## 証明の経路

1. 既存の整数 GN 先頭合同式から `p*t^p ≡ p*u^(p−1) mod p²` を得る。
2. `Int.ModEq.mul_left_cancel'` で両辺と法から p を一つずつ消去し、
   `t^p ≡ u^(p−1) mod p` を得る。
   この段階を `ramified_integral_root_pow_modEq_parameter` として公開した。
   ここではまだ `p∤u` は不要。
3. `ZMod p` に移り、AKSBridge の `prime_zmod_gap_compress_via_GN` により
   u^p=u を得る。u≠0 なので、u^(p−1)*u=u から u^(p−1)=1 を導く。
4. 同じ GN 版 Fermat を t に適用し、t^p=t と前段の合同式から t=1 を得る。
5. `ZMod.intCast_eq_intCast_iff` で整数の合同式へ戻す。

新しい証明は `ZMod.pow_card` や既存の有限体版 `prime_pow_modEq_self` を
呼ばず、GN の単位幅合同式を積み重ねる経路を使う。

## パケットと FLT 入口

`DkMath.FLT.Kummer.GNRamifiedArithmetic` に二つの接続を追加した。

- `ramified_packet_integral_root_modEq_one`：基底パケット P と
  `GN=p*t^p` を受け取り、同じ座標の `t≡1 mod p` を返す。
- `exists_GN_eq_prime_mul_pow_modEq_one_of_ramified_case`：従来の原始性、
  方程式、p∣c の向き、c≠0、類数条件から、
  `GN=p*t^p`、`t≡1 mod p`、`p∤t`、`(a+b)*(p*t^p)=c^p` を同時に返す。

従来のパケットのフィールドと公開定理は保持した。
`DkMath.FLT.Kummer` および `DkMath` から新定理へ到達できる。

## 回帰例と範囲

既存の算術テストに6例を追加した。
非自明な実数値 `GN₃(-54,17)=3*7³` から 7≡1 mod 3 を検証する。
負の parameter、零 gap、p=5 も含む。
一方、u=0,t=0 では結論が壊れ、p=2,x=6,u=1,t=2 でも結論が壊れる。
法を縮小する中間定理は u=0 でも成立する。

新規4定理を、既存15定理に加えて標準3公理の whitelist で検査する。
実行記録は `evidence/validation-ramified-root.txt`。

この剰余条件は整数ノルムの根に関するもの。
円分整数環の単元 εᵢ の合同条件を解決したことや、次の解を作る降下を意味しない。

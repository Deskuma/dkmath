# 幅1 GN の累積による Fermat の小定理

実装: `DkMath/NumberTheory/AKSBridge.lean` の `prime_zmod_gap_compress` 直前。
名前空間: `DkMath.NumberTheory`。GN は既存の `DkMath.CosmicFormula.GN` を使う。

## 補正量を残す

自然数に対して次を定義する。

```
H_p(n) = Σ k < p-1, (choose p (k+1) / p) * n^(p-(k+1))
E_p(u) = Σ n < u, H_p(n)
```

Lean 名はそれぞれ `primeGNUnitStepCorrection` と
`primeGNAccumulatedCorrection`。定義は全域的だが、係数の除算が割り切れることを
使う定理には `p.Prime` が必要である。

`prime_innerBeam_eq_mul_GN_correction` は各内部二項係数の可除性から
beam = p H を証明する。これを既存の weighted tail / GTail 接続と合わせると、
`prime_GN_unit_step_eq_one_add_mul_correction` が `GN p 1 n = 1 + p H_p(n)` を返す。

`sum_GN_unit_steps_eq_pow` は正次数 d に対する望遠和
`Σ n < u, GN d 1 n = u^d`。素数性は不要である。次数0を除くのは、
u=0 で空和0と `0^0=1` が一致しないため。

両者から `prime_pow_eq_self_add_mul_GN_correction` は厳密な等式
`u^p = u + p E_p(u)` を得る。自然数上の等式なので、差の切り捨てを使わずに
補正量が非負であることも保持する。

## 合同式への経路

```
内部二項係数の p 可除性
  → prime_GN_unit_step_modEq_one
  → prime_pow_modEq_self_via_GN（u に関する帰納法）
  → prime_zmod_gap_compress_via_GN（自然数代表 u.val を使う）
```

この経路は既存の `prime_pow_modEq_self` や `ZMod.pow_card` を呼ばない。
既存の `prime_zmod_gap_compress` はそのまま残し、同じ結論への別経路を比較できる。

## 回帰例と範囲

`DkMathTest/NumberTheory/AKSBridgeGN.lean` で H₃(n)=n²+n、H₂(n)=n、
E₃(4)=20、空和、次数1、自然数・ZMod の合同式を検証する。
合成数では幅1の合同式が一般には成り立たない例（d=4, n=1）も含む。
新規8定理の推移的な公理依存を標準3公理の whitelist で検査する。

ここでは自然数上の補正量と、任意の ZMod 元への合同式を構成した。
負整数上の補正多項式、付値の深さ、単元合同解析や Kummer の無限降下の定理は
この実装の結論には含まない。

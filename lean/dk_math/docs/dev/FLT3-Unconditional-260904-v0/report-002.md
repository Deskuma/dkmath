# FLT3U-002 実装報告: Exact Cubic Depth and Forced High-Lift

## 実装した theorem surface

新規 module [CubicValuationDepth.lean](../../../DkMath/FLT/Three/CubicValuationDepth.lean)
を追加した。`PrimitiveCubicLiftPacket` 自体には FLT equation を追加せず、
equation を別引数で受け取る最小設計 A を採用している。

1. `padicValNat_GN_three_eq_three_mul_padicValNat_of_packet`

   ```text
   padicValNat q (GN 3 (c - b) b) = 3 * padicValNat q a
   ```

   `c^3 - b^3 = a^3`、primitive gap の valuation transport、
   `padicValNat.pow` を順に接続した exact equality である。

2. `exists_pos_cubic_depth_multiplier_of_packet`

   ```text
   ∃ k, 0 < k ∧
     padicValNat q (GN 3 (c - b) b) = 3 * k
   ```

   `k := padicValNat q a` とし、`PrimitiveCubicLiftPacket.hdepth` から
   `0 < k` を得る。

3. `cube_dvd_GN_of_primitiveCubicLiftPacket`

   ```text
   q ^ 3 ∣ GN 3 (c - b) b
   ```

   equation を再要求せず、packet の `hdepth` だけから
   `padicValNat_dvd_iff_le` で導出する。

4. `square_dvd_GN_of_primitiveCubicLiftPacket`

   ```text
   q ^ 2 ∣ GN 3 (c - b) b
   ```

   上記の cubic divisor からの短い wrapper として追加した。

## Hensel depth connection

exact depth が `v_q(GN) = 3k` のとき、標準の
`padicValNat_dvd_iff_le` を exponent `3k` に適用すれば `q^(3k) ∣ GN` として
利用できる。したがって既存
`GNThreeHenselDepth.existsUnique_GN_three_powLift_digit` の depth parameter
には `k_H = 3k` を渡せる。その theorem は
`q^(k_H) ∣ GN`、`1 ≤ k_H`、および packet の
`hderivative : ¬ q ∣ 2 * (c - b) + 3 * b` を消費する。

この checkpoint ではその finite Hensel recursion、lift の存在・一意性を
新たに実装せず、depth parameter との接続可能性だけを固定した。lift の存在を
矛盾とは解釈していない。

## 境界

- `NoLift / Lift` splitter、Eisenstein arithmetic、ramifier、conjugate
  coprimality、unit 分類、strict descent、well-founded closure、FLT3 最終定理は
  実装していない。
- universal `q^2 ∤ GN3` theorem は作っていない。
- `DkMath.FLT.Main` および完成済み外部 FLT3 theorem shortcut は import していない。
- `ROADMAP.md` の route は変更していない。high-lift branch を強制するという
  既定の planned route の範囲内である。

## 検証

nested Lean checkout (`lean/dk_math`) で次を実行した。

```text
lake build DkMath.FLT.Three.CubicValuationDepth
```

結果は `Build completed successfully (8699 jobs).` で、今回の build に
warning はない。新規 module の直接 import は次の 1 本である。

```text
import DkMath.FLT.Three.PrimitiveCubicLiftPacket
```

新規 source の `sorry`、`axiom`、禁止された FLT import は検索で検出されない。
主要 constructor / exact-depth theorem / forced-high-lift theorem の
`#print axioms` は `[propext, Classical.choice, Quot.sound]` のみである。

判定は Outcome A: exact cubic depth と forced high-lift packet surface の
production 実装完了。次の Eisenstein descent は FLT3U-003 で開始する。

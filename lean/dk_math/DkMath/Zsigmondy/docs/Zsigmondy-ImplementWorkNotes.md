# Zsigmondy Implement Work Notes

このファイルは、Zsigmondy の定理の実装に関する作業ノートです。実装の過程で発生した問題や解決策、コードの構造などを記録しています。

## 実装記録

- Zsigmondy の定理の実装を開始。まずは、定理の内容を理解し、必要な補題や定義を整理することから始める。

### 2026/03/09 23:06

現状確認

- `DkMath/Zsigmondy.lean` を新規作成し、`BodyZ`, `BodyN`, `KernelZ`, `KernelN` を導入した。
- `DiffPow` 側の因数分解を宇宙式へ specialized し、`BodyZ x u d = x * KernelZ x u d` と `BodyN x u d = x * KernelN x u d` を整備した。
- `PrimitivePrimeDivisor` を定義し、射影補題 `PrimitivePrimeDivisor.prime`, `PrimitivePrimeDivisor.dvd`, `PrimitivePrimeDivisor.not_dvd_lower` を追加した。
- prime exponent 版 Zsigmondy を `PrimitivePrimeDivisor` で束ねる `exists_primitivePrimeDivisor_prime_exp` を追加した。
- 宇宙式 specialized 版として `exists_primitivePrimeDivisor_body_nat` を追加し、`(x + u)^d - u^d` に primitive prime divisor が存在する形を得た。
- `q ∣ BodyN x u d` かつ `¬ q ∣ x` なら `q ∣ KernelN x u d` を返す `prime_dvd_body_of_not_dvd_boundary_imp_dvd_kernel` を追加した。
- existence を kernel 側へ持ち上げる `exists_primitivePrimeDivisor_kernel_nat` を追加し、primitive prime divisor が kernel に落ちる存在定理まで到達した。
- `d = 3` に対して `BodyN x u 3 = x * GN 3 x u`、`Beam 3 x u = 3 * x^2 * u + 3 * x * u^2`、`BodyN x u 3 = x^3 + Beam 3 x u` を追加し、Body と GN / Beam の橋渡しを実装した。
- `q ∣ BodyN x u 3` かつ `¬ q ∣ x` なら `q ∣ GN 3 x u` を返す `prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN` を追加した。
- `PrimitivePrimeDivisor (x + u) u 3 q` から直接 `q ∣ GN 3 x u` を得る `primitivePrimeDivisor_body_three_imp_dvd_GN` を追加した。
- reviewer 提案の 4C にあった Beam 版補題は、仮定のままだと一般に成立しないため採用しない方針にした。
- `lake build DkMath.Zsigmondy` と `lake build DkMath` で今回の追加分が通ることを確認した。既存の別ファイル由来 warning は残存している。

### 2026/03/09 23:20

- 実施内容
- `FLT/Basic.lean` の `pick_primitive_q_data_GN3` を、新設した `DkMath.Zsigmondy` API 経由へ接続する作業を実施した。
- 結果
- `exists_primitivePrimeDivisor_body_nat` と `primitivePrimeDivisor_body_three_imp_dvd_GN` を使う形へ置き換え、FLT 側の「primitive prime を取って GN へ落とす」流れを `Zsigmondy` 側の標準補題へ寄せた。
- 失敗内容
- 初回の書き換えでは `x := A - B`, `u := B` への specialized rewrite が足りず、`BodyN x u 3 = A^3 - B^3` と `Coprime (x + u) u` の型合わせでビルドが落ちた。
- `x + u = A` を明示補題として立てて修正し、再ビルドで解消した。
- 次の予定
- FLT 側の他の hand-rolled な `q ∣ diff-of-powers -> q ∣ GN` 部分も同様に `DkMath.Zsigmondy` API へ寄せる。
- コメント
- 今回の接続で、`Zsigmondy` 側で整えた語彙と FLT 側の実利用箇所が実際に一本につながった。

### 2026/03/09 23:47

- 実施内容
- `FLT/CosmicPetalBridge.lean` の `prime_dvd_S0_via_cosmic_bridge` を、`DkMath.Zsigmondy.prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN` を使う形へ置き換えた。あわせて `FLT/PrimeProvider/CosmicPetalBridgeGNCore.lean` にも同型の差し替え箇所があるか確認した。
- 結果
- `q ∣ c^3 - b^3` かつ `q ∤ (c - b)` から `q ∣ GN 3 (c - b) b` へ落とす部分を、`BodyN (c - b) b 3` を経由して `Zsigmondy` 側 API に寄せた。`CosmicPetalBridgeGNCore.lean` は現状 `q ∣ GN` を前提にもらって `diff` 側へ戻す流れが中心で、今回の `diff -> GN` 補題を直接差し込む箇所はなかった。
- 失敗内容
- なし。
- 次の予定
- `FLT` 側でまだ `prime_dvd_GN_of_dvd_sub_not_dvd_left` を直接使っている箇所を整理し、`d = 3` の specialized bridge に寄せられる部分と、一般 `d` のまま残すべき部分を切り分ける。
- コメント
- `lake build DkMath.FLT.CosmicPetalBridge` と `lake build DkMath.FLT.PrimeProvider.CosmicPetalBridgeGNCore` は通過した。今回の置換で `CosmicPetalBridge` は `Zsigmondy` 側の新 API を実利用する形になった。

---

## テンプレート

今後、作業のたびに、この記録長に

```md
### タイムスタンプ

- 実施内容
- 結果
- 失敗内容
- 次の予定
- コメント
```

を書いて記録。

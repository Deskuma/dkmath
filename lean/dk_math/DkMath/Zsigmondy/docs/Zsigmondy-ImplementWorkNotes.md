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

### 2026/03/09 23:59

- 実施内容
- `FLT/PrimeProvider` 側に残っていた `prime_dvd_GN_of_dvd_sub_not_dvd_left` 参照を整理し、`z^d - y^d` 形の入力から直接 `GN d (z - y) y` を返す `dvd_GN_of_dvd_sub_pow` に置き換えた。あわせて `CosmicPetalBridge.lean` に `d = 3` の `Zsigmondy` 接続補題を追加した。
- 結果
- `TriominoCosmicGapInvariant.lean` と `CosmicPetalBridgeGNDescentB.lean` では、いったん `((z - y) + y)^p - y^p` に組み替える補助ステップが不要になった。`CosmicPetalBridge.lean` 側には、一般補題の `d = 3` specialized 版が `DkMath.Zsigmondy.prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN` から従うことを明示する補題を追加した。
- 失敗内容
- なし。
- 次の予定
- `FLT` 側で `d = 3` の specialized bridge をさらに使える箇所がないか確認し、一般 `p` と立方専用ルートの境界を整理する。
- コメント
- 一般 `p` の箇所は `Zsigmondy` の `Body -> GN` をまだ直接は使えないため、`dvd_GN_of_dvd_sub_pow` を正面 API にした。`d = 3` については `Zsigmondy` との接続を補題としてそばに固定した。

### 2026/03/10 00:12

- 実施内容
- `CosmicPetalBridge.lean` の `dvd_GN_of_dvd_sub_pow` の近くに、`d = 3` specialized 版が `DkMath.Zsigmondy` 由来であることを示す補題を追加し、下流の `prime_dvd_S0_via_cosmic_bridge` もそれを経由する形に寄せた。
- 結果
- `dvd_GN_of_dvd_sub_cube_via_zsigmondy` を追加し、`q ∣ z^3 - y^3` かつ `q ∤ (z - y)` から `q ∣ GN 3 (z - y) y` への橋が、`BodyN (z - y) y 3` と `prime_dvd_body_three_of_not_dvd_boundary_imp_dvd_GN` を通ることがコード上で見えるようになった。
- 失敗内容
- なし。
- 次の予定
- `d = 3` 専用の FLT ルートで、この新しい `via_zsigmondy` 補題を説明用 API として使うべき箇所が他にないか確認する。
- コメント
- 一般 `d` の `dvd_GN_of_dvd_sub_pow` 自体は純粋な因数分解補題として残し、`d = 3` だけ `Zsigmondy` 由来を別名で明示する構成にした。

### 2026/03/10 00:41

- 実施内容
- `gcd` と `GN` の整備に入る前の事前調査として、説明メモ `What_is_the_reason_why_GN_becomes_the_center_of_Zsigmondy.md` と `Zsigmondy-GcdGN.md` を確認し、既存 Lean 実装の `gcd` 系補題を横断検索した。
- 結果
- 一般骨格は既にある。`GcdDiffPow.gcd_divides_d` が整数環で `gcd(a-b, diffPowSum a b d) ∣ d` を与え、`GcdNext.gcd_specialized_divides_d` がこれを `a := x + u, b := u` に specialized している。`FLT/Basic.lean` には `gcd_u_GN3 : gcd(u, GN 3 u y) = gcd(u, 3)` が既にあり、`FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean` には一般 `p` の gap/GN に対する `Int.gcd ... ∣ p` と coprime 化の橋が既に入っている。未整備なのは、これらを `DkMath.Zsigmondy` / `GN` 語彙で再編した薄い接続層と、`Nat` 側で使いやすい名前の補題群。
- 失敗内容
- なし。
- 次の予定
- `GcdGN.lean` を新規作成するか `DkMath.Zsigmondy` に section を足し、まず `Int` 側で `gcd(x, KernelZ x u d) ∣ d`、次に `Nat` 側で `d = 3` の `gcd(x, GN 3 x u)` 明示版、最後に `Nat.Coprime x u -> gcd(x, GN 3 x u) ∣ 3` までを正規 API として切り出す。
- コメント
- 実装難度は「一般 `Int` は低め、一般 `Nat` は減法とキャストで中程度、`d = 3` 特化は低め」。次の一手としては、まず `d = 3` 特化と `Int` 側 specialized wrapper を揃えるのが最も効率が良い。

### 2026/03/10 01:37

- 実施内容
- `NumberTheory` 側の `gcd` 補題を集約する入口として、`DkMath/NumberTheory/Gcd.lean` 配下の API スケルトンを整備した。`Gcd/Basic.lean` を基礎再 export 層にし、新たに `Gcd/GN.lean` を追加して `GN` specialization の集約先を用意した。
- 結果
- `DkMath.NumberTheory.Gcd` から `Gcd.Basic` と `Gcd.GN` を引く構成になり、今後は「点在補題 -> Gcd/GN 系 -> Gcd.lean API」という形で集中化を進められる状態になった。まだ theorem の再命名や wrapper 追加はしていないが、集約先の名前と import 経路は確定した。
- 失敗内容
- 新設した `Gcd/GN.lean` の先頭コメントを C 風コメントで書いてしまい、初回ビルドで `unexpected token '/'` が出た。Lean コメント `/- ... -/` に直して解消した。
- 次の予定
- `Gcd.GN` に `gcd_specialized_divides_d` や `gcd_u_GN3` 相当の正規 API を順次移し、下流からはこの層を参照するように寄せる。
- コメント
- 先に import 経路だけ固めると、その後の theorem 移送や alias 追加を小分けで進めやすい。今回は大きな移動はせず、再 export の骨組みだけを先に立てた。

### 2026/03/10 01:41

- 実施内容
- `DkMath/NumberTheory/Gcd/GN.lean` に、`gcd_specialized_divides_d` と `gcd_u_GN3` 系を正規 API として薄く追加した。
- 結果
- 一般 `Int` 側の wrapper として `gcd_boundary_sd_divides_exp_int` を追加した。`d = 3` の `Nat` 側には `gcd_boundary_GN_three_eq_gcd_boundary_three`, `gcd_boundary_GN_three_dvd_three`, `coprime_boundary_GN_three_of_coprime_of_not_dvd_three` を追加し、今後は `GN` 視点の gcd 議論を `DkMath.NumberTheory.Gcd.GN` から参照できるようにした。
- 失敗内容
- 初回実装では `GN` を `GcdNext` 名前空間の識別子として直接参照してしまい、完全修飾が必要だった。また `coprime_boundary_GN_three_of_coprime_of_not_dvd_three` の最後の書き換えも `rw` / `simpa` の当て方を調整する必要があった。修正後に `lake build DkMath.NumberTheory.Gcd.GN` と `lake build DkMath.NumberTheory.Gcd` は通過した。
- 次の予定
- 下流の `FLT.Basic` などで使っている局所補題を、この新しい `Gcd.GN` API へ順次寄せる。
- コメント
- `gcd_u_GN3` そのものは `FLT.Basic` に残したままでも、今後の参照先は `NumberTheory/Gcd/GN.lean` に寄せられる状態になった。後続のリファクタリングでは、重複補題の統合と命名整理を行う。

### 2026/03/10 01:47

- 実施内容
- `FLT/Basic.lean` で使っていた局所補題 `gcd_u_GN3` の参照を、新設した `DkMath.NumberTheory.Gcd.GN` API へ差し替えた。あわせて `FLT/Basic.lean` 内の重複定義 `gcd_u_GN3` を削除した。
- 結果
- `FLT.Basic` は `DkMath.NumberTheory.Gcd.gcd_boundary_GN_three_eq_gcd_boundary_three` を直接呼ぶ形になり、`gcd(u, GN 3 u y) = gcd(u, 3)` の根拠が `NumberTheory` 側の集中化された API に揃った。
- 失敗内容
- なし。
- 次の予定
- ほかの `FLT` 系ファイルでも、局所の gcd 補題や再証明を `DkMath.NumberTheory.Gcd.GN` へ寄せられる箇所がないか確認する。
- コメント
- 今回の差し替えで、`FLT.Basic` は `gcd_u_GN3` のローカル所有者ではなく利用者になった。責務分離としてはこの形が自然。

### 2026/03/10 02:00

- 実施内容
- `FLT/PrimeProvider/CosmicPetalBridgeGNDescentB.lean` に埋まっていた一般 gcd/GN 補題の核を `DkMath/NumberTheory/Gcd/GN.lean` へ引き上げた。具体的には、`GN p (z - y) y` の整数版が `diffPowSum z y p` に一致する補題と、`Int.gcd(gap, GN) ∣ p` の一般補題を `NumberTheory` 側へ追加した。
- 結果
- `DkMath.NumberTheory.Gcd.gn_sub_eq_sd_int` と `DkMath.NumberTheory.Gcd.gcd_gap_GN_dvd_exp_int` を新設し、`CosmicPetalBridgeGNDescentB` 側の `triominoWieferichShrink_int_GN_eq_Sd_core` と `triominoWieferichShrink_gap_gcd_GN_dvd_p_int` は wrapper 化できた。これで gcd/GN の一般骨格は `PrimeProvider` ではなく `NumberTheory` 側から参照できる。
- 失敗内容
- なし。
- 次の予定
- `CosmicPetalBridgeGNDescentB` の coprime 化補題も、一般部分と FLT 文脈部分をさらに分離できるか確認する。
- コメント
- 今回の引き上げで、「一般 gcd/GN 理論」と「FLT 反例パック由来の coprime 条件供給」が分離された。整理の方向としてはかなり良い。

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

# 容量閉包・既存 PCK・高次数 signature

## 検証済み

`PrimeWorld`, `Capacity`, `Conservation`, `Signature` の各 focused build は成功。

- 左右合同障害、積周期、剰余への還元、prime insert の観測条件、CRT による全周期内の実現。
- 局所禁止数は `if r∣2*n then 1 else 2`。局所生存数は `r` からこの数を引いた値。
- 真の有限区間について、生存数と被覆和集合の濃度の和は `n-1`。
- 被覆和集合の濃度は prime-seat incidence の総数以下。各素数ごとの上界を与えれば総上界へ移せる。
- `StrongGoldbach ↔ GoldbachCapacityEscape` を証明。後者は正確な被覆濃度が常に `n-1` 未満という命題で、証明済みの provider ではない。
- 既存 PCK を実際に import し、両端点への old/fresh 分解を取得。既存の平方窓閉包から、両側の support-disjoint 条件を入力した素数対閉包も証明。
- 高次数 GN signature を有限集合で定義し、素数ターゲットでの次数の素数性、`d∣P-1`、`2^d-1≤P` と有限フィルタへの包含を証明。次数 2 は正の任意の奇数に存在する。

## 証明可能性の明確化

正確な `GoldbachCapacityEscape` は Goldbach と同値である。名前を付け替えて仮定として受け取るだけでは未解決条件を解消しない。既存 PCK は各端点の分解を与えるが、old-generated 側を排除せず、同じ offset における両端点の脱出も与えない。

次に、全周期の積計数を完成させ、素数ごとの障害数の単純和では上界が強すぎる具体例、および端点例外と非周期性の回帰を kernel で検証する。

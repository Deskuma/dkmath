# ABC Core Insertion Candidates

最終更新: 2026/04/18

## 目的

`PrimitiveWitnessFamily` から得られる counting spine

- `channelCount -> channelProduct`
- `channelProduct -> supportMass`
- `channelProduct -> ABC.rad`
- `2 ^ channelCount -> ABC.rad`

を、既存 ABC コアのどこへ差し込むと効くかを 3 箇所まで絞って整理する。

ここでは「今の bridge API だけで足りるか」と「何がまだ足りないか」を切り分ける。

---

## Candidate 1: `ABC038.quality_le_of_not_bad_with_tail`

場所:

- [ABC038.lean](/lean/dk_math/DkMath/ABC/ABC038.lean)
- `quality_le_of_not_bad_with_tail`
- `quality_le_of_not_bad_with_log`

現状の役割:

- `¬Bad` から `piSqRad c ≤ rad(a*b)^δ` を取り、
- `TailBound γ a b c` と合成して
- `quality ≤ 1 + ε` を閉じる。

bridge が刺さる理由:

- quality 系は最終的に `rad(...)` の下界/上界を介して動く。
- 今回の bridge は `PrimitiveWitnessFamily` から
  `2 ^ channelCount ≤ ABC.rad(diff)` あるいは
  `channelProduct ≤ ABC.rad(diff)` を直接出せる。

今の API だけで足りるか:

- 足りない。

不足しているもの:

- 既存 theorem は `ABC.rad (a * b)` を使う。
- bridge は `ABC.rad (a ^ d - b ^ d)` を出す。
- したがって、次のどちらかが必要。
  - `diff = c` という形に乗る新しい family existence
  - あるいは `rad(a*b)` 側へ橋渡しする別補題

判定:

- 本命候補。
- ただし差し込み直前には「family がどの triple / diff に付くか」の整理が必要。

---

## Candidate 2: `ABC016.twoTail_le_rad_pow_of_log_bound`

場所:

- [ABC016.lean](/lean/dk_math/DkMath/ABC/ABC016.lean)
- `twoTail_le_rad_pow_of_log_bound`
- その上流の `piSqRad_adjacent_le_of_not_is_bad_a`

現状の役割:

- `twoTail c` の対数境界から `(twoTail c : ℝ) ≤ (rad (a*b) : ℝ)^γ` を出す。
- adjacent triple 系では `rad (X * (X+1))` が主役。

bridge が刺さる理由:

- `rad` 側に下界が入ると `twoTail` の許容量や square-excess budget の読み替えに使える可能性がある。
- 特に adjacent triple 系は small concrete family と相性がよい。

今の API だけで足りるか:

- 足りない。

不足しているもの:

- ここでもターゲットは `rad(a*b)`。
- bridge 側は `rad(diff)` を与える。
- さらに `twoTail` 側は上界制御で、bridge は下界制御なので、
  実際に刺すには
  - どの quantity に対する family existence か
  - 下界が quality/budget のどこで効くか
  の中間命題が要る。

判定:

- 構造的な接続候補。
- ただし直接の drop-in ではなく、1 本中間命題を挟む必要がある。

---

## Candidate 3: `RatioBound.count_with_rad_eq_le_div`

場所:

- [RatioBound.lean](/lean/dk_math/DkMath/ABC/RatioBound.lean)
- `count_with_rad_eq_le_div`

現状の役割:

- 固定された `r = rad a` に対して、
  `rad a = r` を満たす `a ≤ X` の個数を `X / r + 1` で抑える。

bridge が刺さる理由:

- bridge は `ABC.rad(diff)` の下界を supply する。
- この系は `rad` 下界をそのまま count bound に変換する層なので、
  現 API と最も型が合う。

今の API だけで足りるか:

- かなり近い。

不足しているもの:

- `PrimitiveWitnessFamily` から出るのは特定の `diff` に対する `ABC.rad diff` の下界。
- `count_with_rad_eq_le_div` は一般の `a ≤ X` を数える命題なので、
  次の packaging が要る。
  - `diff` を数え上げ対象の `a` に埋め込む
  - あるいは `rad a ≥ R` なら count class がどう縮むか、という薄い corollary

判定:

- 最も実装に近い候補。
- `rad lower bound -> counting upper bound` の補助補題を 1 本作れば差し込みやすい。

---

## 優先順位

1. `RatioBound.count_with_rad_eq_le_div`
   - 現在の bridge API と一番型が近い。
   - `rad` 下界を count 側へ送る薄い補題を足せば接続しやすい。

2. `ABC038.quality_le_of_not_bad_with_tail`
   - quality 本体への入口。
   - ただし `rad(diff)` と `rad(a*b)` のズレを埋める中間命題が必要。

3. `ABC016.twoTail_le_rad_pow_of_log_bound`
   - 構造的には重要。
   - ただし上界/下界と対象 quantity のズレが最も大きい。

---

## 次の実装候補

最小で進めるなら次のどちらか。

1. `RatioBound` 側に
   `rad a ≥ R` を仮定した count-class 上界の薄い corollary を追加する。

2. `ABC038` 側に進む前段として、
   `rad(diff)` 下界を quality 系の入力へ送るために何が必要かを
   Lean theorem 名レベルでさらに細分化する。

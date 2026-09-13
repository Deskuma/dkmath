# instruction-007 実装レポート

日付: 2026-09-10

## 実装した内容

instruction-006 の overlap / pair-overlap owner を基礎に、Pascal の pair 層を追加した。

- `PairOverlap.lean`
  - `goldbachLocalPairOverlapResidual n u := Nat.choose ((goldbachObstructionSupport n u).card - 1) 2`
  - `goldbachOffsetROverlapMultiplicity` と `r=0,1,2` の簡約定理
  - 局所恒等式
    `goldbachOffsetPrimePairMultiplicity n u = goldbachLocalOverlapExcess n u + goldbachLocalPairOverlapResidual n u`
  - 大域 residual `goldbachPairOverlapResidual`
  - 大域恒等式
    `goldbachPrimePairOverlapCount n = goldbachOverlapExcess n + goldbachPairOverlapResidual n`
  - 既存の `goldbachOverlapExcess_le_primePairOverlapCount` を大域恒等式からの corollary に整理
- facade、回帰テスト、`AxiomAudit.lean`、宣言索引、README、verification notes を更新した。

変更ファイルは `DkMath/NumberTheory/Goldbach.lean`、
`DkMath/NumberTheory/Goldbach/PairOverlap.lean`、
`DkMathTest/NumberTheory/GoldbachGNFiber.lean`、`AxiomAudit.lean`、
`README.md`、`declaration-index.md`、`verification-notes.md`、および本レポートである。

## 数学的な意味

一つの offset の obstruction support の濃度を `k` とすると、unordered obstruction pair の数は

```text
choose k 2 = (k - 1) + choose (k - 1) 2.
```

第一項は overlap ledger の最初の支払い、第二項は三つ以上の obstruction が同じ offset に重なる高次 residual である。この等式を offset 全体で加算したため、pair-overlap count の過剰分を正確に残差として記録できる。generic `r`-fold observer は有限 Pascal 階層の記録用 API であり、GTail との形式的同値は主張していない。

## 回帰と検証

- `n=2`: local/global residual は 0。
- `n=6`: incidence は 5、overlap excess と pair-overlap count はともに 1。
- `n=35,u=5`: support は `{2,3,5}`、cardinality は 3、local residual は 1。したがって higher residual が実際に正になることを kernel で確認した。
- `n=10`: `GoldbachPairAt 10` と一般 pair-overlap 上界を確認した。exact residual の重い `decide` は回帰から除き、不要な計算負荷を増やしていない。

実行した検証:

```text
./lean-build.sh DkMath.NumberTheory.Goldbach.PairOverlap
./lean-build.sh DkMath.NumberTheory.Goldbach
./lean-build.sh DkMathTest.NumberTheory.GoldbachGNFiber
lake env lean docs/dev/NumberTheory-Goldbach-GNFiber-260910-v0/AxiomAudit.lean
git diff --check
./lean-build.sh DkMath
```

focused build、facade、回帰、axiom audit、root build は終了コード 0。新規宣言の監査は標準の `propext`、`Classical.choice`、`Quot.sound` 以外の依存を持たない。新しい `sorry`、`admit`、`axiom`、`native_decide`、`unsafe` は追加していない。root 出力に残る 5 件の `sorry` 警告は既存研究モジュールのものだった。

## 不足要因と停止境界

この checkpoint は有限の fixed-center obstruction / incidence / pair-overlap 帳簿を閉じるもので、Strong Goldbach の全称証明ではない。残る不足は、全中心で短い admissible interval に生存 offset を供給する独立 provider、重複を使った一様な容量評価、端点例外を含む product-wave の閉包である。

GTail import や Pascal/GTail equivalence、CRT occupancy、near/far・mirror、universal escape、StrongGoldbach theorem は実装していない。現在の Goldbach branch はこの有限帳簿層までで develop へ統合可能な停止点とし、次段階は GTail refactor 後に独立して設計する。

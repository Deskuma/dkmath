# Lean --profile

## Result

```bash
# branch `refactor/import-diet-nightly-261001` build time

$ lake clean && lake update
$ time lake build

Build completed successfully (10334 jobs).

real    53m32.209s
user    244m25.744s
sys     45m36.214s

# branch `nightly` build time

Build completed successfully (10333 jobs).

real    53m49.892s
user    254m48.658s
sys     43m17.234s
```


大差なかったですね。

根本的に証明方法の最適化とモジュール細分化が必要かもしれませんね。

`lean --profile` なるものがあると聞いたのですが。

clean からの build time

## Codex Agent

この比較では、import diet の効果は次のように見えます。

- wall-clock: 53:49.892 → 53:32.209（約 0.55% 改善）
- user CPU: 約 4.1% 改善
- sys CPU: 約 5.4% 増加
- user+sys 合計: 約 2.7% 改善

したがって、実時間では測定誤差に近い一方、Lean が処理した仕事量は多少減っていそうです。ただし 1 回の測定なので、まだ「有意な高速化」とは断定しない方がよいです。

この環境の `lean --profile` は利用できます。

```bash
lake env lean --profile DkMath/NumberTheory/CyclotomicQRProduct.lean
```

実際に測ると、同モジュールでは次のような内訳が出ました。

- `import`: 7.38 秒
- `typeclass inference`: 7.37 秒
- `simp`: 2.27 秒
- `interpretation`: 2.09 秒

つまり、証明本体だけでなく、import と typeclass inference がかなり大きな比率を占めています。

`--profile` は単一の Lean 起動を測る機能で、`lake build` 全体に自動適用されるわけではありません。全体を調べる場合は、一時的に `lakefile.toml` の `[leanOptions]` に追加します。

```toml
profiler = true
profiler.threshold = 100
```

その後:

```bash
lake clean
time lake build 2> /tmp/dkmath-profile.log
```

ただし、これはプロファイラ自体のオーバーヘッドがあり、通常の clean build の時間比較には使わない方がよいです。まずは大きなモジュールを数個選び、

```bash
lake env lean --profile DkMath/FLT/Core.lean
lake env lean --profile DkMath/NumberTheory/CyclotomicQRProduct.lean
lake env lean --profile DkMathTest/FLT/Prime/GaussianPeriodFactorizationProbe.lean
```

のように調べるのが効率的です。

方針としては、次の順番がよいと思います。

1. `import` 時間が大きいモジュールを特定
2. `typeclass inference`、`simp`、`tactic execution` が大きい定理を特定
3. その定理群を意味のある単位で別モジュールへ分割
4. `Mathlib` umbrella import を直接 import へ縮小
5. 最後に clean build を再測定

モジュールを細かくしすぎると import とジョブ管理の overhead が増えるため、まずは「大きくて、変更頻度が高く、依存先が少ない証明群」から分割するのがよいです。

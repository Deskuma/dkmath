# NOTE-032 — 同じ還元核の一致と商の単射

2026-10-27。開始 HEAD `179d84e60`。前回のフルビルドはユーザーから通過報告を受けた。

## 数学的内容

源の零成分の実際の還元像を `R`、同じ有限核 `H` の還元像を `H̄`、前回構成した還元準同型を `ψ` とする。今回は以下を証明した。

1. `P ∈ E₀` の還元点が `H̄` と衝突しなければ、商像の実際の座標は整である。商像は有限点なので、滑らかさの下でその還元は無限遠 `O` ではない。
2. 以前証明した `H̄ ⊆ ker ψ` と合わせ、`ker ψ = H̄` を得る。
3. 従って、`ψ(P̄) = O` と、ある `Q ∈ H` について `P̄ = Q̄` は同値である。
4. 誘導された `R / H̄ → E'` の準同型は単射である。

`H̄` は同じ一般ファイバー上の `H` の還元であり、仮定なしに別の核を導入していない。定義域は実際の還元像 `R` である。全剰余点が持ち上がることや、標的全体への全射性は結論しない。

Frey Source についても同じ核 `L` を使って零ファイバー判定を適用した。`p ≥ 5`、`q ≠ p` の悪い住所では、源の節点 Frame と方向の分離を内部供給する。`L ≤ E₀[p]` および判定対象 `P ∈ E₀` は保持する。2進住所も含む。

## 検証

- `./lean-build.sh DkMath.Lib.NumberTheory.EllipticFiniteKernelReducedHom`
- `./lean-build.sh DkMath.FLT.FreyFiniteKernelReducedHom`
- `./lean-build.sh DkMathTest.Lib.NumberTheory.EllipticFiniteKernelReducedHom`
- `lake env lean docs/dev/FLT-GN-regular-261018-v0/evidence/Note032ReducedKernelSmoke.lean`

47 上の実 3 点核では零ファイバーの必要十分条件と商の単射を検査した。Source 37 の 2 進住所でも、Frame を入力しない同じ零ファイバー判定を検査した。新しい一般・Frey 定理6件とスモーク1件の `#print axioms` は `propext`, `Classical.choice`, `Quot.sound` のみで、`sorryAx` を含まない。

## 残る境界

これは零成分内の **無限遠への還元の逆像**であり、商像が零成分に入ることから源点が零成分に入るという逆像判定は含まない。全剰余点への写像・全射性、節点比の冪写像との同定、正確な Δ 深さ、`q = p`、スキーム isogeny、有理捩れ排除、一般 hno は未完成。

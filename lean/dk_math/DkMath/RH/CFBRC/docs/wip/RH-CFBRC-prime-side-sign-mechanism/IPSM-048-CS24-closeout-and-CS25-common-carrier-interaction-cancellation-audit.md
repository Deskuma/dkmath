# IPSM-048 — CS24 closeout and CS25 common-carrier / interaction cancellation audit

## 0. Branch / scope

正本 branch:

`wip/RH-CFBRC-prime-side-sign-mechanism-260813-v1`

本 checkpoint は CS24 `PascalCenteredXiPrimeSideCanonicalPolarizationSignedMassAudit.lean` の closeout と、次の CS25 の実装方針を固定する。

CS25 では新しい同値 predicate を増やすことを目的にしない。CS24 で得られた canonical positive mass がなぜ source estimate として重いかを、plus/minus energy に共通する carrier mass の exact cancellation として解剖し、有限 prime-side source が実際に依存する signed interaction だけを抽出する。

無限和交換、無限 Euler product、height limit、endpoint sign、fixed-Xi defect の符号、RH は非目標とする。

---

## 1. CS24 verdict: Green-B

CS24 は Green-B とする。

確定済み事項:

- finite normalized prime contribution の係数は exact に `2 / π`。
- aggregate plus/minus energy difference と prime contribution の exact bridge がある。
- correction-only source は cutoff-independent な3項 source として分離された。
- canonical mass は `E₊ / 2` であり source-derived に非負。
- finite radial-contact deficit は canonical remainder minus canonical mass に exact 分解された。
- cutoff zero では prime support、aggregate plus energy、aggregate minus energy、canonical mass がすべてゼロ。
- canonical remainder は exact に `G(0) + E₋(X)/2`。
- canonical remainder の cofinal smallness は zero-target radial contact の十分条件。
- canonical remainder の cofinal smallness は最低でも `G(0) ≤ 0` を要求する。
- independent cofinal canonical remainder provider は未証明 gap のまま。

主要 exact identities は以下。

$$
\operatorname{Prime}_{\varepsilon,W,X}
=\frac{2}{\pi}\sum_{n\le X}\Lambda(n)K_{\varepsilon,W}(n)
=\frac{E_+^{\mathrm{agg}}(X)-E_-^{\mathrm{agg}}(X)}{2\pi}.
$$

$$
M^{\mathrm{can}}_{\varepsilon,W,X}=\frac12E_+^{\mathrm{agg}}(X)\ge0.
$$

$$
R^{\mathrm{can}}_{\varepsilon,W,X}
=\pi\bigl(Q_R-C_{\varepsilon,W}\bigr)+\frac12E_-^{\mathrm{agg}}(X).
$$

$$
G_{\varepsilon,W,X}
=R^{\mathrm{can}}_{\varepsilon,W,X}-M^{\mathrm{can}}_{\varepsilon,W,X}.
$$

cutoff zero baseline は

$$
G_{\varepsilon,W,0}=\pi\bigl(Q_R-C_{\varepsilon,W}\bigr),
$$

したがって

$$
R^{\mathrm{can}}_{\varepsilon,W,X}
=G_{\varepsilon,W,0}+\frac12E_-^{\mathrm{agg}}(X).
$$

ここまでの algebra / finite analysis は Green。

独立な `R^{can}` の cofinal estimate は未供給なので全体 verdict は Green-B とする。

---

## 2. CS24 が露出した strength issue

CS24 の canonical mass は本物の nonnegative source mass である。しかし target deficit 自体は `E₊` と `E₋` の差だけに依存するのに、canonical decomposition は `E₊` 全体を mass 側へ、`E₋` 全体を remainder 側へ置く。

この分離は plus/minus の双方に共有される大きな carrier を消去する前に行われている。

したがって CS25 ではまず polarization を centered form に戻す。

---

## 3. Normalized ray state

CS17 の finite geometric ray amplitude を

$$
Z_{\varepsilon,W,X,p}(t)
:=\operatorname{RayAmplitude}_{\varepsilon,W,X,p}(t)
$$

と読む。

CS17 には amplitude の exact quotient representation

$$
Z=\frac{A}{B}
$$

があり、prime `p` では `normSq(B) > 0` が証明済み。

CS25 では CS17 の normalized density が pointwise に次へ落ちることをまず theorem 化する。

$$
\operatorname{PlusDensity}=|Z+1|^2.
$$

$$
\operatorname{MinusDensity}=|Z-1|^2.
$$

必要なら denominator form から直接証明してよい。既存 CS17 theorem を壊さない。

---

## 4. Common carrier and interaction density

新しい source-derived density を定義する。

$$
\operatorname{CommonDensity}(Z):=|Z|^2+1.
$$

$$
\operatorname{InteractionDensity}(Z):=2\operatorname{Re}Z.
$$

純代数として exact に

$$
|Z+1|^2=\operatorname{CommonDensity}(Z)+\operatorname{InteractionDensity}(Z),
$$

$$
|Z-1|^2=\operatorname{CommonDensity}(Z)-\operatorname{InteractionDensity}(Z).
$$

従って

$$
|Z+1|^2+|Z-1|^2=2\operatorname{CommonDensity}(Z),
$$

$$
|Z+1|^2-|Z-1|^2=2\operatorname{InteractionDensity}(Z)=4\operatorname{Re}Z.
$$

`CommonDensity ≥ 0` は source-derived に証明する。

`InteractionDensity` には符号を仮定しない。

---

## 5. Ray-level integrated common / interaction energies

各 prime ray に有限 interval energy を定義する。

推奨名:

- `pascalCenteredXiPrimeSideFiniteGeometricRayCommonEnergy`
- `pascalCenteredXiPrimeSideFiniteGeometricRayInteractionEnergy`

定義は `[0,T]` 上の有限 interval integral とする。

狙う exact identities:

$$
E_{+,p}=C_p+I_p,
$$

$$
E_{-,p}=C_p-I_p.
$$

従って

$$
E_{+,p}-E_{-,p}=2I_p.
$$

既存 CS17 の

$$
4K_p=E_{+,p}-E_{-,p}
$$

と合わせて

$$
I_p=2K_p.
$$

を得る。

ここでは個別 ray sign を主張しない。

---

## 6. Prime-weighted aggregate common / interaction energies

既存 prime support と `log p` weighting をそのまま使う。

推奨名:

- `pascalCenteredXiPrimeSideAggregateRayCommonEnergy`
- `pascalCenteredXiPrimeSideAggregateRayInteractionEnergy`

exact に

$$
E_+^{\mathrm{agg}}=C^{\mathrm{agg}}+I^{\mathrm{agg}},
$$

$$
E_-^{\mathrm{agg}}=C^{\mathrm{agg}}-I^{\mathrm{agg}}.
$$

従って

$$
E_+^{\mathrm{agg}}-E_-^{\mathrm{agg}}=2I^{\mathrm{agg}}.
$$

CS17 から

$$
4\sum_{n\le X}\Lambda(n)K(n)
=E_+^{\mathrm{agg}}-E_-^{\mathrm{agg}}
$$

なので

$$
I^{\mathrm{agg}}
=2\sum_{n\le X}\Lambda(n)K(n).
$$

CS24 の normalization と接続すると

$$
\operatorname{PrimeContribution}_{\varepsilon,W,X}
=\frac{I^{\mathrm{agg}}_{\varepsilon,W,X}}{\pi}.
$$

この theorem は CS25 の主要成果候補。

---

## 7. Complete source after common-carrier cancellation

CS24 correction-only source を

$$
C_{\varepsilon,W}^{\mathrm{corr}}
$$

とする。

complete normalized source は exact に

$$
\operatorname{CompleteSource}_{\varepsilon,W,X}
=C_{\varepsilon,W}^{\mathrm{corr}}
+\frac{I^{\mathrm{agg}}_{\varepsilon,W,X}}{\pi}.
$$

従って radial-contact deficit は

$$
G_{\varepsilon,W,X}
=\pi\bigl(Q_R-C_{\varepsilon,W}^{\mathrm{corr}}\bigr)
-I^{\mathrm{agg}}_{\varepsilon,W,X}.
$$

cutoff-zero baseline を使えばさらに

$$
G_{\varepsilon,W,X}
=G_{\varepsilon,W,0}-I^{\mathrm{agg}}_{\varepsilon,W,X}.
$$

これが CS25 で最も重要な exact cancellation identity である。

ここでは `CommonEnergy` が完全に消えることを theorem 名・コメントの双方で明示する。

---

## 8. Canonical CS24 decomposition の再解釈

CS25 では CS24 mass/remainder を common/interaction で書き直す。

$$
M^{\mathrm{can}}
=\frac12\bigl(C^{\mathrm{agg}}+I^{\mathrm{agg}}\bigr).
$$

$$
R^{\mathrm{can}}
=G_{\varepsilon,W,0}
+\frac12\bigl(C^{\mathrm{agg}}-I^{\mathrm{agg}}\bigr).
$$

差を取ると common carrier は exact に消え、

$$
R^{\mathrm{can}}-M^{\mathrm{can}}
=G_{\varepsilon,W,0}-I^{\mathrm{agg}}
=G_{\varepsilon,W,X}.
$$

この identity により、canonical remainder の cofinal smallness は target deficit に必要な条件より強い可能性があることを source structure 上で説明できる。

可能なら generic real algebra counterexample も追加する。

目的は「canonical remainder smallness が一般には direct contact の必要条件ではない」ことを、RH source に偽 counterexample を入れず純代数モデルで示すこと。

一例として `G0 = 0`, `C = 2`, `I = 0` なら direct deficit `G0 - I = 0` だが canonical remainder `G0 + (C-I)/2 = 1` となる。

これは source theorem ではなく strength countermodel として明示する。

---

## 9. New provider frontier: interaction reach, not whole-energy ordering

CS25 後の真正の finite source target は

$$
G_{\varepsilon,W,X}\le\eta
$$

と

$$
I^{\mathrm{agg}}_{\varepsilon,W,X}
\ge G_{\varepsilon,W,0}-\eta
$$

の exact 同値になる。

ただし新しい predicate を作ること自体を成果としない。

成果と認めるのは、complete source が `common carrier + interaction` に分解され、radial deficit から common carrier が exact に消えることまで。

独立 provider がなければ named gap は例えば

`PascalCenteredXiPrimeSideAggregateInteractionReachGap.noIndependentCofinalInteractionReachProvider`

として残す。

---

## 10. Why this matters for CF2D / ThreeElement

CS18 ですでに `Complex.normSq ↔ Vec.q2` と complex multiplication ↔ `Vec.star` は exact bridge 済み。

今回の

$$
|Z\pm1|^2=|Z|^2+1\pm2\operatorname{Re}Z
$$

は ThreeElement の

`Common / Core mass ± Interaction beam`

そのものとして読むことができる。

ただし CS25 の mainline 実装では CF2D import を増やす必要はない。まず通常の complex / real algebra で common-carrier cancellation を確定する。

CS25 完了後、必要なら既存 CS18 bridge で representation theorem を追加する。

重要な見方は、plus/minus whole の positivity そのものではなく、**両 whole に共有される mass は prime source difference では消え、残る interaction が arithmetic sourceを運ぶ**という点。

これは CS17 の ordering route と CS24 の signed-mass route の双方を統一する。

---

## 11. Firewalls

CS25 で禁止するもの:

- `InteractionDensity ≥ 0` の仮定・主張
- `InteractionEnergy ≥ 0` の仮定・主張
- individual prime ray ordering
- aggregate ordering の provider 化
- canonical remainder smallness の provider 化
- zero-side fixed defect の符号を interaction provider に使うこと
- RH-equivalent theorem を source provider に使うこと
- infinite prime sum / infinite ray / Euler product
- sum-integral infinite exchange
- height `T → ∞`
- endpoint sign / RH conclusion

---

## 12. CS25 acceptance criteria

Green となるための最低条件:

1. normalized plus/minus density を ray state `Z ± 1` の `normSq` と exact に同定。
2. common density / interaction density を定義。
3. plus/minus density の `Common ± Interaction` 分解。
4. finite ray common / interaction energies と exact energy decomposition。
5. aggregate common / interaction energies と exact decomposition。
6. aggregate interaction が finite mode sum の2倍であること。
7. normalized prime contribution が aggregate interaction divided by `π` であること。
8. complete source が correction-only source plus interaction/π と exact に分解されること。
9. radial deficit が `G(0) - AggregateInteraction` と exact に縮約されること。
10. CS24 canonical mass/remainder 内の common carrier が差で exact cancellation すること。
11. independent interaction-reach provider が無いなら named gap として明示。
12. 新規 `sorry` / `axiom` / `native_decide` なし。
13. `lake env lean`、`lake build DkMath.RH`、`git diff --check` 成功。

Green-B となる想定:

- 1–10 が閉じる。
- 11 の independent provider は未証明。

---

## 13. Expected next branch after CS25

CS25 で common carrier cancellation が閉じた場合、次 route は interaction 自体をどう source-derived に下から制御するかを選ぶ。

優先候補:

1. **block-local interaction accumulation**
   - cumulative whole energy ではなく finite block の interaction increment を使う。
   - oscillation / cancellation を残したまま good cutoff を探す。

2. **phase / geometric endpoint reduction**
   - CS16 の four-endpoint signed numeratorへ戻る。
   - interaction が各 prime ray の endpoint phase 4項だけで表現できる利点を使う。

3. **CF2D interaction-beam representation audit**
   - CS18 bridge を使い、aggregate interaction を `ThreeElement` interaction beam と exact に同定。
   - collision theorem を使うのではなく、interaction accumulation に既存 generic invariant が使えるかだけを監査。

ここでも provider を仮定して進めない。

---

## 14. Research interpretation

CS24 は「positive whole energy を一つ mass として取る」ことに成功した。しかし CS25 の仮説は、そこからさらに一段深く、plus/minus の whole に共通する carrier を消去すれば prime arithmetic source の本体は interaction だけになる、というもの。

もし Lean がこれを exact に閉じれば、研究線は

`prime powers → geometric rays → q2 whole energies → common carrier cancellation → interaction → radial contact`

と一本化される。

これは CF2D / ThreeElement が外から持ち込まれた説明ではなく、finite prime-side source の polarization を完全に展開した結果として再出現した構造である。

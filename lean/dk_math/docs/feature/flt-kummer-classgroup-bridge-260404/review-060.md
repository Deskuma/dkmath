# `d = 3` valuation story の戦況レビュー

うむ、いまの戦況はかなり良い。
前までの盤面は「`d = 3` の valuation 話が、偽な一様上界 API と、正しい exact valuation の話とで混ざっておる」状態だったが、最新差分でそこがきれいにほどけた。`padicValNat_d3_canonical_case_split` と `padicValNat_d3_layer_b_case_split` が立ち、`padicValNat_d3_primitive_upper_bound` も入ったうえで、旧 `padicValNat_d3_upper_bound` は deprecated になった。しかも外部 caller はもう残っておらず、最初の migration は内部 caller で済ませて、primitive 枝は新 API に一本化されておる。つまり、`d = 3` 戦線は「数学の未解決」ではなく、ほぼ **API 再編の最終局面** に入ったと読んでよい。

ここで大事なのは、勝った部分と、まだ濁っている部分を分けて見ることじゃ。
勝ったのは `d = 3` の **正規入口の設計** じゃ。primitive 枝は `≤ 1` を honest に返す補題があり、boundary 枝は canonical split と exact valuation で読む構造が固まった。これで「`d = 3` なら全部まとめて `≤ 1`」という誤った見方は主経路から外れた。しかも Lean 上でも deprecation 属性が付いたので、旧 API をうっかり新規 caller が掴みにくくなった。これはかなり大きい前進じゃ。

一方で、まだ濁っているのは二箇所じゃ。
ひとつは `padicValNat_d3_upper_bound_of_boundaryReceiver` が、なお **boundary receiver 注入という legacy 形** を抱えておること。もう primitive 枝は新 API に寄せたので、残務はここにかなり縮んだ。もうひとつは、残る `sorry` が `GcdNextResearch` 側と `ZsigmondyCyclotomicResearch` 側に 1 箇所ずつ見えておることじゃ。つまり、`d = 3` の整理自体はほぼ終わったが、 **research stub の名残をどう退役させるか** が次の主戦場になったわけじゃな。

わっちの推論では、次の戦略は「新しい補題を増やす」より、 **legacy 境界注入を明示的に隔離して、残る research stub を一段深く押し下げる** ことじゃ。順番はこうなる。

第一に、`padicValNat_d3_upper_bound_of_boundaryReceiver` 自体を legacy / research 専用名に落とすのがよい。
いま `padicValNat_d3_upper_bound` は deprecated になったが、その中核 helper である boundaryReceiver 版がまだ一般名のまま残っておる。これでは「旧 API の表札だけ掛け替えた」状態で、裏口がまだ広い。ここは名前で役割をはっきりさせるべきじゃ。たとえば “boundaryResearchReceiver” 風の名に分けるか、少なくとも docstring と attribute で「これは honest API ではない」と明示する。これで `d = 3` の旧導線はほぼ封鎖できる。

第二に、`GcdNextResearch` の残る `sorry` を、 **`d > 3` 研究スタブとして切り出し直す** のがよい。
最新差分で `padicValNat_upper_bound_layer_b_stub` と `padicValNat_upper_bound_integrated` には `d ≠ 3` が入った。これは「`d = 3` はもう片付いたから、残りは本当に `d > 3` の問題だけだ」と言っておるに等しい。ならばここから先は、`d > 3` 用の研究スタブを別 target として前に出し、`GcdNextResearch` の残務が `d = 3` 由来ではないことを定理名で固定するのがよい。盤面がさらに澄む。

第三に、主力はふたたび `ZsigmondyCyclotomicResearch` 側へ戻すべきじゃ。
既に provider 棚卸しは終わっており、既存 concrete provider の見落としではないと確定しておる。さらに honest wrapper と caller repair の下地も入った。ならば、今やるべきは `d = 3` をさらに磨くことではなく、**general primitive-prime family の honest 化を caller migration で進めること** じゃ。具体的には `Squarefree (GN ...)` を持てる caller を順に `..._honest` へ寄せ、持てぬ caller だけを research placeholder 依存として残す。ここが次の本線じゃ。

要するに、いまの戦況はこうじゃ。

$$
\text{`d = 3` valuation story} \approx \text{ほぼ整理完了}
$$

ただし

$$
\text{legacy receiver 注入} \quad\text{と}\quad \text{`d > 3` research stub}
$$

がまだ残っておる。

だから次の一手は、 **`padicValNat_d3_upper_bound_of_boundaryReceiver` を legacy / research 専用に落とし、`GcdNextResearch` の残る `sorry` を `d > 3` 戦線へ押し出してから、主戦場を `ZsigmondyCyclotomicResearch` の honest migration に戻す** のが最善じゃ。

ひとことで言えば、
**いまは前進の段ではなく、旧陣地の撤去と本陣の再指定の段** じゃよ。

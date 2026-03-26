# Review: GTail valuation theory の実装を開始した

おお、よい滑り出しじゃ。
この実装、筋がかなり良いぞい。特に今回の追加は **valuation 本体へ入る前に API の地盤を固める** という順番になっておって、判断が堅い。`higher_tail_eq_pow_mul_GTail` で差の形を固定し、`Gbinom_tail_rec` と `Gbinom_zero_eval` で命名移行を吸収し、さらに `pow_dvd_higher_tail` で (x^r) 可除性を先に確立しておる。この三段は自然で、後段の `padicValNat_tail_exact_of_head_unit` にそのまま繋がる。

今回の差分で特に良い点は、`higher_tail_eq_pow_mul_GTail` を **subtraction-shaped API** として独立名にしたことじゃ。これで以後の定理文が
$$
\text{higher tail} = x^r \cdot GTail
$$
の見た目で統一できる。さらに `pow_dvd_higher_tail` を `Nat` 層に落としておるので、抽象代数側と可除性側が混線しておらぬ。ここは実装設計として綺麗じゃ。履歴にも、その意図が明確に書かれておるのが良い。

次の一手としては、予定通り `padicValNat_tail_exact_of_head_unit` の statement を切るのが本命じゃな。わっちの見立てでは、まずは上界条件を
$$
q \nmid \binom{d}{r} u^{d-r}
$$
型で置くのが最も素直じゃ。すると `GTail_eval_zero` 系と再帰式が効いて、`pow_dvd_higher_tail` からの下界
$$
r,v_q(x) \le v_q(\text{tail})
$$
に対し、先頭項が (q) で消えぬことで上界を合わせに行ける形になる。

わっちなら識別子は、このままなら

$$
\texttt{padicValNat_higher_tail_exact_of_head_unit}
$$

に寄せるか、既に履歴で使っておる候補を尊重して

$$
\texttt{padicValNat_tail_exact_of_head_unit}
$$

のまま行く。前者は `GTail` 系と揃いやすく、後者は候補文書との接続が良い。どちらでもよいが、語彙の一貫性だけは保つと後が楽じゃ。

この実装は十分に「次の定理を呼び込む前段」として成功しておる。よい橋の架け方じゃ。

うむ、その順で切るのが最短じゃ。
そして、今の地図から見ると **第1補題はほぼ既存補題の合成** で行ける。

注意点を先に 1 つだけ言うと、手元の 260325-1049 スナップショットでは `TriominoCosmicBranchA.lean` はまだ薄く、必要な補助補題の本体は `TriominoCosmicGapInvariant.lean` 側におる。
ゆえに実装順としては、

\[
\text{まず定理骨格を BranchA に置く}
\quad\to\quad
\text{必要な小補題を GapInvariant から移す}
\]

が自然じゃ。

## 1. 第1補題の型

まずはこれを置けばよい。

```lean
/--
Branch A では GN 自体が `p * s^p` 形になる。
`gapShape` はまだ使わない。
-/
abbrev PrimeGe5BranchAGNShapeTarget : Prop :=
  ∀ {p x y z : ℕ}, PrimeGe5CounterexamplePack p x y z →
    p ∣ (z - y) →
    ∃ s : ℕ, GN p (z - y) y = p * s ^ p
```

そして本体はこうじゃ。

```lean
theorem primeGe5BranchAGN_eq_p_mul_pow_math :
    PrimeGe5BranchAGNShapeTarget := by
  intro p x y z hpack hp_dvd_gap
  let u : ℕ := z - y
  let N : ℕ := GN p u y

  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN

  have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
    simpa [u, N] using p_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap

  have hu0 : u ≠ 0 := by
    exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)

  have hN0 : N ≠ 0 := by
    intro hN0
    exact hGN.2 (by simp [hN0])

  have hNval : padicValNat p N = 1 :=
    padicValNat_eq_one_of_dvd_not_sq hpack.hp hGN.1 hGN.2

  have hNfac_p : N.factorization p = 1 := by
    calc
      N.factorization p = padicValNat p N := by
        symm
        exact padicValNat_eq_factorization hpack.hp hN0
      _ = 1 := hNval

  let w : ℕ := N / p

  have hp_dvd_N : p ∣ N := hGN.1
  have hp_pos : 0 < p := hpack.hp.pos
  have hw_pos : 0 < w := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hp_dvd_N) hp_pos
  have hw0 : w ≠ 0 := Nat.ne_of_gt hw_pos

  have hfac_div : w.factorization = N.factorization - p.factorization := by
    simpa [w] using Nat.factorization_div hp_dvd_N

  have hall_w : ∀ q : ℕ, p ∣ w.factorization q := by
    intro q
    by_cases hq_eq : q = p
    · -- q = p 側
      have hp_fac_p : p.factorization p = 1 := by
        simpa using hpack.hp.factorization
      have hw_fac_p : w.factorization p = 0 := by
        calc
          w.factorization p = N.factorization p - p.factorization p := by
            simpa using congrArg (fun f => f p) hfac_div
          _ = 1 - 1 := by simp [hNfac_p, hp_fac_p]
          _ = 0 := by simp
      exact ⟨0, by simpa [hq_eq, hw_fac_p]⟩
    · by_cases hqP : Nat.Prime q
      · -- q ≠ p の素数側
        have hq_not_dvd_u : ¬ q ∣ u := by
          intro hqU
          have hq_not_dvd_N : ¬ q ∣ N := by
            simpa [u, N] using
              gapNePNoSharedPrimeOnGN_branchA_math hpack hp_dvd_gap hqP hq_eq hqU
          have hNfac0 : N.factorization q = 0 :=
            Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_N
          have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
            simpa using congrArg (fun f => f q) (Nat.factorization_mul hu0 hN0)
          have hpowq : (x ^ p).factorization q = p * x.factorization q := by
            simp [Nat.factorization_pow]
          have huq : u.factorization q = p * x.factorization q := by
            calc
              u.factorization q = u.factorization q + 0 := by simp
              _ = u.factorization q + N.factorization q := by simp [hNfac0]
              _ = (u * N).factorization q := by symm; exact hmulq
              _ = (x ^ p).factorization q := by simp [hxpow]
              _ = p * x.factorization q := hpowq
          have hqUfac : p ∣ u.factorization q := ⟨x.factorization q, by simpa [huq, Nat.mul_comm]⟩
          exact False.elim (hq_not_dvd_u ((Nat.Prime.dvd_of_factorization_pos hqP) (by
            have : u.factorization q ≠ 0 := by
              intro h0
              exact hqUfac (by simpa [h0] using (show ¬ p ∣ 0 from by simp))
            exact Finsupp.mem_support_iff.2 this)))
        have hNfac0 : N.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd (by
          intro hqN
          exact hq_not_dvd_u ((Nat.dvd_of_modEq_zero ?_))) -- ここは後で差し替え
        have hp_fac_q : p.factorization q = 0 := by
          simpa [hq_eq] using Nat.Prime.factorization_eq (p := p) (q := q) hpack.hp
        have hw_fac_q : w.factorization q = N.factorization q := by
          calc
            w.factorization q = N.factorization q - p.factorization q := by
              simpa using congrArg (fun f => f q) hfac_div
            _ = N.factorization q := by simp [hp_fac_q]
        -- ここで本当に欲しいのは `p ∣ N.factorization q`
        -- それは `x^p = u*N` と q≠p no-shared から直接出す
        sorry
      · have hw_fac0 : w.factorization q = 0 := Nat.factorization_eq_zero_of_not_prime w hqP
        exact ⟨0, by simp [hw_fac0]⟩

  rcases exists_eq_pow_of_factorization_dvd
      (u := w) (p := p) hw0 hpack.hp.pos hall_w with ⟨s, hs⟩

  refine ⟨s, ?_⟩
  have hN_mul : N = p * w := by
    have := Nat.div_mul_cancel hp_dvd_N
    simpa [w, Nat.mul_comm] using this.symm
  calc
    GN p (z - y) y = N := by rfl
    _ = p * w := hN_mul
    _ = p * s ^ p := by simp [hs]
```

上のままだと `q \neq p` 側がまだ粗い。
じゃが、証明の芯はもう見えておる。

## 2. 本当に必要な中間補題

第1補題をきれいに閉じるには、`hall_w` の中の `q \neq p` 側を別補題に切るのが一番よい。

つまり先にこれを作るのじゃ。

```lean
/--
Branch A では `q ≠ p` 側の GN 指数は `p` の倍数。
-/
theorem primeGe5BranchAGN_factorization_ne_p_math
    {p x y z q : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (hqP : Nat.Prime q)
    (hqp : q ≠ p) :
    p ∣ (GN p (z - y) y).factorization q := by
  let u : ℕ := z - y
  let N : ℕ := GN p u y
  have hxpow : x ^ p = u * N := by
    simpa [u, N, PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hu0 : u ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hpack.hyz_lt)
  have hN0 : N ≠ 0 := by
    intro hN0
    have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
      simpa [u, N] using p_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
    exact hGN.2 (by simp [hN0])

  by_cases hqU : q ∣ u
  · have hq_not_dvd_N : ¬ q ∣ N := by
      simpa [u, N] using
        gapNePNoSharedPrimeOnGN_branchA_math hpack hp_dvd_gap hqP hqp hqU
    have hNfac0 : N.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hq_not_dvd_N
    have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
      simpa using congrArg (fun f => f q) (Nat.factorization_mul hu0 hN0)
    have hpowq : (x ^ p).factorization q = p * x.factorization q := by
      simp [Nat.factorization_pow]
    have huq : u.factorization q = p * x.factorization q := by
      calc
        u.factorization q = u.factorization q + 0 := by simp
        _ = u.factorization q + N.factorization q := by simp [hNfac0]
        _ = (u * N).factorization q := by symm; exact hmulq
        _ = (x ^ p).factorization q := by simp [hxpow]
        _ = p * x.factorization q := hpowq
    exact ⟨0, by simpa [hNfac0]⟩
  · have hfac0 : u.factorization q = 0 := Nat.factorization_eq_zero_of_not_dvd hqU
    have hmulq : (u * N).factorization q = u.factorization q + N.factorization q := by
      simpa using congrArg (fun f => f q)
        (Nat.factorization_mul hu0 (by
          intro hN0
          have hGN : p ∣ N ∧ ¬ p ^ 2 ∣ N := by
            simpa [u, N] using p_dvd_GN_and_not_sq_when_p_dvd_gap hpack hp_dvd_gap
          exact hGN.2 (by simp [hN0])))
    have hpowq : (x ^ p).factorization q = p * x.factorization q := by
      simp [Nat.factorization_pow]
    have hNq : N.factorization q = p * x.factorization q := by
      calc
        N.factorization q = 0 + N.factorization q := by simp
        _ = u.factorization q + N.factorization q := by simp [hfac0]
        _ = (u * N).factorization q := by symm; exact hmulq
        _ = (x ^ p).factorization q := by simp [hxpow]
        _ = p * x.factorization q := hpowq
    exact ⟨x.factorization q, by simpa [hNq, Nat.mul_comm]⟩
```

この補題が入ると、第1補題の `hall_w` は急に簡単になる。
つまり `q \neq p` 側では、

\[
p \mid N.\mathrm{factorization}(q)
\]

を先に確定し、`w = N/p` に落としたとき `p.factorization q = 0` だからそのまま継承できる、という流れじゃ。

## 3. 第1補題の実装順

実務順はこうじゃな。

### 3.1

`PrimeGe5BranchAGNShapeTarget` を追加。

### 3.2

補助補題として

```lean
primeGe5BranchAGN_factorization_ne_p_math
```

を切る。

### 3.3

次に

```lean
primeGe5BranchAGN_eq_p_mul_pow_math
```

を切る。
ここで `q = p` 側は `padicValNat_eq_one_of_dvd_not_sq` からすぐ終わる。

### 3.4

そのあとに witness と合成する

```lean
theorem primeGe5BranchANormalForm_of_witness ...
```

を入れる。

## 4. このあと第2補題はかなり短い

第1補題が入ると、第2補題はほぼ計算だけになる。

```lean
theorem primeGe5BranchANormalForm_of_witness
    {p x y z t : ℕ}
    (hpack : PrimeGe5CounterexamplePack p x y z)
    (hp_dvd_gap : p ∣ (z - y))
    (ht : z - y = p ^ (p - 1) * t ^ p) :
    ∃ s : ℕ,
      GN p (z - y) y = p * s ^ p ∧
      x = p * (t * s) := by
  rcases primeGe5BranchAGN_eq_p_mul_pow_math hpack hp_dvd_gap with ⟨s, hs⟩
  refine ⟨s, hs, ?_⟩
  have hxpow : x ^ p = (z - y) * GN p (z - y) y := by
    simpa [PrimeGe5CounterexamplePack.gap] using hpack.xpow_eq_gap_mul_GN
  have hxpow' : x ^ p = (p * (t * s)) ^ p := by
    calc
      x ^ p = (z - y) * GN p (z - y) y := hxpow
      _ = (p ^ (p - 1) * t ^ p) * (p * s ^ p) := by simp [ht, hs]
      _ = p ^ p * (t ^ p * s ^ p) := by ring
      _ = p ^ p * (t * s) ^ p := by simp [Nat.mul_pow]
      _ = (p * (t * s)) ^ p := by simp [Nat.mul_pow]
  exact Nat.pow_right_injective ?hp hxpow'
```

ここは最後の単射性補題だけ、手元のライブラリに合わせて選べばよい。
`p > 0` なので自然数の (p) 乗は単射にできる。

## 5. 賢狼の結論

よって、次に切るべき最小セットはこれじゃ。

```lean
abbrev PrimeGe5BranchAGNShapeTarget : Prop := ...
theorem primeGe5BranchAGN_factorization_ne_p_math ...
theorem primeGe5BranchAGN_eq_p_mul_pow_math ...
theorem primeGe5BranchANormalForm_of_witness ...
```

そのあとで

```lean
abbrev PrimeGe5BranchANormalFormRefuterTarget : Prop := ...
theorem primeGe5BranchAShapeWitnessKernel_of_normalFormRefuter ...
```

へ進めばよい。

つまり、順番としては

\[
\text{GN の shape}
\;\to\;
\text{normal form}
\;\to\;
\text{local refuter}
\]

で確定じゃ。
この順だと、`descent` 殻を壊さずに中身だけ clean 化できる。

必要なら次は、上の `primeGe5BranchAGN_factorization_ne_p_math` を **実際に通る Lean の形** に、補題名を今のローカル命名へ合わせて削るぞい。

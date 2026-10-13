# findings-011 — primitive prime-power allocations

instruction-011 と full-sieve actual membership / coprimality / size / branch fields、mod42 divisor guard、same-r mod5 exclusion、gate010 proof structureを確認。開始時変更なし。

nを上から制限せず、13∤rなら Euclid でr∣2、13∣rなら actual complementary t に13が割らず Euclid でt∣2を導く。後者は M=r*t≤2*r と343*r^7<Mで矛盾。n=0も含めて試す。最終familyに global M bound を持ち込まない。

## Calibration

Initial calibration exit0。n=0を含む定理のまま成功し、追加positivity条件不要。Euclidは Nat.Coprime.dvd_mul_right / pow_right と Nat.Prime.coprime_iff_not_dvd を再利用する。全kのmod42/mod5は小さいbase congruenceの冪と積で証明。固定上限なし。

## Final outcome

Outcome A。focused build exit0 (9091jobs)、final tests exit0、warning/errorなし。Two production exports plus injectivity/countermodel have only standard three axioms, no sorryAx.

Mechanism is unbounded in n/k, with actual membership/cop/complement retained. k0 recovers9653618, k1/k2 are checked. r13,n10 demonstrates coprimality cannot be discarded. No global core upper bound or source existence premise.

Optional cheap subfamily work remains unimplemented. Existing files unchanged, no Git mutation. Compact evidence is provenance-labelled.

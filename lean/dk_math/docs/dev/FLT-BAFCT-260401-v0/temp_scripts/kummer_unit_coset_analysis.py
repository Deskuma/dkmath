#!/usr/bin/env python3
"""
Kummer p-th power residue 制約の精密版:
Z[ζ_p] の単数群の影響を考慮する。

Z[ζ_5] の単数群: <ζ_5> × <ε>  (ε = (1+√5)/2 golden ratio 関連)
ζ_5 → ω (mod q) への射影
ε → ε̄ (mod q) への射影

制約: (ω^j₀ - ω^j)·y / ε̄ が p 乗剰余 ↔ (ω^j₀ - ω^j) が {unit image} · {p乗冪} に属する

{p乗冪} は (Z/qZ)* の index p の部分群。
{unit image} = <ω> × <ε̄> の像。

(Z/qZ)* が巡回群 C_{q-1} で、p乗冪は C_{(q-1)/p}。
ω は位数 p の元 → ω ∈ C_{q-1} の部分群 C_p。
C_p と C_{(q-1)/p} の積が C_{q-1} 全体かどうか？

gcd(p, (q-1)/p) = 1 (q-1 = p·m, gcd(p,m) で場合分け) なら |C_p · C_{(q-1)/p}| = p · m = q-1。
つまり <ω> · {p乗冪} = (Z/qZ)* → 制約が自明に満たされる！

これは p が q-1 をちょうど 1 回割る場合（p ∤ m = (q-1)/p）。
p=5, q=11: q-1=10, m=2, gcd(5,2)=1 → 自明！
p=5, q=31: q-1=30, m=6, gcd(5,6)=1 → 自明！
p=5, q=41: q-1=40, m=8, gcd(5,8)=1 → 自明！

一般に p ≡ 1 mod p で p^2 ∤ (q-1) なら常に自明。
p^2 | (q-1) のときのみ非自明な制約が残る。
"""

def analysis():
    p = 5
    print(f"===== 単数群考慮版 p-乗冪剰余制約 =====")
    print()
    
    # Find primes q ≡ 1 (mod p)
    primes_1modp = []
    for q in range(p + 1, 500):
        if (q - 1) % p == 0 and all(q % d != 0 for d in range(2, int(q**0.5) + 1)):
            primes_1modp.append(q)
    
    print(f"Primes q ≡ 1 (mod {p}), q < 500:")
    for q in primes_1modp[:20]:
        m = (q - 1) // p
        v_p_m = 0
        temp = m
        while temp % p == 0:
            v_p_m += 1
            temp //= p
        
        trivial = (v_p_m == 0)  # gcd(p, m) = 1
        status = "TRIVIAL (ω coset covers all)" if trivial else f"NON-TRIVIAL (p^{v_p_m+1} | q-1)"
        print(f"  q={q:4d}: q-1={q-1:4d}, m=(q-1)/p={m:3d}, v_p(m)={v_p_m}  {status}")
    
    # Find the FIRST non-trivial case
    print(f"\nNon-trivial primes (p^2 | q-1):")
    non_trivial = [q for q in primes_1modp if ((q - 1) // p) % p == 0]
    for q in non_trivial[:10]:
        m = (q - 1) // p
        v = 0
        temp = q - 1
        while temp % p == 0:
            v += 1
            temp //= p
        print(f"  q={q}: q-1={q-1}, v_p(q-1)={v}")
    
    if not non_trivial:
        print("  None found in range!")
    
    print(f"\n{'='*60}")
    print(f"SECOND ANALYSIS: ε (Golden ratio unit) の影響")
    print(f"{'='*60}")
    
    # For p=5: Z[ζ_5] = Z[ζ] where ζ = e^{2πi/5}
    # Fundamental unit: ε = -ζ^2 - ζ^3 = (1 + √5)/2 in real quadratic subfield
    # Actually Z[ζ_5] has 2 fundamental units (rank = (p-1)/2 - 1 = 1 for p=5)
    # Unit group: ±ζ^k · ε^n for k=0,...,4, n ∈ Z
    
    # The minimal polynomial of ε = (1+√5)/2 over Q: x^2 - x - 1
    # In Z[ζ_5]: ε = -ζ^2 - ζ^3
    # (This follows from: 2cos(2π/5) = (√5-1)/2 = ε - 1, etc.)
    
    # Reduce mod q: we need to know ω = ζ mod q (chosen root of Φ_5)
    # Then ε̄ = -ω^2 - ω^3 mod q
    
    for q in primes_1modp[:15]:
        # Find primitive 5th root ω
        omega = None
        for a in range(2, q):
            if pow(a, (q-1)//p, q) != 1 and pow(a, q-1, q) == 1:
                r = pow(a, (q-1)//p, q)
                if pow(r, p, q) == 1 and r != 1:
                    omega = r
                    break
        
        if omega is None:
            continue
        
        # ε̄ = -ω^2 - ω^3 mod q  
        eps_bar = (-pow(omega, 2, q) - pow(omega, 3, q)) % q
        
        # p-th power residues
        pth_powers = set()
        for a in range(q):
            pth_powers.add(pow(a, p, q))
        nonzero_pth = pth_powers - {0}
        
        # Unit image in (Z/qZ)*: <ω, ε̄, -1>
        unit_image = set()
        for k in range(p):
            for sign in [1, -1]:
                # ε̄ has some order ℓ in (Z/qZ)*
                # enumerate ε̄^n · ω^k · sign for n = 0,...,q-2
                eps_power = 1
                for n in range(q - 1):
                    val = (sign * pow(omega, k, q) * eps_power) % q
                    if val != 0:
                        unit_image.add(val)
                    eps_power = (eps_power * eps_bar) % q
        
        # Product: unit_image · pth_powers
        product_set = set()
        for u in unit_image:
            for r in nonzero_pth:
                product_set.add((u * r) % q)
        
        covers_all = product_set == set(range(1, q))
        
        # Order of ε̄
        eps_order = 1
        temp = eps_bar
        while temp != 1:
            temp = (temp * eps_bar) % q
            eps_order += 1
            if eps_order > q:
                eps_order = -1
                break
        
        m = (q - 1) // p
        
        print(f"\n  q={q}: ω={omega}, ε̄={eps_bar}, ord(ε̄)={eps_order}")
        print(f"    |{p}乗冪| = {len(nonzero_pth)}, |unit image| = {len(unit_image)}")
        print(f"    |unit · {p}乗冪| = {len(product_set)}, |(Z/{q}Z)*| = {q-1}")
        print(f"    Covers all: {covers_all}")
        
        if not covers_all:
            print(f"    *** NON-TRIVIAL CONSTRAINT EXISTS! ***")
            missing = set(range(1, q)) - product_set
            print(f"    Missing: {sorted(missing)[:20]}")


    print(f"\n\n{'='*60}")
    print(f"CONCLUSION")
    print(f"{'='*60}")
    print(f"")
    print(f"For regular prime p=5:")
    print(f"  - Single-prime Kummer constraint is TRIVIAL when p^2 ∤ (q-1)")
    print(f"  - Most primes q ≡ 1 (mod 5) have p^2 ∤ (q-1): constraint is vacuous")
    print(f"  - For p^2 | (q-1) primes: non-trivial constraint MAY exist")
    print(f"  - BUT: even non-trivial constraints use ONE prime at a time")
    print(f"  - Kummer's ACTUAL argument combines multiple primes + unit equations")
    print(f"")
    print(f"BOTTOM LINE:")
    print(f"  GNReducedGap cannot be proven by single-prime mod-q analysis.")
    print(f"  The proof requires algebraic number theory (Z[ζ_p]) or equivalent.")
    print(f"  This is consistent with §21 circularity finding.")


if __name__ == '__main__':
    analysis()

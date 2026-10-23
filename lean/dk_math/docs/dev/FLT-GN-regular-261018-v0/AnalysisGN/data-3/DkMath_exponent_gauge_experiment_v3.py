#!/usr/bin/env python3
"""DkMath: exponent-gauge numerical experiment v3 (exact integers, stdlib).

Reproduce: python3 DkMath_exponent_gauge_experiment_v3.py
By design this is NOT a proof of Fermat's Last Theorem.
"""
import argparse
import csv
import sys
from collections import Counter
from math import gcd, prod, isqrt
from pathlib import Path
if hasattr(sys,'set_int_max_str_digits'):
    sys.set_int_max_str_digits(100000)


def primes_through(B):
    a=bytearray(b'\x01')*(B+1)
    a[0:2]=b'\x00\x00'
    for p in range(2,isqrt(B)+1):
        if a[p]:a[p*p::p]=b'\x00'*((B-p*p)//p+1)
    return [p for p in range(2,B+1) if a[p]]


def val(a,p):
    assert a>0 and p>1
    k=0
    while a%p==0:a//=p;k+=1
    return k


def R(n,x,y):
    assert n>=1 and x>y>0
    a=x**n-y**n
    assert a%(x-y)==0
    return a//(x-y)


def order_if_divides_n(x,y,q,n):
    assert y%q and q>1
    a=(x%q)*pow(y,-1,q)%q
    if pow(a,n,q)!=1:return None
    return next(d for d in range(1,n+1) if n%d==0 and pow(a,d,q)==1)


def write_csv(path,rows,fields):
    with path.open('w',newline='',encoding='utf-8') as f:
        w=csv.DictWriter(f,fieldnames=fields);w.writeheader();w.writerows(rows)


def initial_sweep(primes,bound,max_degree,out):
    pairs=[(x,y) for x in range(2,bound+1) for y in range(1,x) if gcd(x,y)==1]
    stats=[];rare=[]
    for n in range(3,max_degree+1):
        counts=Counter()
        for x,y in pairs:
            r=R(n,x,y);s=x+y;g=x-y
            d=s**(n-1)-r;borrow=x*y*R(n-2,x,y)
            assert d>0 and r+borrow==s*R(n-1,x,y)
            assert r+d==s**(n-1)
            assert gcd(r,g)==gcd(g,n)
            assert gcd(r,R(n-1,x,y))==1
            assert gcd(r,R(n-2,x,y))==(1 if n%2 else s)
            assert gcd(r,d)==(1 if n%2 else s*gcd(n//2,s**(n-2)))
            certified=False;primitive=False;high_primitive=False
            for q in primes:
                if r%q:continue
                v=val(r,q);vg=val(g,q) if g%q==0 else 0
                if (v+vg)%n:certified=True
                if x%q and y%q and order_if_divides_n(x,y,q,n)==n:
                    primitive=True
                    if v>=2:
                        high_primitive=True
                        if len(rare)<350:
                            rare.append(dict(n=n,x=x,y=y,q=q,order=n,v_q_R=v,
                                             v_q_gap=vg,v_q_full=v+vg,R=str(r)))
            counts['certified']+=int(certified)
            counts['primitive']+=int(primitive)
            counts['high']+=int(high_primitive)
        stats.append(dict(n=n,pairs=len(pairs),obstructed_by_q_le_cap=counts['certified'],
                          not_certified_by_small_primes=len(pairs)-counts['certified'],
                          primitive_prime_detected_pairs=counts['primitive'],
                          primitive_valuation_ge_2_pairs=counts['high']))
    write_csv(out/'DkMath_gauge_v3_sweep.csv',stats,list(stats[0]))
    write_csv(out/'DkMath_gauge_v3_primitive_rare.csv',rare,
              ['n','x','y','q','order','v_q_R','v_q_gap','v_q_full','R'])
    return stats,rare


def targeted(primes,ymax,out):
    rows=[]
    for p in (3,5,7,11,13,17):
        g=p**(p-1)
        for y in range(1,ymax+1):
            if gcd(y,g)!=1:continue
            x=g+y;r=R(p,x,y);full=g*r
            assert val(g,p)==p-1 and val(r,p)==1 and val(full,p)==p
            hit=None
            for q in primes:
                if q==p or full%q:continue
                v=val(full,q)
                if v%p:
                    o=order_if_divides_n(x,y,q,p)
                    assert o==p and q%p==1
                    hit=(q,v);break
            rows.append(dict(p=p,x=str(x),y=y,g=str(g),vp_g=p-1,vp_R=1,vp_total=p,
                first_other_obstruction_q_le_cap=hit[0] if hit else '',
                first_other_obstruction_v=hit[1] if hit else '',
                total_digits=len(str(full))))
    write_csv(out/'DkMath_gauge_v3_targeted.csv',rows,list(rows[0]))
    return rows


def lift_root_exact(p,q):
    assert (q-1)%p==0 and q!=p
    a=next(a for a in range(2,q) if pow(a,p,q)==1)
    assert order_if_divides_n(a,1,q,p)==p
    mod=q
    for k in range(1,p):
        nxt=mod*q
        a=next(a+t*mod for t in range(q) if pow(a+t*mod,p,nxt)==1)
        mod=nxt
    assert pow(a,p,mod)==1
    a=next(a+t*mod for t in range(q) if pow(a+t*mod,p,mod*q)!=1)
    assert val(a**p-1,q)==p
    return a,mod*q


def crt(a,m,b,n):
    assert gcd(m,n)==1
    x=(a+m*((b-a)*pow(m,-1,n)%n))%(m*n)
    assert x%m==a%m and x%n==b%n
    return x,m*n


def simultaneous(primes,out):
    rows=[]
    for p,qs in ((3,(7,13)),(5,(11,31,41)),(7,(29,43,71)),
                 (11,(23,67)),(13,(53,)),(17,(103,))):
        x=1+p**(p-1);mod=p**p
        for q in qs:
            assert q in primes
            b,m=lift_root_exact(p,q)
            x,mod=crt(x,mod,b,m)
        if x<=1:x+=mod
        full=x**p-1
        assert all(val(full,q)==p for q in (p,*qs))
        other=None
        for q in primes:
            if q==p or q in qs or full%q:continue
            if val(full,q)%p:
                other=q;break
        rows.append(dict(p=p,completed_q=';'.join(map(str,(p,*qs))),
                         all_selected_vq=p,x=str(x),x_digits=len(str(x)),
                         other_obstructing_q_le_cap=other or ''))
    write_csv(out/'DkMath_gauge_v3_crt.csv',rows,list(rows[0]))
    return rows


def escaped_prime(primes,out):
    # This construction makes EVERY prime q<=B have v_q(x^p-1)=p,
    # yet x^p-1 is not a pth power. A large prime obstruction is forced.
    rows=[]
    for p in (3,5,7):
        for B in (7,17,31,97,251):
            small=[q for q in primes if q<=B]
            assert p in small
            M=prod(q for q in small if q!=p)
            g=p**(p-1)*M**p;x=g+1
            r=R(p,x,1);k=r//p
            assert k>1 and val(r,p)==1
            assert all(k%q!=0 for q in small)
            assert all(val(g*r,q)==p for q in small)
            assert (x-1)**p < x**p-1 < x**p
            hit=None
            for q in primes:
                if q<=B or k%q:continue
                if val(k,q)%p:
                    assert q%p==1 and order_if_divides_n(x,1,q,p)==p
                    hit=(q,val(k,q));break
            rows.append(dict(p=p,small_prime_bound=B,small_prime_count=len(small),
                x_digits=len(str(x)),R_div_p_digits=len(str(k)),
                all_q_le_B_have_exact_valuation_p=True,
                R_div_p_has_no_small_prime_factor=True,
                detected_escaping_q=hit[0] if hit else '',
                escaping_q_valuation=hit[1] if hit else '',
                q_above_B_with_nonmultiple_p_valuation='mathematically guaranteed'))
    write_csv(out/'DkMath_gauge_v3_prime_escape.csv',rows,list(rows[0]))
    return rows


def primality_by_trial(q):
    if q<2:return False
    for d in range(2,isqrt(q)+1):
        if q%d==0:return False
    return True


def note(stats,rare,target,crtrows,escape,out,args):
    p5=30762501251
    assert primality_by_trial(p5)
    assert (626**5-1)==5**5*p5
    t_by={p:[r for r in target if r['p']==p] for p in (3,5,7,11,13,17)}
    lines=['# DkMath 指数ゲージ・冪差余因子 数値実験 v3',
           '', '対象：`(x^n-y^n)=(x-y)R_n` の付値補填、Prime Address と完成負債。',
           'すべて Python の任意精度整数による計算。Lean ビルドは実施していない。',
           f'実行条件：`--bound {args.bound} --max-degree {args.max_degree} --prime-bound {args.prime_bound} --target-y-max {args.target_y_max}`。',
           '', '## 1. 前回の探索空白を埋める',
           '', '奇素数 p について `g=x-y=p^(p-1)`、`gcd(y,p)=1` とすると LTE から',
           '`v_p(g)=p-1`、`v_p(R_p)=1`、`v_p(x^p-y^p)=p`。',
           'したがって局所的な p 乗完成はすべての奇素数次数で構成可能。',
           '', '| p | g | 検査 y の数 | q<=探索上限で別素数の不足を検出 | y=1 の最初の q |',
           '|---:|---:|---:|---:|---:|']
    for p,rows in t_by.items():
        c=sum(bool(r['first_other_obstruction_q_le_cap']) for r in rows)
        y1=next(r for r in rows if r['y']==1)
        lines.append(f'| {p} | {p**(p-1)} | {len(rows)} | {c} | {y1["first_other_obstruction_q_le_cap"] or "未検出"} |')
    lines+=['', '注：未検出は完全冪の証拠ではなく、有限素数走査の限界。',
            '厳密な例：`626^5 - 1 = 5^5 × 30762501251`。後者は試し割りで素数と確認。',
            '小素数 3000 以下だけを見ても、この五乗の失敗理由は見落とされる。',
            '', '## 2. CRT による複数の素数での同時完成',
            '', 'q≡1 (mod p) の素数 q について、位数 p の根を q^p まで持ち上げ、',
            '`v_q(x^p-1)=p` を強制できる。互いに素な法を CRT で同時に満たす。',
            '', '| p | 付値が p に揃った素数 | x の桁数 | 残った最初の q<=探索上限 |',
            '|---:|---|---:|---:|']
    for r in crtrows:
        lines.append(f'| {r["p"]} | {r["completed_q"]} | {r["x_digits"]} | {r["other_obstructing_q_le_cap"] or "未検出"} |')
    lines+=['', '結論：選んだ有限個の素数を局所的に同時完成させても、全体の完全冪は保証されない。',
            '', '## 3. もっと強い数値構成：負債を小素数から一掃して外へ追い出す',
            '', 'p を奇素数、B>=p とし `M=prod(q<=B, q prime, q!=p)`、',
            '`g=p^(p-1) M^p`、`x=g+1`、`y=1` とする。すると、',
            '', '- `R_p(x,1) = p K`、`gcd(K, prod(q<=B))=1`。',
            '- 全素数 `q<=B` で `v_q(x^p-1)=p`（すべて局所完済）。',
            '- しかし `(x-1)^p < x^p-1 < x^p` より `x^p-1` は p 乗数でない。',
            '- よって必ず `q>B` で `v_q(K)` が p の倍数でない素数が存在する。',
            '- この q は `ord_q(x)=p` より `q≡1 (mod p)` を満たす。',
            '', '| p | B | 小素数の個数 | x の桁数 | 発見した q>B（なければ未検出） |',
            '|---:|---:|---:|---:|---:|']
    for r in escape:
        lines.append(f'| {r["p"]} | {r["small_prime_bound"]} | {r["small_prime_count"]} | {r["x_digits"]} | {r["detected_escaping_q"] or "未検出"} |')
    lines+=['', '最後の「q>B が必ず存在する」は計算探索ではなく、上の不等式と素因数分解からの数学的帰結。',
            'ただし一般の FLT の証明ではない。特に y=1 の特別な状況を利用している。',
            '', '## 4. 小領域の全件監査と原始素数',
            '', '| n | 原始的な組 | 小素数で非完全冪確認 | 原始素数検出の組 | 原始素数の付値>=2 の組 |',
            '|---:|---:|---:|---:|---:|']
    for r in stats:
        lines.append(f'| {r["n"]} | {r["pairs"]} | {r["obstructed_by_q_le_cap"]} | {r["primitive_prime_detected_pairs"]} | {r["primitive_valuation_ge_2_pairs"]} |')
    lines+=['', '原始素数とは、`q|R_n` かつ `ord_q(x/y)=n` の素数。検査上限を越す原始素数は数えられない。',
            '例：`R_3(18,1)=343=7^3`。原始素数 7 自体は既に 3 乗として完成している。',
            'だが `18^3-1=17×7^3` で、素数17の付値が残る。',
            '', '## 5. 研究判断',
            '', '「どれか一つの素数が常に足りない」では不十分。',
            'むしろ **任意の有限な小素数の負債を完済しても、より大きな素数に未完成の付値が現れる** という構造を観察できた。',
            'ただしこの構成は既知の初等数論で説明でき、FLT 一般の不可能性は導いていない。',
            '', '次は元の両端に両方の正の p 乗がある一般の `x^p-y^p=z^p` 仮定で、',
            '素数住所・新しい原始素数の出現と、降下写像が同時に保存できるか検討する。',
            '', '## 6. ファイル',
            '', '- `DkMath_exponent_gauge_experiment_v3.py`（再現可能なスクリプト）',
            '- `DkMath_gauge_v3_targeted.csv`（局所補填）',
            '- `DkMath_gauge_v3_crt.csv`（複数素数 CRT）',
            '- `DkMath_gauge_v3_prime_escape.csv`（大きな素数への脱出）',
            '- `DkMath_gauge_v3_sweep.csv`（全件統計）',
            '- `DkMath_gauge_v3_primitive_rare.csv`（原始素数の高付値例）',
            '']
    (out/'DkMath_gauge_v3_research_note.md').write_text('\n'.join(lines),encoding='utf-8')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--bound',type=int,default=90)
    ap.add_argument('--max-degree',type=int,default=12)
    ap.add_argument('--prime-bound',type=int,default=3000)
    ap.add_argument('--target-y-max',type=int,default=60)
    ap.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    a=ap.parse_args()
    assert a.bound>=3 and a.max_degree>=5 and a.prime_bound>=251 and a.target_y_max>=1
    o=a.output_dir;o.mkdir(exist_ok=True,parents=True)
    primes=primes_through(a.prime_bound)
    targeted_rows=targeted(primes,a.target_y_max,o)
    crt_rows=simultaneous(primes,o)
    escape_rows=escaped_prime(primes_through(max(12000,a.prime_bound)),o)
    stats,rare=initial_sweep(primes,a.bound,a.max_degree,o)
    note(stats,rare,targeted_rows,crt_rows,escape_rows,o,a)
    for r in targeted_rows:
        if r['y']==1: print('TARGET',r['p'],r['x'],r['first_other_obstruction_q_le_cap'] or 'undetected')
    for r in crt_rows: print('CRT',r['p'],r['completed_q'],r['other_obstructing_q_le_cap'] or 'undetected')
    for r in escape_rows:
        print('ESCAPE',r['p'],r['small_prime_bound'],r['x_digits'],r['detected_escaping_q'] or 'undetected')
    for r in stats: print('SWEEP',r)
    print('WROTE',o)

if __name__=='__main__':main()

# Collatz PetalBridge Retention Tower Scan

- max modulus: `1024`
- scanned levels: `7`
- all transitions matched expected law: `True`

## Law

For depth `d >= 3`:

```text
parent:       2^d - 1 mod 2^d
recovery:     2^d - 1 mod 2^(d+1)
continuation: 2^(d+1) - 1 mod 2^(d+1)

T1(recovery)     = 2^(d-1) - 1 mod 2^d
T1(continuation) = 2^d - 1 mod 2^d
```

where `T1(x) = (3*x + 1) / 2` is the exact height-one visible step.

## Table

| d | parent | recovery child | continuation child | recovery target | continuation target | ok |
|---:|---:|---:|---:|---:|---:|:---:|
| 3 | 7 mod 8 | 7 mod 16 | 15 mod 16 | 3 mod 8 | 7 mod 8 | True |
| 4 | 15 mod 16 | 15 mod 32 | 31 mod 32 | 7 mod 16 | 15 mod 16 | True |
| 5 | 31 mod 32 | 31 mod 64 | 63 mod 64 | 15 mod 32 | 31 mod 32 | True |
| 6 | 63 mod 64 | 63 mod 128 | 127 mod 128 | 31 mod 64 | 63 mod 64 | True |
| 7 | 127 mod 128 | 127 mod 256 | 255 mod 256 | 63 mod 128 | 127 mod 128 | True |
| 8 | 255 mod 256 | 255 mod 512 | 511 mod 512 | 127 mod 256 | 255 mod 256 | True |
| 9 | 511 mod 512 | 511 mod 1024 | 1023 mod 1024 | 255 mod 512 | 511 mod 512 | True |

## Lean Inference

The table supports replacing one-off named arithmetic anchors by the
existing generic residue theorem whenever the call site can tolerate
the power-of-two parameters.  For readability, the concrete Lean
aliases remain useful at the active frontier levels.
